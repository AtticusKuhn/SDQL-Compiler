import PartIiProject.HList
import PartIiProject.Term

namespace PartIiProject
open Classical
set_option maxRecDepth 4096

/-
Surface layer with named products (records) and field selection by name.
We keep terms minimal and focus on named records/projection, plus a
surface→core translation that erases names to positional records.
-/

inductive SurfaceTy : Type where
  | bool : SurfaceTy
  | int : SurfaceTy
  | string : SurfaceTy
  | dict : SurfaceTy → SurfaceTy → SurfaceTy
  | record : (List (String × SurfaceTy)) → SurfaceTy
  deriving Inhabited

abbrev Schema := List (String × SurfaceTy)

-- Field-membership proof with index extraction
inductive HasField : Schema → String → SurfaceTy → Type where
  | here  {nm σ t} : HasField (⟨nm, t⟩ :: σ) nm t
  | there {σ nm' t' nm t} (p : HasField σ nm t) : HasField (⟨nm', t'⟩ :: σ) nm t

def HasField.index : {σ : Schema} → {n : String} → {t : SurfaceTy} → HasField σ n t → Nat
  | _, _, _, HasField.here => 0
  | _, _, _, HasField.there p => HasField.index p + 1

-- Surface terms (PHOAS) with named records only
-- Surface-level semimodule evidence (mirrors core AddM/ScaleM)
inductive SAdd : SurfaceTy → Type where
  | boolA : SAdd .bool
  | intA  : SAdd .int
  | dictA {k v : SurfaceTy} (av : SAdd v) : SAdd (.dict k v)
  | recordA {σ : Schema} : (HList (fun (_, t) => SAdd t) σ) →  SAdd (.record σ)

inductive SScale : SurfaceTy → SurfaceTy → Type where
  | boolS : SScale SurfaceTy.bool SurfaceTy.bool
  | intS : SScale SurfaceTy.int SurfaceTy.int
  | dictS {sc dom range : SurfaceTy} (sRange : SScale sc range) : SScale sc (SurfaceTy.dict dom range)


-- def toHList {T : Type} {l : List T} {ftype : T → Type} (f : ∀ (t : T), t ∈ l → ftype t) : HList ftype l :=
--   match l with
--     | [] => HList.nil
--     | t :: ts => HList.cons (f t (by simp only [List.mem_cons, true_or])) (toHList (fun t' => f t' ∘ List.mem_cons_of_mem t))

-- Surface tensor shape (matches core `tensor` on erased types)
-- marked unsafe because the termination checker cannot prove that stensor terminates

@[simp, reducible]
unsafe def stensor (a b : SurfaceTy) : SurfaceTy :=
  match a with
  | .dict dom range => .dict dom (stensor range b)
  | .record σ => .record (σ.map (fun (nm, t) => (nm, stensor t b)))
  | _ => b

unsafe inductive STerm' (rep : SurfaceTy → Type) {n : Nat} (fvar : Fin n → SurfaceTy) : SurfaceTy → Type where
  | var   : {ty : SurfaceTy} → rep ty → STerm' rep fvar ty
  | freeVariable : (f : Fin n) → STerm' rep fvar (fvar f)
  | constInt : Int → STerm' rep fvar SurfaceTy.int
  | constBool : Bool → STerm' rep fvar SurfaceTy.bool
  | constString : String → STerm' rep fvar SurfaceTy.string
  | not : STerm' rep fvar SurfaceTy.bool → STerm' rep fvar SurfaceTy.bool
  | ite : {ty : SurfaceTy} → STerm' rep fvar SurfaceTy.bool → STerm' rep fvar ty → STerm' rep fvar ty → STerm' rep fvar ty
  | letin : {ty₁ ty₂ : SurfaceTy} → STerm' rep fvar ty₁ → (rep ty₁ → STerm' rep fvar ty₂) → STerm' rep fvar ty₂
  | add : {ty : SurfaceTy} → (a : SAdd ty) → STerm' rep fvar ty → STerm' rep fvar ty → STerm' rep fvar ty
  | emptyDict : {dom range : SurfaceTy} → STerm' rep fvar (SurfaceTy.dict dom range)
  | dictInsert : {dom range : SurfaceTy} → STerm' rep fvar dom → STerm' rep fvar range → STerm' rep fvar (SurfaceTy.dict dom range) → STerm' rep fvar (SurfaceTy.dict dom range)
  | lookup : {dom range : SurfaceTy} → (aRange : SAdd range) → STerm' rep fvar (SurfaceTy.dict dom range) → STerm' rep fvar dom → STerm' rep fvar range
  | sum : {dom range ty : SurfaceTy} → (a : SAdd ty) → STerm' rep fvar (SurfaceTy.dict dom range) → (rep dom → rep range → STerm' rep fvar ty) → STerm' rep fvar ty
  | constRecord : {l : Schema}
      → HList (fun (_, t) => STerm' rep fvar t) l
      → STerm' rep fvar (.record l)
  | projByName {nm t} : {σ : Schema}
      → (p : HasField σ nm t)
      → STerm' rep fvar (.record σ)
      → STerm' rep fvar t

unsafe def STerm {n : Nat} (fvar : Fin n → SurfaceTy) (ty : SurfaceTy) :=
  {rep : SurfaceTy → Type} → STerm' rep fvar ty

/- Surface → Core translation -/
namespace ToCore

-- Helper to project and coerce the result type via an index/equality proof
def projCast {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty} {l : List Ty}
    (r : Term' rep fvar (Ty.record l)) (i : Nat) {t : Ty}
    (h : l.getD i Ty.int = t) : Term' rep fvar t :=
  by cases h; simpa using (Term'.proj l r i)

mutual
  def ty : SurfaceTy → Ty
    | .bool => .bool
    | .int => .int
    | .string => .string
    | .dict k v => .dict (ty k) (ty v)
    | .record σ => .record (tyFields σ)

  def tyFields : Schema → List Ty
    | [] => []
    | (_, t) :: σ => ty t :: tyFields σ
end

-- Translate surface semimodule evidence to core
def toCoreAdd : {t : SurfaceTy} → SAdd t → AddM (ty t)
  | _, SAdd.boolA => AddM.boolA
  | _, SAdd.intA => AddM.intA
  | _, @SAdd.dictA dom range aRange => AddM.dictA (toCoreAdd aRange)
  | _, @SAdd.recordA σ fields =>
    let rec trFields
      : (σ' : Schema)
      → HList (fun (p : String × SurfaceTy) => SAdd p.snd) σ'
      → HList AddM (tyFields σ')
      | [], HList.nil => HList.nil
      | (_ :: σ'), HList.cons h t =>
          HList.cons (toCoreAdd h) (trFields σ' t)
    AddM.recordA (trFields σ fields)

 def toCoreScale : {sc t : SurfaceTy} → SScale sc t → ScaleM (ty sc) (ty t)
    | _, _, SScale.boolS => ScaleM.boolS
    | _, _, SScale.intS => ScaleM.intS
    | _, _, @SScale.dictS sc dom range sRange => ScaleM.dictS (toCoreScale sRange)

@[simp]
theorem tyFields_cons (nm : String) (t : SurfaceTy) (σ : Schema) :
    tyFields ((nm, t) :: σ) = ty t :: tyFields σ := rfl

@[simp]
theorem List.getD_cons_zero {α} (x : α) (xs : List α) (d : α) :
    (List.getD (x :: xs) 0 d) = x := by
  simp [List.getD]

@[simp]
theorem List.getD_cons_succ {α} (x : α) (xs : List α) (n : Nat) (d : α) :
    (List.getD (x :: xs) (n+1) d) = List.getD xs n d := by
  simp [List.getD]

-- The type at the index computed by `HasField.index` is exactly the field type.
theorem HasField.index_getD_ty
    : ∀ {σ : Schema} {nm : String} {t : SurfaceTy}
        (p : HasField σ nm t),
        (tyFields σ).getD (HasField.index p) Ty.int = ty t
  | (_, t) :: σ, _, _, HasField.here => by
      simp [HasField.index]
  | (nm', t') :: σ, _, _, HasField.there p => by
      simpa [HasField.index] using HasField.index_getD_ty p
-- Note: a lemma relating `stensor` and core `tensor` was previously used in
-- the translation of multiplication. Since the current surface translation
-- does not emit core multiplication directly, we do not need it here.


mutual
  unsafe def trRecordFields {rep : Ty → Type} {n : Nat}
      (fvar : Fin n → SurfaceTy)
      : {l : Schema}
      → HList (fun (_, t) => STerm' (rep ∘ ty) (fun i => fvar i) t) l
      → HList (Term' rep (fun i => ty (fvar i))) (tyFields l)
    | [], HList.nil => HList.nil
    | (_ :: _), HList.cons h t =>
        HList.cons (tr (fvar := fvar) h) (trRecordFields (fvar := fvar) t)

  unsafe def tr {rep : Ty → Type} {n : Nat}
      {fvar : Fin n → SurfaceTy} {t : SurfaceTy}
      (e : STerm' (rep ∘ ty) fvar t) : Term' rep (ty ∘ fvar) (ty t) :=
    match e with
    | STerm'.var v => Term'.var v
    | STerm'.freeVariable i => Term'.freeVariable i
    | STerm'.constInt i => Term'.constInt i
    | STerm'.constBool b => Term'.constBool b
    | STerm'.constString s => Term'.constString s
    | STerm'.not e => Term'.not (tr e)
    | STerm'.ite c t u => Term'.ite (tr c) (tr t) (tr u)
    | STerm'.letin t f => Term'.letin (tr t) (fun v => tr (f v))
    | @STerm'.add _ _ _ ty a t1 t2 => Term'.add (toCoreAdd a) (tr t1) (tr t2)
    | STerm'.emptyDict => Term'.emptyDict
    | STerm'.dictInsert k v d => Term'.dictInsert (tr k) (tr v) (tr d)
    | STerm'.lookup aRange d k => Term'.lookup (toCoreAdd aRange) (tr d) (tr k)
    | STerm'.sum a d f =>
        Term'.sum (toCoreAdd a) (tr d) (fun kd vd => tr (f kd vd))
    | STerm'.constRecord (l := l) fields =>
        by
          have h : Term' rep (fun i => ty (fvar i)) (Ty.record (tyFields l)) :=
            Term'.constRecord (trRecordFields (fvar := fvar) fields)
          exact h
    | STerm'.projByName (σ := σ) (nm := _nm) (t := t) p r =>
        -- compute positional index from field proof and project
        let idx := HasField.index p
        have rr : Term' rep (fun i => ty (fvar i)) (Ty.record (tyFields σ)) :=
          tr r
        have pr : Term' rep (fun i => ty (fvar i)) ((tyFields σ).getD idx Ty.int) :=
          Term'.proj (tyFields σ) rr idx
        -- Coerce the projected type to the named field's core type via the index lemma
        show Term' rep (ty ∘ fvar) (ty t) from
          (by
            simpa using (projCast (rep := rep) (fvar := fun i => ty (fvar i)) rr idx (HasField.index_getD_ty (σ := σ) (nm := _nm) (t := t) p)))

end

end ToCore

end PartIiProject
