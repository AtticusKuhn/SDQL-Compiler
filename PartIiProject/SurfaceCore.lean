import PartIiProject.HList
import PartIiProject.Term

namespace PartIiProject

/-
Surface layer with named products (records) and field selection by name.
We keep terms minimal and focus on named records/projection, plus a
surface→core translation that erases names to positional records.
-/

inductive SurfaceTy : Type where
  | bool : SurfaceTy
  | record : (List (String × SurfaceTy)) → SurfaceTy
  | string : SurfaceTy
  | int : SurfaceTy
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
inductive STerm' (rep : SurfaceTy → Type) {n : Nat} (fvar : Fin n → SurfaceTy) : SurfaceTy → Type where
  | var   : {ty : SurfaceTy} → rep ty → STerm' rep fvar ty
  | freeVariable : (f : Fin n) → STerm' rep fvar (fvar f)
  | constInt : Int → STerm' rep fvar SurfaceTy.int
  | constBool : Bool → STerm' rep fvar SurfaceTy.bool
  | constString : String → STerm' rep fvar SurfaceTy.string
  | constRecord : {l : Schema}
      → HList (fun (_, t) => STerm' rep fvar t) l
      → STerm' rep fvar (.record l)
  | projByName {nm t} : {σ : Schema}
      → (p : HasField σ nm t)
      → STerm' rep fvar (.record σ)
      → STerm' rep fvar t

def STerm {n : Nat} (fvar : Fin n → SurfaceTy) (ty : SurfaceTy) :=
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
    | .record σ => .record (tyFields σ)

  def tyFields : Schema → List Ty
    | [] => []
    | (_, t) :: σ => ty t :: tyFields σ
end

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

mutual
  unsafe def trRecordFields {rep : Ty → Type} {n : Nat}
      (fvar : Fin n → SurfaceTy)
      : {l : Schema}
      → HList (fun (_, t) => STerm' (rep ∘ ty) (fun i => fvar i) t) l
      → HList (Term' rep (fun i => ty (fvar i))) (tyFields l)
    | [], HList.nil => HList.nil
    | (_ :: l), HList.cons h t =>
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
