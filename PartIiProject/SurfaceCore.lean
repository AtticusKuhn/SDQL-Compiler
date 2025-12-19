import PartIiProject.HList
import PartIiProject.Term
import PartIiProject.Mem
import Std

namespace PartIiProject

-- Re-export SourceLocation from Term.lean for convenience
-- (SourceLocation is now defined in Term.lean for sharing with core terms)

/-
Surface layer with named products (records) and field selection by name.
We keep terms minimal and focus on named records/projection, plus a
surface→core translation that erases names to positional records.
-/

inductive SurfaceTy : Type where
  | bool : SurfaceTy
  | int : SurfaceTy
  | real : SurfaceTy
  | date : SurfaceTy
  | string : SurfaceTy
  | dict : SurfaceTy → SurfaceTy → SurfaceTy
  -- | record : Std.TreeMap.Raw String SurfaceTy → SurfaceTy
  | record : (List (String × SurfaceTy)) → SurfaceTy
  deriving Inhabited, Repr

abbrev Schema := List (String × SurfaceTy)
-- abbrev Schema := Std.TreeMap.Raw String SurfaceTy

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
  | boolA   : SAdd .bool
  | intA    : SAdd .int
  | realA   : SAdd .real
  | dateA   : SAdd .date
  | stringA : SAdd .string
  | dictA   {k v : SurfaceTy} (av : SAdd v) : SAdd (.dict k v)
  | recordA {σ : Schema} : (HList (fun (_, t) => SAdd t) σ ) →  SAdd (.record σ)

inductive SScale : SurfaceTy → SurfaceTy → Type where
  | boolS : SScale SurfaceTy.bool SurfaceTy.bool
  | intS : SScale SurfaceTy.int SurfaceTy.int
  | realS : SScale SurfaceTy.real SurfaceTy.real
  | dictS {sc dom range : SurfaceTy} (sRange : SScale sc range) : SScale sc (SurfaceTy.dict dom range)
  | recordS {sc : SurfaceTy} {σ : Schema}
      (fields : (p : String × SurfaceTy) → Mem p σ → SScale sc p.snd) :
      SScale sc (SurfaceTy.record σ)


-- def toHList {T : Type} {l : List T} {ftype : T → Type} (f : ∀ (t : T), t ∈ l → ftype t) : HList ftype l :=
--   match l with
--     | [] => HList.nil
--     | t :: ts => HList.cons (f t (by simp only [List.mem_cons, true_or])) (toHList (fun t' => f t' ∘ List.mem_cons_of_mem t))

-- Surface tensor shape (matches core `tensor` on erased types)
-- This function computes the type of (e1 * e2) where e1 : a and e2 : b
-- marked unsafe because the termination checker cannot prove that stensor terminates

@[simp, reducible]
unsafe def stensor (a b : SurfaceTy) : SurfaceTy :=
  match a with
  | .dict dom range => .dict dom (stensor range b)
  | .record σ => .record (σ.map (fun (n,t) => (n, stensor t b)))
  | _ => b

unsafe def stensor_real_real : stensor .real .real = .real := rfl

inductive SBuiltin : SurfaceTy → SurfaceTy → Type where
  | And : SBuiltin (.record [("_1", .bool), ("_2", .bool)]) .bool
  | Or  : SBuiltin (.record [("_1", .bool), ("_2", .bool)]) .bool
  | Eq {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) .bool
  | Leq {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) .bool  -- <=
  | Sub {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) t      -- subtraction
  | StrEndsWith : SBuiltin (.record [("_1", .string), ("_2", .string)]) .bool
  | Dom {dom range : SurfaceTy} : SBuiltin (.dict dom range) (.dict dom .bool)
  | Range : SBuiltin .int (.dict .int .bool)
  | DateLit (yyyymmdd : Int) : SBuiltin (.record []) .date  -- date(YYYYMMDD)
  | Concat (σ1 σ2 : Schema) : SBuiltin (.record [("_1", .record σ1), ("_2", .record σ2)]) (.record (σ1 ++ σ2))  -- concat two records

/-
  Surface terms (PHOAS) with source location tracking.

  `STermLoc'` pairs a term with its source location from the syntax macro.
  `STerm'` is the underlying term structure.

  These are mutually inductive: `STermLoc'` wraps `STerm'`, and `STerm'`
  recursively contains `STermLoc'` in its sub-expressions.
-/
mutual
  /-- A term paired with its source location -/
  unsafe inductive STermLoc' (rep : SurfaceTy → Type) {n : Nat} (fvar : Fin n → SurfaceTy) : SurfaceTy → Type where
    | mk : {ty : SurfaceTy} → (loc : SourceLocation) → STerm' rep fvar ty → STermLoc' rep fvar ty

  /-- Core surface term constructors -/
  unsafe inductive STerm' (rep : SurfaceTy → Type) {n : Nat} (fvar : Fin n → SurfaceTy) : SurfaceTy → Type where
    | var   : {ty : SurfaceTy} → rep ty → STerm' rep fvar ty
    | freeVariable : (f : Fin n) → STerm' rep fvar (fvar f)
    | constInt : Int → STerm' rep fvar SurfaceTy.int
    | constReal : Float → STerm' rep fvar SurfaceTy.real
    | constBool : Bool → STerm' rep fvar SurfaceTy.bool
    | constString : String → STerm' rep fvar SurfaceTy.string
    | not : STermLoc' rep fvar SurfaceTy.bool → STerm' rep fvar SurfaceTy.bool
    | ite : {ty : SurfaceTy} → STermLoc' rep fvar SurfaceTy.bool → STermLoc' rep fvar ty → STermLoc' rep fvar ty → STerm' rep fvar ty
    | letin : {ty₁ ty₂ : SurfaceTy} → STermLoc' rep fvar ty₁ → (rep ty₁ → STermLoc' rep fvar ty₂) → STerm' rep fvar ty₂
    | add : {ty : SurfaceTy} → (a : SAdd ty) → STermLoc' rep fvar ty → STermLoc' rep fvar ty → STerm' rep fvar ty
    | mul : {sc t1 t2 : SurfaceTy} → (s1 : SScale sc t1) → (s2 : SScale sc t2)
        → STermLoc' rep fvar t1 → STermLoc' rep fvar t2 → STerm' rep fvar (stensor t1 t2)
    | emptyDict : {domain ran : SurfaceTy} → STerm' rep fvar (SurfaceTy.dict domain ran)
    | dictInsert : {dom range : SurfaceTy} → STermLoc' rep fvar dom → STermLoc' rep fvar range → STermLoc' rep fvar (SurfaceTy.dict dom range) → STerm' rep fvar (SurfaceTy.dict dom range)
    | lookup : {dom range : SurfaceTy} → (aRange : SAdd range) → STermLoc' rep fvar (SurfaceTy.dict dom range) → STermLoc' rep fvar dom → STerm' rep fvar range
    | sum : {dom range ty : SurfaceTy} → (a : SAdd ty) → STermLoc' rep fvar (SurfaceTy.dict dom range) → (rep dom → rep range → STermLoc' rep fvar ty) → STerm' rep fvar ty
    | constRecord : {l : Schema}
        → HList (fun (_, t) => STermLoc' rep fvar t) l
        → STerm' rep fvar (.record l)
    | projByName {nm t} : {σ : Schema}
        → (p : HasField σ nm t)
        → STermLoc' rep fvar (.record σ)
        → STerm' rep fvar t
    | builtin : {a b : SurfaceTy} → SBuiltin a b → STermLoc' rep fvar a → STerm' rep fvar b
end

namespace STermLoc'
  /-- Extract the source location from a located term -/
  unsafe def loc {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy} {ty : SurfaceTy}
      (e : STermLoc' rep fvar ty) : SourceLocation :=
    match e with
    | mk l _ => l

  /-- Extract the underlying term from a located term -/
  unsafe def term {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy} {ty : SurfaceTy}
      (e : STermLoc' rep fvar ty) : STerm' rep fvar ty :=
    match e with
    | mk _ t => t

  /-- Create a located term with an unknown location -/
  unsafe def withUnknownLoc {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy} {ty : SurfaceTy}
      (t : STerm' rep fvar ty) : STermLoc' rep fvar ty :=
    mk SourceLocation.unknown t
end STermLoc'


/-- A closed surface term (no free representation variables) -/
unsafe def STerm {n : Nat} (fvar : Fin n → SurfaceTy) (ty : SurfaceTy) :=
  {rep : SurfaceTy → Type} → STerm' rep fvar ty

/-- A closed surface term with location -/
unsafe def STermLoc {n : Nat} (fvar : Fin n → SurfaceTy) (ty : SurfaceTy) :=
  {rep : SurfaceTy → Type} → STermLoc' rep fvar ty

/-- A program with located terms -/
unsafe structure SProg : Type 1 where
  t : SurfaceTy
  n : Nat
  fvar : Fin n → SurfaceTy
  term : {rep : SurfaceTy → Type} → STermLoc' rep fvar t
  loadPaths : Fin n → String


def f0 (f : Fin 0) : SurfaceTy  := nomatch f

/- Surface → Core translation -/
namespace ToCore

-- Helper to project and coerce the result type via an index/equality proof
-- Works with TermLoc' (takes a located record and returns an unlocated projected term)
def projCast {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty} {l : List Ty}
    (r : TermLoc' rep fvar (Ty.record l)) (i : Nat) {t : Ty}
    (h : l.getD i Ty.int = t) : Term' rep fvar t :=
  by cases h; simpa using (Term'.proj l r i)

mutual
  def ty : SurfaceTy → Ty
    | .bool => .bool
    | .int => .int
    | .real => .real
    | .date => .date
    | .string => .string
    | .dict k v => .dict (ty k) (ty v)
    | .record σ => .record (tyFields σ)

  def tyFields : Schema → List Ty
    | [] => []
    | (_, t) :: σ => ty t :: tyFields σ
end

-- Translate surface semimodule evidence to core
 def toCoreAdd : {t : SurfaceTy} → SAdd t → AddM (ty t)
  | _, SAdd.boolA   => AddM.boolA
  | _, SAdd.intA    => AddM.intA
  | _, SAdd.realA   => AddM.realA
  | _, SAdd.dateA   => AddM.dateA
  | _, SAdd.stringA => AddM.stringA
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

-- (unused helper removed)

-- def mem_empty {α : Type} {x : α} : ¬ (Mem x ([] : List α)) :=
--   fun h => by cases h

def toCoreScale : {sc t : SurfaceTy} → SScale sc t → ScaleM (ty sc) (ty t)
  | _, _, SScale.boolS => ScaleM.boolS
  | _, _, SScale.intS => ScaleM.intS
  | _, _, SScale.realS => ScaleM.realS
  | _, _, @SScale.dictS sc dom range sRange => ScaleM.dictS (toCoreScale sRange)
  | _, _, @SScale.recordS sc σ fields =>
      -- Build the per-field scaling function by recursion on the schema,
      -- using the typed membership `Mem` so we can pattern match.
      let rec go
          (σ : Schema)
          (flds : ∀ (p : String × SurfaceTy), Mem p σ → SScale sc p.snd)
          : ∀ (t' : Ty), Mem t' (tyFields σ) → ScaleM (ty sc) t'
        :=
        match σ with
        | [] =>
            fun _ h => by cases h
        | (nm, tt) :: σ' =>
            fun t' (h : Mem t' (tyFields ((nm, tt) :: σ'))) => by
              -- Reexpress membership to expose the head of the list.
              have h0 : Mem t' (ty tt :: tyFields σ') := by
                exact h
              cases h0 with
              | head _ =>
                  -- Here, definitionaly, t' = ty tt.
                  simpa using (toCoreScale (flds (nm, tt) (Mem.head σ')))
              | tail _ hRest =>
                  -- Recurse on the tail with a restricted field function.
                  let flds' : ∀ (p : String × SurfaceTy), Mem p σ' → SScale sc p.snd :=
                    fun p hp => flds p (Mem.tail (nm, tt) hp)
                  exact go σ' flds' t' hRest
      ScaleM.recordS (go σ fields)

@[simp]
theorem tyFields_cons (nm : String) (t : SurfaceTy) (σ : Schema) :
    tyFields ((nm, t) :: σ) = ty t :: tyFields σ := rfl

-- tyFields distributes over concatenation
theorem tyFields_append (σ1 σ2 : Schema) :
    tyFields (σ1 ++ σ2) = tyFields σ1 ++ tyFields σ2 := by
  induction σ1 with
  | nil => simp [tyFields]
  | cons h t ih =>
    simp [tyFields, ih]

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

-- Relate surface `stensor` to core `tensor`
mutual
  unsafe def ty_stensor_eq : ∀ (a b : SurfaceTy), ty (stensor a b) = tensor (ty a) (ty b)
    | .bool, b => rfl
    | .int, b => rfl
    | .real, b => rfl
    | .date, b => rfl
    | .string, b => rfl
    | .dict dom range, b => by
        rw [ty]
        rw [ty_stensor_eq]
        rw [ty]
        rw [tensor]
    | .record σ, b => by
        rw [ty]
        rw [tyFields_map_stensor]
        rw [ty]
        rw [tensor]

  unsafe def tyFields_map_stensor
      : ∀ (σ : Schema) (b : SurfaceTy),
        tyFields (σ.map (fun (p : String × SurfaceTy) => (p.fst, stensor p.snd b)))
          = (tyFields σ).map (fun t => tensor t (ty b))
    | [], b => rfl
    | (nm, t) :: σ, b => by
        -- Head by `ty_stensor_eq`, tail by recursion

        simp [tyFields_map_stensor,ty_stensor_eq, -stensor]
end


mutual
  /-- Translate a list of located record fields, preserving locations -/
  unsafe def trRecordFields {rep : Ty → Type} {n : Nat}
      (fvar : Fin n → SurfaceTy)
      : {l : Schema}
      → HList (fun (_, t) => STermLoc' (rep ∘ ty) (fun i => fvar i) t) l
      → HList (TermLoc' rep (fun i => ty (fvar i))) (tyFields l)
    | [], HList.nil => HList.nil
    | (_ :: _), HList.cons h t =>
        HList.cons (trLoc (fvar := fvar) h) (trRecordFields (fvar := fvar) t)

  /-- Translate a located surface term to core, preserving location info -/
  unsafe def trLoc {rep : Ty → Type} {n : Nat}
      {fvar : Fin n → SurfaceTy} {t : SurfaceTy}
      (e : STermLoc' (rep ∘ ty) fvar t) : TermLoc' rep (ty ∘ fvar) (ty t) :=
    match e with
    | STermLoc'.mk loc inner => TermLoc'.mk loc (tr loc inner)

  /-- Translate an unlocated surface term to core, using provided location -/
  unsafe def tr {rep : Ty → Type} {n : Nat}
      {fvar : Fin n → SurfaceTy} {t : SurfaceTy}
      (loc : SourceLocation)
      (e : STerm' (rep ∘ ty) fvar t) : Term' rep (ty ∘ fvar) (ty t) :=
    match e with
    | STerm'.var v => Term'.var v
    | STerm'.freeVariable i => Term'.freeVariable i
    | STerm'.constInt i => Term'.constInt i
    | STerm'.constReal r => Term'.constReal r
    | STerm'.constBool b => Term'.constBool b
    | STerm'.constString s => Term'.constString s
    | STerm'.not e => Term'.not (trLoc e)
    | STerm'.ite c t u => Term'.ite (trLoc c) (trLoc t) (trLoc u)
    | STerm'.letin t f => Term'.letin (trLoc t) (fun v => trLoc (f v))
    | @STerm'.add _ _ _ ty a t1 t2 => Term'.add (toCoreAdd a) (trLoc t1) (trLoc t2)
    | STerm'.emptyDict => Term'.emptyDict
    | STerm'.dictInsert k v d => Term'.dictInsert (trLoc k) (trLoc v) (trLoc d)
    | STerm'.lookup aRange d k => Term'.lookup (toCoreAdd aRange) (trLoc d) (trLoc k)
    | STerm'.sum a d f =>
        Term'.sum (toCoreAdd a) (trLoc d) (fun kd vd => trLoc (f kd vd))
    | @STerm'.mul _ _ _ sc t1 t2 s1 s2 e1 e2 =>
        -- Cast the result type via `ty_stensor_eq` to match core `tensor`.
        by
          have hmul : Term' rep (fun i => ty (fvar i)) (tensor (ty t1) (ty t2)) :=
            Term'.mul (toCoreScale s1) (toCoreScale s2) (trLoc e1) (trLoc e2)
          simpa [ty_stensor_eq, -stensor] using hmul
    | STerm'.constRecord (l := l) fields =>
        by
          have h : Term' rep (fun i => ty (fvar i)) (Ty.record (tyFields l)) :=
            Term'.constRecord (trRecordFields (fvar := fvar) fields)
          exact h
    | STerm'.projByName (σ := σ) (nm := _nm) (t := t) p r =>
        -- compute positional index from field proof and project
        let idx := HasField.index p
        have rr : TermLoc' rep (fun i => ty (fvar i)) (Ty.record (tyFields σ)) :=
          trLoc r
        have pr : Term' rep (fun i => ty (fvar i)) ((tyFields σ).getD idx Ty.int) :=
          Term'.proj (tyFields σ) rr idx
        -- Coerce the projected type to the named field's core type via the index lemma
        show Term' rep (ty ∘ fvar) (ty t) from
          (by
            simpa using (projCast (rep := rep) (fvar := fun i => ty (fvar i)) rr idx (HasField.index_getD_ty (σ := σ) (nm := _nm) (t := t) p)))
    | STerm'.builtin b a =>
        match b with
        | SBuiltin.And => Term'.builtin BuiltinFn.And (trLoc a)
        | SBuiltin.Or  => Term'.builtin BuiltinFn.Or (trLoc a)
        | @SBuiltin.Eq (t := t) =>
            Term'.builtin (BuiltinFn.Eq (ty t)) (trLoc a)
        | @SBuiltin.Leq (t := t) =>
            Term'.builtin (BuiltinFn.Leq (ty t)) (trLoc a)
        | @SBuiltin.Sub (t := t) =>
            Term'.builtin (BuiltinFn.Sub (ty t)) (trLoc a)
        | SBuiltin.StrEndsWith => Term'.builtin BuiltinFn.StrEndsWith (trLoc a)
        | @SBuiltin.Dom dom range => Term'.builtin (BuiltinFn.Dom (dom := ty dom) (range := ty range)) (trLoc a)
        | SBuiltin.Range => Term'.builtin BuiltinFn.Range (trLoc a)
        | SBuiltin.DateLit yyyymmdd => Term'.builtin (BuiltinFn.DateLit yyyymmdd) (trLoc a)
        | @SBuiltin.Concat σ1 σ2 =>
            -- Translate surface Concat to core Concat, adjusting types via tyFields_append
            -- The result type of core Concat is `Ty.record (l1 ++ l2)`
            -- The expected type is `ty (SurfaceTy.record (σ1 ++ σ2))` = `Ty.record (tyFields (σ1 ++ σ2))`
            -- We need to show these are equal via tyFields_append
            by
              have h : tyFields σ1 ++ tyFields σ2 = tyFields (σ1 ++ σ2) := by
                rw [tyFields_append]
              rw [ty, ← h]
              exact Term'.builtin (BuiltinFn.Concat (tyFields σ1) (tyFields σ2)) (trLoc a)

end

/-- Translate a program with located terms to core, preserving locations -/
unsafe def trProg (p : SProg) : Prog :=
  { t := ty p.t
    n := p.n
    fvar := ty ∘ p.fvar
    term := trLoc p.term
    loadPaths := p.loadPaths }

-- Examples updated for STermLoc'
unsafe def ex1 : STermLoc' (fun _ => String) f0 (.record [("name", .string), ("age", .int)]) :=
  STermLoc'.mk SourceLocation.unknown
    (.constRecord
      (.cons (STermLoc'.mk SourceLocation.unknown (.constString "Alice"))
        (.cons (STermLoc'.mk SourceLocation.unknown (.constInt 30)) .nil)))

unsafe def ex2 : STermLoc' (fun _ => String) f0 .string :=
  STermLoc'.mk SourceLocation.unknown (.projByName HasField.here ex1)

#eval TermLoc'.show (trLoc (fvar := f0) ex1)
#eval TermLoc'.show (trLoc (fvar := f0) ex2)
-- Note: denote example removed as it requires fully instantiated rep type

end ToCore

end PartIiProject
