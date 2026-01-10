import PartIiProject.Term
import PartIiProject.Mem
import PartIiProject.HList
import PartIiProject.SurfaceCore2

open PartIiProject

/-!
# DeBruijn-indexed Core Terms (Term2)

This module defines a DeBruijn-indexed representation of core terms,
as an alternative to the PHOAS representation in Term.lean.

Key differences from PHOAS (Term.lean):
- Variables are represented by `Mem ty ctx` proofs instead of `rep ty` values
- Context is a `List Ty` instead of being implicit in the `rep` type
- No `fvar` parameter - free variables are handled by extending the context
- No higher-order body functions - bodies are just terms in extended contexts
-/

/-
Core types and related definitions (AddM, ScaleM, tensor, BuiltinFn, etc.)
are imported from Term.lean.
-/

-- ============================================================================
-- DeBruijn-indexed Core Terms
-- ============================================================================

mutual
  /-- A DeBruijn core term with source location -/
  inductive TermLoc2 : (ctx : List Ty) → Ty → Type where
    | mk : {ctx : List Ty} → {ty : Ty} → (loc : SourceLocation) → Term2 ctx ty → TermLoc2 ctx ty

  /-- Record fields for DeBruijn core terms -/
  inductive TermFields2 : (ctx : List Ty) → List Ty → Type where
    | nil : {ctx : List Ty} → TermFields2 ctx []
    | cons : {ctx : List Ty} → {t : Ty} → {rest : List Ty}
        → TermLoc2 ctx t → TermFields2 ctx rest → TermFields2 ctx (t :: rest)

  /-- DeBruijn-indexed core term constructors -/
  inductive Term2 : (ctx : List Ty) → Ty → Type where
    | var : {ctx : List Ty} → {ty : Ty} → Mem ty ctx → Term2 ctx ty
    | constInt : {ctx : List Ty} → Int → Term2 ctx Ty.int
    | constReal : {ctx : List Ty} → Float → Term2 ctx Ty.real
    | constBool : {ctx : List Ty} → Bool → Term2 ctx Ty.bool
    | constString : {ctx : List Ty} → String → Term2 ctx Ty.string
    | constRecord : {ctx : List Ty} → {l : List Ty}
        → TermFields2 ctx l
        → Term2 ctx (.record l)
    | emptyDict : {ctx : List Ty} → {dom range : Ty}
        → Term2 ctx (.dict dom range)
    | dictInsert : {ctx : List Ty} → {dom range : Ty}
        → TermLoc2 ctx dom
        → TermLoc2 ctx range
        → TermLoc2 ctx (.dict dom range)
        → Term2 ctx (.dict dom range)
    | lookup : {ctx : List Ty} → {dom range : Ty}
        → (aRange : AddM range)
        → TermLoc2 ctx (.dict dom range)
        → TermLoc2 ctx dom
        → Term2 ctx range
    | not : {ctx : List Ty}
        → TermLoc2 ctx Ty.bool
        → Term2 ctx Ty.bool
    | ite : {ctx : List Ty} → {ty : Ty}
        → TermLoc2 ctx Ty.bool
        → TermLoc2 ctx ty
        → TermLoc2 ctx ty
        → Term2 ctx ty
    | letin : {ctx : List Ty} → {ty₁ ty₂ : Ty}
        → TermLoc2 ctx ty₁
        → TermLoc2 (ty₁ :: ctx) ty₂
        → Term2 ctx ty₂
    | add : {ctx : List Ty} → {ty : Ty}
        → (a : AddM ty)
        → TermLoc2 ctx ty
        → TermLoc2 ctx ty
        → Term2 ctx ty
    | mul : {ctx : List Ty} → {sc t1 t2 t3 : Ty}
        → (s1 : ScaleM sc t1)
        → (s2 : ScaleM sc t2)
        → [has_tensor t1 t2 t3]
        → TermLoc2 ctx t1
        → TermLoc2 ctx t2
        → Term2 ctx t3
    | promote : {ctx : List Ty} → {fromType toType : Ty}
        → TermLoc2 ctx fromType → Term2 ctx toType
    | sum : {ctx : List Ty} → {dom range ty : Ty}
        → (a : AddM ty)
        → TermLoc2 ctx (.dict dom range)
        → TermLoc2 (dom :: range :: ctx) ty
        → Term2 ctx ty
    | proj : {ctx : List Ty} → (l : List Ty) → {t : Ty}
        → TermLoc2 ctx (.record l)
        → (i : Nat)
        → [has_proj l i t]
        → Term2 ctx t
    | builtin : {ctx : List Ty} → {a b : Ty}
        → BuiltinFn a b
        → TermLoc2 ctx a
        → Term2 ctx b
end

-- ============================================================================
-- TermLoc2 utilities
-- ============================================================================

namespace TermLoc2
  /-- Extract the source location from a located term -/
  def loc {ctx : List Ty} {ty : Ty}
      (e : TermLoc2 ctx ty) : SourceLocation :=
    match e with
    | mk l _ => l

  /-- Extract the underlying term from a located term -/
  def term {ctx : List Ty} {ty : Ty}
      (e : TermLoc2 ctx ty) : Term2 ctx ty :=
    match e with
    | mk _ t => t

  /-- Create a located term with an unknown location -/
  def withUnknownLoc {ctx : List Ty} {ty : Ty}
      (t : Term2 ctx ty) : TermLoc2 ctx ty :=
    mk SourceLocation.unknown t
end TermLoc2

-- ============================================================================
-- Program structure using DeBruijn terms
-- ============================================================================

/-- A core program using DeBruijn-indexed terms.
    The `ctx` represents the types of loaded inputs (free variables at the start). -/
structure Prog2 : Type where
  t : Ty
  ctx : List Ty
  term : TermLoc2 ctx t
  loadPaths : List String

-- ============================================================================
-- Pretty printing for Term2
-- ============================================================================

namespace Term2

mutual
  /-- Show a located term -/
  partial def showTermLoc2 {ctx : List Ty} {ty : Ty}
      (names : List String) : TermLoc2 ctx ty → String
    | TermLoc2.mk _ inner => showTerm2 names inner

  /-- Show the list of located record fields -/
  partial def showFields2 {ctx : List Ty}
      (names : List String) : {l : List Ty} → TermFields2 ctx l → String
    | [], .nil => ""
    | _, .cons h t =>
        let hStr := showTermLoc2 names h
        let tStr := showFields2 names t
        if tStr = "" then hStr else s!"{hStr}, {tStr}"

  /-- Show a term -/
  partial def showTerm2 {ctx : List Ty} {ty : Ty}
      (names : List String) : Term2 ctx ty → String
    | .var m => getVarName names m
    | .constInt n => toString n
    | .constReal r => toString r
    | .constBool b => toString b
    | .constString s => s
    | .constRecord fields => "<" ++ showFields2 names fields ++ ">"
    | .emptyDict => "{}"
    | .dictInsert k v d =>
        s!"\{{showTermLoc2 names k} -> {showTermLoc2 names v}} ++ {showTermLoc2 names d}"
    | .lookup _ d k => s!"{showTermLoc2 names d}({showTermLoc2 names k})"
    | .not e => s!"not {showTermLoc2 names e}"
    | .ite c t f =>
        s!"if {showTermLoc2 names c} then {showTermLoc2 names t} else {showTermLoc2 names f}"
    | .letin bound body =>
        let x := freshName names
        s!"let {x} = {showTermLoc2 names bound} in {showTermLoc2 (x :: names) body}"
    | .add _ t1 t2 => s!"{showTermLoc2 names t1} + {showTermLoc2 names t2}"
    | @Term2.mul _ _ _ _ _ _ _ _ t1 t2 =>
        s!"{showTermLoc2 names t1} * {showTermLoc2 names t2}"
    | .promote e => s!"promote({showTermLoc2 names e})"
    | .sum _ d body =>
        let k := freshName names
        let v := freshName (k :: names)
        s!"sum({k}, {v} in {showTermLoc2 names d}) {showTermLoc2 (k :: v :: names) body}"
    | @Term2.proj _ _ _ record i _ => s!"{showTermLoc2 names record}.{i}"
    | .builtin _ arg => s!"builtin({showTermLoc2 names arg})"
where
  /-- Get a variable name from its Mem proof -/
  getVarName {ty : Ty} (names : List String) : {ctx : List Ty} → Mem ty ctx → String
    | [], m => nomatch m
    | _ :: _, .head _ => names.headD "?"
    | _ :: _, .tail _ m' => getVarName names.tail m'

  /-- Generate a fresh variable name -/
  freshName (used : List String) : String :=
    let base := ["x", "y", "z", "k", "v", "a", "b", "c", "d", "e"]
    let candidate := base.find? (fun s => !used.contains s)
    match candidate with
    | some s => s
    | none => s!"x{used.length}"
end

end Term2

-- ============================================================================
-- Surface → Core Translation for DeBruijn Terms
-- ============================================================================

namespace ToCore2

/-!
This namespace contains the translation from DeBruijn-indexed surface terms
(`STerm2`/`STermLoc2` from `SurfaceCore2.lean`) to DeBruijn-indexed core terms
(`Term2`/`TermLoc2`).

The translation:
- Erases field names from records (named records → positional tuples)
- Translates surface types to core types
- Translates semimodule evidence (SAdd → AddM, SScale → ScaleM)
- Preserves source locations
-/

-- Type translation
mutual
  def ty : SurfaceTy → Ty
    | .bool => .bool
    | .int => .int
    | .real => .real
    | .maxProduct => .maxProduct
    | .date => .date
    | .string => .string
    | .dict k v => .dict (ty k) (ty v)
    | .record σ => .record (tyFields σ)

  def tyFields : Schema → List Ty
    | [] => []
    | (_, t) :: σ => ty t :: tyFields σ
end

-- Context translation
def tyCtx : List SurfaceTy → List Ty
  | [] => []
  | t :: ts => ty t :: tyCtx ts

-- Prove that tyCtx preserves length
theorem tyCtx_length : ∀ (ctx : List SurfaceTy), (tyCtx ctx).length = ctx.length
  | [] => rfl
  | _ :: ts => by simp [tyCtx, tyCtx_length ts]

-- Membership translation: if t is in ctx, then (ty t) is in (tyCtx ctx)
def tyMem : {t : SurfaceTy} → {ctx : List SurfaceTy} → Mem t ctx → Mem (ty t) (tyCtx ctx)
  | _, _ :: _, Mem.head _ => Mem.head _
  | _, _ :: _, Mem.tail _ m => Mem.tail _ (tyMem m)

-- Evidence translation: SAdd → AddM
mutual
  def toCoreAdd : {t : SurfaceTy} → SAdd t → AddM (ty t)
    | _, SAdd.boolA => AddM.boolA
    | _, SAdd.intA => AddM.intA
    | _, SAdd.realA => AddM.realA
    | _, SAdd.maxProductA => AddM.maxProductA
    | _, SAdd.dateA => AddM.dateA
    | _, SAdd.stringA => AddM.stringA
    | _, @SAdd.dictA _ _ aRange => AddM.dictA (toCoreAdd aRange)
    | _, @SAdd.recordA σ fields => AddM.recordA (toCoreAddFields σ fields)

  def toCoreAddFields : (σ : Schema) → HList (fun (p : String × SurfaceTy) => SAdd p.snd) σ
      → HList AddM (tyFields σ)
    | [], HList.nil => HList.nil
    | _ :: σ', HList.cons h t => HList.cons (toCoreAdd h) (toCoreAddFields σ' t)
end

-- Evidence translation: SScale → ScaleM
def toCoreScale : {sc t : SurfaceTy} → SScale sc t → ScaleM (ty sc) (ty t)
  | _, _, SScale.boolS => ScaleM.boolS
  | _, _, SScale.intS => ScaleM.intS
  | _, _, SScale.realS => ScaleM.realS
  | _, _, SScale.maxProductS => ScaleM.maxProductS
  | _, _, @SScale.dictS _ _ _ sRange => ScaleM.dictS (toCoreScale sRange)
  | _, _, @SScale.recordS sc σ fields =>
      -- Build the per-field scaling function using typed membership
      let rec go
          (σ : Schema)
          (flds : ∀ (p : String × SurfaceTy), Mem p σ → SScale sc p.snd)
          : ∀ (t' : Ty), Mem t' (tyFields σ) → ScaleM (ty sc) t'
        :=
        match σ with
        | [] => fun _ h => by cases h
        | (nm, tt) :: σ' =>
            fun t' (h : Mem t' (tyFields ((nm, tt) :: σ'))) => by
              have h0 : Mem t' (ty tt :: tyFields σ') := h
              cases h0 with
              | head _ =>
                  simpa using (toCoreScale (flds (nm, tt) (Mem.head σ')))
              | tail _ hRest =>
                  let flds' : ∀ (p : String × SurfaceTy), Mem p σ' → SScale sc p.snd :=
                    fun p hp => flds p (Mem.tail (nm, tt) hp)
                  exact go σ' flds' t' hRest
      ScaleM.recordS (go σ fields)

-- Type equality lemmas
@[simp]
theorem tyFields_cons (nm : String) (t : SurfaceTy) (σ : Schema) :
    tyFields ((nm, t) :: σ) = ty t :: tyFields σ := rfl

theorem tyFields_append (σ1 σ2 : Schema) :
    tyFields (σ1 ++ σ2) = tyFields σ1 ++ tyFields σ2 := by
  induction σ1 with
  | nil => simp [tyFields]
  | cons h t ih => simp [tyFields, ih]

-- HasField index computes the correct type
theorem HasField.index_getD_ty2
    : ∀ {σ : Schema} {nm : String} {t : SurfaceTy}
        (p : HasField σ nm t),
        (tyFields σ).getD (HasField.index p) Ty.int = ty t
  | (_, t) :: _, _, _, HasField.here => by simp [HasField.index, tyFields]
  | _ :: σ, _, _, HasField.there p => by simp [HasField.index, tyFields]; exact HasField.index_getD_ty2 p

-- Surface tensor → core tensor relationship

mutual
  unsafe def ty_stensor_eq2 : ∀ (a b : SurfaceTy), ty (stensor a b) = tensor (ty a) (ty b)
    | .bool, b => rfl
    | .int, b => rfl
    | .real, b => rfl
    | .maxProduct, b => rfl
    | .date, b => rfl
    | .string, b => rfl
    | .dict dom range, b => by
        rw [ty]
        rw [ty_stensor_eq2]
        rw [ty]
        rw [tensor]
    | .record σ, b => by
        rw [ty]
        rw [tyFields_map_stensor2]
        rw [ty]
        rw [tensor]

  unsafe def tyFields_map_stensor2
      : ∀ (σ : Schema) (b : SurfaceTy),
        tyFields (σ.map (fun (p : String × SurfaceTy) => (p.fst, stensor p.snd b)))
          = (tyFields σ).map (fun t => tensor t (ty b))
    | [], _ => rfl
    | (nm, t) :: σ, b => by
        simp [tyFields_map_stensor2, ty_stensor_eq2, -stensor]
end

-- Main translation functions
mutual
  /-- Translate DeBruijn surface term fields to core term fields -/
  unsafe def trFields2 {ctx : List SurfaceTy}
      : {σ : Schema} → STermFields2 ctx σ → TermFields2 (tyCtx ctx) (tyFields σ)
    | [], STermFields2.nil => TermFields2.nil
    | _ :: _, STermFields2.cons h t => TermFields2.cons (trLoc2 h) (trFields2 t)

  /-- Translate a located DeBruijn surface term to core, preserving location -/
  unsafe def trLoc2 {ctx : List SurfaceTy} {t : SurfaceTy}
      (e : STermLoc2 ctx t) : TermLoc2 (tyCtx ctx) (ty t) :=
    match e with
    | STermLoc2.mk loc inner => TermLoc2.mk loc (tr2 loc inner)

  /-- Translate an unlocated DeBruijn surface term to core -/
  unsafe def tr2 {ctx : List SurfaceTy} {t : SurfaceTy}
      (loc : SourceLocation)
      (e : STerm2 ctx t) : Term2 (tyCtx ctx) (ty t) :=
    match e with
    | STerm2.var m => Term2.var (tyMem m)
    | STerm2.constInt i => Term2.constInt i
    | STerm2.constReal r => Term2.constReal r
    | STerm2.constBool b => Term2.constBool b
    | STerm2.constString s => Term2.constString s
    | STerm2.not e => Term2.not (trLoc2 e)
    | STerm2.ite c t f => Term2.ite (trLoc2 c) (trLoc2 t) (trLoc2 f)
    | @STerm2.letin _ ty₁ _ bound body =>
        -- Body is in context (ty₁ :: ctx), which translates to (ty ty₁ :: tyCtx ctx)
        Term2.letin (trLoc2 bound) (trLoc2 body)
    | @STerm2.add _ sty a e1 e2 =>
        Term2.add (toCoreAdd a) (trLoc2 e1) (trLoc2 e2)
    | @STerm2.mul _ sc t1 t2 s1 s2 e1 e2 =>
        -- Cast the result type via ty_stensor_eq2 to match core tensor.
        by
          have hmul : Term2 (tyCtx ctx) (tensor (ty t1) (ty t2)) :=
            Term2.mul (toCoreScale s1) (toCoreScale s2) (trLoc2 e1) (trLoc2 e2)
          simpa [ty_stensor_eq2, -stensor] using hmul
    | @STerm2.promote _ fromType toType e =>
        Term2.promote (fromType := ty fromType) (toType := ty toType) (trLoc2 e)
    | STerm2.emptyDict => Term2.emptyDict
    | STerm2.dictInsert k v d =>
        Term2.dictInsert (trLoc2 k) (trLoc2 v) (trLoc2 d)
    | @STerm2.lookup _ _ _ aRange d k =>
        Term2.lookup (toCoreAdd aRange) (trLoc2 d) (trLoc2 k)
    | @STerm2.sum _ dom range _ a d body =>
        -- Body is in context (dom :: range :: ctx)
        Term2.sum (toCoreAdd a) (trLoc2 d) (trLoc2 body)
    | @STerm2.constRecord _ σ fields =>
        by
          have h : Term2 (tyCtx ctx) (Ty.record (tyFields σ)) :=
            Term2.constRecord (trFields2 fields)
          exact h
    | @STerm2.projByName _ nm t σ p r =>
        -- Project by index, coercing the result type
        let idx := HasField.index p
        have rr : TermLoc2 (tyCtx ctx) (Ty.record (tyFields σ)) := trLoc2 r
        have pr : Term2 (tyCtx ctx) ((tyFields σ).getD idx Ty.int) :=
          Term2.proj (tyFields σ) rr idx
        by
          have heq : (tyFields σ).getD idx Ty.int = ty t := HasField.index_getD_ty2 p
          rw [heq] at pr
          exact pr
    | STerm2.builtin b a =>
        match b with
        | SBuiltin.And => Term2.builtin BuiltinFn.And (trLoc2 a)
        | SBuiltin.Or => Term2.builtin BuiltinFn.Or (trLoc2 a)
        | @SBuiltin.Eq st => Term2.builtin (BuiltinFn.Eq (ty st)) (trLoc2 a)
        | @SBuiltin.Leq st => Term2.builtin (BuiltinFn.Leq (ty st)) (trLoc2 a)
        | @SBuiltin.Lt st => Term2.builtin (BuiltinFn.Lt (ty st)) (trLoc2 a)
        | @SBuiltin.Sub st => Term2.builtin (BuiltinFn.Sub (ty st)) (trLoc2 a)
        | SBuiltin.Div => Term2.builtin BuiltinFn.Div (trLoc2 a)
        | SBuiltin.StrEndsWith => Term2.builtin BuiltinFn.StrEndsWith (trLoc2 a)
        | SBuiltin.StrStartsWith => Term2.builtin BuiltinFn.StrStartsWith (trLoc2 a)
        | SBuiltin.StrContains => Term2.builtin BuiltinFn.StrContains (trLoc2 a)
        | SBuiltin.FirstIndex => Term2.builtin BuiltinFn.FirstIndex (trLoc2 a)
        | SBuiltin.LastIndex => Term2.builtin BuiltinFn.LastIndex (trLoc2 a)
        | SBuiltin.SubString => Term2.builtin BuiltinFn.SubString (trLoc2 a)
        | @SBuiltin.Dom dom range =>
            Term2.builtin (BuiltinFn.Dom (dom := ty dom) (range := ty range)) (trLoc2 a)
        | SBuiltin.Range => Term2.builtin BuiltinFn.Range (trLoc2 a)
        | @SBuiltin.Size dom range =>
            Term2.builtin (BuiltinFn.Size (dom := ty dom) (range := ty range)) (trLoc2 a)
        | SBuiltin.DateLit yyyymmdd => Term2.builtin (BuiltinFn.DateLit yyyymmdd) (trLoc2 a)
        | SBuiltin.Year => Term2.builtin BuiltinFn.Year (trLoc2 a)
        | @SBuiltin.Concat σ1 σ2 =>
            let result : Term2 (tyCtx ctx) (Ty.record (tyFields σ1 ++ tyFields σ2)) :=
              Term2.builtin (BuiltinFn.Concat (tyFields σ1) (tyFields σ2)) (trLoc2 a)
            by
              simpa [ty, tyFields_append] using result
end

/-- Translate a DeBruijn surface program to a core program -/
unsafe def trProg2 (p : SProg2) : Prog2 :=
  { t := ty p.t
    ctx := tyCtx p.ctx
    term := trLoc2 p.term
    loadPaths := p.loadPaths }

end ToCore2
