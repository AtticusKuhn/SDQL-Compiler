import PartIiProject.SurfaceCore

open PartIiProject

/-!
Untyped DeBruijn terms (after load extraction), with `SourceLocation`s for errors.
-/

mutual
  /-- Core UntypedTerm constructors without location -/
  inductive UntypedTerm' : (ctx : Nat) → Type where
    | var : {ctx : Nat} → Fin ctx → UntypedTerm' ctx
    | constInt : {ctx : Nat} → Int → UntypedTerm' ctx
    | constReal : {ctx : Nat} → Float → UntypedTerm' ctx
    | constBool : {ctx : Nat} → Bool → UntypedTerm' ctx
    | constString : {ctx : Nat} → String → UntypedTerm' ctx
    | constRecord : {ctx : Nat} → UntypedTermFields ctx → UntypedTerm' ctx
    /-- Unannotated empty dictionary; should only appear as the tail of a dictionary literal. -/
    | emptyDict : {ctx : Nat} → UntypedTerm' ctx
    /-- Type-annotated empty dictionary: `{}_{ Tdom, Trange }`. -/
    | emptyDictAnn : {ctx : Nat} → SurfaceTy → SurfaceTy → UntypedTerm' ctx  -- dom, range types
    | dictInsert : {ctx : Nat} → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    | not : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | ite : {ctx : Nat} → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    /-- `if c then t` (no `else`); desugars during type inference using the additive identity of the expected type. -/
    | iteThen : {ctx : Nat} → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    | letin : {ctx : Nat} → UntypedTermLoc ctx → (UntypedTermLoc ctx.succ) → UntypedTerm' ctx
    | add : {ctx : Nat} → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    /-- Multiplication. Optional scalar annotation `*{S}` may be provided to disambiguate. -/
    | mul : {ctx : Nat} → Option SurfaceTy → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    | projByName : {ctx : Nat} → String → UntypedTermLoc ctx → UntypedTerm' ctx
    | lookup : {ctx : Nat} → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    | sum : {ctx : Nat} → UntypedTermLoc ctx → (UntypedTermLoc (ctx + 2)) → UntypedTerm' ctx
    | builtinAnd : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinOr : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinEq : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinLeq : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinLt : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinSub : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinDiv : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinStrEndsWith : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinDom : {ctx : Nat} → SurfaceTy → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinRange : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinSize : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinDateLit : {ctx : Nat} → Int → UntypedTerm' ctx
    | builtinYear : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinConcat : {ctx : Nat} → Schema → Schema → UntypedTermLoc ctx → UntypedTerm' ctx

  /-- An UntypedTerm with source location for error reporting -/
  inductive UntypedTermLoc : (ctx : Nat) → Type where
    | mk : {ctx : Nat} → (stx : SourceLocation) → UntypedTerm' ctx → UntypedTermLoc ctx

  /-- Record fields for untyped terms (avoids nested inductive with List) -/
  inductive UntypedTermFields : (ctx : Nat) → Type where
    | nil : {ctx : Nat} → UntypedTermFields ctx
    | cons : {ctx : Nat} → (name : String) → UntypedTermLoc ctx → UntypedTermFields ctx → UntypedTermFields ctx
end

namespace UntypedTermLoc
  unsafe def stx {ctx : Nat} : UntypedTermLoc ctx → SourceLocation
    | mk s _ => s

  unsafe def term {ctx : Nat} : UntypedTermLoc ctx → UntypedTerm' ctx
    | mk _ t => t

  unsafe def withStx {ctx : Nat} (stx : SourceLocation) (t : UntypedTerm' ctx) : UntypedTermLoc ctx :=
    mk stx t
end UntypedTermLoc

namespace UntypedTermFields
  /-- Convert UntypedTermFields to a list of (name, term) pairs -/
  unsafe def toList {ctx : Nat} : UntypedTermFields ctx → List (String × UntypedTermLoc ctx)
    | .nil => []
    | .cons name term rest => (name, term) :: toList rest

  /-- Convert a list of (name, term) pairs to UntypedTermFields -/
  unsafe def fromList {ctx : Nat} : List (String × UntypedTermLoc ctx) → UntypedTermFields ctx
    | [] => .nil
    | (name, term) :: rest => .cons name term (fromList rest)

  /-- Sort fields by name and return as UntypedTermFields -/
  unsafe def sortByName {ctx : Nat} (fields : UntypedTermFields ctx) : UntypedTermFields ctx :=
    let list := toList fields
    -- Sort by name, but preserve original order for ties (stable sort).
    -- This matters for SDQL records that intentionally reuse the "_" field name (tuple-like records).
    let rec enumerate (i : Nat) : List (String × UntypedTermLoc ctx) → List (String × Nat × UntypedTermLoc ctx)
      | [] => []
      | (nm, term) :: rest => (nm, i, term) :: enumerate (i + 1) rest
    let indexed : Array (String × Nat × UntypedTermLoc ctx) :=
      (enumerate 0 list).toArray
    let sorted :=
      indexed.qsort (fun a b => if a.1 == b.1 then a.2.1 < b.2.1 else a.1 < b.1)
        |>.toList
        |>.map (fun (nm, (_i, term)) => (nm, term))
    fromList sorted
end UntypedTermFields
