import PartIiProject.SurfaceCore

open PartIiProject

/-!
Parser output AST (PHOAS) with `load` constructs and `SourceLocation`s.
-/

mutual
  /-- Core LoadTerm constructors without location -/
  inductive LoadTerm' (rep : Type) : Type where
    | var : rep → LoadTerm' rep
    | constInt : Int → LoadTerm' rep
    | constReal : Float → LoadTerm' rep
    | constBool : Bool → LoadTerm' rep
    | constString : String → LoadTerm' rep
    | constRecord : List (String × LoadTermLoc rep) → LoadTerm' rep
    /-- Unannotated empty dictionary; used internally by the parser when building dictionary literals. -/
    | emptyDict : LoadTerm' rep
    /-- Type-annotated empty dictionary: `{}_{ Tdom, Trange }`. -/
    | emptyDictAnn : SurfaceTy → SurfaceTy → LoadTerm' rep  -- dom, range types for empty dict
    | dictInsert : LoadTermLoc rep → LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
    | not : LoadTermLoc rep → LoadTerm' rep
    | ite : LoadTermLoc rep → LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
    /-- `if c then t` (no `else`); desugars during type inference using the additive identity of the expected type. -/
    | iteThen : LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
    | letin : LoadTermLoc rep → (rep → LoadTermLoc rep) → LoadTerm' rep
    | add : LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
    /-- Multiplication. Optional scalar annotation `*{S}` may be provided to disambiguate. -/
    | mul : Option SurfaceTy → LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
    /-- Scalar promotion: `promote[T](e)` changes the scalar type annotation. -/
    | promote : SurfaceTy → LoadTermLoc rep → LoadTerm' rep
    | projByName : String → LoadTermLoc rep → LoadTerm' rep
    | lookup : LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
    | sum : LoadTermLoc rep → (rep → rep → LoadTermLoc rep) → LoadTerm' rep
    | load : String → SurfaceTy → LoadTerm' rep  -- file path, expected type
    | builtinAnd : LoadTermLoc rep → LoadTerm' rep
    | builtinOr : LoadTermLoc rep → LoadTerm' rep
    | builtinEq : SurfaceTy → LoadTermLoc rep → LoadTerm' rep
    | builtinLeq : SurfaceTy → LoadTermLoc rep → LoadTerm' rep
    | builtinLt : SurfaceTy → LoadTermLoc rep → LoadTerm' rep
    | builtinSub : SurfaceTy → LoadTermLoc rep → LoadTerm' rep
    | builtinDiv : LoadTermLoc rep → LoadTerm' rep
    | builtinStrEndsWith : LoadTermLoc rep → LoadTerm' rep
    | builtinStrStartsWith : LoadTermLoc rep → LoadTerm' rep
    | builtinStrContains : LoadTermLoc rep → LoadTerm' rep
    | builtinFirstIndex : LoadTermLoc rep → LoadTerm' rep
    | builtinLastIndex : LoadTermLoc rep → LoadTerm' rep
    | builtinSubString : LoadTermLoc rep → LoadTerm' rep
    | builtinDom : SurfaceTy → SurfaceTy → LoadTermLoc rep → LoadTerm' rep  -- dom, range
    | builtinRange : LoadTermLoc rep → LoadTerm' rep
    | builtinSize : LoadTermLoc rep → LoadTerm' rep
    | builtinDateLit : Int → LoadTerm' rep  -- DateLit doesn't need an arg term
    | builtinYear : LoadTermLoc rep → LoadTerm' rep
    | builtinConcat : Schema → Schema → LoadTermLoc rep → LoadTerm' rep

  /-- A LoadTerm with source location from the parser -/
  inductive LoadTermLoc (rep : Type) : Type where
    | mk : (stx : SourceLocation) → LoadTerm' rep → LoadTermLoc rep
end

namespace LoadTermLoc
  def stx {rep : Type} : LoadTermLoc rep → SourceLocation
    | mk s _ => s

  def term {rep : Type} : LoadTermLoc rep → LoadTerm' rep
    | mk _ t => t

  def withStx {rep : Type} (stx : SourceLocation) (t : LoadTerm' rep) : LoadTermLoc rep :=
    mk stx t
end LoadTermLoc

/-- A closed load term (polymorphic in rep) -/
def LoadTerm := {rep : Type} → LoadTermLoc rep
