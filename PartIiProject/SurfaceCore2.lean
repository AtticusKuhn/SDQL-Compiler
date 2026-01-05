import PartIiProject.SurfaceCore

open PartIiProject

/-!
# DeBruijn-indexed Surface Terms (SurfaceCore2)

This module defines a DeBruijn-indexed representation of surface terms,
as an alternative to the PHOAS representation in SurfaceCore.lean.

Key differences from PHOAS:
- Variables are represented by `Mem ty ctx` proofs instead of `rep ty` values
- Context is a `List SurfaceTy` instead of being implicit in the `rep` type
- No higher-order body functions - bodies are just terms in extended contexts
-/

mutual
  /-- A DeBruijn surface term with source location -/
  unsafe inductive STermLoc2 : (ctx : List SurfaceTy) → SurfaceTy → Type where
    | mk : {ctx : List SurfaceTy} → {ty : SurfaceTy} → (loc : SourceLocation) → STerm2 ctx ty → STermLoc2 ctx ty

  /-- DeBruijn-indexed surface term constructors -/
  unsafe inductive STerm2 : (ctx : List SurfaceTy) → SurfaceTy → Type where
    | var   : {ctx : List SurfaceTy} → {ty : SurfaceTy} → Mem ty ctx → STerm2 ctx ty
    | constInt : {ctx : List SurfaceTy} → Int → STerm2 ctx SurfaceTy.int
    | constReal : {ctx : List SurfaceTy} → Float → STerm2 ctx SurfaceTy.real
    | constBool : {ctx : List SurfaceTy} → Bool → STerm2 ctx SurfaceTy.bool
    | constString : {ctx : List SurfaceTy} → String → STerm2 ctx SurfaceTy.string
    | not : {ctx : List SurfaceTy} → STermLoc2 ctx SurfaceTy.bool → STerm2 ctx SurfaceTy.bool
    | ite : {ctx : List SurfaceTy} → {ty : SurfaceTy} → STermLoc2 ctx SurfaceTy.bool → STermLoc2 ctx ty → STermLoc2 ctx ty → STerm2 ctx ty
    | letin : {ctx : List SurfaceTy} → {ty₁ ty₂ : SurfaceTy} → STermLoc2 ctx ty₁ → STermLoc2 (ty₁ :: ctx) ty₂ → STerm2 ctx ty₂
    | add : {ctx : List SurfaceTy} → {ty : SurfaceTy} → (a : SAdd ty) → STermLoc2 ctx ty → STermLoc2 ctx ty → STerm2 ctx ty
    | mul : {ctx : List SurfaceTy} → {sc t1 t2 : SurfaceTy} → (s1 : SScale sc t1) → (s2 : SScale sc t2)
        → STermLoc2 ctx t1 → STermLoc2 ctx t2 → STerm2 ctx (stensor t1 t2)
    | promote : {ctx : List SurfaceTy} → {fromType toType : SurfaceTy}
        → STermLoc2 ctx fromType → STerm2 ctx toType
    | emptyDict : {ctx : List SurfaceTy} → {domain ran : SurfaceTy} → STerm2 ctx (SurfaceTy.dict domain ran)
    | dictInsert : {ctx : List SurfaceTy} → {dom range : SurfaceTy} → STermLoc2 ctx dom → STermLoc2 ctx range → STermLoc2 ctx (SurfaceTy.dict dom range) → STerm2 ctx (SurfaceTy.dict dom range)
    | lookup : {ctx : List SurfaceTy} → {dom range : SurfaceTy} → (aRange : SAdd range) → STermLoc2 ctx (SurfaceTy.dict dom range) → STermLoc2 ctx dom → STerm2 ctx range
    | sum : {ctx : List SurfaceTy} → {dom range ty : SurfaceTy} → (a : SAdd ty) → STermLoc2 ctx (SurfaceTy.dict dom range) → STermLoc2 (dom :: range :: ctx) ty → STerm2 ctx ty
    | constRecord : {ctx : List SurfaceTy} → {l : Schema}
        → STermFields2 ctx l
        → STerm2 ctx (.record l)
    | projByName : {ctx : List SurfaceTy} → {nm : String} → {t : SurfaceTy} → {σ : Schema}
        → (p : HasField σ nm t)
        → STermLoc2 ctx (.record σ)
        → STerm2 ctx t
    | builtin : {ctx : List SurfaceTy} → {a b : SurfaceTy} → SBuiltin a b → STermLoc2 ctx a → STerm2 ctx b

  /-- Record fields for DeBruijn terms -/
  unsafe inductive STermFields2 : (ctx : List SurfaceTy) → Schema → Type where
    | nil : {ctx : List SurfaceTy} → STermFields2 ctx []
    | cons : {ctx : List SurfaceTy} → {name : String} → {t : SurfaceTy} → {rest : Schema}
        → STermLoc2 ctx t → STermFields2 ctx rest → STermFields2 ctx ((name, t) :: rest)
end

namespace STermLoc2
  /-- Extract the source location from a located term -/
  unsafe def loc {ctx : List SurfaceTy} {ty : SurfaceTy}
      (e : STermLoc2 ctx ty) : SourceLocation :=
    match e with
    | mk l _ => l

  /-- Extract the underlying term from a located term -/
  unsafe def term {ctx : List SurfaceTy} {ty : SurfaceTy}
      (e : STermLoc2 ctx ty) : STerm2 ctx ty :=
    match e with
    | mk _ t => t

  /-- Create a located term with an unknown location -/
  unsafe def withUnknownLoc {ctx : List SurfaceTy} {ty : SurfaceTy}
      (t : STerm2 ctx ty) : STermLoc2 ctx ty :=
    mk SourceLocation.unknown t
end STermLoc2

/-- A program using DeBruijn-indexed terms -/
unsafe structure SProg2 : Type where
  t : SurfaceTy
  ctx : List SurfaceTy
  term : STermLoc2 ctx t
  loadPaths : List String

unsafe instance : ToString SProg2 :=
  { toString := fun sp =>  "sprog"}
