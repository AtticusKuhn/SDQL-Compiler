import Std.Data.TreeMap.Basic
import Std.Data.TreeMap
import PartIiProject.SurfaceCore
import PartIiProject.SurfaceCore2
import PartIiProject.HList
import Lean

open PartIiProject
open Lean

/-!
# Type Inference for Untyped SDQL Terms with Source Location Tracking

This module implements a pipeline for SDQL parsing and type inference:

```
  Parser → LoadTermLoc → UntypedTermLoc → STermLoc'
```

## Design

### Location Tracking with SourceLocation

Both `LoadTermLoc` and `UntypedTermLoc` carry `SourceLocation` objects from the parser.
This enables precise error messages via `throwErrorAt SourceLocation msg` when type
inference fails.

### PHOAS with Location

We use mutually inductive types:
- `LoadTermLoc rep` wraps a `LoadTerm' rep` with its `SourceLocation`
- `UntypedTermLoc rep` wraps an `UntypedTerm' rep` with its `SourceLocation`

The `SourceLocation` is threaded through all operations so type errors can be
reported at the exact source location.

### Type Inference Errors

The `infer` function returns `Except (SourceLocation × String) result`:
- On success: a typed `STermLoc'`
- On failure: `(SourceLocation, errorMessage)` for use with `throwErrorAt`

## Usage

```lean
-- In a macro/elaboration context:
match typeinfer expectedTy untypedTerm with
| .ok sterm => -- use the typed term
| .error (stx, msg) => throwErrorAt stx msg
```
-/

-- ============================================================================
-- Load Terms: Parser output with `load` constructs
-- ============================================================================

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
    | mul : SurfaceTy → LoadTermLoc rep → LoadTermLoc rep → LoadTerm' rep
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
    | builtinStrEndsWith : LoadTermLoc rep → LoadTerm' rep
    | builtinDom : SurfaceTy → SurfaceTy → LoadTermLoc rep → LoadTerm' rep  -- dom, range
    | builtinRange : LoadTermLoc rep → LoadTerm' rep
    | builtinDateLit : Int → LoadTerm' rep  -- DateLit doesn't need an arg term
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

-- ============================================================================
-- Untyped Terms: After load extraction, with SourceLocation for error reporting
-- ============================================================================

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
    | mul : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    | projByName : {ctx : Nat} → String → UntypedTermLoc ctx → UntypedTerm' ctx
    | lookup : {ctx : Nat} → UntypedTermLoc ctx → UntypedTermLoc ctx → UntypedTerm' ctx
    | sum : {ctx : Nat} → UntypedTermLoc ctx → (UntypedTermLoc (ctx + 2)) → UntypedTerm' ctx
    | builtinAnd : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinOr : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinEq : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinLeq : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinLt : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinSub : {ctx : Nat} → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinStrEndsWith : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinDom : {ctx : Nat} → SurfaceTy → SurfaceTy → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinRange : {ctx : Nat} → UntypedTermLoc ctx → UntypedTerm' ctx
    | builtinDateLit : {ctx : Nat} → Int → UntypedTerm' ctx
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
    let sorted := list.toArray.qsort (fun (n1, _) (n2, _) => n1 < n2) |>.toList
    fromList sorted
end UntypedTermFields

-- ============================================================================
-- Type Error: SourceLocation + Message
-- ============================================================================

/-- A type inference error with source location -/
abbrev TypeError := SourceLocation × String

/-- Create a type error with SourceLocation location -/
def typeError (stx : SourceLocation) (msg : String) : TypeError := (stx, msg)

/-- Human-readable location snippet for error messages. -/
def sourceLocWhere (stx : SourceLocation) : String :=
  if stx.substring.isEmpty then
    "unknown location"
  else
    stx.substring

-- ============================================================================
-- Type Equality and Utilities
-- ============================================================================

/-- Check if two SurfaceTy are equal -/
unsafe def tyEq : SurfaceTy → SurfaceTy → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .real, .real => true
  | .date, .date => true
  | .string, .string => true
  | .dict k1 v1, .dict k2 v2 => tyEq k1 k2 && tyEq v1 v2
  | .record σ1, .record σ2 => schemaEq σ1 σ2
  | _, _ => false
where
  schemaEq : Schema → Schema → Bool
    | [], [] => true
    | (n1, t1) :: rest1, (n2, t2) :: rest2 =>
        n1 == n2 && tyEq t1 t2 && schemaEq rest1 rest2
    | _, _ => false

/-- Pretty print a SurfaceTy -/
unsafe def tyToString : SurfaceTy → String
  | .bool => "bool"
  | .int => "int"
  | .real => "real"
  | .date => "date"
  | .string => "string"
  | .dict k v => s!"\{ {tyToString k} -> {tyToString v} }"
  | .record σ => s!"<{schemaToString σ}>"
where
  schemaToString : Schema → String
    | [] => ""
    | [(n, t)] => s!"{n}: {tyToString t}"
    | (n, t) :: rest => s!"{n}: {tyToString t}, {schemaToString rest}"

/-- Check type equality and produce a term via unsafe cast if equal -/
unsafe def checkTyEq2 {ctx : List SurfaceTy}
    (stx : SourceLocation)
    (ty1 ty2 : SurfaceTy)
    (mkTerm : STermLoc2 ctx ty1)
    : Except TypeError (STermLoc2 ctx ty2) :=
  if tyEq ty1 ty2 then
    pure (unsafeCast (α := STermLoc2 ctx ty1) mkTerm)
  else
    .error (stx, s!"Type mismatch: expected {tyToString ty2}, got {tyToString ty1}")

-- ============================================================================
-- Type Computation (typeof) for DeBruijn terms
-- ============================================================================

/-- Get the type at a given index in a context -/
unsafe def getTypeAt (ctx : List SurfaceTy) (i : Fin ctx.length) : SurfaceTy :=
  ctx[i.val]'(by exact i.isLt)

/-- Convert a Fin index to a Mem proof -/
unsafe def finToMem : (ctx : List SurfaceTy) → (i : Fin ctx.length) → Mem (getTypeAt ctx i) ctx
  | [], i => nomatch i
  | t :: ts, ⟨0, _⟩ => Mem.head ts
  | _ :: ts, ⟨n + 1, h⟩ =>
      let i' : Fin ts.length := ⟨n, Nat.lt_of_succ_lt_succ h⟩
      Mem.tail _ (finToMem ts i')

/-- Compute the type of an untyped term in a given context.
    Returns an error with SourceLocation location if the term cannot be typed. -/
unsafe def typeof2 (ctx : List SurfaceTy) (e : UntypedTermLoc ctx.length) : Except TypeError SurfaceTy := do
  match e with
  | .mk stx inner =>
    match inner with
    | .var i => pure (getTypeAt ctx i)
    | .constInt _ => pure .int
    | .constReal _ => pure .real
    | .constBool _ => pure .bool
    | .constString _ => pure .string
    | .constRecord fields => do
        let sortedFields := UntypedTermFields.sortByName fields
        let schema ← typeofFields2 ctx (sortedFields.toList)
        pure (.record schema)
    | .emptyDict =>
        .error (stx, "cannot infer type of unannotated empty dict; use {}_{Tdom, Trange}")
    | .emptyDictAnn domTy rangeTy => pure (.dict domTy rangeTy)
    | .dictInsert k v _ => do
        let domTy ← typeof2 ctx k
        let rangeTy ← typeof2 ctx v
        pure (.dict domTy rangeTy)
    | .not _ => pure .bool
    | .ite _ t _ => typeof2 ctx t
    | .iteThen _ t => typeof2 ctx t
    | .letin bound body => do
        let boundTy ← typeof2 ctx bound
        typeof2 (boundTy :: ctx) body
    | .add e1 _ => typeof2 ctx e1
    | .mul _ e1 e2 => do
        let t1 ← typeof2 ctx e1
        let t2 ← typeof2 ctx e2
        pure (stensor t1 t2)
    | .projByName name inner => do
        let ty ← typeof2 ctx inner
        match ty with
        | .record σ =>
            match σ.find? (fun (n, _) => n == name) with
            | some (_, fieldTy) => pure fieldTy
            | none => .error (stx, s!"Field '{name}' not found in record")
        | _ => .error (stx, s!"Cannot project from non-record type {tyToString ty}")
    | .lookup d _ => do
        let dictTy ← typeof2 ctx d
        match dictTy with
        | .dict _ rangeTy => pure rangeTy
        | _ => .error (stx, s!"Cannot lookup in non-dictionary type {tyToString dictTy}")
    | .sum d body => do
        let dictTy ← typeof2 ctx d
        match dictTy with
        | .dict domTy rangeTy => typeof2 (domTy :: rangeTy :: ctx) body
        | _ => .error (stx, s!"sum expects dictionary, got {tyToString dictTy}")
    | .builtinAnd _ => pure .bool
    | .builtinOr _ => pure .bool
    | .builtinEq _ _ => pure .bool
    | .builtinLeq _ _ => pure .bool
    | .builtinLt _ _ => pure .bool
    | .builtinSub _ arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .record [("_1", t1), ("_2", t2)] =>
            if tyEq t1 t2 then
              pure t1
            else
              .error (stx, s!"- expects both operands to have the same type, got {tyToString t1} and {tyToString t2}")
        | other =>
            .error (stx, s!"- expects a pair record argument, got {tyToString other}")
    | .builtinStrEndsWith _ => pure .bool
    | .builtinDom _ _ arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .dict domTy _ => pure (.dict domTy .bool)
        | other => .error (stx, s!"dom expects a dictionary argument, got {tyToString other}")
    | .builtinRange _ => pure (.dict .int .bool)
    | .builtinDateLit _ => pure .date
    | .builtinConcat _ _ arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .record [("_1", .record σ1), ("_2", .record σ2)] =>
            pure (.record (σ1 ++ σ2))
        | other =>
            .error (stx, s!"concat expects a pair of records, got {tyToString other}")
where
  typeofFields2 (ctx : List SurfaceTy) : List (String × UntypedTermLoc ctx.length) → Except TypeError Schema
    | [] => pure []
    | (name, e) :: rest => do
        let ty ← typeof2 ctx e
        let restSchema ← typeofFields2 ctx rest
        pure ((name, ty) :: restSchema)

-- ============================================================================
-- Evidence Synthesis
-- ============================================================================

-- Synthesize SAdd evidence for a type
mutual
  unsafe def synthSAdd (stx : SourceLocation) (ty : SurfaceTy) : Except TypeError (SAdd ty) :=
    match ty with
    | .bool => pure SAdd.boolA
    | .int => pure SAdd.intA
    | .real => pure SAdd.realA
    | .date => pure SAdd.dateA
    | .string => pure SAdd.stringA
    | .dict _ range => do
        let aRange ← synthSAdd stx range
        pure (SAdd.dictA aRange)
    | .record σ => do
        let hlist ← synthSAddFields stx σ
        pure (SAdd.recordA hlist)

  unsafe def synthSAddFields (stx : SourceLocation) : (σ : Schema) → Except TypeError (HList (fun p => SAdd p.snd) σ)
    | [] => pure HList.nil
    | (_, t) :: rest => do
        let h ← synthSAdd stx t
        let tl ← synthSAddFields stx rest
        pure (HList.cons h tl)
end

/-- Synthesize SScale evidence for scaling type t by scalar sc -/
unsafe def synthSScale (stx : SourceLocation) (sc : SurfaceTy) (t : SurfaceTy) : Except TypeError (SScale sc t) :=
  match sc, t with
  | .bool, .bool => pure SScale.boolS
  | .int, .int => pure SScale.intS
  | .real, .real => pure SScale.realS
  | sc, .dict _ range => do
      let sRange ← synthSScale stx sc range
      pure (SScale.dictS sRange)
  | sc, .record σ => do
      -- Validate all fields can be scaled
      for (_, ft) in σ do
        let _ ← synthSScale stx sc ft
      -- Build the fields function
      let fieldsOk : (p : String × SurfaceTy) → Mem p σ → SScale sc p.snd :=
        fun (_, ft) _ =>
          match synthSScale stx sc ft with
          | .ok s => s
          | .error _ => unsafeCast SScale.intS  -- unreachable: already validated
      pure (SScale.recordS fieldsOk)
  | _, _ => .error (stx, s!"Cannot scale {tyToString t} by {tyToString sc}")

/-- Find a field in a schema and return its type and HasField proof -/
unsafe def findField (stx : SourceLocation) : (σ : Schema) → (name : String)
    → Except TypeError ((t : SurfaceTy) × HasField σ name t)
  | [], name => .error (stx, s!"Field '{name}' not found in record")
  | (n, t) :: rest, name =>
      if h : n = name then
        pure ⟨t, h ▸ HasField.here⟩
      else do
        let ⟨t', pf⟩ ← findField stx rest name
        pure ⟨t', HasField.there pf⟩

-- ============================================================================
-- Type Inference for DeBruijn terms (producing STerm2/STermLoc2)
-- ============================================================================

namespace TypeInfer2

/-- Build typed record fields from sorted (name, term) pairs and an expected schema. -/
unsafe def inferRecordFields2 {ctx : List SurfaceTy}
    (inferFn : (stx : SourceLocation) → (ty : SurfaceTy) → UntypedTermLoc ctx.length
               → Except TypeError (STermLoc2 ctx ty))
    : (stx : SourceLocation) → (σ : Schema) → List (String × UntypedTermLoc ctx.length)
    → Except TypeError (STermFields2 ctx σ)
  | _, [], [] => pure STermFields2.nil
  | stx, [], _ :: _ => .error (stx, "Too many fields in record")
  | stx, _ :: _, [] => .error (stx, "Too few fields in record")
  | stx, (expectedName, expectedTy) :: restSchema, (actualName, e) :: restFields => do
      if expectedName != actualName then
        .error (e.stx, s!"Field name mismatch: expected '{expectedName}', got '{actualName}'")
      else
        let term ← inferFn e.stx expectedTy e
        let restTerms ← inferRecordFields2 inferFn stx restSchema restFields
        pure (STermFields2.cons term restTerms)

-- Additive identities as surface terms (used for `if-then` sugar).
mutual
  /-- Additive identity term for the given `SAdd` evidence. -/
  unsafe def zeroOfSAddLoc {ctx : List SurfaceTy} {ty : SurfaceTy}
      (stx : SourceLocation) (a : SAdd ty) : STermLoc2 ctx ty :=
    match ty, a with
    | .bool, .boolA => STermLoc2.mk stx (STerm2.constBool false)
    | .int, .intA => STermLoc2.mk stx (STerm2.constInt 0)
    | .real, .realA => STermLoc2.mk stx (STerm2.constReal 0.0)
    | .date, .dateA =>
        let emptyRec : STermLoc2 ctx (.record []) :=
          STermLoc2.mk stx (STerm2.constRecord STermFields2.nil)
        STermLoc2.mk stx (STerm2.builtin (SBuiltin.DateLit 10101) emptyRec)
    | .string, .stringA => STermLoc2.mk stx (STerm2.constString "")
    | .dict dom range, .dictA _ =>
        STermLoc2.mk stx (STerm2.emptyDict (domain := dom) (ran := range))
    | .record σ, .recordA fields =>
        STermLoc2.mk stx (STerm2.constRecord (zerosForSAddFields (ctx := ctx) stx σ fields))

  unsafe def zerosForSAddFields {ctx : List SurfaceTy} (stx : SourceLocation)
      : (σ : Schema) → HList (fun p => SAdd p.snd) σ → STermFields2 ctx σ
    | [], .nil => STermFields2.nil
    | (_name, t) :: rest, .cons h tl =>
        STermFields2.cons (zeroOfSAddLoc (ctx := ctx) (ty := t) stx h) (zerosForSAddFields (ctx := ctx) stx rest tl)
end

/-- Main type inference function for DeBruijn terms.

    Parameters:
    - `ctx`: typed context (List SurfaceTy)
    - `expectedTy`: expected type
    - `e`: the untyped term with location

    Returns: either a type error with SourceLocation location, or a typed DeBruijn surface term
-/
unsafe def infer2 (ctx : List SurfaceTy)
    (expectedTy : SurfaceTy)
    (e : UntypedTermLoc ctx.length)
    : Except TypeError (STermLoc2 ctx expectedTy) := do
  let stx := e.stx
  match e.term with
  | .var i =>
      let varTy := getTypeAt ctx i
      if tyEq varTy expectedTy then
        let mem := finToMem ctx i
        pure (STermLoc2.mk stx (STerm2.var (unsafeCast mem)))
      else
        .error (stx, s!"Variable type mismatch: expected {tyToString expectedTy}, got {tyToString varTy}")

  | .constInt i =>
      match expectedTy with
      | .int => pure (STermLoc2.mk stx (STerm2.constInt i))
      | ty => .error (stx, s!"Type mismatch: expected {tyToString ty}, got int")

  | .constReal r =>
      match expectedTy with
      | .real => pure (STermLoc2.mk stx (STerm2.constReal r))
      | ty => .error (stx, s!"Type mismatch: expected {tyToString ty}, got real")

  | .constBool b =>
      match expectedTy with
      | .bool => pure (STermLoc2.mk stx (STerm2.constBool b))
      | ty => .error (stx, s!"Type mismatch: expected {tyToString ty}, got bool")

  | .constString s =>
      match expectedTy with
      | .string => pure (STermLoc2.mk stx (STerm2.constString s))
      | ty => .error (stx, s!"Type mismatch: expected {tyToString ty}, got string")

  | .constRecord fields =>
      match expectedTy with
      | .record σ => do
          let sortedFields := UntypedTermFields.sortByName fields
          let fieldTerms ← inferRecordFields2 (fun stx ty e => infer2 ctx ty e) stx σ (sortedFields.toList)
          pure (STermLoc2.mk stx (STerm2.constRecord fieldTerms))
      | ty => .error (stx, s!"Type mismatch: expected {tyToString ty}, got record")

  | .emptyDict =>
      match expectedTy with
      | .dict expDom expRange =>
          pure (STermLoc2.mk stx (STerm2.emptyDict (domain := expDom) (ran := expRange)))
      | ty =>
          .error (stx, s!"Expected dictionary type for empty dict, got {tyToString ty}")

  | .emptyDictAnn domTy rangeTy =>
      match expectedTy with
      | .dict expDom expRange =>
          if tyEq domTy expDom && tyEq rangeTy expRange then
            pure (STermLoc2.mk stx (STerm2.emptyDict (domain := expDom) (ran := expRange)))
          else
            let expected := tyToString (.dict expDom expRange)
            let got := tyToString (.dict domTy rangeTy)
            .error (stx, s!"Empty dict type mismatch: expected type {expected}, got type {got}")
      | ty =>
          .error (stx, s!"Expected dictionary type for empty dict, got {tyToString ty}")

  | .dictInsert k v d =>
      match expectedTy with
      | .dict domTy rangeTy => do
          let kTerm ← infer2 ctx domTy k
          let vTerm ← infer2 ctx rangeTy v
          let dTerm ← infer2 ctx (.dict domTy rangeTy) d
          pure (STermLoc2.mk stx (STerm2.dictInsert kTerm vTerm dTerm))
      | ty =>
          .error (stx, s!"Expected dictionary type for dict insert, got {tyToString ty}")

  | .not inner =>
      match expectedTy with
      | .bool => do
          let innerTerm ← infer2 ctx .bool inner
          pure (STermLoc2.mk stx (STerm2.not innerTerm))
      | ty => .error (stx, s!"Type mismatch: expected {tyToString ty}, got bool (from not)")

  | .ite c t f => do
      let condTerm ← infer2 ctx .bool c
      let thenTerm ← infer2 ctx expectedTy t
      let elseTerm ← infer2 ctx expectedTy f
      pure (STermLoc2.mk stx (STerm2.ite condTerm thenTerm elseTerm))

  | .iteThen c t => do
      let condTerm ← infer2 ctx .bool c
      let thenTerm ← infer2 ctx expectedTy t
      let addEv ← synthSAdd stx expectedTy
      let elseTerm : STermLoc2 ctx expectedTy := zeroOfSAddLoc (ctx := ctx) (ty := expectedTy) stx addEv
      pure (STermLoc2.mk stx (STerm2.ite condTerm thenTerm elseTerm))

  | .letin bound body => do
      let boundTy ← typeof2 ctx bound
      let boundTerm ← infer2 ctx boundTy bound
      let bodyTerm ← infer2 (boundTy :: ctx) expectedTy body
      pure (STermLoc2.mk stx (STerm2.letin boundTerm bodyTerm))

  | .add e1 e2 => do
      let term1 ← infer2 ctx expectedTy e1
      let term2 ← infer2 ctx expectedTy e2
      let addEv ← synthSAdd stx expectedTy
      pure (STermLoc2.mk stx (STerm2.add addEv term1 term2))

  | .mul scTy e1 e2 => do
      let ty1 ← typeof2 ctx e1
      let ty2 ← typeof2 ctx e2
      let resultTy := stensor ty1 ty2
      let term1 ← infer2 ctx ty1 e1
      let term2 ← infer2 ctx ty2 e2
      let s1 ← synthSScale stx scTy ty1
      let s2 ← synthSScale stx scTy ty2
      let mulTerm : STermLoc2 ctx resultTy :=
        STermLoc2.mk stx (STerm2.mul s1 s2 term1 term2)
      checkTyEq2 stx resultTy expectedTy mulTerm

  | .projByName name inner => do
      let innerTy ← typeof2 ctx inner
      match innerTy with
      | .record σ => do
          let ⟨fieldTy, pf⟩ ← findField stx σ name
          let innerTerm ← infer2 ctx (.record σ) inner
          let projTerm : STermLoc2 ctx fieldTy :=
            STermLoc2.mk stx (STerm2.projByName pf innerTerm)
          checkTyEq2 stx fieldTy expectedTy projTerm
      | ty => .error (stx, s!"Cannot project from non-record type {tyToString ty}")

  | .lookup d k => do
      let dictTy ← typeof2 ctx d
      let keyTy ← typeof2 ctx k
      match dictTy with
      | .dict domTy rangeTy =>
          if !tyEq keyTy domTy then
            .error (k.stx, s!"Lookup key type mismatch: expected {tyToString domTy}, got {tyToString keyTy}")
          else do
            let dTerm ← infer2 ctx (.dict domTy rangeTy) d
            let kTerm ← infer2 ctx domTy k
            let addEv ← synthSAdd stx rangeTy
            let lookupTerm : STermLoc2 ctx rangeTy :=
              STermLoc2.mk stx (STerm2.lookup addEv dTerm kTerm)
            checkTyEq2 stx rangeTy expectedTy lookupTerm
      | ty => .error (stx, s!"Cannot lookup in non-dictionary type {tyToString ty}")

  | .sum d body => do
      let dictTy ← typeof2 ctx d
      match dictTy with
      | .dict domTy rangeTy => do
          let dTerm ← infer2 ctx (.dict domTy rangeTy) d
          let bodyTerm ← infer2 (domTy :: rangeTy :: ctx) expectedTy body
          let addEv ← synthSAdd stx expectedTy
          pure (STermLoc2.mk stx (STerm2.sum addEv dTerm bodyTerm))
      | ty => .error (stx, s!"sum expects dictionary, got {tyToString ty}")

  | .builtinAnd arg => do
      let argTerm ← infer2 ctx (.record [("_1", .bool), ("_2", .bool)]) arg
      let builtinTerm : STermLoc2 ctx .bool :=
        STermLoc2.mk stx (STerm2.builtin SBuiltin.And argTerm)
      checkTyEq2 stx .bool expectedTy builtinTerm

  | .builtinOr arg => do
      let argTerm ← infer2 ctx (.record [("_1", .bool), ("_2", .bool)]) arg
      let builtinTerm : STermLoc2 ctx .bool :=
        STermLoc2.mk stx (STerm2.builtin SBuiltin.Or argTerm)
      checkTyEq2 stx .bool expectedTy builtinTerm

  | .builtinEq _ arg => do
      -- Infer the type of the argument to get the actual comparison type
      let argTy ← typeof2 ctx arg
      match argTy with
      | .record [("_1", t1), ("_2", _)] =>
          let argTerm ← infer2 ctx (.record [("_1", t1), ("_2", t1)]) arg
          let builtinTerm : STermLoc2 ctx .bool :=
            STermLoc2.mk stx (STerm2.builtin SBuiltin.Eq argTerm)
          checkTyEq2 stx .bool expectedTy builtinTerm
      | other => .error (stx, s!"== expects a pair record argument, got {tyToString other}")

  | .builtinLeq _ arg => do
      -- Infer the type of the argument to get the actual comparison type
      let argTy ← typeof2 ctx arg
      match argTy with
      | .record [("_1", t1), ("_2", _)] =>
          let argTerm ← infer2 ctx (.record [("_1", t1), ("_2", t1)]) arg
          let builtinTerm : STermLoc2 ctx .bool :=
            STermLoc2.mk stx (STerm2.builtin SBuiltin.Leq argTerm)
          checkTyEq2 stx .bool expectedTy builtinTerm
      | other => .error (stx, s!"<= expects a pair record argument, got {tyToString other}")

  | .builtinLt _ arg => do
      -- Infer the type of the argument to get the actual comparison type
      let argTy ← typeof2 ctx arg
      match argTy with
      | .record [("_1", t1), ("_2", _)] =>
          let argTerm ← infer2 ctx (.record [("_1", t1), ("_2", t1)]) arg
          let builtinTerm : STermLoc2 ctx .bool :=
            STermLoc2.mk stx (STerm2.builtin SBuiltin.Lt argTerm)
          checkTyEq2 stx .bool expectedTy builtinTerm
      | other => .error (stx, s!"< expects a pair record argument, got {tyToString other}")

  | .builtinSub _ arg => do
      -- Infer the type of the argument to get the actual subtraction type
      let argTy ← typeof2 ctx arg
      match argTy with
      | .record [("_1", t1), ("_2", _)] =>
          let argTerm ← infer2 ctx (.record [("_1", t1), ("_2", t1)]) arg
          let builtinTerm : STermLoc2 ctx t1 :=
            STermLoc2.mk stx (STerm2.builtin SBuiltin.Sub argTerm)
          checkTyEq2 stx t1 expectedTy builtinTerm
      | other => .error (stx, s!"- expects a pair record argument, got {tyToString other}")

  | .builtinStrEndsWith arg => do
      let argTerm ← infer2 ctx (.record [("_1", .string), ("_2", .string)]) arg
      let builtinTerm : STermLoc2 ctx .bool :=
        STermLoc2.mk stx (STerm2.builtin SBuiltin.StrEndsWith argTerm)
      checkTyEq2 stx .bool expectedTy builtinTerm

  | .builtinDom _ _ arg => do
      -- First infer the type of the argument to get actual dom/range
      let argTy ← typeof2 ctx arg
      match argTy with
      | .dict actualDom actualRange =>
          let argTerm ← infer2 ctx (.dict actualDom actualRange) arg
          let builtinTerm : STermLoc2 ctx (.dict actualDom .bool) :=
            STermLoc2.mk stx (STerm2.builtin SBuiltin.Dom argTerm)
          checkTyEq2 stx (.dict actualDom .bool) expectedTy builtinTerm
      | other => .error (stx, s!"dom expects a dictionary argument, got {tyToString other}")

  | .builtinRange arg => do
      let argTerm ← infer2 ctx .int arg
      let builtinTerm : STermLoc2 ctx (.dict .int .bool) :=
        STermLoc2.mk stx (STerm2.builtin SBuiltin.Range argTerm)
      checkTyEq2 stx (.dict .int .bool) expectedTy builtinTerm

  | .builtinDateLit yyyymmdd => do
      let emptyRec : STermLoc2 ctx (.record []) :=
        STermLoc2.mk stx (STerm2.constRecord STermFields2.nil)
      let builtinTerm : STermLoc2 ctx .date :=
        STermLoc2.mk stx (STerm2.builtin (SBuiltin.DateLit yyyymmdd) emptyRec)
      checkTyEq2 stx .date expectedTy builtinTerm

  | .builtinConcat σ1 σ2 arg => do
      let argTy ← typeof2 ctx arg
      match argTy with
      | .record [("_1", .record σ1), ("_2", .record σ2)] => do
          let argTerm ← infer2 ctx (.record [("_1", .record σ1), ("_2", .record σ2)]) arg
          let builtinTerm : STermLoc2 ctx (.record (σ1 ++ σ2)) :=
            STermLoc2.mk stx (STerm2.builtin (SBuiltin.Concat σ1 σ2) argTerm)
          checkTyEq2 stx (.record (σ1 ++ σ2)) expectedTy builtinTerm
      | other => .error (stx, s!"concat expects a pair of records, got {tyToString other}")

end TypeInfer2

-- ============================================================================
-- Top-level API for DeBruijn type inference
-- ============================================================================

/-- Type-check a closed untyped term (context = []) with an expected result type.

    Returns either:
    - `.ok sterm`: a typed DeBruijn surface term
    - `.error (stx, msg)`: for use with `throwErrorAt stx msg`
-/
unsafe def typeinfer2 (expectedTy : SurfaceTy) (e : UntypedTermLoc 0)
    : Except TypeError (STermLoc2 [] expectedTy) :=
  TypeInfer2.infer2 [] expectedTy e

/-- Type-check an untyped term in a given typed context.

    Parameters:
    - `ctx`: typed context (List SurfaceTy)
    - `expectedTy`: expected result type
    - `e`: untyped term with ctx.length variables in scope

    Returns either:
    - `.ok sterm`: a typed DeBruijn surface term
    - `.error (stx, msg)`: for use with `throwErrorAt stx msg`
-/
unsafe def typeinferOpen2 (ctx : List SurfaceTy)
    (expectedTy : SurfaceTy) (e : UntypedTermLoc ctx.length)
    : Except TypeError (STermLoc2 ctx expectedTy) :=
  TypeInfer2.infer2 ctx expectedTy e

-- ============================================================================
-- Load Extraction: LoadTerm (PHOAS) → UntypedTerm (DeBruijn)
-- ============================================================================

/-- Collect all distinct (path, type, SourceLocation) triples from a LoadTerm.
    Sorted alphabetically by path. If the same path appears with different types,
    later occurrences are ignored.
    Note: Uses Nat as rep for PHOAS instantiation during traversal. -/
unsafe def collectLoads (e : LoadTermLoc Unit) : List (String × SurfaceTy × SourceLocation) :=
  let collected := go e []
  let sorted := collected.toArray.qsort (fun (p1, _, _) (p2, _, _) => p1 < p2) |>.toList
  dedup sorted
where
  go : LoadTermLoc Unit → List (String × SurfaceTy × SourceLocation) → List (String × SurfaceTy × SourceLocation)
    | .mk stx inner, acc =>
      match inner with
      | .var _ => acc
      | .constInt _ => acc
      | .constReal _ => acc
      | .constBool _ => acc
      | .constString _ => acc
      | .constRecord fields =>
          fields.foldl (fun acc' (_, e) => go e acc') acc
      | .emptyDict => acc
      | .emptyDictAnn _ _ => acc
      | .dictInsert k v d => go d (go v (go k acc))
      | .not e => go e acc
      | .ite c t f => go f (go t (go c acc))
      | .iteThen c t => go t (go c acc)
      | .letin bound body =>
          let boundLoads := go bound acc
          go (body ()) boundLoads  -- dummy Nat for PHOAS traversal
      | .add e1 e2 => go e2 (go e1 acc)
      | .mul _ e1 e2 => go e2 (go e1 acc)
      | .projByName _ e => go e acc
      | .lookup d k => go k (go d acc)
      | .sum d body =>
          let dLoads := go d acc
          go (body () ()) dLoads  -- dummy Nats for PHOAS traversal
      | .load path ty =>
          if acc.any (fun (p, _, _) => p == path) then acc
          else (path, ty, stx) :: acc
      | .builtinAnd arg => go arg acc
      | .builtinOr arg => go arg acc
      | .builtinEq _ arg => go arg acc
      | .builtinLeq _ arg => go arg acc
      | .builtinLt _ arg => go arg acc
      | .builtinSub _ arg => go arg acc
      | .builtinStrEndsWith arg => go arg acc
      | .builtinDom _ _ arg => go arg acc
      | .builtinRange arg => go arg acc
      | .builtinDateLit _ => acc
      | .builtinConcat _ _ arg => go arg acc

  dedup : List (String × SurfaceTy × SourceLocation) → List (String × SurfaceTy × SourceLocation)
    | [] => []
    | [x] => [x]
    | (p1, t1, s1) :: (p2, t2, s2) :: rest =>
        if p1 == p2 then dedup ((p1, t1, s1) :: rest)
        else (p1, t1, s1) :: dedup ((p2, t2, s2) :: rest)

/-- Result of extracting loads from a LoadTerm -/
structure ExtractedLoads2 where
  ctx       : List SurfaceTy        -- Types of loads (the context)
  loadPaths : List String           -- File paths for loads
  term      : UntypedTermLoc ctx.length  -- The transformed DeBruijn term

/-- Convert a LoadTerm (PHOAS) to an UntypedTerm (DeBruijn) by:
    1. Replacing load nodes with variables referencing the context
    2. Converting PHOAS variables to DeBruijn indices

    The transformation uses Nat as rep for PHOAS, where the Nat value
    represents the "level" (depth) at which a variable was bound.
    DeBruijn index = currentDepth - 1 - level.

    Loads are placed at the beginning of the context (indices 0..n-1).
-/
unsafe def extractLoads2 (e : LoadTerm) : Except TypeError ExtractedLoads2 := do
  let eNat : LoadTermLoc Nat := e (rep := Nat)
  let loads := collectLoads e
  let ctx : List SurfaceTy := loads.map (fun (_, ty, _) => ty)
  let loadPaths : List String := loads.map (fun (path, _, _) => path)
  let pathToIndex := zipWithIndex loads
  -- Transform starting with ctx.length as the base depth (loads occupy indices 0..n-1)
  have hlen : ctx.length = loads.length := by simp [ctx]
  let term0 : UntypedTermLoc loads.length ← transform loads.length pathToIndex eNat
  let term : UntypedTermLoc ctx.length := by
    simpa [hlen] using term0
  pure { ctx := ctx, loadPaths := loadPaths, term := term }
where
  zipWithIndex (l : List (String × SurfaceTy × SourceLocation)) : List (String × Nat) :=
    let rec go (l : List (String × SurfaceTy × SourceLocation)) (i : Nat) : List (String × Nat) :=
      match l with
      | [] => []
      | (path, _, _) :: rest => (path, i) :: go rest (i + 1)
    go l 0

  findIndex (pathToIndex : List (String × Nat)) (path : String) : Option Nat :=
    pathToIndex.find? (fun (p, _) => p == path) |>.map (·.2)

  -- Convert PHOAS level to DeBruijn index
  -- In PHOAS with Nat, level is the depth when introduced
  -- DeBruijn index = currentDepth - 1 - level
  -- Note: level < currentDepth invariant holds for well-formed PHOAS terms
  mkFin (stx : SourceLocation) (n i : Nat) : Except TypeError (Fin n) :=
    if h : i < n then
      pure ⟨i, h⟩
    else
      .error (stx, s!"internal error: index {i} out of bounds for context size {n}")

  levelToIndex (stx : SourceLocation) (currentDepth : Nat) (level : Nat) : Except TypeError (Fin currentDepth) := do
    if level < currentDepth then
      mkFin stx currentDepth (currentDepth - 1 - level)
    else
      .error (stx, s!"internal error: ill-scoped PHOAS variable (level={level}, depth={currentDepth})")

  -- Transform LoadTermLoc (PHOAS) to UntypedTermLoc (DeBruijn)
  transform (depth : Nat) (pathToIndex : List (String × Nat))
      : LoadTermLoc Nat → Except TypeError (UntypedTermLoc depth)
    | .mk stx inner => do
      let inner' ← transformInner depth stx pathToIndex inner
      pure (.mk stx inner')

  -- Transform LoadTerm record fields to UntypedTermFields
  transformFields (depth : Nat) (pathToIndex : List (String × Nat))
      : List (String × LoadTermLoc Nat) → Except TypeError (UntypedTermFields depth)
    | [] => pure .nil
    | (name, e) :: rest => do
        let e' ← transform depth pathToIndex e
        let rest' ← transformFields depth pathToIndex rest
        pure (.cons name e' rest')

  transformInner (depth : Nat) (stx : SourceLocation) (pathToIndex : List (String × Nat))
      : LoadTerm' Nat → Except TypeError (UntypedTerm' depth)
    | .var level =>
        -- Convert PHOAS level to DeBruijn index
        return .var (← levelToIndex stx depth level)
    | .constInt i => pure (.constInt i)
    | .constReal r => pure (.constReal r)
    | .constBool b => pure (.constBool b)
    | .constString s => pure (.constString s)
    | .constRecord fields => do
        let fields' ← transformFields depth pathToIndex fields
        pure (.constRecord fields')
    | .emptyDict => pure .emptyDict
    | .emptyDictAnn dom range => pure (.emptyDictAnn dom range)
    | .dictInsert k v d =>
        return .dictInsert (← transform depth pathToIndex k) (← transform depth pathToIndex v) (← transform depth pathToIndex d)
    | .not e => return .not (← transform depth pathToIndex e)
    | .ite c t f =>
        return .ite (← transform depth pathToIndex c) (← transform depth pathToIndex t) (← transform depth pathToIndex f)
    | .iteThen c t =>
        return .iteThen (← transform depth pathToIndex c) (← transform depth pathToIndex t)
    | .letin bound body =>
        -- Increase depth for the body, pass current depth as the PHOAS level
        return .letin (← transform depth pathToIndex bound) (← transform (depth + 1) pathToIndex (body depth))
    | .add e1 e2 =>
        return .add (← transform depth pathToIndex e1) (← transform depth pathToIndex e2)
    | .mul sc e1 e2 =>
        return .mul sc (← transform depth pathToIndex e1) (← transform depth pathToIndex e2)
    | .projByName name e =>
        return .projByName name (← transform depth pathToIndex e)
    | .lookup d k =>
        return .lookup (← transform depth pathToIndex d) (← transform depth pathToIndex k)
    | .sum d body =>
        -- sum binds key and value, so increase depth by 2
        -- In DeBruijn context (dom :: range :: ctx):
        --   Index 0 = key (dom), Index 1 = value (range)
        -- PHOAS body is (fun key value => ...), so we pass:
        --   key gets level (depth + 1) → index 0 at depth (depth + 2)
        --   value gets level depth → index 1 at depth (depth + 2)
        return .sum (← transform depth pathToIndex d) (← transform (depth + 2) pathToIndex (body (depth + 1) depth))
    | .load path _ =>
        -- Load becomes a variable at its index in the context
        match findIndex pathToIndex path with
        | some i =>
            -- Load index i maps to a Fin in the DeBruijn context
            -- At depth d with n loads, load i is at index (d - n + i)
            -- because loads start at indices 0..n-1, then let bindings push them deeper
            let numLoads := pathToIndex.length
            let loadIndex := depth - numLoads + i
            return .var (← mkFin stx depth loadIndex)
        | none => .error (stx, s!"internal error: load path not found in load map: {path}")
    | .builtinAnd arg => return .builtinAnd (← transform depth pathToIndex arg)
    | .builtinOr arg => return .builtinOr (← transform depth pathToIndex arg)
    | .builtinEq t arg => return .builtinEq t (← transform depth pathToIndex arg)
    | .builtinLeq t arg => return .builtinLeq t (← transform depth pathToIndex arg)
    | .builtinLt t arg => return .builtinLt t (← transform depth pathToIndex arg)
    | .builtinSub t arg => return .builtinSub t (← transform depth pathToIndex arg)
    | .builtinStrEndsWith arg => return .builtinStrEndsWith (← transform depth pathToIndex arg)
    | .builtinDom dom range arg => return .builtinDom dom range (← transform depth pathToIndex arg)
    | .builtinRange arg => return .builtinRange (← transform depth pathToIndex arg)
    | .builtinDateLit yyyymmdd => pure (.builtinDateLit yyyymmdd)
    | .builtinConcat σ1 σ2 arg => return .builtinConcat σ1 σ2 (← transform depth pathToIndex arg)

-- ============================================================================
-- Full Pipeline: LoadTerm → SProg2 (DeBruijn)
-- ============================================================================

/-- A dummy SProg2 for error cases -/
unsafe def dummySProg2 : SProg2 :=
  { t := .int
    ctx := []
    term := STermLoc2.withUnknownLoc (STerm2.constInt 0)
    loadPaths := [] }

unsafe instance : Inhabited SProg2 := ⟨dummySProg2⟩

/-- Process a LoadTerm and return an SProg2 directly.

    This is the main entry point for the program-level DSL.
    Uses the new DeBruijn-indexed pipeline:
    1. Extract loads from LoadTerm (PHOAS) to get UntypedTerm (DeBruijn)
    2. Type-infer to get STerm2 (DeBruijn typed)

    If type inference fails, panics with an error message.
-/
unsafe def loadTermToSProg2 (expectedTy : SurfaceTy) (e : LoadTerm) : SProg2 :=
  match extractLoads2 e with
  | .error (stx, msg) =>
      let whereBlock := sourceLocWhere stx
      panic! s!"Internal error while extracting loads\nExpected: {tyToString expectedTy}\nAt: {whereBlock}\n{msg}"
  | .ok extracted =>
      match typeinferOpen2 extracted.ctx expectedTy extracted.term with
      | .ok sterm =>
          { t := expectedTy
            ctx := extracted.ctx
            term := sterm
            loadPaths := extracted.loadPaths }
      | .error (stx, msg) =>
          let loadLines :=
            (extracted.loadPaths.zip extracted.ctx).map (fun (p, ty) => s!"  - {p} : {tyToString ty}")
          let loadsBlock :=
            if loadLines.isEmpty then
              ""
            else
              "\nLoads:\n" ++ String.intercalate "\n" loadLines
          let whereBlock := sourceLocWhere stx
          panic! s!"Type error while typechecking SDQL program\nExpected: {tyToString expectedTy}\nAt: {whereBlock}\n{msg}{loadsBlock}"

/-- Process a LoadTerm through the pipeline with error handling.

    Pipeline:
    1. Extract loads to get context (List SurfaceTy) and UntypedTerm (DeBruijn)
    2. Type-infer to get STermLoc2 (DeBruijn typed)

    Returns either:
    - `.ok sprog`: the typed program
    - `.error (stx, msg)`: for use with `throwErrorAt stx msg`
-/
unsafe def processLoadTerm2 (expectedTy : SurfaceTy) (e : LoadTerm)
    : Except TypeError SProg2 := do
  let extracted ← extractLoads2 e
  match typeinferOpen2 extracted.ctx expectedTy extracted.term with
  | .ok sterm =>
      .ok { t := expectedTy,
            ctx := extracted.ctx,
            term := sterm,
            loadPaths := extracted.loadPaths }
  | .error (stx, msg) =>
      -- let syn : Lean.Syntax := ofRange
      .error (stx, msg)

-- ============================================================================
-- Tests (DeBruijn)
-- ============================================================================

/-- Helper to show the result of DeBruijn \ inference -/
unsafe def showResult2 {ctx : List SurfaceTy} (expectedTy : SurfaceTy)
    (result : Except TypeError (STermLoc2 ctx expectedTy)) : String :=
  match result with
  | .ok _ => s!"OK: {tyToString expectedTy}"
  | .error (_, msg) => s!"Error: {msg}"

/-- Helper: create a dummy SourceLocation for testing -/
def dummyStx : SourceLocation := ⟨ 0, 0, ""⟩

/-- Helper: wrap a term with dummy SourceLocation (for closed terms) -/
def withDummy (t : UntypedTerm' 0) : UntypedTermLoc 0 :=
  .mk dummyStx t

-- Test: integer literal
unsafe def test_int : String :=
  let term := withDummy (.constInt 42)
  showResult2 .int (typeinfer2 .int term)

#eval! test_int  -- "OK: int"

-- Test: boolean literal
unsafe def test_bool : String :=
  let term := withDummy (.constBool true)
  showResult2 .bool (typeinfer2 .bool term)

#eval! test_bool  -- "OK: bool"

-- Test: addition
unsafe def test_add : String :=
  let term : UntypedTermLoc 0 := .mk dummyStx (.add
    (.mk dummyStx (.constInt 1))
    (.mk dummyStx (.constInt 2)))
  showResult2 .int (typeinfer2 .int term)

#eval! test_add  -- "OK: int"

-- Test: type error - expected int, got bool
unsafe def test_type_error : String :=
  let term := withDummy (.constBool true)
  showResult2 .int (typeinfer2 .int term)

#eval! test_type_error  -- "Error: Type mismatch: expected int, got bool"

-- Test: empty dict with type annotation
unsafe def test_empty_dict : String :=
  let term := withDummy (.emptyDictAnn .int .bool)
  showResult2 (.dict .int .bool) (typeinfer2 (.dict .int .bool) term)

#eval! test_empty_dict  -- "OK: { int -> bool }"

-- Test: record
unsafe def test_record : String :=
  let fields : UntypedTermFields 0 := .cons "name" (.mk dummyStx (.constString "Alice"))
    (.cons "age" (.mk dummyStx (.constInt 30)) .nil)
  let term : UntypedTermLoc 0 := .mk dummyStx (.constRecord fields)
  showResult2 (.record [("age", .int), ("name", .string)]) (typeinfer2 (.record [("age", .int), ("name", .string)]) term)

#eval! test_record  -- "OK: <age: int, name: string>"

-- Test: field projection
unsafe def test_proj : String :=
  let fields : UntypedTermFields 0 := .cons "name" (.mk dummyStx (.constString "Alice"))
    (.cons "age" (.mk dummyStx (.constInt 30)) .nil)
  let record : UntypedTermLoc 0 := .mk dummyStx (.constRecord fields)
  let term : UntypedTermLoc 0 := .mk dummyStx (.projByName "age" record)
  match typeof2 [] term with
  | .ok ty => showResult2 ty (typeinfer2 ty term)
  | .error (_, msg) => s!"Error: {msg}"

#eval! test_proj  -- "OK: int"
