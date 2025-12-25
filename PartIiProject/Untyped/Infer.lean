import PartIiProject.SurfaceCore2
import PartIiProject.Untyped.Evidence
import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.TypeOf
import PartIiProject.Untyped.TypeUtil
import PartIiProject.Untyped.UntypedTerm

open PartIiProject

/-!
Type inference from untyped DeBruijn terms to typed DeBruijn surface terms (`STermLoc2`).
-/

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
      let dTy ← typeof2 ctx d
      match dTy with
      | .dict domTy rangeTy =>
          let keyTy ← typeof2 ctx k
          if !tyEq keyTy domTy then
            .error (k.stx, s!"Lookup key type mismatch: expected {tyToString domTy}, got {tyToString keyTy}")
          else do
            let dTerm ← infer2 ctx (.dict domTy rangeTy) d
            let kTerm ← infer2 ctx domTy k
            let addEv ← synthSAdd stx rangeTy
            let lookupTerm : STermLoc2 ctx rangeTy :=
              STermLoc2.mk stx (STerm2.lookup addEv dTerm kTerm)
            checkTyEq2 stx rangeTy expectedTy lookupTerm
      | .record σ =>
          -- SDQL sugar: `r(n)` for constant integer `n` means positional projection.
          match k.term with
          | .constInt i =>
              if i < 0 then
                .error (k.stx, s!"Record projection index must be nonnegative, got {i}")
              else
                let idx := Int.toNat i
                let ⟨_nm, ⟨fieldTy, pf⟩⟩ ← findFieldByIndex k.stx σ idx
                let dTerm ← infer2 ctx (.record σ) d
                let projTerm : STermLoc2 ctx fieldTy :=
                  STermLoc2.mk stx (STerm2.projByName pf dTerm)
                checkTyEq2 stx fieldTy expectedTy projTerm
          | _ =>
              .error (k.stx, "Record projection expects a constant integer index")
      | ty =>
          .error (stx, s!"Cannot lookup in non-dictionary type {tyToString ty}")

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

