import PartIiProject.SurfaceCore2
import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.ExtractLoads
import PartIiProject.Untyped.Infer
import PartIiProject.Untyped.TypeUtil

open PartIiProject

/-!
Full pipeline: `LoadTerm` → `SProg2`.
-/

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

