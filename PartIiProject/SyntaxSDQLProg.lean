import Lean
import Lean.Elab.Util
import PartIiProject.SyntaxSDQL
import PartIiProject.untyped
import PartIiProject.Term2
import PartIiProject.CodegenRust
import Std

open Lean

namespace PartIiProject

/-!
Program-level EDSL for SDQL via `[SDQLProg2 { ty }| ... ]`.

Pipeline:
`sdql` syntax → `LoadTerm` → `UntypedTermLoc` → `SProg2` → `Prog2` → Rust.
-/

/- The core SDQL syntax (including `sum(<k,v> <- d)`) is declared in `SyntaxSDQL.lean`. -/

/- Program quasiquoter using DeBruijn pipeline (new architecture)
   Pipeline: Parser → LoadTerm → UntypedTerm → STerm2/SProg2 → Prog2 → Rust
-/
syntax (name := sdqlProg2) "[SDQLProg2" "{" sdqlty "}" "|" sdql "]" : term

@[term_elab sdqlProg2] unsafe def elabSdqlProg2 : Lean.Elab.Term.TermElab := fun stx _expectedType? => do
  withRef stx do
    match stx with
    | `([SDQLProg2 { $t:sdqlty }| $e:sdql ]) => do
        -- Step 1: Elaborate to LoadTermLoc using the parser
        let loadTermBodyStx ← Lean.Elab.liftMacroM <| elabSDQLToLoad e

        -- Step 2: Elaborate the expected result type
        let tTermStx ← Lean.Elab.liftMacroM <| elabTy t

        -- Step 3: Elaborate the generated terms to expressions and evaluate them, so we can
        -- fail with a proper elaboration error (instead of `panic!` defaulting to `Inhabited`).
        let expectedTyExpr ← Lean.Elab.Term.elabTerm tTermStx (some (Lean.mkConst ``SurfaceTy))
        let loadExpr ← Lean.Elab.Term.elabTerm loadTermBodyStx (some (Lean.mkConst ``LoadTerm))

        let expectedTy ← Lean.Meta.evalExpr SurfaceTy (Lean.mkConst ``SurfaceTy) expectedTyExpr (safety := .unsafe)

        -- Run the checker during elaboration.
        let checkExpr := Lean.mkApp2 (Lean.mkConst ``processLoadTerm2) expectedTyExpr loadExpr
        let checkType ← Lean.Meta.inferType checkExpr
        let checkRes ← Lean.Meta.evalExpr (Except TypeError SProg2) checkType checkExpr (safety := .unsafe)
        match checkRes with
        | .ok _ =>
            -- Expand to the normal runtime pipeline (now guaranteed to succeed).
            return Lean.mkApp2 (Lean.mkConst ``loadTermToSProg2) expectedTyExpr loadExpr
        | .error (loc, msg) =>
            let whereBlock := sourceLocWhere loc
            throwErrorAt (Syntax.node (.original ⟨ loc.substring, ⟨ loc.startPos⟩ , ⟨ loc.endPos⟩⟩  ⟨ loc.startPos⟩   ⟨ loc.substring, ⟨ loc.startPos⟩ , ⟨ loc.endPos⟩⟩  ⟨ loc.endPos⟩ ) .anonymous #[]) s!"Type error while typechecking SDQL program\nExpected: {tyToString expectedTy}\nAt: {whereBlock}\n{msg}"

            -- throwError s!"Type error while typechecking SDQL program\nExpected: {tyToString expectedTy}\nAt: {whereBlock}\n{msg}"
    | _ => Lean.Elab.throwUnsupportedSyntax

end PartIiProject

-- Examples for DeBruijn pipeline
namespace PartIiProject

-- DeBruijn pipeline examples (SProg2)
unsafe def ex_prog2_add : SProg2 := [SDQLProg2 { int }| 3 + 5 ]

unsafe def ex_prog2_dict_load : SProg2 :=
  [SDQLProg2 { { int -> int } }|
    { 3 -> 7 } + load[{ int -> int }]("data.tbl")
  ]

open ToCore2 in
unsafe def showProg2Term (p : SProg2) : String :=
  Term2.showTermLoc2 [] (trProg2 p).term

#eval! showProg2Term ex_prog2_add
#eval! showProg2Term ex_prog2_dict_load

-- Test Rust codegen from SProg2
open ToCore2 in
unsafe def renderRustFromSProg2 (p : SProg2) : String :=
  renderRustProg2Shown (trProg2 p)

#eval! renderRustFromSProg2 ex_prog2_add

end PartIiProject
