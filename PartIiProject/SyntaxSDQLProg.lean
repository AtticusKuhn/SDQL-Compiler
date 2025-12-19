import Lean
import PartIiProject.SyntaxSDQL
import PartIiProject.SurfaceCore
import PartIiProject.untyped
import PartIiProject.Term2
import PartIiProject.CodegenRust
import Std

open Lean

namespace PartIiProject

/-
  Program-level EDSL for SDQL via `[SDQLProg { ty }| ... ]` quasiquotation.

  ## New Architecture (Pipeline-based)

  The parser now produces a `LoadTermLoc` which is then processed through:

  ```
    Parser (sdql syntax) → LoadTermLoc → UntypedTermLoc → STermLoc'
  ```

  Pipeline steps:
  1. `elabSDQLToLoad`: Parse SDQL syntax to `LoadTermLoc` (untyped, contains `load` constructs)
  2. `extractLoads`: Extract all `load` occurrences, replace with free variables, produce `UntypedTermLoc`
  3. `typeinferOpen`: Type-check the untyped term to produce a typed `STermLoc'`

  Benefits:
  - Simpler parser: no type inference or evidence synthesis at parse time
  - Better error messages: type errors include source location via `Syntax`
  - Cleaner separation of concerns: parsing vs type checking

  Usage: `[SDQLProg { <SurfaceTy> }| <sdql term with load[...] ...> ]`.
  The outer `{ <SurfaceTy> }` provides the program's overall result type.
-/

/- The core SDQL syntax (including `sum(<k,v> <- d)`) is declared in `SyntaxSDQL.lean`. -/

/- Program quasiquoter using the new pipeline -/
syntax "[SDQLProg" "{" sdqlty "}" "|" sdql "]" : term

macro_rules
  | `([SDQLProg { $t:sdqlty }| $e:sdql ]) => do
      -- Step 1: Elaborate to LoadTermLoc using the new pipeline
      let loadTermBody ← elabSDQLToLoad e

      -- Step 2: Elaborate the expected result type
      let tTerm ← elabTy t

      -- Step 3: Use loadTermToSProg to extract loads, type-check, and build SProg
      `(loadTermToSProg $tTerm $loadTermBody)

/- Program quasiquoter using DeBruijn pipeline (new architecture)
   Pipeline: Parser → LoadTerm → UntypedTerm → STerm2/SProg2 → Prog2 → Rust
-/
syntax "[SDQLProg2" "{" sdqlty "}" "|" sdql "]" : term

macro_rules
  | `([SDQLProg2 { $t:sdqlty }| $e:sdql ]) => do
      -- Step 1: Elaborate to LoadTermLoc using the parser
      let loadTermBody ← elabSDQLToLoad e

      -- Step 2: Elaborate the expected result type
      let tTerm ← elabTy t
    --   let y := loadTermToSProg2 tTerm loadTermBody

      -- Step 3: Use loadTermToSProg2 to extract loads, type-check with DeBruijn, and build SProg2
      `(loadTermToSProg2 $tTerm $loadTermBody)

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
