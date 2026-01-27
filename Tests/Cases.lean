import PartIiProject.Term2
import PartIiProject.CodegenRust
import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg
import Tests.GuardMsgs
import Tests.TPCH.Q01
import Tests.TPCH.Q02
import Tests.TPCH.Q03
import Tests.TPCH.Q04
import Tests.TPCH.Q05
import Tests.TPCH.Q06
import Tests.TPCH.Q07
import Tests.TPCH.Q09
import Tests.TPCH.Q10
import Tests.TPCH.Q11
import Tests.TPCH.Q12
import Tests.TPCH.Q13
import Tests.TPCH.Q14
import Tests.TPCH.Q15
import Tests.TPCH.Q16
import Tests.TPCH.Q17
import Tests.TPCH.Q18
import Tests.TPCH.Q19
import Tests.TPCH.Q20
import Tests.TPCH.Q21
import Tests.TPCH.Q22


namespace Tests
namespace Cases

open PartIiProject
open PartIiProject.Optimisations

/- Expected-output strings are produced by evaluating the term in Lean
   and pretty-printing the resulting value via `showValue`. -/

/- Sample test cases ported from inline demos. -/
/- Test cases support both closed terms and open terms with runtime parameters. -/
unsafe inductive TestCase where
  | program (name : String) (p : SProg2) (expected : String) : TestCase
  | programRef (name : String) (p : SProg2) (refBinPath : String) (envVars : List (String × String)) : TestCase
  | compileOnly (name : String) (p : SProg2) : TestCase
  | optimisationEq (name : String) (p : SProg2) (opts : List Optimisation)
      (envVars : List (String × String)) : TestCase

open TestCase

-- Build sample programs using the SDQL program DSL (no loads)
unsafe def p_add_int : SProg2 :=
  [SDQLProg2 { int }| 3 + 5 ]


unsafe def p_dict_is : SProg2 :=
  [SDQLProg2 { { int -> string } }| { 1 -> "one" } ]

unsafe def p_dict_ii : SProg2 :=
  [SDQLProg2 { { int -> int } }| { 1 -> 2, 3 -> 4 } ]

unsafe def p_lookup_hit : SProg2 :=
  [SDQLProg2 { int }| { 1 -> 2, 3 -> 4 } (1) ]

unsafe def p_lookup_miss : SProg2 :=
  [SDQLProg2 { int }| { 1 -> 2, 3 -> 4 } (0) ]

unsafe def p_sum_vals : SProg2 :=
  [SDQLProg2 { int }| sum( <k, v> in { 3 -> 4, 5 -> 6 } ) v ]

unsafe def p_underscore_ident : SProg2 :=
  [SDQLProg2 { int }| let _ = 3 in _ + 1 ]

unsafe def p_if_then_true : SProg2 :=
  [SDQLProg2 { int }| if true then 7 ]

unsafe def p_if_then_false : SProg2 :=
  [SDQLProg2 { int }| if false then 7 ]

unsafe def p_semiring_mul_real : SProg2 :=
  [SDQLProg2 { real }| 2.0 *s 3.0 ]

unsafe def p_closure_bool : SProg2 :=
  [SDQLProg2 { bool }| closure(false) ]

unsafe def p_closure_real : SProg2 :=
  [SDQLProg2 { real }| closure(0.5) ]

unsafe def smallCases : List TestCase :=
  [ TestCase.program "add_int" p_add_int "8"
  , TestCase.program "dict_insert" p_dict_is "{1 -> \"one\", }"
  , TestCase.program "lookup_hit" p_lookup_hit "2"
  , TestCase.program "lookup_miss" p_lookup_miss "0"
  , TestCase.program "sum_vals" p_sum_vals "10"
  , TestCase.program "underscore_ident" p_underscore_ident "4"
  , TestCase.program "if_then_true" p_if_then_true "7"
  , TestCase.program "if_then_false" p_if_then_false "0"
  , TestCase.program "semiring_mul_real" p_semiring_mul_real "6"
  , TestCase.program "closure_bool" p_closure_bool "true"
  , TestCase.program "closure_real" p_closure_real "2"
  ]

/- End-to-end optimisation correctness checks (Lean → Rust → binary). -/

unsafe def p_vertical_loop_fusion_key_map : SProg2 :=
  [SDQLProg2 { { int -> int } }|
    let y = sum( <x, x_v> <- ({ 1 -> 10, 2 -> 20 }) ) { x + 1 -> x_v } in
    sum( <x, x_v> <- y ) { x + 2 -> x_v }
  ]

unsafe def p_vertical_loop_fusion_value_map : SProg2 :=
  [SDQLProg2 { { int -> int } }|
    let y = sum( <x, x_v> <- ({ 1 -> 10, 2 -> 20 }) ) { x -> x_v + 1 } in
    sum( <x, x_v> <- y ) { x -> x_v + 2 }
  ]

unsafe def p_horizontal_loop_fusion : SProg2 :=
  [SDQLProg2 { int }|
    let d = { 1 -> 10, 2 -> 20 } in
    let y1 = sum( <k, v> <- d ) v in
    let y2 = sum( <k, v> <- d ) (v + 1) in
    y1 + y2
  ]

unsafe def p_loop_factorization_left : SProg2 :=
  [SDQLProg2 { int }|
    sum( <k, v> <- ({ 1 -> 10, 2 -> 20 }) ) (2 * v)
  ]

unsafe def p_loop_factorization_right : SProg2 :=
  [SDQLProg2 { int }|
    sum( <k, v> <- ({ 1 -> 10, 2 -> 20 }) ) (v * 2)
  ]

unsafe def p_loop_invariant_code_motion : SProg2 :=
  [SDQLProg2 { int }|
    let d = { 1 -> 10, 2 -> 20 } in
    sum( <k, v> <- d ) (let y = 5 in v + y)
  ]

unsafe def p_loop_memoization_lookup : SProg2 :=
  [SDQLProg2 { int }|
    sum( <k, v> <- ({ 1 -> 10, 2 -> 20 }) ) (if k == 1 then v)
  ]

unsafe def p_loop_memoization_partition : SProg2 :=
  [SDQLProg2 { { int -> int } }|
    sum( <k, v> <- ({ 1 -> 10, 2 -> 20 }) ) (if k == 1 then { k -> v })
  ]

unsafe def optimisationCases : List TestCase :=
  [ TestCase.optimisationEq "vertical_loop_fusion_key_map" p_vertical_loop_fusion_key_map
      [verticalLoopFusionKeyMap2, verticalLoopFusionValueMap2] []
  , TestCase.optimisationEq "vertical_loop_fusion_value_map" p_vertical_loop_fusion_value_map
      [verticalLoopFusionKeyMap2, verticalLoopFusionValueMap2] []
  , TestCase.optimisationEq "horizontal_loop_fusion" p_horizontal_loop_fusion
      [horizontalLoopFusion2] []
  , TestCase.optimisationEq "loop_factorization_left" p_loop_factorization_left
      [loopFactorizationLeft2] []
  , TestCase.optimisationEq "loop_factorization_right" p_loop_factorization_right
      [loopFactorizationRight2] []
  , TestCase.optimisationEq "loop_invariant_code_motion" p_loop_invariant_code_motion
      [loopInvariantCodeMotion2] []
  , TestCase.optimisationEq "loop_memoization_lookup" p_loop_memoization_lookup
      [loopMemoizationLookup2] []
  , TestCase.optimisationEq "loop_memoization_partition" p_loop_memoization_partition
      [loopMemoizationPartition2] []
  ]

/- TPCH-style programs exercise file-loading pipelines. Queries listed here are
   compiled to Rust, executed against the tiny TPCH dataset, and their outputs
   compared against the reference implementation results. -/
unsafe def tpchCases : List TestCase :=
  [ TestCase.programRef "tpch_q01" TPCH.Q01 "sdql-rs/target/release/tpch_q01_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q02" TPCH.Q02 "sdql-rs/target/release/tpch_q02_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q03" TPCH.Q03 "sdql-rs/target/release/tpch_q03_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q04" TPCH.Q04 "sdql-rs/target/release/tpch_q04_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q05" TPCH.Q05 "sdql-rs/target/release/tpch_q05_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q06" TPCH.Q06 "sdql-rs/target/release/tpch_q06_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q07" TPCH.Q07 "sdql-rs/target/release/tpch_q07_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q09" TPCH.Q09 "sdql-rs/target/release/tpch_q09_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q10" TPCH.Q10 "sdql-rs/target/release/tpch_q10_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q11" TPCH.Q11 "sdql-rs/target/release/tpch_q11_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q12" TPCH.Q12 "sdql-rs/target/release/tpch_q12_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q13" TPCH.Q13 "sdql-rs/target/release/tpch_q13_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q14" TPCH.Q14 "sdql-rs/target/release/tpch_q14_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q16" TPCH.Q16 "sdql-rs/target/release/tpch_q16_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q17" TPCH.Q17 "sdql-rs/target/release/tpch_q17_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q18" TPCH.Q18 "sdql-rs/target/release/tpch_q18_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q19" TPCH.Q19 "sdql-rs/target/release/tpch_q19_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q20" TPCH.Q20 "sdql-rs/target/release/tpch_q20_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q21" TPCH.Q21 "sdql-rs/target/release/tpch_q21_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  , TestCase.programRef "tpch_q22" TPCH.Q22 "sdql-rs/target/release/tpch_q22_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")]
  ]

def tpchTinyPrefix : String := "datasets/tpch-tiny/"

def rewriteTpchTinyLoadPathToGeneric (path : String) : String :=
  if path.startsWith tpchTinyPrefix then
    "datasets/tpch/" ++ path.drop tpchTinyPrefix.length
  else
    path

unsafe def rewriteTpchTinyLoadPathsToGeneric (p : SProg2) : SProg2 :=
  { p with loadPaths := p.loadPaths.map rewriteTpchTinyLoadPathToGeneric }

/- Same TPCH queries, but run against the scale factor 0.01 dataset. -/
unsafe def tpchCasesSF001 : List TestCase :=
  let sf001Env : List (String × String) :=
    [("TPCH_DATASET_PATH", "sdql-rs/datasets/tpch_datasets/SF_0.01")]
  [ TestCase.programRef "tpch_q01_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q01)
      "sdql-rs/target/release/tpch_q01_tiny" sf001Env
  , TestCase.programRef "tpch_q02_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q02)
      "sdql-rs/target/release/tpch_q02_tiny" sf001Env
  , TestCase.programRef "tpch_q03_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q03)
      "sdql-rs/target/release/tpch_q03_tiny" sf001Env
  , TestCase.programRef "tpch_q04_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q04)
      "sdql-rs/target/release/tpch_q04_tiny" sf001Env
  , TestCase.programRef "tpch_q05_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q05)
      "sdql-rs/target/release/tpch_q05_tiny" sf001Env
  , TestCase.programRef "tpch_q06_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q06)
      "sdql-rs/target/release/tpch_q06_tiny" sf001Env
  , TestCase.programRef "tpch_q07_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q07)
      "sdql-rs/target/release/tpch_q07_tiny" sf001Env
  , TestCase.programRef "tpch_q09_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q09)
      "sdql-rs/target/release/tpch_q09_tiny" sf001Env
  , TestCase.programRef "tpch_q10_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q10)
      "sdql-rs/target/release/tpch_q10_tiny" sf001Env
  , TestCase.programRef "tpch_q11_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q11)
      "sdql-rs/target/release/tpch_q11_tiny" sf001Env
  , TestCase.programRef "tpch_q12_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q12)
      "sdql-rs/target/release/tpch_q12_tiny" sf001Env
  , TestCase.programRef "tpch_q13_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q13)
      "sdql-rs/target/release/tpch_q13_tiny" sf001Env
  , TestCase.programRef "tpch_q14_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q14)
      "sdql-rs/target/release/tpch_q14_tiny" sf001Env
  , TestCase.programRef "tpch_q15_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q15)
      "sdql-rs/target/release/tpch_q15_tiny" sf001Env
  , TestCase.programRef "tpch_q16_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q16)
      "sdql-rs/target/release/tpch_q16_tiny" sf001Env
  , TestCase.programRef "tpch_q17_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q17)
      "sdql-rs/target/release/tpch_q17_tiny" sf001Env
  , TestCase.programRef "tpch_q18_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q18)
      "sdql-rs/target/release/tpch_q18_tiny" sf001Env
  , TestCase.programRef "tpch_q19_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q19)
      "sdql-rs/target/release/tpch_q19_tiny" sf001Env
  , TestCase.programRef "tpch_q20_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q20)
      "sdql-rs/target/release/tpch_q20_tiny" sf001Env
  , TestCase.programRef "tpch_q21_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q21)
      "sdql-rs/target/release/tpch_q21_tiny" sf001Env
  , TestCase.programRef "tpch_q22_sf001" (rewriteTpchTinyLoadPathsToGeneric TPCH.Q22)
      "sdql-rs/target/release/tpch_q22_tiny" sf001Env
  ]

unsafe def cases : List TestCase :=
  smallCases ++ optimisationCases ++ tpchCases ++ tpchCasesSF001

end Cases
end Tests
