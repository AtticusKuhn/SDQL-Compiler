import PartIiProject.Term2
import PartIiProject.CodegenRust
import PartIiProject.SyntaxSDQLProg
import Tests.TPCH.Q01
import Tests.TPCH.Q02

namespace Tests
namespace Cases

open PartIiProject

/- Expected-output strings are produced by evaluating the term in Lean
   and pretty-printing the resulting value via `showValue`. -/

/- Sample test cases ported from inline demos. -/
/- Test cases support both closed terms and open terms with runtime parameters. -/
unsafe inductive TestCase where
  | program (name : String) (p : SProg2) (expected : String) : TestCase
  | programRef (name : String) (p : SProg2) (refBinPath : String) (envVars : List (String × String)) : TestCase
  | compileOnly (name : String) (p : SProg2) : TestCase

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

unsafe def smallCases : List TestCase :=
  [ TestCase.program "add_int" p_add_int "8"
  , TestCase.program "dict_insert" p_dict_is "{1 -> \"one\", }"
  , TestCase.program "lookup_hit" p_lookup_hit "2"
  , TestCase.program "lookup_miss" p_lookup_miss "0"
  , TestCase.program "sum_vals" p_sum_vals "10"
  ]

/- TPCH-style programs exercise file-loading pipelines. Queries listed here are
   compiled to Rust, executed against the tiny TPCH dataset, and their outputs
   compared against the reference implementation results. -/
unsafe def tpchCases : List TestCase :=
  [ TestCase.compileOnly "tpch_q01" TPCH.Q01
  , TestCase.programRef "tpch_q02" TPCH.Q02 "sdql-rs/target/release/tpch_q02_tiny"
      [("TPCH_DATASET_PATH", "datasets/tpch-tiny")] ]

unsafe def cases : List TestCase :=
  smallCases ++ tpchCases

end Cases
end Tests
