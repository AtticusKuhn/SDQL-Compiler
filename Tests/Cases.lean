import PartIiProject.Term
import PartIiProject.CodegenRust
import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests
namespace Cases

open PartIiProject

/- Expected-output strings are produced by evaluating the term in Lean
   and pretty-printing the resulting value via `showValue`. -/

/- Sample test cases ported from inline demos. -/
/- Test cases support both closed terms and open terms with runtime parameters. -/
unsafe inductive TestCase where
  | program (name : String) (p : PartIiProject.SProg) (expected : String) : TestCase

open TestCase
open PartIiProject.ToCore

-- Build sample programs using the SDQL program DSL (no loads)
unsafe def p_add_int : PartIiProject.SProg :=
  [SDQLProg { int }| 3 + 5 ]


unsafe def p_dict_is : PartIiProject.SProg :=
  [SDQLProg { { int -> string } }| { 1 -> "one" } ]

unsafe def p_dict_ii : PartIiProject.SProg :=
  [SDQLProg { { int -> int } }| { 1 -> 2, 3 -> 4 } ]

unsafe def p_lookup_hit : PartIiProject.SProg :=
  [SDQLProg { int }| { 1 -> 2, 3 -> 4 } (1) ]

unsafe def p_lookup_miss : PartIiProject.SProg :=
  [SDQLProg { int }| { 1 -> 2, 3 -> 4 } (0) ]

unsafe def p_sum_vals : PartIiProject.SProg :=
  [SDQLProg { int }| sum( <k, v> in { 3 -> 4, 5 -> 6 } ) v ]

unsafe def cases : List TestCase :=
  [ TestCase.program "add_int" p_add_int "8"
  , TestCase.program "dict_insert" p_dict_is "{1 -> one, }"
  , TestCase.program "lookup_hit" p_lookup_hit "2"
  , TestCase.program "lookup_miss" p_lookup_miss "0"
  , TestCase.program "sum_vals" p_sum_vals "10"
  ]

end Cases
end Tests
