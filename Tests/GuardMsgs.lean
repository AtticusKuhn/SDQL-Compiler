import PartIiProject.SyntaxSDQLProg
import Tests.Optimisations.HorizontalLoopFusion
import Tests.Optimisations.LoopFactorization
import Tests.Optimisations.LoopInvariantCodeMotion
import Tests.Optimisations.LoopMemoization
import Tests.Optimisations.VerticalLoopFusion

open PartIiProject

/--
error: Type error while typechecking SDQL program
Expected: int
At: true ⏎
Type mismatch: expected int, got bool
-/
#guard_msgs in
#check ([SDQLProg2 { int }| true ] : SProg2)

namespace PerfToString

open PartIiProject

/-- info: "sum(<i,_> <- range(2000000)) 1" -/
#guard_msgs in
#eval toString ([SDQLProg2 { int }| sum( <_, _> <- range(2000000) ) 1 ] : SProg2)

/-- info: "sum(<i,_> <- range(400000)) { i -> 1 }" -/
#guard_msgs in
#eval toString ([SDQLProg2 { { int -> int } }| sum( <i, _> <- range(400000) ) { i -> 1 } ] : SProg2)


/-- info: "let d = sum(<i,_> <- range(200000)) { i -> i }\nsum(<i,_> <- range(200000)) d(i)" -/
#guard_msgs in
#eval (toString (
    [SDQLProg2 { int }|
      let d = sum( <i, _> <- range(200000) ) { i -> i } in
      sum( <i, _> <- range(200000) ) d(i)
    ] : SProg2))


/-- info: "let t = load[int](\"path\")\n1 + t" -/
#guard_msgs in
#eval (toString (
    [SDQLProg2 { int }|
      1 + load[int]("path")
    ] : SProg2))


end PerfToString
