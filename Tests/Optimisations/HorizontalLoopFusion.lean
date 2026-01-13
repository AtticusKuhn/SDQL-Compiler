import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg

open PartIiProject
open PartIiProject.Optimisations

namespace Tests.Optimisations.HorizontalLoopFusion

open ToCore2 in
unsafe def optimiseCoreTerm (p : SProg2) : String :=
  let core := trProg2 p
  let term' := applyOptimisationsLoc [horizontalLoopFusion2] core.term
  Term2.showTermLoc2 [] term'

/-- info: "let x = {1 -> 10} ++ {2 -> 20} ++ {} in let y = sum(y, z in x) <z, z + 1> in let z = y.0 in let k = y.1 in z + k" -/
#guard_msgs in
#eval optimiseCoreTerm
  ([SDQLProg2 { int }|
    let d = { 1 -> 10, 2 -> 20 } in
    let y1 = sum( <_, v> <- d ) v in
    let y2 = sum( <_, v> <- d ) (v + 1) in
    y1 + y2
  ])

end Tests.Optimisations.HorizontalLoopFusion
