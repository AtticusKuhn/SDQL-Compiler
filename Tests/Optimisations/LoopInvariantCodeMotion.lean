import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg

open PartIiProject
open PartIiProject.Optimisations

namespace Tests.Optimisations.LoopInvariantCodeMotion

open ToCore2 in
unsafe def optimiseCoreTerm (p : SProg2) : String :=
  let core := trProg2 p
  let term' := applyOptimisationsLoc [loopInvariantCodeMotion2] core.term
  Term2.showTermLoc2 [] term'

/-- info: "let x = {1 -> 10} ++ {2 -> 20} ++ {} in let y = 5 in sum(z, k in x) k + y" -/
#guard_msgs in
#eval optimiseCoreTerm
  ([SDQLProg2 { int }|
    let d = { 1 -> 10, 2 -> 20 } in
    sum( <_, v> <- d ) (let y = 5 in v + y)
  ])

end Tests.Optimisations.LoopInvariantCodeMotion
