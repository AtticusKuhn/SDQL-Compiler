import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg

open PartIiProject
open PartIiProject.Optimisations

namespace Tests.Optimisations.VerticalLoopFusion

open ToCore2 in
unsafe def optimiseCoreTerm (p : SProg2) : String :=
  let core := trProg2 p
  let term' := applyOptimisationsLoc [verticalLoopFusionKeyMap2, verticalLoopFusionValueMap2] core.term
  Term2.showTermLoc2 [] term'

/-- info: "sum(x, y in {1 -> 10} ++ {} + {2 -> 20} ++ {}) {x + 1 + 2 -> y} ++ {}" -/
#guard_msgs in
#eval optimiseCoreTerm
  ([SDQLProg2 { { int -> int } }|
    let y = sum( <x, x_v> <- ({ 1 -> 10 } + { 2 -> 20 }) ) { x + 1 -> x_v } in
    sum( <x, x_v> <- y ) { x + 2 -> x_v }
  ] : SProg2)

/-- info: "sum(x, y in {1 -> 10} ++ {} + {2 -> 20} ++ {}) {x -> y + 1 + 2} ++ {}" -/
#guard_msgs in
#eval optimiseCoreTerm
  ([SDQLProg2 { { int -> int } }|
    let y = sum( <x, x_v> <- ({ 1 -> 10 } + { 2 -> 20 }) ) { x -> x_v + 1 } in
    sum( <x, x_v> <- y ) { x -> x_v + 2 }
  ] : SProg2)

end Tests.Optimisations.VerticalLoopFusion

