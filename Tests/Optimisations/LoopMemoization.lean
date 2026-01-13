import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg

open PartIiProject
open PartIiProject.Optimisations

namespace Tests.Optimisations.LoopMemoization

open ToCore2 in
unsafe def optimiseCoreTerm (opts : List Optimisation) (p : SProg2) : String :=
  let core := trProg2 p
  let term' := applyOptimisationsLoc opts core.term
  Term2.showTermLoc2 [] term'

/-- info: "let x = sum(x, y in {1 -> 10} ++ {2 -> 20} ++ {}) {x -> y} ++ {} in x(1)" -/
#guard_msgs in
#eval optimiseCoreTerm [loopMemoizationLookup2]
  ([SDQLProg2 { int }|
    sum( <k, v> <- ({ 1 -> 10, 2 -> 20 }) ) (if k == 1 then v)
  ])

/-- info: "let x = sum(x, y in {1 -> 10} ++ {2 -> 20} ++ {}) {x -> {x -> y} ++ {}} ++ {} in sum(y, z in x(1)) {y -> z} ++ {}" -/
#guard_msgs in
#eval optimiseCoreTerm [loopMemoizationPartition2]
  ([SDQLProg2 { { int -> int } }|
    sum( <k, v> <- ({ 1 -> 10, 2 -> 20 }) ) (if k == 1 then { k -> v })
  ])

end Tests.Optimisations.LoopMemoization

