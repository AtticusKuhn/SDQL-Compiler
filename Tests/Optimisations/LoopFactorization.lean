import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg

open PartIiProject
open PartIiProject.Optimisations

namespace Tests.Optimisations.LoopFactorization

open ToCore2 in
unsafe def optimiseCoreTerm (opts : List Optimisation) (p : SProg2) : String :=
  let core := trProg2 p
  let term' := applyOptimisationsLoc opts core.term
  Term2.showTermLoc2 [] term'

/-- info: "2 * sum(x, y in {1 -> 10} ++ {2 -> 20} ++ {}) y" -/
#guard_msgs in
#eval optimiseCoreTerm [loopFactorizationLeft2]
  ([SDQLProg2 { int }|
    sum( <_, v> <- ({ 1 -> 10, 2 -> 20 }) ) (2 * v)
  ])

/-- info: "sum(x, y in {1 -> 10} ++ {2 -> 20} ++ {}) y * 2" -/
#guard_msgs in
#eval optimiseCoreTerm [loopFactorizationRight2]
  ([SDQLProg2 { int }|
    sum( <_, v> <- ({ 1 -> 10, 2 -> 20 }) ) (v * 2)
  ])

end Tests.Optimisations.LoopFactorization
