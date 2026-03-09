import PartIiProject.Optimisations.Apply

open PartIiProject

namespace PartIiProject.Optimisations

open PartIiProject.Optimisations.Term2

/--
Loop factorization (left):
`sum(<k,v> in d) (e2 * f(k,v)) ↦ e2 * sum(<k,v> in d) f(k,v)`

Side condition: `e2` does not mention `k` or `v`.
-/
def loopFactorizationLeft2 : Optimisation :=
  fun {ctx} {ty} t =>
    match (t : Term2 ctx ty) with
    | @Term2.sum _ dom range tyOut _ d
        (.mk bodyLoc (@Term2.mul _ sc t1 t2 _ s1 s2 inst e2 f)) =>
        do
          let e2' : TermLoc2 ctx t1 ← Term2.extractInvariant2 e2
          let aF : AddM t2 := Ty.synthAddM t2
          let summedF : TermLoc2 ctx t2 := .mk bodyLoc (Term2.sum aF d f)
          some (@Term2.mul _ sc t1 t2 tyOut s1 s2 inst e2' summedF)
    | _ => none

/--
Loop factorization (right):
`sum(<k,v> in d) (f(k,v) * e2) ↦ (sum(<k,v> in d) f(k,v)) * e2`

Side condition: `e2` does not mention `k` or `v`.
-/
def loopFactorizationRight2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | @Term2.sum _ dom range tyOut a d
        (.mk bodyLoc (@Term2.mul _ sc t1 t2 _ s1 s2 inst f e2)) =>
        do
          let e2' : TermLoc2 ctx t2 ← Term2.extractInvariant2 e2
          let aF : AddM t1 := Ty.synthAddM t1
          let summedF : TermLoc2 ctx t1 := .mk bodyLoc (Term2.sum aF d f)
          some (@Term2.mul _ sc t1 t2 tyOut s1 s2 inst summedF e2')
    | _ => none

end PartIiProject.Optimisations
