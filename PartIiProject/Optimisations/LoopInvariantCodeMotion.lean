import PartIiProject.Optimisations.Apply

open PartIiProject

namespace PartIiProject.Optimisations

open PartIiProject.Optimisations.Term2

/--
Loop-invariant code motion:

`sum(<k,v> in d) (let y = e2 in f(k,v,y))`
`↦ let y = e2 in sum(<k,v> in d) f(k,v,y)`

Side condition: `e2` does not mention `k` or `v`.
-/
def loopInvariantCodeMotion2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | @Term2.sum _ dom range tyOut a d
        (.mk sumBodyLoc (@Term2.letin _ tyY _ bound body)) =>
        if Term2.mentionsIndexLoc bound 0 || Term2.mentionsIndexLoc bound 1 then
          none
        else
          let dropKV : Term2.Subst (dom :: range :: ctx) ctx :=
            fun m =>
              match m with
              | .head _ => Term2.defaultTerm2
              | .tail _ m =>
                  match m with
                  | .head _ => Term2.defaultTerm2
                  | .tail _ m => .var m

          let bound' : TermLoc2 ctx tyY := Term2.substLoc2 dropKV bound
          let d' : TermLoc2 (tyY :: ctx) (.dict dom range) := Term2.renameLoc2 Term2.wkRen d

          let ρ : Term2.Renaming (tyY :: dom :: range :: ctx) (dom :: range :: tyY :: ctx) :=
            fun m =>
              match m with
              | .head _ => .tail _ (.tail _ (.head _))
              | .tail _ m =>
                  match m with
                  | .head _ => .head _
                  | .tail _ m =>
                      match m with
                      | .head _ => .tail _ (.head _)
                      | .tail _ m => .tail _ (.tail _ (.tail _ m))

          let body' : TermLoc2 (dom :: range :: tyY :: ctx) tyOut := Term2.renameLoc2 ρ body
          let sumInLet : TermLoc2 (tyY :: ctx) tyOut := .mk sumBodyLoc (Term2.sum a d' body')
          some (Term2.letin bound' sumInLet)
    | _ => none

end PartIiProject.Optimisations
