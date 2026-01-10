import PartIiProject.Optimisations.Apply

open PartIiProject

namespace PartIiProject.Optimisations

open PartIiProject.Optimisations.Term2

/--
Vertical loop fusion, specialized to the two common "singleton dict" shapes:

1. Key-map fusion:
   `let y = sum(<x,x_v> in e1) { f1(x) -> x_v } in sum(<x,x_v> in y) { f2(x) -> x_v }`
   `↦ sum(<x,x_v> in e1) { f2(f1(x)) -> x_v }`

2. Value-map fusion:
   `let y = sum(<x,x_v> in e1) { x -> f1(x_v) } in sum(<x,x_v> in y) { x -> f2(x_v) }`
   `↦ sum(<x,x_v> in e1) { x -> f2(f1(x_v)) }`
-/
def verticalLoopFusionKeyMap2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | Term2.letin
        (.mk _ (Term2.sum _ e₁ (.mk _ (.dictInsert k₁ v₁ (.mk _ .emptyDict)))))
        (.mk _ (Term2.sum a₂
          (.mk _ (.var (.head _)))
          (.mk bodyLoc (.dictInsert k₂ v₂ (.mk emptyLoc .emptyDict))))) =>
        match v₁.term, v₂.term with
        | .var (.tail _ (.head _)), .var (.tail _ (.head _)) =>
            if Term2.mentionsIndexLoc k₁ 1 || Term2.mentionsIndexLoc k₂ 1 || Term2.mentionsIndexLoc k₂ 2 then
              none
            else
              let σ : Term2.Subst (_ :: _ :: (.dict _ _) :: ctx) (_ :: _ :: ctx) :=
                fun {ty} m =>
                  match m with
                  | .head _ => k₁.term
                  | .tail _ m =>
                      match m with
                      | .head _ => .var (.tail _ (.head ctx))
                      | .tail _ m =>
                          match m with
                          | .head _ => Term2.defaultTerm2
                          | .tail _ m => .var (.tail _ (.tail _ m))
              let k₂' := Term2.substLoc2 σ k₂
              let v₂' := Term2.substLoc2 σ v₂
              let emptyFused : TermLoc2 (_ :: _ :: ctx) (.dict _ _) := .mk emptyLoc .emptyDict
              let fusedBody : TermLoc2 (_ :: _ :: ctx) (.dict _ _) :=
                .mk bodyLoc (.dictInsert k₂' v₂' emptyFused)
              some (Term2.sum a₂ e₁ fusedBody)
        | _, _ => none
    | _ => none

def verticalLoopFusionValueMap2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | Term2.letin
        (.mk _ (Term2.sum _ e₁ (.mk _ (.dictInsert k₁ v₁ (.mk _ .emptyDict)))))
        (.mk _ (Term2.sum a₂
          (.mk _ (.var (.head _)))
          (.mk bodyLoc (.dictInsert k₂ v₂ (.mk emptyLoc .emptyDict))))) =>
        match k₁.term, k₂.term with
        | .var (.head _), .var (.head _) =>
            if Term2.mentionsIndexLoc v₁ 0 || Term2.mentionsIndexLoc v₂ 0 || Term2.mentionsIndexLoc v₂ 2 then
              none
            else
              let σ : Term2.Subst (_ :: _ :: (.dict _ _) :: ctx) (_ :: _ :: ctx) :=
                fun {ty} m =>
                  match m with
                  | .head _ => k₁.term
                  | .tail _ m =>
                      match m with
                      | .head _ => v₁.term
                      | .tail _ m =>
                          match m with
                          | .head _ => Term2.defaultTerm2
                          | .tail _ m => .var (.tail _ (.tail _ m))
              let k₂' := Term2.substLoc2 σ k₂
              let v₂' := Term2.substLoc2 σ v₂
              let emptyFused : TermLoc2 (_ :: _ :: ctx) (.dict _ _) := .mk emptyLoc .emptyDict
              let fusedBody : TermLoc2 (_ :: _ :: ctx) (.dict _ _) :=
                .mk bodyLoc (.dictInsert k₂' v₂' emptyFused)
              some (Term2.sum a₂ e₁ fusedBody)
        | _, _ => none
    | _ => none


end PartIiProject.Optimisations
