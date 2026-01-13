import PartIiProject.Optimisations.Apply

open PartIiProject

namespace PartIiProject.Optimisations

open PartIiProject.Optimisations.Term2

/--
Horizontal loop fusion, specialized to sums over the same dictionary variable:

`let y1 = sum(<k,v> in d) b1 in let y2 = sum(<k,v> in d) b2 in e(y1,y2)`
`↦ let tmp = sum(<k,v> in d) <b1, b2> in e(tmp.0, tmp.1)`

Side condition: `b2` does not mention `y1`.
-/
def horizontalLoopFusion2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | @Term2.letin _ ty₁ _
        (.mk y1Loc (@Term2.sum _ dom range _ a₁ (.mk dLoc (.var dVar)) b₁))
        (.mk _ (@Term2.letin _ ty₂ _
          (.mk _ (@Term2.sum _ dom' range' _ a₂ (.mk _ (.var dVar2)) b₂))
          body)) =>
        match (inferInstance : Decidable (dom = dom')), (inferInstance : Decidable (range = range')) with
        | isTrue hDom, isTrue hRange =>
            match hDom with
            | rfl =>
              match hRange with
              | rfl =>
                match dVar2 with
            | .tail _ dVar' =>
                if PartIiProject.Optimisations.Mem.index dVar' != PartIiProject.Optimisations.Mem.index dVar then
                  none
                else if Term2.mentionsIndex b₂.term 2 then
                  none
                else
                  let recordTy : Ty := .record [ty₁, ty₂]
                  let aRecord : AddM recordTy :=
                    AddM.recordA (HList.cons a₁ (HList.cons a₂ HList.nil))

                  let dropY1 : Term2.Subst (dom :: range :: ty₁ :: ctx) (dom :: range :: ctx) :=
                    fun {_} m =>
                      match m with
                      | .head _ => .var (.head _)
                      | .tail _ m =>
                          match m with
                          | .head _ => .var (.tail dom (.head _))
                          | .tail _ m =>
                              match m with
                              | .head _ => Term2.defaultTerm2
                              | .tail _ m => .var (.tail dom (.tail range m))

                  let b₂' : TermLoc2 (dom :: range :: ctx) ty₂ := Term2.substLoc2 dropY1 b₂

                  let recBody : TermLoc2 (dom :: range :: ctx) recordTy :=
                    .mk (TermLoc2.loc b₁)
                      (.constRecord (TermFields2.cons b₁ (TermFields2.cons b₂' TermFields2.nil)))

                  let fusedSum : Term2 ctx recordTy :=
                    Term2.sum aRecord (.mk dLoc (.var dVar)) recBody

                  let tmpBound : TermLoc2 ctx recordTy := .mk y1Loc fusedSum
                  let tmpVarLoc : TermLoc2 (recordTy :: ctx) recordTy := .mk y1Loc (.var (.head _))
                  let y1Bound : TermLoc2 (recordTy :: ctx) ty₁ :=
                    .mk y1Loc (Term2.proj [ty₁, ty₂] (t := ty₁) tmpVarLoc 0)

                  let tmpVarLocWk : TermLoc2 (ty₁ :: recordTy :: ctx) recordTy :=
                    Term2.renameLoc2 Term2.wkRen tmpVarLoc
                  let y2Bound : TermLoc2 (ty₁ :: recordTy :: ctx) ty₂ :=
                    .mk y1Loc (Term2.proj [ty₁, ty₂] (t := ty₂) tmpVarLocWk 1)

                  let ρ : Term2.Renaming (ty₂ :: ty₁ :: ctx) (ty₂ :: ty₁ :: recordTy :: ctx) :=
                    fun m =>
                      match m with
                      | .head _ => .head _
                      | .tail _ m =>
                          match m with
                          | .head _ => .tail ty₂ (.head _)
                          | .tail _ m => .tail ty₂ (.tail ty₁ (.tail recordTy m))

                  let bodyRenamed : TermLoc2 (ty₂ :: ty₁ :: recordTy :: ctx) ty :=
                    Term2.renameLoc2 ρ body

                  let withY2 : TermLoc2 (ty₁ :: recordTy :: ctx) ty :=
                    .mk (TermLoc2.loc body) (Term2.letin y2Bound bodyRenamed)
                  let withY1 : TermLoc2 (recordTy :: ctx) ty :=
                    .mk (TermLoc2.loc body) (Term2.letin y1Bound withY2)

                  some (Term2.letin tmpBound withY1)
            | _ => none
        | _, _ => none
    | _ => none

end PartIiProject.Optimisations
