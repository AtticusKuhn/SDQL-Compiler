import PartIiProject.Optimisations.Apply

open PartIiProject

namespace PartIiProject.Optimisations

open PartIiProject.Optimisations.Term2

/--
Loop memoization (lookup):

`sum(<k,v> in d) (if p(k,v) == e then f(k,v) else 0)`
`↦ let tmp = sum(<k,v> in d) { p(k,v) -> f(k,v) } in tmp(e)`

Side conditions:
- `e` does not mention `k` or `v`
- the `else` branch is syntactic zero for the surrounding `sum`'s `AddM`.
-/
def loopMemoizationLookup2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | @Term2.sum _ dom range ty a d
        (.mk iteLoc
          (.ite
            (.mk _ (.builtin (.Eq pTy)
              (.mk _ (.constRecord (.cons p (.cons e TermFields2.nil))))))
            f
            z)) =>
        if !AddM.isZeroTerm2 a z.term then
          none
        else if Term2.mentionsIndexLoc e 0 || Term2.mentionsIndexLoc e 1 then
          none
        else
          let tmpTy : Ty := .dict pTy ty
          let aTmp : AddM tmpTy := .dictA a

          let emptyTmp : TermLoc2 (dom :: range :: ctx) tmpTy := .mk iteLoc .emptyDict
          let tmpBody : TermLoc2 (dom :: range :: ctx) tmpTy :=
            .mk iteLoc (.dictInsert p f emptyTmp)

          let tmpSum : Term2 ctx tmpTy := Term2.sum aTmp d tmpBody
          let tmpBound : TermLoc2 ctx tmpTy := .mk (TermLoc2.loc d) tmpSum

          let dropKV : Term2.Subst (dom :: range :: ctx) ctx :=
            fun m =>
              match m with
              | .head _ => Term2.defaultTerm2
              | .tail _ m =>
                  match m with
                  | .head _ => Term2.defaultTerm2
                  | .tail _ m => .var m

          let e' : TermLoc2 ctx pTy := Term2.substLoc2 dropKV e
          let eWk : TermLoc2 (tmpTy :: ctx) pTy := Term2.renameLoc2 Term2.wkRen e'
          let tmpVarLoc : TermLoc2 (tmpTy :: ctx) tmpTy := .mk (TermLoc2.loc d) (.var (.head _))
          let lookupTmp : Term2 (tmpTy :: ctx) ty := Term2.lookup a tmpVarLoc eWk
          some (Term2.letin tmpBound (.mk iteLoc lookupTmp))
    | _ => none

/--
Loop memoization (partition/filter):

`sum(<k,v> in d) (if p(k,v) == e then g(k,v) else 0)`
`↦ let tmp = sum(<k,v> in d) { p(k,v) -> { k -> v } } in sum(<k,v> in tmp(e)) g(k,v)`

Side conditions:
- `e` does not mention `k` or `v`
- the `else` branch is syntactic zero for the surrounding `sum`'s `AddM`.
-/
def loopMemoizationPartition2 : Optimisation :=
  fun {ctx} {ty} t =>
    match t with
    | @Term2.sum _ dom range ty a d
        (.mk iteLoc
          (.ite
            (.mk _ (.builtin (.Eq pTy)
              (.mk _ (.constRecord (.cons p (.cons e TermFields2.nil))))))
            g
            z)) =>
        if !AddM.isZeroTerm2 a z.term then
          none
        else if Term2.mentionsIndexLoc e 0 || Term2.mentionsIndexLoc e 1 then
          none
        else
          let innerDictTy : Ty := .dict dom range
          let tmpTy : Ty := .dict pTy innerDictTy

          let aInnerDict : AddM innerDictTy := Ty.synthAddM innerDictTy
          let aTmp : AddM tmpTy := .dictA aInnerDict

          let kLoc : TermLoc2 (dom :: range :: ctx) dom := .mk iteLoc (.var (.head _))
          let vLoc : TermLoc2 (dom :: range :: ctx) range := .mk iteLoc (.var (.tail _ (.head _)))
          let innerEmpty : TermLoc2 (dom :: range :: ctx) innerDictTy := .mk iteLoc .emptyDict
          let innerDict : TermLoc2 (dom :: range :: ctx) innerDictTy :=
            .mk iteLoc (.dictInsert kLoc vLoc innerEmpty)

          let tmpEmpty : TermLoc2 (dom :: range :: ctx) tmpTy := .mk iteLoc .emptyDict
          let tmpBody : TermLoc2 (dom :: range :: ctx) tmpTy :=
            .mk iteLoc (.dictInsert p innerDict tmpEmpty)

          let tmpSum : Term2 ctx tmpTy := Term2.sum aTmp d tmpBody
          let tmpBound : TermLoc2 ctx tmpTy := .mk (TermLoc2.loc d) tmpSum

          let dropKV : Term2.Subst (dom :: range :: ctx) ctx :=
            fun m =>
              match m with
              | .head _ => Term2.defaultTerm2
              | .tail _ m =>
                  match m with
                  | .head _ => Term2.defaultTerm2
                  | .tail _ m => .var m

          let e' : TermLoc2 ctx pTy := Term2.substLoc2 dropKV e
          let eWk : TermLoc2 (tmpTy :: ctx) pTy := Term2.renameLoc2 Term2.wkRen e'
          let tmpVarLoc : TermLoc2 (tmpTy :: ctx) tmpTy := .mk (TermLoc2.loc d) (.var (.head _))
          let lookupTmp : TermLoc2 (tmpTy :: ctx) innerDictTy :=
            .mk iteLoc (Term2.lookup aInnerDict tmpVarLoc eWk)

          let wkAfter2 : Term2.Renaming (dom :: range :: ctx) (dom :: range :: tmpTy :: ctx) :=
            fun m =>
              match m with
              | .head _ => .head _
              | .tail _ m =>
                  match m with
                  | .head _ => .tail _ (.head _)
                  | .tail _ m => .tail _ (.tail _ (.tail _ m))

          let g' : TermLoc2 (dom :: range :: tmpTy :: ctx) ty := Term2.renameLoc2 wkAfter2 g
          let sumG : Term2 (tmpTy :: ctx) ty := Term2.sum a lookupTmp g'
          some (Term2.letin tmpBound (.mk iteLoc sumG))
    | _ => none

end PartIiProject.Optimisations

