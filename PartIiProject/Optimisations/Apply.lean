import PartIiProject.Optimisations.Term2Utils

open PartIiProject

namespace PartIiProject.Optimisations

abbrev Optimisation : Type :=
  {ctx : List Ty} → {ty : Ty} → Term2 ctx ty → Option (Term2 ctx ty)

def tryOptimisations {ctx : List Ty} {ty : Ty} (opts : List Optimisation) (t : Term2 ctx ty) :
    Option (Term2 ctx ty) :=
  match opts with
  | [] => none
  | o :: os =>
      match o t with
      | some t' => some t'
      | none => tryOptimisations os t

mutual
  def applyOptimisationsOnceTerm {ctx : List Ty} {ty : Ty} (opts : List Optimisation) :
      Term2 ctx ty → Term2 ctx ty × Bool
    | .var m => (.var m, false)
    | .constInt n => (.constInt n, false)
    | .constReal r => (.constReal r, false)
    | .constBool b => (.constBool b, false)
    | .constString s => (.constString s, false)
    | .constRecord fields =>
        let (fields', ch) := applyOptimisationsOnceFields opts fields
        let t' := Term2.constRecord fields'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | .emptyDict => (.emptyDict, false)
    | .dictInsert k v d =>
        let (k', chK) := applyOptimisationsOnceLoc opts k
        let (v', chV) := applyOptimisationsOnceLoc opts v
        let (d', chD) := applyOptimisationsOnceLoc opts d
        let ch := chK || chV || chD
        let t' := Term2.dictInsert k' v' d'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | .lookup aRange d k =>
        let (d', chD) := applyOptimisationsOnceLoc opts d
        let (k', chK) := applyOptimisationsOnceLoc opts k
        let ch := chD || chK
        let t' := Term2.lookup aRange d' k'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | .not e =>
        let (e', chE) := applyOptimisationsOnceLoc opts e
        let t' := Term2.not e'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', chE)
    | .ite c t f =>
        let (c', chC) := applyOptimisationsOnceLoc opts c
        let (t', chT) := applyOptimisationsOnceLoc opts t
        let (f', chF) := applyOptimisationsOnceLoc opts f
        let ch := chC || chT || chF
        let term' := Term2.ite c' t' f'
        match tryOptimisations opts term' with
        | some term'' => (term'', true)
        | none => (term', ch)
    | .letin bound body =>
        let (bound', chB) := applyOptimisationsOnceLoc opts bound
        let (body', chBody) := applyOptimisationsOnceLoc opts body
        let ch := chB || chBody
        let t' := Term2.letin bound' body'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | .add a t1 t2 =>
        let (t1', ch1) := applyOptimisationsOnceLoc opts t1
        let (t2', ch2) := applyOptimisationsOnceLoc opts t2
        let ch := ch1 || ch2
        let t' := Term2.add a t1' t2'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | @Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1 e2 =>
        let (t1', ch1) := applyOptimisationsOnceLoc opts e1
        let (t2', ch2) := applyOptimisationsOnceLoc opts e2
        let ch := ch1 || ch2
        let t' := @Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst t1' t2'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | .promote e =>
        let (e', chE) := applyOptimisationsOnceLoc opts e
        let t' := Term2.promote e'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', chE)
    | .sum a d body =>
        let (d', chD) := applyOptimisationsOnceLoc opts d
        let (body', chBody) := applyOptimisationsOnceLoc opts body
        let ch := chD || chBody
        let t' := Term2.sum a d' body'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', ch)
    | @Term2.proj _ l t record i inst =>
        let (record', chR) := applyOptimisationsOnceLoc opts record
        let t' := @Term2.proj _ l t record' i inst
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', chR)
    | .builtin f arg =>
        let (arg', chA) := applyOptimisationsOnceLoc opts arg
        let t' := Term2.builtin f arg'
        match tryOptimisations opts t' with
        | some t'' => (t'', true)
        | none => (t', chA)

  def applyOptimisationsOnceLoc {ctx : List Ty} {ty : Ty} (opts : List Optimisation) :
      TermLoc2 ctx ty → TermLoc2 ctx ty × Bool
    | .mk loc inner =>
        let (inner', ch) := applyOptimisationsOnceTerm opts inner
        (.mk loc inner', ch)

  def applyOptimisationsOnceFields {ctx : List Ty} (opts : List Optimisation) :
      {l : List Ty} → TermFields2 ctx l → TermFields2 ctx l × Bool
    | [], .nil => (.nil, false)
    | _ :: _, .cons h t =>
        let (h', chH) := applyOptimisationsOnceLoc opts h
        let (t', chT) := applyOptimisationsOnceFields opts t
        (.cons h' t', chH || chT)
end

def applyOptimisationOnce {ctx : List Ty} {ty : Ty} (opt : Optimisation) (t : Term2 ctx ty) :
    Term2 ctx ty :=
  (applyOptimisationsOnceTerm [opt] t).fst

def applyOptimisationOnceLoc {ctx : List Ty} {ty : Ty} (opt : Optimisation) (t : TermLoc2 ctx ty) :
    TermLoc2 ctx ty :=
  (applyOptimisationsOnceLoc [opt] t).fst

partial def applyOptimisations {ctx : List Ty} {ty : Ty}
    (opts : List Optimisation) (t : Term2 ctx ty) (fuel : Nat := 32) : Term2 ctx ty :=
  match fuel with
  | 0 => t
  | fuel + 1 =>
      let (t', changed) := applyOptimisationsOnceTerm opts t
      if changed then
        applyOptimisations opts t' fuel
      else
        t'

partial def applyOptimisationsLoc {ctx : List Ty} {ty : Ty}
    (opts : List Optimisation) (t : TermLoc2 ctx ty) (fuel : Nat := 32) : TermLoc2 ctx ty :=
  match fuel with
  | 0 => t
  | fuel + 1 =>
      let (t', changed) := applyOptimisationsOnceLoc opts t
      if changed then
        applyOptimisationsLoc opts t' fuel
      else
        t'

def applyOptimisation {ctx : List Ty} {ty : Ty} (opt : Optimisation) (t : Term2 ctx ty) (fuel : Nat := 32) :
    Term2 ctx ty :=
  applyOptimisations [opt] t fuel

def applyOptimisationLoc {ctx : List Ty} {ty : Ty}
    (opt : Optimisation) (t : TermLoc2 ctx ty) (fuel : Nat := 32) : TermLoc2 ctx ty :=
  applyOptimisationsLoc [opt] t fuel

end PartIiProject.Optimisations
