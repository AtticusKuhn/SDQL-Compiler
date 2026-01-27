import PartIiProject.Term2

open PartIiProject

namespace PartIiProject.Optimisations

namespace Mem

def index {α : Type} {a : α} {ctx : List α} : Mem a ctx → Nat
  | .head _ => 0
  | .tail _ m => index m + 1

end Mem

namespace Term2

abbrev Renaming (ctx ctx' : List Ty) : Type :=
  ∀ {ty : Ty}, Mem ty ctx → Mem ty ctx'

abbrev Subst (ctx ctx' : List Ty) : Type :=
  ∀ {ty : Ty}, Mem ty ctx → Term2 ctx' ty

def liftRen {ctx ctx' : List Ty} {a : Ty} (ρ : Renaming ctx ctx') :
    Renaming (a :: ctx) (a :: ctx')
  | _, .head _ => .head _
  | _, .tail _ m => .tail _ (ρ m)

def liftRen2 {ctx ctx' : List Ty} {a b : Ty} (ρ : Renaming ctx ctx') :
    Renaming (a :: b :: ctx) (a :: b :: ctx') :=
  liftRen (a := a) (liftRen (a := b) ρ)

mutual
  def renameTerm2 {ctx ctx' : List Ty} {ty : Ty}
      (ρ : Renaming ctx ctx') : Term2 ctx ty → Term2 ctx' ty
    | .var m => .var (ρ m)
    | .constInt n => .constInt n
    | .constReal r => .constReal r
    | .constBool b => .constBool b
    | .constString s => .constString s
    | .constRecord fields => .constRecord (renameFields2 ρ fields)
    | .emptyDict => .emptyDict
    | .dictInsert k v d => .dictInsert (renameLoc2 ρ k) (renameLoc2 ρ v) (renameLoc2 ρ d)
    | .lookup aRange d k => .lookup aRange (renameLoc2 ρ d) (renameLoc2 ρ k)
    | .not e => .not (renameLoc2 ρ e)
    | .ite c t f => .ite (renameLoc2 ρ c) (renameLoc2 ρ t) (renameLoc2 ρ f)
    | .letin bound body => .letin (renameLoc2 ρ bound) (renameLoc2 (liftRen ρ) body)
    | .add a t1 t2 => .add a (renameLoc2 ρ t1) (renameLoc2 ρ t2)
    | @Term2.mul _ sc t1 t2 t3 s1 s2 inst e1 e2 =>
        @Term2.mul _ sc t1 t2 t3 s1 s2 inst (renameLoc2 ρ e1) (renameLoc2 ρ e2)
    | .semiringMul hm e1 e2 =>
        .semiringMul hm (renameLoc2 ρ e1) (renameLoc2 ρ e2)
    | .closure hc e =>
        .closure hc (renameLoc2 ρ e)
    | .promote e => .promote (renameLoc2 ρ e)
    | .sum a d body => .sum a (renameLoc2 ρ d) (renameLoc2 (liftRen2 ρ) body)
    | @Term2.proj _ l t record i inst =>
        @Term2.proj _ l t (renameLoc2 ρ record) i inst
    | .builtin f arg => .builtin f (renameLoc2 ρ arg)

  def renameLoc2 {ctx ctx' : List Ty} {ty : Ty}
      (ρ : Renaming ctx ctx') : TermLoc2 ctx ty → TermLoc2 ctx' ty
    | .mk loc inner => .mk loc (renameTerm2 ρ inner)

  def renameFields2 {ctx ctx' : List Ty} (ρ : Renaming ctx ctx') :
      {l : List Ty} → TermFields2 ctx l → TermFields2 ctx' l
    | [], .nil => .nil
    | _ :: _, .cons h t => .cons (renameLoc2 ρ h) (renameFields2 ρ t)
end

def wkRen {ctx : List Ty} {a : Ty} : Renaming ctx (a :: ctx) :=
  fun m => .tail _ m

def wk {ctx : List Ty} {ty : Ty} {a : Ty} : Term2 ctx ty → Term2 (a :: ctx) ty :=
  renameTerm2 wkRen

def liftSubst {ctx ctx' : List Ty} {a : Ty} (σ : Subst ctx ctx') :
    Subst (a :: ctx) (a :: ctx')
  | _, .head _ => .var (.head _)
  | _, .tail _ m => wk (a := a) (σ m)

def liftSubst2 {ctx ctx' : List Ty} {a b : Ty} (σ : Subst ctx ctx') :
    Subst (a :: b :: ctx) (a :: b :: ctx') :=
  liftSubst (a := a) (liftSubst (a := b) σ)

mutual
  /-- A "dummy" term of a given type, intended only for unreachable substitution branches. -/
  def defaultTerm2 {ctx : List Ty} : {ty : Ty} → Term2 ctx ty
    | .bool => .constBool false
    | .int => .constInt 0
    | .real => .constReal 0.0
    | .maxProduct => .promote (.mk SourceLocation.unknown (.constReal 0.0))
    | .date => .builtin (.DateLit 0) (.mk SourceLocation.unknown (.constRecord .nil))
    | .string => .constString ""
    | .record l => .constRecord (defaultFields2 (ctx := ctx) l)
    | .dict _ _ => .emptyDict

  def defaultLoc2 {ctx : List Ty} : {ty : Ty} → TermLoc2 ctx ty
    | ty => .mk SourceLocation.unknown (defaultTerm2 (ctx := ctx) (ty := ty))

  def defaultFields2 {ctx : List Ty} : (l : List Ty) → TermFields2 ctx l
    | [] => .nil
    | t :: ts => .cons (defaultLoc2 (ctx := ctx) (ty := t)) (defaultFields2 (ctx := ctx) ts)
end

mutual
  def substTerm2 {ctx ctx' : List Ty} {ty : Ty}
      (σ : Subst ctx ctx') : Term2 ctx ty → Term2 ctx' ty
    | .var m => σ m
    | .constInt n => .constInt n
    | .constReal r => .constReal r
    | .constBool b => .constBool b
    | .constString s => .constString s
    | .constRecord fields => .constRecord (substFields2 σ fields)
    | .emptyDict => .emptyDict
    | .dictInsert k v d => .dictInsert (substLoc2 σ k) (substLoc2 σ v) (substLoc2 σ d)
    | .lookup aRange d k => .lookup aRange (substLoc2 σ d) (substLoc2 σ k)
    | .not e => .not (substLoc2 σ e)
    | .ite c t f => .ite (substLoc2 σ c) (substLoc2 σ t) (substLoc2 σ f)
    | .letin bound body => .letin (substLoc2 σ bound) (substLoc2 (liftSubst σ) body)
    | .add a t1 t2 => .add a (substLoc2 σ t1) (substLoc2 σ t2)
    | @Term2.mul _ sc t1 t2 t3 s1 s2 inst e1 e2 =>
        @Term2.mul _ sc t1 t2 t3 s1 s2 inst (substLoc2 σ e1) (substLoc2 σ e2)
    | .semiringMul hm e1 e2 =>
        .semiringMul hm (substLoc2 σ e1) (substLoc2 σ e2)
    | .closure hc e =>
        .closure hc (substLoc2 σ e)
    | .promote e => .promote (substLoc2 σ e)
    | .sum a d body => .sum a (substLoc2 σ d) (substLoc2 (liftSubst2 σ) body)
    | @Term2.proj _ l t record i inst =>
        @Term2.proj _ l t (substLoc2 σ record) i inst
    | .builtin f arg => .builtin f (substLoc2 σ arg)

  def substLoc2 {ctx ctx' : List Ty} {ty : Ty}
      (σ : Subst ctx ctx') : TermLoc2 ctx ty → TermLoc2 ctx' ty
    | .mk loc inner => .mk loc (substTerm2 σ inner)

  def substFields2 {ctx ctx' : List Ty} (σ : Subst ctx ctx') :
      {l : List Ty} → TermFields2 ctx l → TermFields2 ctx' l
    | [], .nil => .nil
    | _ :: _, .cons h t => .cons (substLoc2 σ h) (substFields2 σ t)
end

mutual
  def mentionsIndex {ctx : List Ty} {ty : Ty} (t : Term2 ctx ty) (i : Nat) : Bool :=
    match t with
    | .var m => (Mem.index m == i)
    | .constInt _ => false
    | .constReal _ => false
    | .constBool _ => false
    | .constString _ => false
    | .constRecord fields => mentionsIndexFields fields i
    | .emptyDict => false
    | .dictInsert k v d => mentionsIndexLoc k i || mentionsIndexLoc v i || mentionsIndexLoc d i
    | .lookup _ d k => mentionsIndexLoc d i || mentionsIndexLoc k i
    | .not e => mentionsIndexLoc e i
    | .ite c t f => mentionsIndexLoc c i || mentionsIndexLoc t i || mentionsIndexLoc f i
    | .letin bound body => mentionsIndexLoc bound i || mentionsIndexLoc body (i + 1)
    | .add _ t1 t2 => mentionsIndexLoc t1 i || mentionsIndexLoc t2 i
    | @Term2.mul _ _ _ _ _ _ _ _ t1 t2 => mentionsIndexLoc t1 i || mentionsIndexLoc t2 i
    | .semiringMul _ t1 t2 => mentionsIndexLoc t1 i || mentionsIndexLoc t2 i
    | .closure _ e => mentionsIndexLoc e i
    | .promote e => mentionsIndexLoc e i
    | .sum _ d body => mentionsIndexLoc d i || mentionsIndexLoc body (i + 2)
    | @Term2.proj _ _ _ record _ _ => mentionsIndexLoc record i
    | .builtin _ arg => mentionsIndexLoc arg i

  def mentionsIndexLoc {ctx : List Ty} {ty : Ty} (t : TermLoc2 ctx ty) (i : Nat) : Bool :=
    match t with
    | .mk _ inner => mentionsIndex inner i

def mentionsIndexFields {ctx : List Ty} {l : List Ty} (fs : TermFields2 ctx l) (i : Nat) : Bool :=
    match fs with
    | .nil => false
    | .cons h t => mentionsIndexLoc h i || mentionsIndexFields t i
end

end Term2

namespace Ty

mutual
  def synthAddM : (t : Ty) → AddM t
    | .bool => .boolA
    | .int => .intA
    | .real => .realA
    | .maxProduct => .maxProductA
    | .date => .dateA
    | .string => .stringA
    | .dict dom range => .dictA (synthAddM range)
    | .record l => .recordA (synthAddMHList l)

  def synthAddMHList : (l : List Ty) → HList AddM l
    | [] => .nil
    | t :: ts => .cons (synthAddM t) (synthAddMHList ts)
end

end Ty

namespace AddM

mutual
  /-- Syntactic check for whether a term is the additive identity for the given `AddM`. -/
  def isZeroTerm2 {ctx : List Ty} : {ty : Ty} → AddM ty → Term2 ctx ty → Bool
    | .bool, .boolA, .constBool false => true
    | .int, .intA, .constInt 0 => true
    | .real, .realA, .constReal r => r == 0.0
    | .maxProduct, .maxProductA, .promote (fromType := .real) (toType := .maxProduct) (.mk _ (.constReal r)) =>
        r == 0.0
    | .date, .dateA, .builtin (.DateLit 10101) (.mk _ (.constRecord .nil)) => true
    | .string, .stringA, .constString "" => true
    | .dict _ _, .dictA _, .emptyDict => true
    | .record _, .recordA fieldsEv, .constRecord fields =>
        isZeroFields2 fieldsEv fields
    | _, _, _ => false

  def isZeroFields2 {ctx : List Ty}
      : {l : List Ty} → HList AddM l → TermFields2 ctx l → Bool
    | [], .nil, .nil => true
    | _ :: _, .cons hEv tEv, .cons h t =>
        isZeroTerm2 hEv h.term && isZeroFields2 tEv t
end

end AddM

end PartIiProject.Optimisations
