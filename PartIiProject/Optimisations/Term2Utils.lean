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

abbrev ContextParser (ctx₁ ctx₂ : List Ty) : Type :=
  ∀ {ty : Ty}, Term2 ctx₁ ty → Option (Term2 ctx₂ ty)

private abbrev VarParser (ctx₁ ctx₂ : List Ty) : Type :=
  ∀ {ty : Ty}, Mem ty ctx₁ → Option (Term2 ctx₂ ty)

private def liftVarParser {ctx₁ ctx₂ : List Ty} {a : Ty}
    (parse : ContextParser ctx₁ ctx₂) : VarParser (a :: ctx₁) (a :: ctx₂)
  | _, .head _ => pure (.var (.head _))
  | _, .tail _ m => do
      let t ← parse (.var m)
      pure (wk (a := a) t)

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
  private partial def parseTerm2 {ctx₁ ctx₂ : List Ty}
      (parseVar : VarParser ctx₁ ctx₂) : {ty : Ty} → Term2 ctx₁ ty → Option (Term2 ctx₂ ty)
    | _, .var m => parseVar m
    | _, .constInt n => pure (.constInt n)
    | _, .constReal r => pure (.constReal r)
    | _, .constBool b => pure (.constBool b)
    | _, .constString s => pure (.constString s)
    | _, .constRecord fields => do
        let fields' ← parseFields2 parseVar fields
        pure (.constRecord fields')
    | _, .emptyDict => pure .emptyDict
    | _, .dictInsert k v d => do
        let k' ← parseLoc2 parseVar k
        let v' ← parseLoc2 parseVar v
        let d' ← parseLoc2 parseVar d
        pure (.dictInsert k' v' d')
    | _, .lookup aRange d k => do
        let d' ← parseLoc2 parseVar d
        let k' ← parseLoc2 parseVar k
        pure (.lookup aRange d' k')
    | _, .not e => do
        let e' ← parseLoc2 parseVar e
        pure (.not e')
    | _, .ite c t f => do
        let c' ← parseLoc2 parseVar c
        let t' ← parseLoc2 parseVar t
        let f' ← parseLoc2 parseVar f
        pure (.ite c' t' f')
    | _, .letin bound body => do
        let parseHere : ContextParser ctx₁ ctx₂ :=
          fun {_} t => parseTerm2 parseVar t
        let bound' ← parseLoc2 parseVar bound
        let body' ← parseLoc2 (liftVarParser parseHere) body
        pure (.letin bound' body')
    | _, .add a t₁ t₂ => do
        let t₁' ← parseLoc2 parseVar t₁
        let t₂' ← parseLoc2 parseVar t₂
        pure (.add a t₁' t₂')
    | _, @Term2.mul _ sc t₁ t₂ t₃ s₁ s₂ inst e₁ e₂ => do
        let e₁' ← parseLoc2 parseVar e₁
        let e₂' ← parseLoc2 parseVar e₂
        pure (@Term2.mul _ sc t₁ t₂ t₃ s₁ s₂ inst e₁' e₂')
    | _, .semiringMul hm e₁ e₂ => do
        let e₁' ← parseLoc2 parseVar e₁
        let e₂' ← parseLoc2 parseVar e₂
        pure (.semiringMul hm e₁' e₂')
    | _, .closure hc e => do
        let e' ← parseLoc2 parseVar e
        pure (.closure hc e')
    | _, .promote e => do
        let e' ← parseLoc2 parseVar e
        pure (.promote e')
    | _, .sum a d body => do
        let parseHere : ContextParser ctx₁ ctx₂ :=
          fun {_} t => parseTerm2 parseVar t
        let parseUnder : ContextParser (_ :: ctx₁) (_ :: ctx₂) :=
          fun {_} t => parseTerm2 (liftVarParser parseHere) t
        let d' ← parseLoc2 parseVar d
        let body' ← parseLoc2 (liftVarParser parseUnder) body
        pure (.sum a d' body')
    | _, @Term2.proj _ l t record i inst => do
        let record' ← parseLoc2 parseVar record
        pure (@Term2.proj _ l t record' i inst)
    | _, .builtin f arg => do
        let arg' ← parseLoc2 parseVar arg
        pure (.builtin f arg')

  private partial def parseLoc2 {ctx₁ ctx₂ : List Ty} {ty : Ty}
      (parseVar : VarParser ctx₁ ctx₂) : TermLoc2 ctx₁ ty → Option (TermLoc2 ctx₂ ty)
    | .mk loc inner => do
        let inner' ← parseTerm2 parseVar inner
        pure (.mk loc inner')

  private partial def parseFields2 {ctx₁ ctx₂ : List Ty}
      (parseVar : VarParser ctx₁ ctx₂) :
      {l : List Ty} → TermFields2 ctx₁ l → Option (TermFields2 ctx₂ l)
    | [], .nil => pure .nil
    | _ :: _, .cons h t => do
        let h' ← parseLoc2 parseVar h
        let t' ← parseFields2 parseVar t
        pure (.cons h' t')
end

/-- Parse a term in `(a :: ctx)` as one that is actually independent of the head variable. -/
def dropUnusedHead {ctx : List Ty} {a ty : Ty} : Term2 (a :: ctx) ty → Option (Term2 ctx ty) :=
  parseTerm2 (ctx₁ := a :: ctx) (ctx₂ := ctx) (fun {_} m =>
    match m with
    | .head _ => none
    | .tail _ m => pure (.var m))

/-- Lift a parser under one additional binder, keeping the bound variable available. -/
def underBinder {ctx₁ ctx₂ : List Ty} {a : Ty}
    (parse : ContextParser ctx₁ ctx₂) :
    {ty : Ty} → Term2 (a :: ctx₁) ty → Option (Term2 (a :: ctx₂) ty) :=
  parseTerm2 (ctx₁ := a :: ctx₁) (ctx₂ := a :: ctx₂) (liftVarParser parse)

abbrev dropVar {ctx : List Ty} {a ty : Ty} :
    Term2 (a :: ctx) ty → Option (Term2 ctx ty) :=
  dropUnusedHead

abbrev under {ctx₁ ctx₂ : List Ty} {a : Ty}
    (parse : ContextParser ctx₁ ctx₂) :
    {ty : Ty} → Term2 (a :: ctx₁) ty → Option (Term2 (a :: ctx₂) ty) :=
  underBinder parse

def dropUnusedHeadLoc {ctx : List Ty} {a ty : Ty} :
    TermLoc2 (a :: ctx) ty → Option (TermLoc2 ctx ty) :=
  parseLoc2 (ctx₁ := a :: ctx) (ctx₂ := ctx) (fun {_} m =>
    match m with
    | .head _ => none
    | .tail _ m => pure (.var m))

def underBinderLoc {ctx₁ ctx₂ : List Ty} {a : Ty}
    (parse : ContextParser ctx₁ ctx₂) :
    {ty : Ty} → TermLoc2 (a :: ctx₁) ty → Option (TermLoc2 (a :: ctx₂) ty) :=
  parseLoc2 (ctx₁ := a :: ctx₁) (ctx₂ := a :: ctx₂) (liftVarParser parse)

abbrev dropVarLoc {ctx : List Ty} {a ty : Ty} :
    TermLoc2 (a :: ctx) ty → Option (TermLoc2 ctx ty) :=
  dropUnusedHeadLoc

abbrev underLoc {ctx₁ ctx₂ : List Ty} {a : Ty}
    (parse : ContextParser ctx₁ ctx₂) :
    {ty : Ty} → TermLoc2 (a :: ctx₁) ty → Option (TermLoc2 (a :: ctx₂) ty) :=
  underBinderLoc parse

/-- Extract an invariant term under two binders by parsing it as independent of both binders. -/
def extractInvariant {ctx : List Ty} {a b ty : Ty}
    (e : TermLoc2 (a :: b :: ctx) ty) : Option (TermLoc2 ctx ty) :=
  do
    let e' ← dropUnusedHeadLoc (a := a) e
    dropUnusedHeadLoc (a := b) e'


abbrev extractInvariant2 {ctx : List Ty} {a b ty : Ty}
    (e : TermLoc2 (a :: b :: ctx) ty) : Option (TermLoc2 ctx ty) :=
  extractInvariant e

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
