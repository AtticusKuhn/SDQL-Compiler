import PartIiProject.Optimisations.Term2Utils

open PartIiProject

namespace PartIiProject.Optimisations

abbrev Optimisation : Type :=
  {ctx : List Ty} → {ty : Ty} → Term2 ctx ty → Option (Term2 ctx ty)

def fail : Optimisation :=
  fun _ => none

def seq : Optimisation → Optimisation → Optimisation :=
  (fun t => · t <|> · t)

instance :  OrElse Optimisation where
    orElse x y := seq x (y ())

instance : Inhabited Optimisation where
    default := fail

mutual
  partial def anySubexpressionTerm (o : Optimisation) {ctx : List Ty} {ty : Ty} :
      Term2 ctx ty → Option (Term2 ctx ty)
    | t =>
        o t <|>
        match t with
        | .var _
        | .constInt _
        | .constReal _
        | .constBool _
        | .constString _
        | .emptyDict => none
        | .constRecord fields =>
            Term2.constRecord <$> anySubexpressionFields o fields
        | .dictInsert k v d =>
            ((Term2.dictInsert · v d) <$> anySubexpressionLoc o k) <|>
            ((Term2.dictInsert k · d) <$> anySubexpressionLoc o v) <|>
            ((Term2.dictInsert k v) <$> anySubexpressionLoc o d)
        | .lookup aRange d k =>
            ((fun d' => Term2.lookup aRange d' k) <$> anySubexpressionLoc o d) <|>
            ((fun k' => Term2.lookup aRange d k') <$> anySubexpressionLoc o k)
        | .not e =>
            Term2.not <$> anySubexpressionLoc o e
        | .ite c t f =>
            ((fun c' => Term2.ite c' t f) <$> anySubexpressionLoc o c) <|>
            ((fun t' => Term2.ite c t' f) <$> anySubexpressionLoc o t) <|>
            ((fun f' => Term2.ite c t f') <$> anySubexpressionLoc o f)
        | .letin bound body =>
            ((fun bound' => Term2.letin bound' body) <$> anySubexpressionLoc o bound) <|>
            ((fun body' => Term2.letin bound body') <$> anySubexpressionLoc o body)
        | .add a t1 t2 =>
            ((fun t1' => Term2.add a t1' t2) <$> anySubexpressionLoc o t1) <|>
            ((fun t2' => Term2.add a t1 t2') <$> anySubexpressionLoc o t2)
        | @Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1 e2 =>
            ((fun e1' => @Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1' e2) <$> anySubexpressionLoc o e1) <|>
            ((fun e2' => @Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1 e2') <$> anySubexpressionLoc o e2)
        | .semiringMul hm e1 e2 =>
            ((fun e1' => Term2.semiringMul hm e1' e2) <$> anySubexpressionLoc o e1) <|>
            ((fun e2' => Term2.semiringMul hm e1 e2') <$> anySubexpressionLoc o e2)
        | .closure hc e =>
            (fun e' => Term2.closure hc e') <$> anySubexpressionLoc o e
        | .promote e =>
            Term2.promote <$> anySubexpressionLoc o e
        | .sum a d body =>
            ((fun d' => Term2.sum a d' body) <$> anySubexpressionLoc o d) <|>
            ((fun body' => Term2.sum a d body') <$> anySubexpressionLoc o body)
        | @Term2.proj _ l t record i inst =>
            (fun record' => @Term2.proj _ l t record' i inst) <$> anySubexpressionLoc o record
        | .builtin f arg =>
            (fun arg' => Term2.builtin f arg') <$> anySubexpressionLoc o arg

  partial def anySubexpressionLoc (o : Optimisation) {ctx : List Ty} {ty : Ty} :
      TermLoc2 ctx ty → Option (TermLoc2 ctx ty)
    | .mk loc inner =>
        match anySubexpressionTerm o inner with
        | some inner' => some (.mk loc inner')
        | none => none

  partial def anySubexpressionFields (o : Optimisation) {ctx : List Ty} :
      {l : List Ty} → TermFields2 ctx l → Option (TermFields2 ctx l)
    | [], .nil => none
    | _ :: _, .cons h t =>
        match anySubexpressionLoc o h with
        | some h' => some (.cons h' t)
        | none =>
            match anySubexpressionFields o t with
            | some t' => some (.cons h t')
            | none => none
end

def anySubexpression : Optimisation → Optimisation :=
    anySubexpressionTerm

partial def fixpointTerm (o : Optimisation) : Optimisation:= seq o (fixpointTerm o)


def fixpoint : Optimisation → Optimisation :=
  fixpointTerm

def seqAll :   List Optimisation → Optimisation :=
    (·.foldr (β := Optimisation) seq fail)


def seqAnySubexpression : List Optimisation → Optimisation :=
    (·.foldr (β := Optimisation) (seq ∘ anySubexpression) fail)

def optimiseUntilStable: List Optimisation →  Optimisation :=
  fixpoint ∘ seqAnySubexpression

def runOptimisation {ctx : List Ty} {ty : Ty} (o : Optimisation) (t : Term2 ctx ty) :
    Term2 ctx ty :=
    (o t).getD t

def runOptimisationLoc {ctx : List Ty} {ty : Ty}
    (o : Optimisation) (t : TermLoc2 ctx ty) : TermLoc2 ctx ty :=
  match t with
  | .mk loc inner =>
      .mk loc (runOptimisation o inner)

def optimiseTerm {ctx : List Ty} {ty : Ty} : List Optimisation →  Term2 ctx ty →  Term2 ctx ty :=
  runOptimisation ∘ optimiseUntilStable


def optimiseLoc {ctx : List Ty} {ty : Ty} (opts : List Optimisation) (t : TermLoc2 ctx ty) :
    TermLoc2 ctx ty :=
  runOptimisationLoc (optimiseUntilStable opts) t

end PartIiProject.Optimisations
