import PartIiProject.Optimisations.Term2Utils

open PartIiProject

namespace PartIiProject.Optimisations

abbrev Optimisation : Type :=
  {ctx : List Ty} → {ty : Ty} → Term2 ctx ty → Option (Term2 ctx ty)

def fail : Optimisation :=
  fun _ => none

def seq (o1 o2 : Optimisation) : Optimisation :=
  fun t =>
    match o1 t with
    | some t' => some t'
    | none => o2 t

mutual
  partial def anySubexpressionTerm (o : Optimisation) {ctx : List Ty} {ty : Ty} :
      Term2 ctx ty → Option (Term2 ctx ty)
    | t =>
        match o t with
        | some t' => some t'
        | none =>
            match t with
            | .var _ => none
            | .constInt _ => none
            | .constReal _ => none
            | .constBool _ => none
            | .constString _ => none
            | .constRecord fields =>
                match anySubexpressionFields o fields with
                | some fields' => some (Term2.constRecord fields')
                | none => none
            | .emptyDict => none
            | .dictInsert k v d =>
                match anySubexpressionLoc o k with
                | some k' => some (Term2.dictInsert k' v d)
                | none =>
                    match anySubexpressionLoc o v with
                    | some v' => some (Term2.dictInsert k v' d)
                    | none =>
                        match anySubexpressionLoc o d with
                        | some d' => some (Term2.dictInsert k v d')
                        | none => none
            | .lookup aRange d k =>
                match anySubexpressionLoc o d with
                | some d' => some (Term2.lookup aRange d' k)
                | none =>
                    match anySubexpressionLoc o k with
                    | some k' => some (Term2.lookup aRange d k')
                    | none => none
            | .not e =>
                match anySubexpressionLoc o e with
                | some e' => some (Term2.not e')
                | none => none
            | .ite c t f =>
                match anySubexpressionLoc o c with
                | some c' => some (Term2.ite c' t f)
                | none =>
                    match anySubexpressionLoc o t with
                    | some t' => some (Term2.ite c t' f)
                    | none =>
                        match anySubexpressionLoc o f with
                        | some f' => some (Term2.ite c t f')
                        | none => none
            | .letin bound body =>
                match anySubexpressionLoc o bound with
                | some bound' => some (Term2.letin bound' body)
                | none =>
                    match anySubexpressionLoc o body with
                    | some body' => some (Term2.letin bound body')
                    | none => none
            | .add a t1 t2 =>
                match anySubexpressionLoc o t1 with
                | some t1' => some (Term2.add a t1' t2)
                | none =>
                    match anySubexpressionLoc o t2 with
                    | some t2' => some (Term2.add a t1 t2')
                    | none => none
            | @Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1 e2 =>
                match anySubexpressionLoc o e1 with
                | some e1' => some (@Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1' e2)
                | none =>
                    match anySubexpressionLoc o e2 with
                    | some e2' => some (@Term2.mul _ sc t1Ty t2Ty t3 s1 s2 inst e1 e2')
                    | none => none
            | .semiringMul hm e1 e2 =>
                match anySubexpressionLoc o e1 with
                | some e1' => some (Term2.semiringMul hm e1' e2)
                | none =>
                    match anySubexpressionLoc o e2 with
                    | some e2' => some (Term2.semiringMul hm e1 e2')
                    | none => none
            | .closure hc e =>
                match anySubexpressionLoc o e with
                | some e' => some (Term2.closure hc e')
                | none => none
            | .promote e =>
                match anySubexpressionLoc o e with
                | some e' => some (Term2.promote e')
                | none => none
            | .sum a d body =>
                match anySubexpressionLoc o d with
                | some d' => some (Term2.sum a d' body)
                | none =>
                    match anySubexpressionLoc o body with
                    | some body' => some (Term2.sum a d body')
                    | none => none
            | @Term2.proj _ l t record i inst =>
                match anySubexpressionLoc o record with
                | some record' => some (@Term2.proj _ l t record' i inst)
                | none => none
            | .builtin f arg =>
                match anySubexpressionLoc o arg with
                | some arg' => some (Term2.builtin f arg')
                | none => none

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

def anySubexpression (o : Optimisation) : Optimisation :=
  fun t => anySubexpressionTerm o t

partial def fixpointTerm {ctx : List Ty} {ty : Ty} (o : Optimisation) (t : Term2 ctx ty) :
    Option (Term2 ctx ty) :=
  match o t with
  | some t' =>
      match fixpointTerm o t' with
      | some t'' => some t''
      | none => some t'
  | none => none

def fixpoint (o : Optimisation) : Optimisation :=
  fun t => fixpointTerm o t

def seqAll (opts : List Optimisation) : Optimisation :=
  match opts with
  | [] => fail
  | o :: os => seq o (seqAll os)

def seqAnySubexpression (opts : List Optimisation) : Optimisation :=
  match opts with
  | [] => fail
  | o :: os => seq (anySubexpression o) (seqAnySubexpression os)

def optimiseUntilStable (opts : List Optimisation) : Optimisation :=
  fixpoint (seqAnySubexpression opts)

def runOptimisation {ctx : List Ty} {ty : Ty} (o : Optimisation) (t : Term2 ctx ty) :
    Term2 ctx ty :=
  match o t with
  | some t' => t'
  | none => t

def runOptimisationLoc {ctx : List Ty} {ty : Ty}
    (o : Optimisation) (t : TermLoc2 ctx ty) : TermLoc2 ctx ty :=
  match t with
  | .mk loc inner =>
      .mk loc (runOptimisation o inner)

def optimiseTerm {ctx : List Ty} {ty : Ty} (opts : List Optimisation) (t : Term2 ctx ty) :
    Term2 ctx ty :=
  runOptimisation (optimiseUntilStable opts) t

def optimiseLoc {ctx : List Ty} {ty : Ty} (opts : List Optimisation) (t : TermLoc2 ctx ty) :
    TermLoc2 ctx ty :=
  runOptimisationLoc (optimiseUntilStable opts) t

end PartIiProject.Optimisations
