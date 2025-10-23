import PartIiProject.Term
import PartIiProject.CodegenRust

namespace Tests
namespace Cases

open PartIiProject

/- A tiny measure used to compare Lean vs. Rust outputs. It mirrors the
   `SDQLMeasure` trait in the generated Rust runtime. -/
mutual
unsafe def sdqlMeasureHList : {l : List Ty} → HList Ty.denote l → Int
  | [], .nil => 0
  | _ :: ts, .cons h t => sdqlMeasure h + sdqlMeasureHList t

unsafe def sdqlMeasure : {t : Ty} → t.denote → Int
  | .int, n => n
  | .bool, b => if b then 1 else 0
  | .string, s => Int.ofNat s.length
  | .record l, r => sdqlMeasureHList r
  | .dict dom range, d =>
      d.map.foldl (fun acc k v => acc + 31 * sdqlMeasure (t := dom) k + sdqlMeasure (t := range) v) 0
end

/- Sample test cases ported from inline demos. -/
/- Test cases support both closed terms and open terms with runtime parameters. -/
unsafe inductive TestCase where
  | closed {ty : Ty} (name : String) (term : Term f0 ty) (expected : Int) : TestCase
  | openCase {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      (name : String)
      (termEval : Term fvar ty)
      (termCode : Term' (fun _ => String) fvar ty)
      (args : (i : Fin n) → (fvar i).denote)
      (expected : Int) : TestCase

open TestCase

-- SDQL terms
def t_add_int : Term f0 Ty.int :=
  Term'.add (AddM.intA) (Term'.constInt 3) (Term'.constInt 5)

def t_add_bool : Term f0 Ty.bool :=
  Term'.add (AddM.boolA) (Term'.constBool true) (Term'.constBool false)

def t_dict_is : Term f0 (Ty.dict Ty.int Ty.string) :=
  Term'.dictInsert (.constInt 1) (.constString "one") (Term'.emptyDict)

def t_dict_ii : Term f0 (Ty.dict Ty.int Ty.int) :=
  Term'.dictInsert (.constInt 1) (.constInt 2)
    (Term'.dictInsert (.constInt 3) (.constInt 4) (Term'.emptyDict))

def t_lookup_hit : Term f0 Ty.int :=
  Term'.lookup (aRange := AddM.intA) (t_dict_ii) (.constInt 1)

def t_lookup_miss : Term f0 Ty.int :=
  Term'.lookup (aRange := AddM.intA) (t_dict_ii) (.constInt 0)

def t_sum_vals : Term f0 Ty.int :=
  Term'.sum (a := AddM.intA) (t_dict_ii) (fun _ v => Term'.var v)

unsafe def cases : List TestCase :=
  let mkClosed {ty} (name : String) (t : Term f0 ty) : TestCase :=
    let v := Term'.denote (fvar := f0) env0 (t (rep := Ty.denote))
    let m := sdqlMeasure (t := ty) v
    TestCase.closed name t m

  -- Open-term examples with runtime parameters
  -- Case 1: int addition with param: (arg0 : int) + 5
  let fvar1 : Fin 1 → Ty := fun _ => Ty.int
  let t_add_int_param_eval : Term fvar1 Ty.int :=
    fun {rep} => Term'.add AddM.intA (.freeVariable ⟨0, Nat.zero_lt_one⟩) (.constInt 5)
  let t_add_int_param_code : Term' (fun _ => String) fvar1 Ty.int :=
    Term'.add AddM.intA (.freeVariable ⟨0, Nat.zero_lt_one⟩) (.constInt 5)
  let args1 : (i : Fin 1) → (fvar1 i).denote := fun _ => (7 : Int)
  let v1 := Term'.denote (env := args1) (t_add_int_param_eval (rep := Ty.denote))
  let m1 := sdqlMeasure (t := Ty.int) v1

  -- Case 2: bool guard param in if: if arg0 then 10 else 20
  let fvar2 : Fin 1 → Ty := fun _ => Ty.bool
  let t_if_bool_param_eval : Term fvar2 Ty.int :=
    fun {rep} => Term'.ite (.freeVariable ⟨0, Nat.zero_lt_one⟩) (.constInt 10) (.constInt 20)
  let t_if_bool_param_code : Term' (fun _ => String) fvar2 Ty.int :=
    Term'.ite (.freeVariable ⟨0, Nat.zero_lt_one⟩) (.constInt 10) (.constInt 20)
  let args2t : (i : Fin 1) → (fvar2 i).denote := fun _ => true
  let v2 := Term'.denote (env := args2t) (t_if_bool_param_eval (rep := Ty.denote))
  let m2 := sdqlMeasure (t := Ty.int) v2

  -- Case 3: dict lookup with runtime dict and key
  let fvar3 : Fin 2 → Ty :=
    fun i => match i.val with | 0 => Ty.dict Ty.int Ty.int | _ => Ty.int
  let dParam : Dict Int Int :=
    let o := Dict.empty (Ty.ord Ty.int)
    Dict.insert (Dict.insert o 1 42) 2 5
  let t_lookup_param_eval : Term fvar3 Ty.int :=
    fun {rep} =>
      let i0 : Fin 2 := ⟨0, by decide⟩
      let i1 : Fin 2 := ⟨1, by decide⟩
      Term'.lookup (aRange := AddM.intA) (.freeVariable i0) (.freeVariable i1)
  let t_lookup_param_code : Term' (fun _ => String) fvar3 Ty.int :=
      let i0 : Fin 2 := ⟨0, by decide⟩
      let i1 : Fin 2 := ⟨1, by decide⟩
      Term'.lookup (aRange := AddM.intA) (.freeVariable i0) (.freeVariable i1)
  let args3 : (i : Fin 2) → (fvar3 i).denote :=
    fun
    | ⟨0, _⟩ => dParam
    | ⟨1, _⟩ => (1 : Int)
  let v3 := Term'.denote (env := args3) (t_lookup_param_eval (rep := Ty.denote))
  let m3 := sdqlMeasure (t := Ty.int) v3

  -- Case 4: sum over runtime dict of ints
  let fvar4 : Fin 1 → Ty := fun _ => Ty.dict Ty.int Ty.int
  let d4 : Dict Int Int :=
    let o := Dict.empty (Ty.ord Ty.int)
    Dict.insert (Dict.insert o 3 4) 5 6
  let t_sum_param_eval : Term fvar4 Ty.int :=
    fun {rep} => Term'.sum (a := AddM.intA) (.freeVariable ⟨0, Nat.zero_lt_one⟩) (fun _ v => Term'.var v)
  let t_sum_param_code : Term' (fun _ => String) fvar4 Ty.int :=
    Term'.sum (a := AddM.intA) (.freeVariable ⟨0, Nat.zero_lt_one⟩) (fun _ v => Term'.var v)
  let args4 : (i : Fin 1) → (fvar4 i).denote := fun _ => d4
  let v4 := Term'.denote (env := args4) (t_sum_param_eval (rep := Ty.denote))
  let m4 := sdqlMeasure (t := Ty.int) v4

  [ mkClosed "add_int" t_add_int
  , mkClosed "add_bool" t_add_bool
  , mkClosed "dict_insert" t_dict_is
  , mkClosed "lookup_hit" t_lookup_hit
  , mkClosed "lookup_miss" t_lookup_miss
  , mkClosed "sum_vals" t_sum_vals
  , TestCase.openCase "add_int_param" t_add_int_param_eval t_add_int_param_code args1 m1
  , TestCase.openCase "if_bool_param" t_if_bool_param_eval t_if_bool_param_code args2t m2
  , TestCase.openCase "lookup_param" t_lookup_param_eval t_lookup_param_code args3 m3
  , TestCase.openCase "sum_param" t_sum_param_eval t_sum_param_code args4 m4
  ]

end Cases
end Tests
