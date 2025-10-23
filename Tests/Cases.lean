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
inductive TestCase where
  | mk {ty : Ty} (name : String) (term : Term f0 ty) (expected : Int) : TestCase

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
  let mkExp {ty} (name : String) (t : Term f0 ty) : TestCase :=
    let v := Term'.denote (fvar := f0) env0 (t (rep := Ty.denote))
    let m := sdqlMeasure (t := ty) v
    TestCase.mk name t m
  [ mkExp "add_int" t_add_int
  , mkExp "add_bool" t_add_bool
  , mkExp "dict_insert" t_dict_is
  , mkExp "lookup_hit" t_lookup_hit
  , mkExp "lookup_miss" t_lookup_miss
  , mkExp "sum_vals" t_sum_vals
  ]

end Cases
end Tests
