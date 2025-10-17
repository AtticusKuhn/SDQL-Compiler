import Std.Data.TreeMap.Basic
import Mathlib.Data.Prod.Lex
set_option linter.style.longLine false

inductive Ty : Type where
  | bool : Ty
  | dict : Ty → Ty → Ty
  | record : (List (Ty)) → Ty
  | string : Ty
  | int :  Ty
  deriving Inhabited

structure Dict (α β : Type) where
  cmp : Ord α
  map : Std.TreeMap (cmp := fun a b => cmp.compare a b) α β
-- deriving Inhabited

instance toStringDict (a b : Type) [ToString a] [ToString b] : ToString (Dict a b) where
  toString := fun s => "{" ++ s.map.foldl (fun s k v => s ++ s!"{k} => {v}, " ) "" ++ "}"

-- Provide a Repr instance for Dict so #eval can display it using its
-- existing ToString rendering.
instance reprDict (a b : Type) [ToString a] [ToString b] : Repr (Dict a b) where
  reprPrec d _ := repr (toString d)

-- Help the printer for results whose type is of the shape
-- `(tensor (Ty.dict dom range) b).denote`, which is definally
-- `Dict dom.denote ((tensor range b).denote)`. Typeclass search
-- often does not unfold `tensor`/`Ty.denote` here, so we register
-- (moved below, after `Ty.denote`, `showDict`, and `tensor` are defined)

namespace Dict
def empty {α β} (cmp : Ord α) : Dict α β :=
  { cmp := cmp
  , map := Std.TreeMap.empty (α := α) (β := β) (cmp := fun a b => cmp.compare a b)
  }

def insert {α β} (d : Dict α β) (k : α) (v : β) : Dict α β :=
  { d with map := d.map.insert (cmp := fun a b => d.cmp.compare a b) k v }

def find? {α β} (d : Dict α β) (k : α) : Option β :=
  d.map.get? (cmp := fun a b => d.cmp.compare a b) k
end Dict



inductive HList {α : Type} (β : α → Type) : List α → Type where
  | nil : HList β []
  | cons {x xs} : β x → HList β xs → HList β (x :: xs)


def hmap {T : Type} {l : List T} {ftype : T → Type} {gtype : T → Type} (f : {t : T} → ftype t → gtype t) : HList ftype l  → HList gtype l
  | HList.nil => HList.nil
  | HList.cons t ts => HList.cons (f t) (hmap f ts)
@[reducible, simp]
unsafe def Ty.denote (t : Ty) : Type :=
  match t with
  | .bool => Bool
  | .int => Int
  | .string => String
  | .record l => HList Ty.denote l
  | .dict dom range => Dict dom.denote range.denote

-- Pretty-printing for record values (HList Ty.denote l)
mutual
unsafe def showHList {l : List Ty} : HList Ty.denote l → String
| .nil => ""
| .cons h t =>
  let head := showValue h
  let tail := showHList t
  if tail = "" then head else s!"{head}, {tail}"

unsafe def showDict {dom range : Ty} (d : Dict dom.denote range.denote) : String :=
  "{" ++ d.map.foldl (fun s k v =>
    s ++ s!"{showValue (t := dom) k} => {showValue (t := range) v}, "
  ) "" ++ "}"

unsafe def showValue : {t : Ty} → t.denote → String
  | .bool, b => toString b
  | .int, n => toString n
  | .string, s => s
  | .record l, r => "<" ++ showHList r ++ ">"
  | .dict dom range, d => showDict (dom := dom) (range := range) d
end

unsafe instance toStringHList {l : List Ty} : ToString (HList Ty.denote l) where
  toString := fun h => "<" ++ showHList h ++ ">"

unsafe instance reprHList {l : List Ty} : Repr (HList Ty.denote l) where
  reprPrec h _ := repr (toString h)

instance instOrdUnit : Ord Unit where
  compare := fun _ _ => Ordering.eq

instance instOrdDict (a b : Type) : Ord (Dict a b) where
  compare := fun _ _ => Ordering.eq

unsafe def HListOrd {T : Type} {f : T → Type} {l : List T} (o : HList (Ord ∘ f) l) : Ord (HList f l) :=
  match o with
    | HList.nil => ⟨fun _ _ => Ordering.eq⟩
    | HList.cons head tail => ⟨ compareLex (compareOn (ord := head) (fun (HList.cons h _) => h)) (compareOn (ord := HListOrd tail) (fun (HList.cons _ t) => t))⟩

def dmap {T : Type} (l : List T) {ftype : T → Type} (f : (t : T) → ftype t) : HList ftype l :=
  match l with
    | [] => HList.nil
    | t :: ts => HList.cons (f t) (dmap ts f)

unsafe def Ty.ord (t : Ty) : Ord t.denote :=
  match t with
    | .bool => inferInstance
    | .int => inferInstance
    | .string => inferInstance
    | .dict a b => instOrdDict a.denote b.denote
    | .record l => HListOrd (dmap l Ty.ord)

@[simp, reducible]
def tensor (a b : Ty) : Ty :=
  match a with
    | .dict dom range => .dict dom (tensor range b)
    | .record l => .record (l.map (fun t => tensor t b))
    | _ => b
    -- | .int => .int
    -- | .bool => .bool
    -- | .string => .string

-- Help the printer for results whose type is of the shape
-- `(tensor (Ty.dict dom range) b).denote`, which is definally
-- `Dict dom.denote ((tensor range b).denote)`. Typeclass search
-- often does not unfold `tensor`/`Ty.denote` here, so we register
-- a direct instance at that head-type. If needed, we can also provide
-- a custom `Repr` instance here to help `#eval` printing, but we avoid
-- that for now to keep instance search lightweight.

inductive AddM : Ty → Type where
  | boolA : AddM Ty.bool
  | intA : AddM Ty.int
  | dictA {dom range : Ty} (aRange : AddM range) : AddM (Ty.dict dom range)
  | recordA {l : List Ty} : HList AddM l → AddM (Ty.record l)

mutual
unsafe def addHList {l : List Ty} (fields : HList AddM l) (x y : HList Ty.denote l) : HList Ty.denote l :=
  match l, x, y, fields with
    | [], _, _, _ => HList.nil
    | _ :: _, HList.cons xh xt, HList.cons yh yt, HList.cons fh ft => HList.cons (AddM.denote fh xh yh) (addHList ft xt yt)

unsafe def AddM.denote {t : Ty} : AddM t → t.denote → t.denote → t.denote
  | .boolA, x, y => Bool.xor x y
  | .intA, x, y => Int.add x y
  | @AddM.dictA dom range aRange, x, y =>
    let inner := AddM.denote aRange
    -- Merge y into x using inner on values
    y.map.foldl (fun acc k v2 =>
      match Dict.find? acc k with
      | some v1 => Dict.insert acc k (inner v1 v2)
      | none    => Dict.insert acc k v2
    ) x
  | @AddM.recordA l fields, x, y => addHList fields x y
end

inductive ScaleM : Ty → Ty → Type where
  | boolS : ScaleM Ty.bool Ty.bool
  | intS : ScaleM Ty.int Ty.int
  | dictS {sc dom range : Ty} (sRange : ScaleM sc range) : ScaleM sc (Ty.dict dom range)
  | recordS {sc : Ty} {l : List Ty} (fields : ∀ (t : Ty), t ∈ l → ScaleM sc t) : ScaleM sc (Ty.record l)

def toHList {T : Type} {l : List T} {ftype : T → Type} (f : ∀ (t : T), t ∈ l → ftype t) : HList ftype l :=
  match l with
    | [] => HList.nil
    | t :: ts => HList.cons (f t (by simp only [List.mem_cons, true_or])) (toHList (fun t' => f t' ∘ List.mem_cons_of_mem t))

mutual
unsafe def go {sc : Ty} (l : List Ty) (a : sc.denote) (fields : HList (ScaleM sc) l)
    (r : HList Ty.denote l) : HList Ty.denote l :=
  match l, fields, r with
  | [], _, _ => HList.nil
  | _ :: ts, HList.cons fh ft, HList.cons h rest =>
    HList.cons (ScaleM.denote fh a h) (go ts a ft rest)

unsafe def ScaleM.denote {sc t : Ty} : ScaleM sc t → sc.denote → t.denote → t.denote
  | .boolS, a, x => Bool.and a x
  | .intS, a, x => Int.mul a x
  | @ScaleM.dictS sc dom range sRange, a, d =>
    let inner := ScaleM.denote (sc := sc) (t := range) sRange
    d.map.foldl (fun acc k v => Dict.insert acc k (inner a v)) (Dict.empty (Ty.ord dom))
  | @ScaleM.recordS sc l fields, a, r =>
    go l a (toHList fields) r
end


-- inductive Term' (rep : Ty → Type) : Ty → Type
--   | var   : {ty : Ty} → rep ty → Term' rep ty
--   | constInt : Int → Term' rep  Ty.int
--   | constBool : Bool → Term' rep Ty.bool
--   | constString : String → Term' rep Ty.string
--   | add : {ty sc : Ty} → (_s : SM sc ty) → Term' rep ty → Term' rep ty → Term' rep ty

-- mutual
-- inductive RecordFields (rep : Ty → Type) : List Ty → Type where
--   | nil  : RecordFields rep []
--   | cons : {t : Ty} →  {ts : List Ty} → Term' rep t → RecordFields rep ts → RecordFields rep (t :: ts)


inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : {ty : Ty} → rep ty → Term' rep ty
  | constInt : Int → Term' rep Ty.int
  | constBool : Bool → Term' rep Ty.bool
  | constString : String → Term' rep Ty.string
  -- | constRecord : {l : List Ty} → RecordFields rep l → Term' rep (.record l)
  | constRecord : {l : List Ty} → HList (Term' rep) l  → Term' rep (.record l)

  | emptyDict: {dom  : Ty} →  {range : Ty} → Term' rep (.dict dom range)
  | dictInsert : {dom  : Ty} →  {range : Ty} → (Term' rep dom) → (Term' rep range) →  Term' rep (.dict dom range) → Term' rep (.dict dom range)
  -- | constDict : {dom  : OrderableTy} →  {range : Ty} → List ( Bool × Term' rep range) → Term' rep (.dict dom range)
  -- | constRecord : {l : List (Ty)} → (fields : toRecordType (Term' rep) l ) → Term' rep (.record l)
  | not : Term' rep Ty.bool → Term' rep Ty.bool
  | ite : {ty : Ty} → Term' rep Ty.bool → Term' rep ty → Term' rep ty → Term' rep ty
  | letin : {ty₁ ty₂ : Ty} → Term' rep ty₁ → (rep ty₁ → Term' rep ty₂) → Term' rep ty₂
  | add : {ty : Ty} → (a : AddM ty) → Term' rep ty → Term' rep ty → Term' rep ty
  | mul : { sc t1 t2 : Ty} → (_s1 : ScaleM sc t1) →  (_s2 : ScaleM sc t2) → Term' rep t1 → Term' rep t2 → Term' rep (tensor t1 t2)
  | proj : (l : List (Ty)) → Term' rep (.record l) → (i : Nat) → Term' rep (l.getD i Ty.int)
-- end

unsafe def getProj {l : List Ty} (recordVal : Ty.denote (.record l)) (i : Nat) : (l.getD i Ty.int).denote :=
  match i, l, recordVal with
  | 0,   _ :: _, (HList.cons h _) => h
  | n+1, _ :: ts, (HList.cons _ t_val) => getProj t_val n
  | (Nat.succ n), [], HList.nil => by
    simp only [Nat.succ_eq_add_one, List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero,
      not_false_eq_true, getElem?_neg, Option.getD_none, Ty.denote]
    exact 0
  | Nat.zero, [], HList.nil => by
    simp only [Nat.zero_eq, List.getD_eq_getElem?_getD, List.length_nil, Nat.lt_irrefl,
      not_false_eq_true, getElem?_neg, Option.getD_none, Ty.denote]
    exact 0

unsafe def Term'.denote {ty : Ty} : Term' Ty.denote ty → ty.denote
  | Term'.var v => v
  | Term'.constInt n => n
  | Term'.constBool b => b
  | Term'.constString s => s
  | Term'.add a t1 t2 =>
    let add := AddM.denote a
    add (denote t1) (denote t2)
  | .not t => Bool.not (denote t)
  | .ite c t1 t2 => match (denote c) with
    | true => (denote t1)
    | false => (denote t2)
  | .letin t1 f => denote (f (denote t1))
  | .proj l record index =>
    let dr := denote record
    getProj dr index
  | .constRecord fields => hmap denote fields
    -- let rec denoteFields {l : List Ty} : HList (Term' Ty.denote) l → Ty.denote (.record l)
    --   | .nil => HList.nil
    --   | .cons h t => HList.cons (denote h) (denoteFields t)
    -- denoteFields fields
  | @Term'.emptyDict _ dom range => Dict.empty (Ty.ord dom)
  | .dictInsert key val dict => Dict.insert (dict.denote) key.denote val.denote
  | @Term'.mul _ sc t1 t2 s1 s2 t1e t2e =>
    let lval := denote t1e
    let rval := denote t2e
    let rec mulDenote {sc t1 t2 : Ty}
        (s1 : ScaleM sc t1) (s2 : ScaleM sc t2)
        (lval : t1.denote) (rval : t2.denote) : (tensor t1 t2).denote :=
      match s1 with
      | .boolS =>
        by
          -- sc = bool, t1 = bool
          -- tensor Ty.bool t2 = t2, so scale the right value by the left factor
          exact ScaleM.denote s2 lval rval
      | .intS =>
        by
          -- sc = int, t1 = int
          -- tensor Ty.int t2 = t2, so scale the right value by the left factor
          exact ScaleM.denote s2 lval rval
      | @ScaleM.dictS sc dom range sRange =>
        let acc : Dict dom.denote (Ty.denote (tensor range t2)) := Dict.empty (Ty.ord dom)
        let res := lval.map.foldl (fun acc k v =>
          let v' := mulDenote (t1 := range) sRange s2 v rval
          Dict.insert acc k v'
        ) acc
        by
          unfold tensor
          exact res
      | @ScaleM.recordS sc l fields =>
        let rec go (l : List Ty)
            (fields : HList (ScaleM sc) l)
            (lv : Ty.denote (.record l))
            : Ty.denote (.record (l.map (fun t => tensor t t2))) :=
          match l, fields , lv with
          | [], HList.nil, HList.nil => HList.nil
          | t :: ts, HList.cons fh ft, HList.cons h rest =>
            let h' := mulDenote (t1 := t) fh s2 h rval
            let rest' := go ts ft rest
            HList.cons h' rest'
        by
          unfold tensor
          exact (go l (toHList fields) lval)
    mulDenote s1 s2 lval rval

def Term'.show {ty : Ty} : Term' (fun _ => String) ty → String
  | .var v           => v
  | .constInt n      => toString n
  | .constBool b     => toString b
  | .constString s   => s
  | .add _ t1 t2     => s!"{t1.show} + {t2.show}"  -- note: ignore the Add evidence
  | (proj _ b c) => s!"{b.show}.{c}"
  | (mul _ _ b c)=> s!"{b.show} * {c.show}"
  | (letin  a b)=> s!"let x = {a.show} in {(b "x").show}"
  |(ite c t f)=> s!"if {c.show} then {t.show} else {f.show}"
  | (not e)=> s!"not {e.show}"
  |(dictInsert a b c)=> s!"\{{a.show} -> {b.show}} ++ {c.show}"
  | (emptyDict)=> "{}"
  | (constRecord r)=>
    let rec show_r {l : List Ty} (r : HList (Term' (fun _ ↦ String)) l) : String :=
      match r with
        | .nil => ""
        | .cons h t =>
          let hStr := (Term'.show h)
          let tStr := show_r t
          if tStr = "" then hStr else s!"{hStr}, {tStr}"
    "<" ++ show_r r ++ ">"
  -- | _ => "(unsuppoted)"


def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty



def test : Term Ty.int :=
  Term'.add (AddM.intA) (Term'.constInt 3) (Term'.constInt 5)

def test2 : Term Ty.bool :=
  Term'.add (AddM.boolA) (Term'.constBool true) (Term'.constBool false)

def test3 : Term (Ty.dict Ty.int Ty.string) :=
  Term'.dictInsert (.constInt 1) (.constString "one") (Term'.emptyDict)

def test4 : Term Ty.int :=  .add AddM.intA (.constInt 1) (.constInt 2)
def test5 : Term (Ty.record [Ty.int, Ty.bool]) := .constRecord (.cons (Term'.constInt 15) (.cons (Term'.constBool true) .nil))
def test6 : Term Ty.int := .proj [Ty.int, Ty.bool] test5 0
def test7 : Term (Ty.dict Ty.int Ty.string) := .dictInsert (.constInt 1) (.constString "hello") .emptyDict

-- Multiplication examples
def mul_int_int : Term (tensor Ty.int Ty.int) :=
  Term'.mul (ScaleM.intS) (ScaleM.intS) (.constInt 2) (.constInt 4)

def dict_si : Term (Ty.dict Ty.string Ty.int) :=
  Term'.dictInsert (.constString "a") (.constInt 2)
    (Term'.dictInsert (.constString "b") (.constInt 3) (Term'.emptyDict))

def rec_i : Term (Ty.record [Ty.int]) :=
  .constRecord (.cons (.constInt 4) .nil)

-- {"a"->2, "b"->3} * <4>  ==> {"a"-><8>, "b"-><12>}
def mul_dict_record : Term (tensor (Ty.dict Ty.string Ty.int) (Ty.record [Ty.int])) :=
  let fields1 : ∀ (t : Ty), t ∈ [Ty.int] → ScaleM Ty.int t :=
    fun t ht =>
      by
        have : t = Ty.int := by simpa [List.mem_singleton] using ht
        simpa [this] using ScaleM.intS
  Term'.mul (ScaleM.dictS ScaleM.intS)
            (ScaleM.recordS fields1)
            dict_si rec_i

def dict2_si : Term (Ty.dict Ty.string Ty.int) :=
  Term'.dictInsert (.constString "a") (.constInt 4)
    (Term'.dictInsert (.constString "c") (.constInt 5) (Term'.emptyDict))

-- {"a"->2, "b"->3} * {"a"->4, "c"->5}
-- ==> {"a" -> {4 scaled by 2, 5 scaled by 2}, "b" -> {4 scaled by 3, 5 scaled by 3}}
def mul_dict_dict : Term (tensor (Ty.dict Ty.string Ty.int) (Ty.dict Ty.string Ty.int)) :=
  Term'.mul (ScaleM.dictS ScaleM.intS)
            (ScaleM.dictS ScaleM.intS)
            dict_si dict2_si

def rec_ii : Term (Ty.record [Ty.int, Ty.int]) :=
  .constRecord (.cons (.constInt 1) (.cons (.constInt 2) .nil))

-- <1,2> * 3 ==> <3,6>
-- def mul_record_int : Term (tensor (Ty.record [Ty.int, Ty.int]) Ty.int) :=
--   let fields2 : ∀ (t : Ty), t ∈ [Ty.int, Ty.int] → ScaleM Ty.int t :=
--     fun t ht =>
--       by
--         -- From membership in [int, int], t must be int
--         have h' : t = Ty.int ∨ t = Ty.int := by
--           simpa [List.mem_cons, List.mem_singleton] using ht
--         cases h' with
--         | inl h => simpa [h] using ScaleM.intS
--         | inr h => simpa [h] using ScaleM.intS
--   Term'.mul (ScaleM.recordS fields2)
--             (ScaleM.intS)
--             rec_ii (.constInt 3)

-- Additional record examples with pretty-printing
def rec_nested : Term (Ty.record [Ty.int, Ty.record [Ty.bool, Ty.string]]) :=
  .constRecord
    (.cons (.constInt 42)
      (.cons (.constRecord (.cons (.constBool false) (.cons (.constString "ok") .nil)))
        .nil))

def dict_record_values : Term (Ty.dict Ty.string (Ty.record [Ty.int, Ty.bool])) :=
  .dictInsert (.constString "x")
              (.constRecord (.cons (.constInt 7) (.cons (.constBool false) .nil)))
              .emptyDict

def Term.show {ty : Ty} (t : Term ty) : String :=
  Term'.show (t)
-- set_option pp.explicit true

#eval Term'.denote test
#eval Term'.denote test2
#eval Term'.denote test3
#eval Term'.denote test4
#eval ("<" ++ showHList (Term'.denote test5) ++ ">")
#eval Term'.denote test6

-- #eval Term'.denote mul_int_int
-- Note: The following results are complex nested types without a ToString instance.
-- They typecheck and evaluate, but we don't print them here.
-- example :
--    (tensor (Ty.string.dict Ty.int) (Ty.record [Ty.int])).denote = Dict String (Int × Unit) := by
--     simp only [tensor, Ty.denote, Ty.denote.toType]
-- #eval (tensor (Ty.string.dict Ty.int) (Ty.record [Ty.int]))
#eval Term.show mul_dict_record
-- Printing directly via `Repr` for this nested tensor type can trigger
-- heavy instance search/unfolding. Use the explicit pretty-printer.
#eval showDict (dom := Ty.string) (range := Ty.record [Ty.int]) (Term'.denote mul_dict_record)

-- Pretty-printed results for complex nested tensor types via casts
-- (These casts relied on older helper lemmas; they are disabled for now.)
-- #eval (let h : (tensor (Ty.string.dict Ty.int) (Ty.record [Ty.int])).denote
--               = Dict String (Int × Unit) := by
--          simp [Ty.denote]
--        toString (cast h (Term'.denote mul_dict_record)))

-- #eval (let h : (tensor (Ty.string.dict Ty.int) (Ty.string.dict Ty.int)).denote
--               = Dict String (Dict String Int) := by
--          simp [tensor, Ty.denote]
--        toString (cast h (Term'.denote mul_dict_dict)))
-- #eval Term'.denote mul_record_int

#eval Term.show test
#eval Term.show test2

-- Pretty-print record values (via Repr/ToString instances)
#eval ("<" ++ showHList (Term'.denote rec_nested) ++ ">")
#eval showDict (dom := Ty.string) (range := Ty.record [Ty.int, Ty.bool]) (Term'.denote dict_record_values)
