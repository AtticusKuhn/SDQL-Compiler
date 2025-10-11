import Mathlib.Algebra.Module.Defs
import Std.Data.TreeMap.Basic
import Std.Data.ExtTreeMap.Basic
-- import Mathlib.Data.List.Sigma
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Prod.Lex

set_option linter.style.longLine false

def List.keys {A B : Type} (l : List (A × B)) : List A :=
  match l with
    | [] => []
    | (a, _) :: t =>  a :: List.keys t


-- def toRecordType (f : Ty → Type) (l : List (Ty)) : Type := l.foldr (fun (b) c => (f b) × c) Unit

-- HList has to be a Type 1, so it won't work for using in Ty.denote
inductive HList : List Type → Type 1 where
  | nil  : HList []
  | cons : {T : Type} → {Ts : List Type} → (x : T) → (xs : HList Ts) → HList (T :: Ts)
-- def List.lookup_mem {A B : Type} [DecidableEq A] (a : A) (l : List (A × B)) (mem : a ∈ l.keys) : B :=
--   match l with
--     | [] => []
--     | (a, b) :: t =>  a :: List.keys t
inductive OrderableTy : Type where
  | bool : OrderableTy
  | string : OrderableTy
  | int : OrderableTy
  | record : (List OrderableTy) → OrderableTy

deriving Inhabited

@[reducible, simp]
def OrderableTy.denote : OrderableTy → Type
  | .bool => Bool
  | .string => String
  | .int => Int
  | .record l =>
    let rec toType (l : List OrderableTy) : Type :=
      match l with
      | [] => Unit
      | (ty :: tys) => ty.denote × toType tys
    toType l
-- mutual
-- def cmpList {l : List OrderableTy} : (OrderableTy.denote (.record l)) → (OrderableTy.denote (.record l)) → Ordering :=
--     match l with
--       | [] => fun _ _ => .eq
--       | (ty :: tys) => fun (a1, a2) (b1, b2) =>
--         match mkComp ty a1 b1 with
--           | .lt => .lt
--           | .gt => .gt
--           | .eq => cmpList tys a2 b2

instance instOrdUnit : Ord Unit where
  compare := fun _ _ => Ordering.eq



--       cmpList (OrderableTy.record l )
-- end
-- mutual
inductive Ty : Type where
  | bool : Ty
  | dict : Ty → Ty → Ty
  | record : (List (Ty)) → Ty
  | string : Ty
  | int :  Ty
  deriving Inhabited


def tensor (a b : Ty) : Ty :=
  match a with
    | .dict dom range => .dict dom (tensor range b)
    | .record l => .record (l.map (fun t => tensor t b))
    | x => b

class OrdTy (rep : Ty → Type) (t : Ty) : Type where
  hasOrd : Ord (rep t)
-- end
@[reducible, simp]
def orderableTyToTy : OrderableTy → Ty
  | .bool => Ty.bool
  | .string => Ty.string
  | .int => Ty.int
  | .record l => Ty.record (l.map orderableTyToTy)
-- class TyOrd (t : Ty) : Type where
--   or

-- mutual
  -- def mkComp {a : Ty} (x y : Ty.denote a) : Ordering := sorry
-- mutual

@[reducible, simp]
def Ty.denote (t : Ty) : Type  :=
  match t with
    | .bool => Bool
    | .int => Int
    | .string => String
    | .record l =>
      -- let sl := List.mergeSort l (fun (a b : (String × Ty)) => a.1 < b.1)
      -- let ml := l.map (fun (ty) => ty.denote)
      -- ml
      -- let t : Type := l.foldl (fun b ty => Ty.denote ty × b) Unit
       let rec toType (l : List Ty) : Type :=
        match l with
        | [] => Unit
        | (ty :: tys) => ty.denote × toType tys
      -- termination_by l
      -- t
      toType l
      -- HList (l.map (fun ty => ty.denote))
      -- l.foldr (fun ty b => ty.denote × b) Unit

    | .dict dom range => List (dom.denote × range.denote)
      -- let mkComp : Ty.denote dom → Ty.denote dom → Ordering :=
      --   match dom with
      --     | .int => instOrdInt.compare
      --     | .bool => instOrdBool.compare x y
      --     | .string => instOrdString.compare x y
      --     | .record l => sorry
      --     | .dict a b => sorry
      -- let rec mkComp {t : Ty} : Ord t.denote :=
      --   match t with
      --     | .int => instOrdInt
      --     | .bool => instOrdBool
      --     | .string => instOrdString
      --     | .record l =>
      --       let rec helper (l : List Ty) : Ord (Ty.denote (Ty.record l)) :=
      --         match l with
      --           | [] => instOrdUnit
      --           | h :: t => @Prod.Lex.instOrdLexProd h.denote _ (mkComp (t := h)) (helper t)
      --       helper l
      --     | .dict dom range => sorry
      -- Std.TreeMap (cmp := mkComp.compare) dom.denote range.denote
-- end
-- decreasing_by
--   all_goals simp
--   all_goals try omega
  -- simp [sizeOf]
  -- all_goals sorry
  -- def mkComp {a : Ty} (x y : Ty.denote a) : Ordering := sorry

-- example : denote Ty.int = Int := rfl
-- end
theorem orderablety_denote_eq (d : OrderableTy) : Ty.denote (orderableTyToTy d) = d.denote := by
  cases d
  <;> try rfl
  · rename_i l
    match l with
      | [] => rfl
      | h :: t =>
        have m := orderablety_denote_eq (.record t)
        simp only [← m, OrderableTy.denote, OrderableTy.denote.toType]
        rw [orderableTyToTy]
        rw [Ty.denote]
        rw [Ty.denote.toType.eq_def]
        simp only [List.map_cons]
        rw [orderablety_denote_eq h]
        rw [orderableTyToTy]

#eval tensor (.dict Ty.string Ty.int) (.record [Ty.int])
class SM (scalar : Ty) (t : Ty) : Type where
  add : t.denote → t.denote → t.denote
  mutliply : scalar.denote → t.denote → t.denote

instance smb : SM Ty.bool Ty.bool where
  add := Bool.or
  mutliply := Bool.and
instance smi : SM Ty.int Ty.int where
  add := Int.add
  mutliply := Int.mul
-- {dom -> range} + t2 = {dom -> range + t2}
instance deceq {t : Ty} : DecidableEq (t.denote) := by
  cases t
  <;> simp only [Ty.denote]
  <;> try infer_instance
  · rename_i a b
    have := deceq (t := a)
    have := deceq (t := b)
    infer_instance
  · rename_i a
    let rec helper (b : List Ty) : DecidableEq (Ty.denote.toType b) :=
      match b with
        | [] => by
          simp only [Ty.denote.toType]
          infer_instance
        | head :: tail => by
          simp [Ty.denote.toType]
          have := deceq (t := head)
          have := helper tail
          infer_instance
    exact helper a

instance smt {sc t1 t2 : Ty} [s1 : SM sc t1] [s2 : SM sc t2] : SM sc (tensor t1 t2) where
  add := match t1 with
    | .dict dom range => by
      have add1 := s1.add
      have add2 := s2.add
      simp [tensor];
      sorry
    | .record l => by
      have add1 := s1.add
      have add2 := s2.add
      simp [tensor]
      sorry
    | .int  | .string | .bool => by
      simp only [tensor]
      exact s2.add

  mutliply :=  match t1 with
    | .bool | .int | .string =>
      by simp [tensor]; exact s2.mutliply
    | .dict dom range => by
      simp [tensor]
      sorry
      -- Scalar multiplication on a dict: apply it to each value.
      -- let _s_rec : SM sc (tensor range t2) := smt (s1:= s1) (s2:=s2)
      -- exact (fun s d => d.map (fun (k, v) => (k, _s_rec.mutliply s v)))
    | .record l => sorry
-- instance smd (t1 t2 : Ty) [smt2 : SM t2] : SM (Ty.dict t1 t2) where

-- def sm_to_add {t : Ty} (x : SM t) : Add t.denote where
--   add := match t with
--     | .bool => Bool.or
--     | .int => Int.instAdd.add
--     | .string => fun a b =>  panic! "e"
--     | .record l => fun a b =>  panic! "e"
--     | .dict f t => fun a b =>  panic! "e"

inductive hasModule : Ty → Ty → Type where
  | boolOr : hasModule Ty.bool Ty.bool
  | intAdd : hasModule Ty.bool Ty.bool

mutual

inductive RecordFields (rep : Ty → Type) : List Ty → Type where
  | nil  : RecordFields rep []
  | cons : {t : Ty} →  {ts : List Ty} → Term' rep t → RecordFields rep ts → RecordFields rep (t :: ts)

inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : {ty : Ty} → rep ty → Term' rep ty
  | constInt : Int → Term' rep Ty.int
  | constBool : Bool → Term' rep Ty.bool
  | constString : String → Term' rep Ty.string
  | constRecord : {l : List Ty} → RecordFields rep l → Term' rep (.record l)
  | emptyDict: {dom  : Ty} →  {range : Ty} → Term' rep (.dict dom range)
  | dictInsert : {dom  : Ty} →  {range : Ty} → (Term' rep dom) → (Term' rep range) →  Term' rep (.dict dom range) → Term' rep (.dict dom range)
  -- | constDict : {dom  : OrderableTy} →  {range : Ty} → List ( Bool × Term' rep range) → Term' rep (.dict dom range)
  -- | constRecord : {l : List (Ty)} → (fields : toRecordType (Term' rep) l ) → Term' rep (.record l)
  | not : Term' rep Ty.bool → Term' rep Ty.bool
  | ite : {ty : Ty} → Term' rep Ty.bool → Term' rep ty → Term' rep ty → Term' rep ty
  | letin : {ty₁ ty₂ : Ty} → Term' rep ty₁ → (rep ty₁ → Term' rep ty₂) → Term' rep ty₂
  | add : {ty sc : Ty} → [_s : SM sc ty] → Term' rep ty → Term' rep ty → Term' rep ty
  | mul : { sc t1 t2 : Ty} → [_s1 : SM sc t1] →  [_s2 : SM sc t2] → Term' rep t1 → Term' rep t2 → Term' rep (tensor t1 t2)
  | proj : (l : List (Ty)) → Term' rep (.record l) → (i : Nat) → Term' rep (l.getD i Ty.int)
end


def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty
-- def getRecord {types : List Ty} {rep : Ty → Type} (r : RecordFields rep types) (index : Nat) : Term' rep (types[index]!) :=
--   match r, index with
--     | .cons t ts, 0 => t
--     | .cons t ts, Nat.succ i => getRecord ts i
--     | .nil, _ => by simp; sorry

example : Ty.int.denote = Int := rfl
example : (orderableTyToTy OrderableTy.int) = Ty.int := rfl
def test : Term Ty.int :=  .add (sc := Ty.int) (.constInt 1) (.constInt 2)
def test2 : Term (Ty.record [Ty.int, Ty.bool]) :=.constRecord (.cons (Term'.constInt 15) (.cons (Term'.constBool true) .nil))
def test3 : Term (Ty.int) :=  .proj [Ty.int, Ty.bool] (test2) 0
def test4 : Term (Ty.dict Ty.int Ty.string) := .dictInsert (.constInt 1) (.constString "hello") .emptyDict

def getProj {l : List Ty} (recordVal : Ty.denote (.record l)) (i : Nat) : (l.getD i Ty.int).denote :=
  match i, l, recordVal with
  | 0,   _ :: _, (h, _) => h
  | n+1, _ :: ts, (_, t_val) => getProj t_val n
  | (Nat.succ n), [], PUnit.unit => by
    simp only [Nat.succ_eq_add_one, List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero,
      not_false_eq_true, getElem?_neg, Option.getD_none, Ty.denote]
    exact 0
  | Nat.zero, [], PUnit.unit => by
    simp only [Nat.zero_eq, List.getD_eq_getElem?_getD, List.length_nil, Nat.lt_irrefl,
      not_false_eq_true, getElem?_neg, Option.getD_none, Ty.denote]
    exact 0

@[simp] def denote {ty : Ty} : Term' Ty.denote ty → ty.denote
  | .var v => v
  | .constInt n => n
  | .constBool b => b
  | .constString s => s
  | .not t => not (denote t)
  | .ite c t1 t2 => match (denote c) with
    | true => (denote t1)
    | false => (denote t2)
  | .letin t1 f => denote (f (denote t1))
  | .add (_s := s) t1 t2 => s.add (denote t1) (denote t2)
  | .proj l record index =>
    let dr := denote record
    getProj dr index
    -- match l with
    --   | [] => by
    --     simp at dr

    --     sorry
    --   | l :: ls => sorry
    -- getRecord dr index
  -- | .constRecord fields => sorry
  | .constRecord fields =>
    let rec denoteFields {l : List Ty} : RecordFields Ty.denote l → Ty.denote (.record l)
      | .nil => ()
      | .cons h t => (denote h, denoteFields t)
    denoteFields fields
  | .emptyDict => []
  | .dictInsert key val dict => ((denote key), (denote val) ):: (denote dict)
  | .mul (_s1 := s1) (_s2 := s2) t1 t2 => smt (s1 := s1) (s2 := s2).mutliply (denote t1) (denote t2)
#eval! denote (test Ty.denote)
#eval! denote (test2 Ty.denote)
#eval! denote (test3 Ty.denote)
#eval! denote (test4 Ty.denote)
