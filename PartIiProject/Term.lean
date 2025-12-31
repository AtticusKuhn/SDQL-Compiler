import Std.Data.TreeMap.Basic
import PartIiProject.Dict
import PartIiProject.HList
import PartIiProject.Mem

set_option linter.unusedVariables false

/-
Source location information for core terms.
This tracks positions from the original SDQL source code.
-/
structure SourceLocation where
  /-- Start position (byte offset) in the source file -/
  startPos : Nat
  /-- End position (byte offset) in the source file -/
  endPos : Nat
  substring : String := ""
  deriving Inhabited, Repr, BEq

namespace SourceLocation

/-- A default/unknown location -/
def unknown : SourceLocation := ⟨0, 0, ""⟩

/-- Pretty print a source location -/
def toString (loc : SourceLocation) : String :=
  s!"substring {loc.substring}: [{loc.startPos}..{loc.endPos}]"

instance : ToString SourceLocation := ⟨SourceLocation.toString⟩

end SourceLocation

inductive Ty : Type where
  | bool : Ty
  | real : Ty
  | date : Ty
  | dict : Ty → Ty → Ty
  | record : List Ty → Ty
  | string : Ty
  | int : Ty
  deriving Inhabited

-- Date type: represented as YYYYMMDD integer (e.g., 19980902)
-- This matches sdql-rs's date representation
structure SDQLDate where
  yyyymmdd : Int
  deriving Inhabited, BEq, Repr

instance : Ord SDQLDate where
  compare a b := compare a.yyyymmdd b.yyyymmdd

instance : ToString SDQLDate where
  toString d := s!"date({d.yyyymmdd})"

@[reducible, simp]
unsafe def Ty.denote (t : Ty) : Type :=
  match t with
  | .bool => Bool
  | .real => Float
  | .date => SDQLDate
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
      s ++ s!"{showValue (t := dom) k} -> {showValue (t := range) v}, "
    ) "" ++ "}"

  unsafe def showValue : {t : Ty} → t.denote → String
    | .bool, b => toString b
    | .real, n => toString n
    | .date, d => toString d
    | .int, n => toString n
    | .string, s => s
    | .record _, r => "<" ++ showHList r ++ ">"
    | .dict _ _, d => showDict d
end

inductive AddM : Ty → Type where
  | boolA : AddM Ty.bool
  | realA : AddM Ty.real
  | dateA : AddM Ty.date
  | intA : AddM Ty.int
  | stringA : AddM Ty.string
  | dictA {dom range : Ty} (aRange : AddM range) : AddM (Ty.dict dom range)
  | recordA {l : List Ty} : HList AddM l → AddM (Ty.record l)

instance instOrdUnit : Ord Unit where
  compare := fun _ _ => Ordering.eq

instance instOrdDict (a b : Type) : Ord (Dict a b) where
  compare := fun _ _ => Ordering.eq

instance instOrdFloat : Ord Float where
  compare := fun a b =>
    if a < b then Ordering.lt
    else if a == b then Ordering.eq
    else Ordering.gt

unsafe def HListOrd {T : Type} {f : T → Type} {l : List T} (o : HList (Ord ∘ f) l) : Ord (HList f l) :=
  match o with
  | HList.nil => ⟨fun _ _ => Ordering.eq⟩
  | HList.cons head tail =>
      ⟨compareLex
          (compareOn (ord := head) (fun (HList.cons h _) => h))
          (compareOn (ord := HListOrd tail) (fun (HList.cons _ t) => t))⟩

unsafe def Ty.ord (t : Ty) : Ord t.denote :=
  match t with
  | .bool => inferInstance
  | .real => inferInstance
  | .date => inferInstance
  | .int => inferInstance
  | .string => inferInstance
  | .dict a b => instOrdDict a.denote b.denote
  | .record l => HListOrd (dmap l Ty.ord)

-- Default/inhabited values for types (used for fallbacks)
mutual
  unsafe def Ty.inhabited (t : Ty) : t.denote :=
    match t with
    | .bool => false
    | .real => 0.0
    | .date => SDQLDate.mk 0
    | .int => 0
    | .string => ""
    | .record l => Ty.inhabitedHList l
    | .dict dom _ => Dict.empty (Ty.ord dom)

  unsafe def Ty.inhabitedHList : (l : List Ty) → HList Ty.denote l
    | [] => HList.nil
    | t :: ts => HList.cons (Ty.inhabited t) (Ty.inhabitedHList ts)
end

-- Additive identities for AddM types
mutual
  unsafe def zeroHList {l : List Ty} : HList AddM l → HList Ty.denote l
    | .nil => HList.nil
    | .cons h t => HList.cons (AddM.zero h) (zeroHList t)

  unsafe def AddM.zero {t : Ty} : AddM t → t.denote
    | .boolA => false
    | .realA => (0.0 : Float)
    | .dateA => SDQLDate.mk 10101  -- dummy date like sdql-rs (0001-01-01)
    | .intA => 0
    | .stringA => ""
    | @AddM.dictA dom _ _ => Dict.empty (Ty.ord dom)
    | @AddM.recordA _ fields => zeroHList fields
end

unsafe instance toStringHList {l : List Ty} : ToString (HList Ty.denote l) where
  toString := fun h => "<" ++ showHList h ++ ">"

unsafe instance reprHList {l : List Ty} : Repr (HList Ty.denote l) where
  reprPrec h _ := repr (toString h)

@[simp, reducible]
def tensor (a b : Ty) : Ty :=
  match a with
  | .dict dom range => .dict dom (tensor range b)
  | .record l => .record (l.map (fun t => tensor t b))
  | _ => b
termination_by a

mutual
  unsafe def addHList {l : List Ty} (fields : HList AddM l)
      (x y : HList Ty.denote l) : HList Ty.denote l :=
    match l, x, y, fields with
    | [], _, _, _ => HList.nil
    | _ :: _, HList.cons xh xt, HList.cons yh yt, HList.cons fh ft =>
        HList.cons (AddM.denote fh xh yh) (addHList ft xt yt)

  unsafe def AddM.denote {t : Ty} : AddM t → t.denote → t.denote → t.denote
    | .boolA, x, y => x || y
    | .realA, x, y => x + y
    | .dateA, _x, y => y  -- date "addition" overwrites (like sdql-rs AddAssign)
    | .intA, x, y => Int.add x y
    | .stringA, x, y => x ++ y
    | @AddM.dictA dom _ aRange, x, y =>
        let inner := AddM.denote aRange
        y.map.foldl (fun acc k v2 =>
          match Dict.find? acc k with
          | some v1 => Dict.insert acc k (inner v1 v2)
          | none => Dict.insert acc k v2
        ) x
    | @AddM.recordA _ fields, x, y => addHList fields x y
end

inductive ScaleM : Ty → Ty → Type where
  | boolS : ScaleM Ty.bool Ty.bool
  | realS : ScaleM Ty.real Ty.real
  | intS : ScaleM Ty.int Ty.int
  | dictS {sc dom range : Ty} (sRange : ScaleM sc range) : ScaleM sc (Ty.dict dom range)
  | recordS {sc : Ty} {l : List Ty} (fields : ∀ (t : Ty), Mem t l → ScaleM sc t) : ScaleM sc (Ty.record l)

def toHList {T : Type} {l : List T} {ftype : T → Type}
    (f : ∀ (t : T), Mem t l → ftype t) : HList ftype l :=
  match l with
  | [] => HList.nil
  | t :: ts => HList.cons (f t (Mem.head ts)) (toHList (fun t' hp => f t' (Mem.tail t hp)))

mutual
  unsafe def scaleRecordHList {sc : Ty}
      {l : List Ty} (a : sc.denote)
      (fields : HList (ScaleM sc) l)
      (r : HList Ty.denote l) : HList Ty.denote l :=
    match fields, r with
    | HList.nil, HList.nil => HList.nil
    | HList.cons fh ft, HList.cons h rest =>
        HList.cons (ScaleM.denote fh a h) (scaleRecordHList a ft rest)

  unsafe def ScaleM.denote {sc t : Ty} : ScaleM sc t → sc.denote → t.denote → t.denote
    | .boolS, a, x => Bool.and a x
    | .realS, a, x => a * x
    | .intS, a, x => Int.mul a x
    | @ScaleM.dictS sc dom range sRange, a, d =>
        let inner := ScaleM.denote (sc := sc) (t := range) sRange
        d.map.foldl (fun acc k v => Dict.insert acc k (inner a v)) (Dict.empty (Ty.ord dom))
    | @ScaleM.recordS sc _ fields, a, r =>
        scaleRecordHList a (toHList fields) r
end

-- Shape-directed multiplication helper (used by the interpreter/codegen layer)
unsafe def ScaleM.mulDenote {sc t1 t2 : Ty}
    (s1 : ScaleM sc t1) (s2 : ScaleM sc t2)
    : t1.denote → t2.denote → (tensor t1 t2).denote :=
  match s1 with
  | .boolS =>
      fun l r => ScaleM.denote s2 l r
  | .intS =>
      fun l r => ScaleM.denote s2 l r
  | .realS =>
      fun l r => ScaleM.denote s2 l r
  | @ScaleM.dictS sc dom range sRange =>
      fun l r =>
        let res := Dict.mapValues l (fun v => ScaleM.mulDenote (t1 := range) sRange s2 v r)
        by
          unfold tensor
          exact res
  | @ScaleM.recordS sc l fields =>
      fun lval rval =>
        let rec go
            {l : List Ty}
            (fs : HList (ScaleM sc) l)
            (lv : HList Ty.denote l)
            : HList Ty.denote (l.map (fun t => tensor t t2)) :=
          match fs, lv with
          | HList.nil, HList.nil => HList.nil
          | HList.cons fh ft, HList.cons h rest =>
              HList.cons (ScaleM.mulDenote fh s2 h rval) (go ft rest)
        by
          unfold tensor
          exact (go (toHList fields) lval)

inductive BuiltinFn : Ty → Ty → Type
  | Or : BuiltinFn (Ty.record [.bool, .bool]) Ty.bool
  | And : BuiltinFn (Ty.record [.bool, .bool]) Ty.bool
  | Eq (t : Ty) : BuiltinFn (Ty.record [t, t]) Ty.bool
  | Leq (t : Ty) : BuiltinFn (Ty.record [t, t]) Ty.bool
  | Lt (t : Ty) : BuiltinFn (Ty.record [t, t]) Ty.bool
  | Sub (t : Ty) : BuiltinFn (Ty.record [t, t]) t
  | Div : BuiltinFn (Ty.record [.real, .real]) Ty.real
  | StrEndsWith : BuiltinFn (Ty.record [.string, .string]) Ty.bool
  | StrStartsWith : BuiltinFn (Ty.record [.string, .string]) Ty.bool
  | StrContains : BuiltinFn (Ty.record [.string, .string]) Ty.bool
  | FirstIndex : BuiltinFn (Ty.record [.string, .string]) Ty.int
  | LastIndex : BuiltinFn (Ty.record [.string, .string]) Ty.int
  | SubString : BuiltinFn (Ty.record [.string, .int, .int]) Ty.string
  | Dom : {dom range : Ty} → BuiltinFn (.dict dom range) (.dict dom Ty.bool)
  | Range : BuiltinFn Ty.int (Ty.dict Ty.int Ty.bool)
  | Size : {dom range : Ty} → BuiltinFn (.dict dom range) Ty.int
  | DateLit (yyyymmdd : Int) : BuiltinFn (Ty.record []) Ty.date
  | Year : BuiltinFn Ty.date Ty.int
  | Concat (l1 l2 : List Ty) : BuiltinFn (Ty.record [.record l1, .record l2]) (Ty.record (l1 ++ l2))

/-!
The previous PHOAS core term/program layer (`Term'`/`Prog`) has been removed.
Use the DeBruijn-indexed core terms in `PartIiProject.Term2`.
-/
