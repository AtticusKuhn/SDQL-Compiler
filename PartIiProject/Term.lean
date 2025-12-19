import Std.Data.TreeMap.Basic
import PartIiProject.Dict
import PartIiProject.HList
import PartIiProject.Mem

-- set_option linter.style.longLine false
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
  substring: String := ""
  deriving Inhabited, Repr, BEq

namespace SourceLocation

/-- A default/unknown location -/
def unknown : SourceLocation := ⟨0, 0, ""⟩

/-- Pretty print a source location -/
def toString (loc : SourceLocation) : String :=
  s!"substring {loc.substring}: [{loc.startPos}..{loc.endPos}]"

instance : ToString SourceLocation := ⟨SourceLocation.toString ⟩

end SourceLocation

inductive Ty : Type where
  | bool : Ty
  | real : Ty
  | date : Ty
  | dict : Ty → Ty → Ty
  | record : (List (Ty)) → Ty
  | string : Ty
  | int :  Ty
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
  | .record l, r => "<" ++ showHList r ++ ">"
  | .dict dom range, d => showDict (dom := dom) (range := range) d
end
inductive AddM : Ty → Type where
  | boolA   : AddM Ty.bool
  | realA   : AddM Ty.real
  | dateA   : AddM Ty.date
  | intA    : AddM Ty.int
  | stringA : AddM Ty.string
  | dictA   {dom range : Ty} (aRange : AddM range) : AddM (Ty.dict dom range)
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
    | HList.cons head tail => ⟨ compareLex (compareOn (ord := head) (fun (HList.cons h _) => h)) (compareOn (ord := HListOrd tail) (fun (HList.cons _ t) => t))⟩


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
  | @AddM.dictA dom range aRange => Dict.empty (Ty.ord dom)
  | @AddM.recordA l fields => zeroHList fields
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
    -- | .int => .int
    -- | .bool => .bool
    -- | .string => .string
termination_by a
-- The printer for results with shape `(tensor (Ty.dict _ _) b).denote`
-- benefits from the explicit `showDict` defined above.


mutual
unsafe def addHList {l : List Ty} (fields : HList AddM l)
    (x y : HList Ty.denote l) : HList Ty.denote l :=
  match l, x, y, fields with
    | [], _, _, _ => HList.nil
    | _ :: _, HList.cons xh xt, HList.cons yh yt, HList.cons fh ft =>
      HList.cons (AddM.denote fh xh yh) (addHList ft xt yt)

unsafe def AddM.denote {t : Ty} : AddM t → t.denote → t.denote → t.denote
  | .boolA, x, y => Bool.xor x y
  | .realA, x, y => x + y
  | .dateA, _x, y => y  -- date "addition" overwrites (like sdql-rs AddAssign)
  | .intA, x, y => Int.add x y
  | .stringA, x, y => x ++ y
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
  | realS : ScaleM Ty.real Ty.real
  | intS : ScaleM Ty.int Ty.int
  | dictS {sc dom range : Ty} (sRange : ScaleM sc range) : ScaleM sc (Ty.dict dom range)
  | recordS {sc : Ty} {l : List Ty} (fields : ∀ (t : Ty), Mem t l → ScaleM sc t) : ScaleM sc (Ty.record l)

def toHList {T : Type} {l : List T} {ftype : T → Type}
  (f : ∀ (t : T), Mem t l → ftype t) : HList ftype l :=
  match l with
    | [] => HList.nil
    | t :: ts =>
      HList.cons (f t (Mem.head ts)) (toHList (fun t' hp => f t' (Mem.tail t hp)))

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
  | @ScaleM.recordS sc l fields, a, r =>
    scaleRecordHList a (toHList fields) r
end


-- Shape-directed multiplication helper for `Term'.mul`
unsafe def ScaleM.mulDenote {sc t1 t2 : Ty}
    (s1 : ScaleM sc t1) (s2 : ScaleM sc t2)
    : t1.denote → t2.denote → (tensor t1 t2).denote :=
  match s1 with
  | .boolS =>
    fun l r =>
      -- tensor Ty.bool t2 = t2
      ScaleM.denote s2 l r
  | .intS =>
    fun l r =>
      -- tensor Ty.int t2 = t2
      ScaleM.denote s2 l r
  | .realS =>
    fun l r =>
      -- tensor Ty.real t2 = t2
      ScaleM.denote s2 l r
  | @ScaleM.dictS sc dom range sRange =>
    fun l r =>
      -- tensor {dom -> range} t2 = {dom -> (tensor range t2)}
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
          HList.cons (ScaleM.mulDenote fh s2 h rval)
                    (go ft rest)
      by
        unfold tensor
        exact (go (toHList fields) lval)

inductive BuiltinFn : Ty → Ty → Type
  | Or : BuiltinFn (Ty.record [.bool, .bool]) Ty.bool
  | And : BuiltinFn (Ty.record [.bool, .bool]) Ty.bool
  | Eq (t : Ty) : BuiltinFn (Ty.record [t, t]) Ty.bool
  | Leq (t : Ty) : BuiltinFn (Ty.record [t, t]) Ty.bool  -- <= comparison
  | Sub (t : Ty) : BuiltinFn (Ty.record [t, t]) t        -- subtraction
  | StrEndsWith : BuiltinFn (Ty.record [.string, .string]) Ty.bool
  | Dom : {dom range : Ty} →  BuiltinFn (.dict dom range) (.dict dom Ty.bool)
  | Range : BuiltinFn Ty.int (Ty.dict Ty.int Ty.bool)
  | DateLit (yyyymmdd : Int) : BuiltinFn (Ty.record []) Ty.date  -- date(YYYYMMDD)
  | Concat (l1 l2 : List Ty) : BuiltinFn (Ty.record [.record l1, .record l2]) (Ty.record (l1 ++ l2))  -- concat two records

/-
Core terms (PHOAS) with typed addition/multiplication evidence and source location tracking.

`TermLoc'` pairs a term with its source location from the original SDQL code.
`Term'` is the underlying term structure.

These are mutually inductive: `TermLoc'` wraps `Term'`, and `Term'`
recursively contains `TermLoc'` in its sub-expressions.
-/
mutual
  /-- A term paired with its source location -/
  inductive TermLoc' (rep : Ty → Type) {n : Nat} (fvar : Fin n → Ty) : Ty → Type where
    | mk : {ty : Ty} → (loc : SourceLocation) → Term' rep fvar ty → TermLoc' rep fvar ty

  /-- Core term constructors -/
  inductive Term' (rep : Ty → Type) {n : Nat} (fvar : Fin n → Ty) : Ty → Type where
    | var   : {ty : Ty} → rep ty → Term' rep fvar ty
    | constInt : Int → Term' rep fvar Ty.int
    | constReal : Float → Term' rep fvar Ty.real
    | constBool : Bool → Term' rep fvar Ty.bool
    | constString : String → Term' rep fvar Ty.string
    | constRecord : {l : List Ty} → HList (TermLoc' rep fvar) l → Term' rep fvar (.record l)
    | freeVariable : (f : Fin n) → Term' rep fvar (fvar f)
    | emptyDict: {dom : Ty} → {range : Ty} → Term' rep fvar (.dict dom range)
    | dictInsert : {dom : Ty} → {range : Ty} → TermLoc' rep fvar dom → TermLoc' rep fvar range → TermLoc' rep fvar (.dict dom range) → Term' rep fvar (.dict dom range)
    | lookup : {dom range : Ty} → (aRange : AddM range) → TermLoc' rep fvar (.dict dom range) → TermLoc' rep fvar dom → Term' rep fvar range
    | not : TermLoc' rep fvar Ty.bool → Term' rep fvar Ty.bool
    | ite : {ty : Ty} → TermLoc' rep fvar Ty.bool → TermLoc' rep fvar ty → TermLoc' rep fvar ty → Term' rep fvar ty
    | letin : {ty₁ ty₂ : Ty} → TermLoc' rep fvar ty₁ → (rep ty₁ → TermLoc' rep fvar ty₂) → Term' rep fvar ty₂
    | add : {ty : Ty} → (a : AddM ty) → TermLoc' rep fvar ty → TermLoc' rep fvar ty → Term' rep fvar ty
    | mul : {sc t1 t2 : Ty} → (_s1 : ScaleM sc t1) → (_s2 : ScaleM sc t2) → TermLoc' rep fvar t1 → TermLoc' rep fvar t2 → Term' rep fvar (tensor t1 t2)
    | sum : {dom range ty : Ty} → (a : AddM ty) → TermLoc' rep fvar (.dict dom range) → (rep dom → rep range → TermLoc' rep fvar ty) → Term' rep fvar ty
    | proj : (l : List Ty) → TermLoc' rep fvar (.record l) → (i : Nat) → Term' rep fvar (l.getD i Ty.int)
    | builtin : {a b : Ty} → BuiltinFn a b → TermLoc' rep fvar a → Term' rep fvar b
end

namespace TermLoc'
  /-- Extract the source location from a located term -/
  def loc {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      (e : TermLoc' rep fvar ty) : SourceLocation :=
    match e with
    | mk l _ => l

  /-- Extract the underlying term from a located term -/
  def term {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      (e : TermLoc' rep fvar ty) : Term' rep fvar ty :=
    match e with
    | mk _ t => t

  /-- Create a located term with an unknown location -/
  def withUnknownLoc {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      (t : Term' rep fvar ty) : TermLoc' rep fvar ty :=
    mk SourceLocation.unknown t
end TermLoc'



private unsafe def getProj {l : List Ty}
    (recordVal : Ty.denote (.record l)) (i : Nat)
    : (l.getD i Ty.int).denote :=
  match i, recordVal with
  | 0, (HList.cons h _) => h
  | n+1, (HList.cons _ t_val) => getProj t_val n
  | _, HList.nil => by
    simp only [ List.getD_eq_getElem?_getD, List.length_nil, Nat.not_lt_zero,
      not_false_eq_true, getElem?_neg, Option.getD_none, Ty.denote]
    exact 0

mutual
  /-- Denote a located term by extracting and denoting the inner term -/
  unsafe def TermLoc'.denote {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      (env : (s : Fin n) → (fvar s).denote) :
      TermLoc' Ty.denote fvar ty → ty.denote
    | TermLoc'.mk _ inner => Term'.denote env inner

  /-- Denote the HList of located record fields -/
  unsafe def denoteRecordFields {n : Nat} {fvar : Fin n → Ty}
      (env : (s : Fin n) → (fvar s).denote) :
      {l : List Ty} → HList (TermLoc' Ty.denote fvar) l → HList Ty.denote l
    | [], .nil => .nil
    | _ :: _, .cons h t => .cons (TermLoc'.denote env h) (denoteRecordFields env t)

  unsafe def Term'.denote {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      (env : (s : Fin n) → (fvar s).denote) :
      Term' Ty.denote fvar ty → ty.denote
    | Term'.var v => v
    | Term'.freeVariable s => env s
    | Term'.constInt n => n
    | Term'.constReal r => r
    | Term'.constBool b => b
    | Term'.constString s => s
    | Term'.add a t1 t2 =>
      let add := AddM.denote a
      add (TermLoc'.denote env t1) (TermLoc'.denote env t2)
    | .not t => Bool.not (TermLoc'.denote env t)
    | .ite c t1 t2 => match (TermLoc'.denote env c) with
      | true => (TermLoc'.denote env t1)
      | false => (TermLoc'.denote env t2)
    | .letin t1 f => TermLoc'.denote env (f (TermLoc'.denote env t1))
    | .lookup aRange d k =>
      let dv := TermLoc'.denote env d
      let kv := TermLoc'.denote env k
      match Dict.find? dv kv with
      | some v => v
      | none => AddM.zero aRange
    | .proj l record index =>
      let dr := TermLoc'.denote env record
      getProj dr index
    | .constRecord fields => denoteRecordFields env fields
    | @Term'.emptyDict _ _ _ dom _ => Dict.empty (Ty.ord dom)
    | .dictInsert key val dict => Dict.insert (TermLoc'.denote env dict) (TermLoc'.denote env key) (TermLoc'.denote env val)
    | .sum a d f =>
      let dv := TermLoc'.denote env d
      let add := AddM.denote a
      let zero := AddM.zero a
      dv.map.foldl
        (fun acc k v =>
          add acc (TermLoc'.denote env (f k v))
        )
        zero
    | .mul s1 s2 t1e t2e =>
      ScaleM.mulDenote s1 s2 (TermLoc'.denote env t1e) (TermLoc'.denote env t2e)
    | .builtin fn arg =>
      match fn with
      | BuiltinFn.Or =>
          match TermLoc'.denote env arg with
          | HList.cons a (HList.cons b HList.nil) => Bool.or a b
      | BuiltinFn.And =>
          match TermLoc'.denote env arg with
          | HList.cons a (HList.cons b HList.nil) => Bool.and a b
      | BuiltinFn.Eq t =>
          match t, TermLoc'.denote env arg with
          | .int, HList.cons a (HList.cons b HList.nil) => a == b
          | .string, HList.cons a (HList.cons b HList.nil) => decide (a = b)
          | .real, HList.cons a (HList.cons b HList.nil) => a == b
          | _, _ => false
      | BuiltinFn.StrEndsWith =>
          match TermLoc'.denote env arg with
          | HList.cons s (HList.cons suf HList.nil) => s.endsWith suf
      | @BuiltinFn.Dom dom range =>
          let d := TermLoc'.denote env arg
          d.map.foldl (fun acc k _v => Dict.insert acc k true) (Dict.empty (Ty.ord dom))
      | BuiltinFn.Range =>
          let n := TermLoc'.denote env arg
          let rec build (i : Int) (acc : Dict Int Bool) : Dict Int Bool :=
            if i < n then
              build (i + 1) (Dict.insert acc i true)
            else acc
          (build 0 (Dict.empty inferInstance))
      | BuiltinFn.Leq t =>
          match t, TermLoc'.denote env arg with
          | .int, HList.cons a (HList.cons b HList.nil) => a <= b
          | .real, HList.cons a (HList.cons b HList.nil) => a <= b
          | .date, HList.cons a (HList.cons b HList.nil) => a.yyyymmdd <= b.yyyymmdd
          | _, _ => false
      | BuiltinFn.Sub t =>
          match h : t, TermLoc'.denote env arg with
          | .int, HList.cons a (HList.cons b HList.nil) => a - b
          | .real, HList.cons a (HList.cons b HList.nil) => a - b
          | t', _ => h ▸ Ty.inhabited t'  -- fallback for unsupported types
      | BuiltinFn.DateLit yyyymmdd =>
          SDQLDate.mk yyyymmdd
      | BuiltinFn.Concat l1 l2 =>
          match TermLoc'.denote env arg with
          | HList.cons r1 (HList.cons r2 HList.nil) =>
              hAppend r1 r2
end

mutual
  /-- Show a located term -/
  def TermLoc'.show {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
      : TermLoc' (fun _ => String) fvar ty → String
    | TermLoc'.mk _ inner => Term'.show inner

  /-- Show the HList of located record fields -/
  def showRecordFields {n : Nat} {fvar : Fin n → Ty}
      : {l : List Ty} → HList (TermLoc' (fun _ => String) fvar) l → String
    | [], .nil => ""
    | _, .cons h t =>
        let hStr := TermLoc'.show h
        let tStr := showRecordFields t
        if tStr = "" then hStr else s!"{hStr}, {tStr}"

  def Term'.show {n : Nat} {fvar : Fin n → Ty} {ty : Ty} : Term' (fun _ => String) fvar ty → String
    | .var v           => v
    | .freeVariable s  => s!"fv_{toString s}"
    | .constInt n      => toString n
    | .constReal r     => toString r
    | .constBool b     => toString b
    | .constString s   => s
    | .add _ t1 t2     => s!"{TermLoc'.show t1} + {TermLoc'.show t2}"
    | .lookup _ d k    => s!"{TermLoc'.show d}({TermLoc'.show k})"
    | .proj _ b c      => s!"{TermLoc'.show b}.{c}"
    | .mul _ _ b c     => s!"{TermLoc'.show b} * {TermLoc'.show c}"
    | .letin a b       => s!"let x = {TermLoc'.show a} in {TermLoc'.show (b "x")}"
    | .sum _ d f       => s!"sum(x in {TermLoc'.show d}) {TermLoc'.show (f "k" "v")}"
    | .ite c t f       => s!"if {TermLoc'.show c} then {TermLoc'.show t} else {TermLoc'.show f}"
    | .not e           => s!"not {TermLoc'.show e}"
    | .dictInsert a b c => s!"\{{TermLoc'.show a} -> {TermLoc'.show b}} ++ {TermLoc'.show c}"
    | .emptyDict       => "{}"
    | .constRecord r   => "<" ++ showRecordFields r ++ ">"
    | .builtin _ a     => s!"builtin({TermLoc'.show a})"
end

/-- A closed term (no free representation variables) -/
def Term {n : Nat} (fvar : Fin n → Ty) (ty : Ty) := {rep : Ty → Type} → Term' rep fvar ty

/-- A closed located term -/
def TermLoc {n : Nat} (fvar : Fin n → Ty) (ty : Ty) := {rep : Ty → Type} → TermLoc' rep fvar ty

def f0 (f : Fin 0) : Ty := nomatch f

/-
Prog has no semantic meaning, it's just used for code
generation. Now uses TermLoc' to carry source locations.
-/
structure Prog : Type 1 where
  t : Ty
  n : Nat
  fvar : Fin n → Ty
  term : {rep : Ty → Type} → TermLoc' rep fvar t
  loadPaths : Fin n → String


def Term.show {ty : Ty} {n : Nat} {f : Fin n → Ty} (t : Term f ty) : String :=
  Term'.show (t (rep := (fun _ => String)))

def TermLoc.show {ty : Ty} {n : Nat} {f : Fin n → Ty} (t : TermLoc f ty) : String :=
  TermLoc'.show (t (rep := (fun _ => String)))
-- set_option pp.explicit true

-- Quick checks
-- For closed terms (n = 0), `Fin 0` is uninhabited, so an environment is never used.
unsafe def env0 : (s : Fin 0) → (f0 s).denote := fun s => nomatch s
