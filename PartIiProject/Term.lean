import Std.Data.TreeMap.Basic
import PartIiProject.Dict
import PartIiProject.HList
import PartIiProject.Mem

-- set_option linter.style.longLine false
set_option linter.unusedVariables false

inductive Ty : Type where
  | bool : Ty
  | real : Ty
  | dict : Ty → Ty → Ty
  | record : (List (Ty)) → Ty
  | string : Ty
  | int :  Ty
  deriving Inhabited




@[reducible, simp]
unsafe def Ty.denote (t : Ty) : Type :=
  match t with
  | .bool => Bool
  | .real => Float
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
  | .int, n => toString n
  | .string, s => s
  | .record l, r => "<" ++ showHList r ++ ">"
  | .dict dom range, d => showDict (dom := dom) (range := range) d
end
inductive AddM : Ty → Type where
  | boolA : AddM Ty.bool
  | realA : AddM Ty.real
  | intA : AddM Ty.int
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
    | HList.cons head tail => ⟨ compareLex (compareOn (ord := head) (fun (HList.cons h _) => h)) (compareOn (ord := HListOrd tail) (fun (HList.cons _ t) => t))⟩


unsafe def Ty.ord (t : Ty) : Ord t.denote :=
  match t with
    | .bool => inferInstance
    | .real => inferInstance
    | .int => inferInstance
    | .string => inferInstance
    | .dict a b => instOrdDict a.denote b.denote
    | .record l => HListOrd (dmap l Ty.ord)

-- Additive identities for AddM types
mutual
unsafe def zeroHList {l : List Ty} : HList AddM l → HList Ty.denote l
  | .nil => HList.nil
  | .cons h t => HList.cons (AddM.zero h) (zeroHList t)

unsafe def AddM.zero {t : Ty} : AddM t → t.denote
  | .boolA => false
  | .realA => (0.0 : Float)
  | .intA => 0
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
  | StrEndsWith : BuiltinFn (Ty.record [.string, .string]) Ty.bool
  | Dom : {dom range : Ty} →  BuiltinFn (.dict dom range) (.dict dom Ty.bool)
  | Range : BuiltinFn Ty.int (Ty.dict Ty.int Ty.bool)

-- Core terms (PHOAS) with typed addition/multiplication evidence
inductive Term' (rep : Ty → Type) {n : Nat} (fvar : Fin n → Ty) : Ty → Type
  | var   : {ty : Ty} → rep ty → Term' rep fvar ty
  | constInt : Int → Term' rep fvar Ty.int
  | constBool : Bool → Term' rep fvar Ty.bool
  | constString : String → Term' rep fvar Ty.string
  | constRecord : {l : List Ty} → HList (Term' rep fvar) l  → Term' rep fvar (.record l)
  | freeVariable : (f : Fin n) → Term' rep fvar (fvar f)
  | emptyDict: {dom  : Ty} →  {range : Ty} → Term' rep fvar (.dict dom range)
  | dictInsert : {dom  : Ty} →  {range : Ty} → (Term' rep fvar dom) → (Term' rep fvar range) →  Term' rep fvar (.dict dom range) → Term' rep  fvar (.dict dom range)
  | lookup : {dom range : Ty} → (aRange : AddM range) → Term' rep fvar (.dict dom range) → Term' rep fvar dom → Term' rep fvar range
  | not : Term' rep fvar Ty.bool → Term' rep fvar Ty.bool
  | ite : {ty : Ty} → Term' rep fvar Ty.bool → Term' rep fvar ty → Term' rep fvar ty → Term' rep fvar ty
  | letin : {ty₁ ty₂ : Ty} → Term' rep fvar ty₁ → (rep ty₁ → Term' rep fvar ty₂) → Term' rep fvar ty₂
  | add : {ty : Ty} → (a : AddM ty) → Term' rep fvar ty → Term' rep fvar ty → Term' rep fvar ty
  | mul : { sc t1 t2 : Ty} → (_s1 : ScaleM sc t1) →  (_s2 : ScaleM sc t2) → Term' rep fvar t1 → Term' rep fvar t2 → Term' rep fvar (tensor t1 t2)
  | sum : {dom range ty : Ty} → (a : AddM ty) → Term' rep fvar (.dict dom range) → (rep dom → rep range → Term' rep fvar ty) → Term' rep fvar ty
  | proj : (l : List Ty) → Term' rep fvar (.record l) → (i : Nat) → Term' rep fvar (l.getD i Ty.int)
  | builtin : {a b : Ty} → BuiltinFn a b → Term' rep fvar a → Term' rep fvar b



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

unsafe def Term'.denote  {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
    (env : (s : Fin n) → (fvar s).denote) :
    Term' Ty.denote fvar ty → ty.denote
  | Term'.var v => v
  | Term'.freeVariable s => env s
  | Term'.constInt n => n
  | Term'.constBool b => b
  | Term'.constString s => s
  | Term'.add a t1 t2 =>
    let add := AddM.denote a
    add (denote env t1) (denote env t2)
  | .not t => Bool.not (denote env t)
  | .ite c t1 t2 => match (denote env c) with
    | true => (denote env t1)
    | false => (denote env t2)
  | .letin t1 f => denote env (f (denote env t1))
  | .lookup aRange d k =>
    let dv := denote env d
    let kv := denote env k
    match Dict.find? dv kv with
    | some v => v
    | none => AddM.zero aRange
  | .proj l record index =>
    let dr := denote env record
    getProj dr index
  | .constRecord fields => hmap (denote env) fields
  | @Term'.emptyDict _ _ _ dom _ => Dict.empty (Ty.ord dom)
  | .dictInsert key val dict => Dict.insert (denote env dict) (denote env key) (denote env val)
  | .sum a d f =>
    let dv := denote env d
    let add := AddM.denote a
    let zero := AddM.zero a
    dv.map.foldl
      (fun acc k v =>
        add acc (denote env (f k v))
      )
      zero
  | .mul s1 s2 t1e t2e =>
    ScaleM.mulDenote s1 s2 (denote env t1e) (denote env t2e)
  | .builtin fn arg =>
    match fn with
    | BuiltinFn.Or =>
        match denote env arg with
        | HList.cons a (HList.cons b HList.nil) => Bool.or a b
    | BuiltinFn.And =>
        match denote env arg with
        | HList.cons a (HList.cons b HList.nil) => Bool.and a b
    | BuiltinFn.Eq t =>
        match t, denote env arg with
        | .int, HList.cons a (HList.cons b HList.nil) => a == b
        | .string, HList.cons a (HList.cons b HList.nil) => decide (a = b)
        | .real, HList.cons a (HList.cons b HList.nil) => a == b
        | _, _ => false
    | BuiltinFn.StrEndsWith =>
        match denote env arg with
        | HList.cons s (HList.cons suf HList.nil) => s.endsWith suf
    | @BuiltinFn.Dom dom range =>
        let d := denote env arg
        d.map.foldl (fun acc k _v => Dict.insert acc k true) (Dict.empty (Ty.ord dom))
    | BuiltinFn.Range =>
        let n := denote env arg
        let rec build (i : Int) (acc : Dict Int Bool) : Dict Int Bool :=
          if i < n then
            build (i + 1) (Dict.insert acc i true)
          else acc
        (build 0 (Dict.empty inferInstance))

def Term'.show {n : Nat} {fvar : Fin n → Ty} {ty : Ty} : Term' (fun _ => String) fvar ty → String
  | .var v           => v
  | .freeVariable s  => s!"fv_{toString s}"
  | .constInt n      => toString n
  | .constBool b     => toString b
  | .constString s   => s
  | .add _ t1 t2     => s!"{t1.show} + {t2.show}"  -- note: ignore the Add evidence
  | .lookup _ d k    => s!"{d.show}({k.show})"
  | (proj _ b c) => s!"{b.show}.{c}"
  | (mul _ _ b c)=> s!"{b.show} * {c.show}"
  | (letin  a b)=> s!"let x = {a.show} in {(b "x").show}"
  | (sum _ d f) => s!"sum(x in {d.show}) {(f "k" "v").show}"
  |(ite c t f)=> s!"if {c.show} then {t.show} else {f.show}"
  | (not e)=> s!"not {e.show}"
  |(dictInsert a b c)=> s!"\{{a.show} -> {b.show}} ++ {c.show}"
  | (emptyDict)=> "{}"
  | (constRecord r)=>
    let rec show_r {n : Nat} {fvar : Fin n → Ty} {l : List Ty} (r : HList (Term' (fun _ ↦ String) fvar) l) : String :=
      match r with
        | .nil => ""
        | .cons h t =>
          let hStr := (Term'.show h)
          let tStr := show_r t
          if tStr = "" then hStr else s!"{hStr}, {tStr}"
    "<" ++ show_r r ++ ">"
  | (builtin _ a) => s!"builtin({a.show})"


def Term {n : Nat} (fvar : Fin n → Ty) (ty : Ty) := {rep : Ty → Type}  → Term' rep fvar ty
def f0 (f : Fin 0) : Ty := nomatch f

/-
Prog has no semantic meaning, it's just used for code
generation.
-/
structure Prog  : Type 1 where
  t : Ty
  n : Nat
  fvar : Fin n → Ty
  term : Term fvar t
  loadPaths : Fin n → String


def Term.show {ty : Ty} {n : Nat} {f : Fin n → Ty} (t : Term f ty) : String :=
  Term'.show (t (rep := (fun _ => String)))
-- set_option pp.explicit true

-- Quick checks
-- For closed terms (n = 0), `Fin 0` is uninhabited, so an environment is never used.
unsafe def env0 : (s : Fin 0) → (f0 s).denote := fun s => nomatch s
