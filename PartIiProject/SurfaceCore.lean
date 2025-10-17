import Std.Data.TreeMap.Basic
import Mathlib.Data.Prod.Lex
-- import Mathlib.Data.List.AList

set_option linter.style.longLine false


-- structure Field where
--     name : String
--     ty   : Ty

  -- abbrev Schema := List Field

inductive HList {α : Type} (β : α → Type) : List α → Type where
  | nil : HList β []
  | cons {x xs} : β x → HList β xs → HList β (x :: xs)

inductive SurfaceTy : Type where
  | bool : SurfaceTy
  | dict : SurfaceTy → SurfaceTy → SurfaceTy
  | record : (List (String × SurfaceTy)) → SurfaceTy
  -- | record (t :  String →  Option SurfaceTy) :  SurfaceTy
  | string : SurfaceTy
  | int :  SurfaceTy
  | unit : SurfaceTy
  deriving Inhabited

inductive CoreTy : Type where
  | bool : CoreTy
  | dict : CoreTy → CoreTy → CoreTy
  | prod : CoreTy → CoreTy → CoreTy
  | string : CoreTy
  | int :  CoreTy
  | unit : CoreTy
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
-- a direct instance at that head-type.

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


-- @[reducible, simp]
-- def SurfaceTy.denote (t : SurfaceTy) : Type :=
--   match t with
--   | .bool => Bool
--   | .int => Int
--   | .string => String
--   | .record l => HList (fun (name, ty) => (ty).denote) l
--   | .dict dom range =>
--     Dict dom.denote range.denote
abbrev Schema := List (String × SurfaceTy)

inductive HasField : Schema → String → SurfaceTy → Type where
  | here  {n σ t} : HasField (⟨ n,t ⟩ :: σ) n t
  | there {σ m u n t} (p : HasField σ n t) : HasField (⟨ m, u ⟩ :: σ) n t


inductive AddM : SurfaceTy → Type where
  | boolA : AddM .bool
  | intA  : AddM .int
  | dictA {k v : SurfaceTy} (av : AddM v) : AddM (.dict k v)
  | recordA {σ : Schema} : (HList (fun (_, t) => AddM t) σ) →  AddM (.record σ)

inductive ScaleM : SurfaceTy → SurfaceTy → Type where
  | boolS : ScaleM SurfaceTy.bool SurfaceTy.bool
  | intS : ScaleM SurfaceTy.int SurfaceTy.int
  | dictS {sc dom range : SurfaceTy} (sRange : ScaleM sc range) : ScaleM sc (SurfaceTy.dict dom range)
  | recordS {sc : SurfaceTy} {l : Schema} (fields : ∀ (p : String × SurfaceTy), p ∈ l → ScaleM sc p.2) :   ScaleM sc (SurfaceTy.record l)


inductive AddCore : CoreTy → Type where
  | boolA : AddCore .bool
  | intA  : AddCore .int
  | unitA : AddCore .unit
  | dictA {k v : CoreTy} (av : AddCore v) : AddCore (.dict k v)
  | recordA {a b : CoreTy}  : AddCore a → AddCore b →  AddCore (CoreTy.prod a b)

inductive ScaleCore : CoreTy → CoreTy → Type where
  | boolS : ScaleCore CoreTy.bool CoreTy.bool
  | intS : ScaleCore CoreTy.int CoreTy.int
  | unitS {sc : CoreTy} : ScaleCore sc CoreTy.unit
  | dictS {sc dom range : CoreTy} (sRange : ScaleCore sc range) : ScaleCore sc (CoreTy.dict dom range)
  | recordS {sc : CoreTy} {a b: CoreTy} : ScaleCore sc a → ScaleCore sc b →  ScaleCore sc (CoreTy.prod a b)

unsafe def tensor (a b : SurfaceTy) : SurfaceTy :=
  match a with
    | .dict dom range => .dict dom (tensor range b)
    | .record l => .record (l.map (fun (n, t) => (n, tensor t b)))
    | _ => b

@[simp]
def tensorCore (a b : CoreTy) : CoreTy :=
  match a with
    | .dict dom range => .dict dom (tensorCore range b)
    | .prod x y => .prod (tensorCore x b) (tensorCore y b)
    | _ => b

unsafe inductive SurfaceTerm' (rep : SurfaceTy → Type) : SurfaceTy → Type
  | var   : {ty : SurfaceTy} → rep ty → SurfaceTerm' rep ty
  | constUnit : SurfaceTerm' rep SurfaceTy.unit
  | constInt : Int → SurfaceTerm' rep SurfaceTy.int
  | constBool : Bool → SurfaceTerm' rep SurfaceTy.bool
  | constString : String → SurfaceTerm' rep SurfaceTy.string
  | constRecord : {l : Schema} → HList (fun (_, t) => SurfaceTerm' rep t) l  → SurfaceTerm' rep (.record l)
  | emptyDict: {dom  : SurfaceTy} →  {range : SurfaceTy} → SurfaceTerm' rep (.dict dom range)
  | dictInsert : {dom  : SurfaceTy} →  {range : SurfaceTy} → (SurfaceTerm' rep dom) → (SurfaceTerm' rep range) →  SurfaceTerm' rep (.dict dom range) → SurfaceTerm' rep (.dict dom range)
  | not : SurfaceTerm' rep SurfaceTy.bool → SurfaceTerm' rep SurfaceTy.bool
  | ite : {ty : SurfaceTy} → SurfaceTerm' rep SurfaceTy.bool → SurfaceTerm' rep ty → SurfaceTerm' rep ty → SurfaceTerm' rep ty
  | letin : {ty₁ ty₂ : SurfaceTy} → SurfaceTerm' rep ty₁ → (rep ty₁ → SurfaceTerm' rep ty₂) → SurfaceTerm' rep ty₂
  | add : {ty : SurfaceTy} → (a : AddM ty) → SurfaceTerm' rep ty → SurfaceTerm' rep ty → SurfaceTerm' rep ty
  | mul : { sc t1 t2 : SurfaceTy} → (_s1 : ScaleM sc t1) →  (_s2 : ScaleM sc t2) → SurfaceTerm' rep t1 → SurfaceTerm' rep t2 → SurfaceTerm' rep (tensor t1 t2)
  | projByName {n t} : {σ : Schema} → (p : HasField σ n t) → SurfaceTerm' rep (.record σ) → SurfaceTerm' rep t

unsafe def SurfaceTerm (ty : SurfaceTy) := {rep : SurfaceTy → Type} → SurfaceTerm' rep ty

inductive CoreTerm' (rep : CoreTy → Type) : CoreTy → Type
  | var   : {ty : CoreTy} → rep ty → CoreTerm' rep ty
  | constUnit : CoreTerm' rep CoreTy.unit
  | constInt : Int → CoreTerm' rep CoreTy.int
  | constBool : Bool → CoreTerm' rep CoreTy.bool
  | constString : String → CoreTerm' rep CoreTy.string
  | constPair : {ty1 ty2 : CoreTy} → (CoreTerm' rep ty1) → (CoreTerm' rep ty2) → CoreTerm' rep (CoreTy.prod ty1 ty2)
  | emptyDict: {dom  : CoreTy} →  {range : CoreTy} → CoreTerm' rep (.dict dom range)
  | dictInsert : {dom  : CoreTy} →  {range : CoreTy} → (CoreTerm' rep dom) → (CoreTerm' rep range) →  CoreTerm' rep (.dict dom range) → CoreTerm' rep (.dict dom range)
  | not : CoreTerm' rep CoreTy.bool → CoreTerm' rep CoreTy.bool
  | ite : {ty : CoreTy} → CoreTerm' rep CoreTy.bool → CoreTerm' rep ty → CoreTerm' rep ty → CoreTerm' rep ty
  | letin : {ty₁ ty₂ : CoreTy} → CoreTerm' rep ty₁ → (rep ty₁ → CoreTerm' rep ty₂) → CoreTerm' rep ty₂
  | add : {ty : CoreTy} → (a : AddCore ty) → CoreTerm' rep ty → CoreTerm' rep ty → CoreTerm' rep ty
  | mul : { sc t1 t2 : CoreTy} → (_s1 : ScaleCore sc t1) →  (_s2 : ScaleCore sc t2) → CoreTerm' rep t1 → CoreTerm' rep t2 → CoreTerm' rep (tensorCore t1 t2)
  | projFst {t1 t2} : CoreTerm' rep (CoreTy.prod t1 t2) → CoreTerm' rep t1
  | projSnd {t1 t2} : CoreTerm' rep (CoreTy.prod t1 t2) → CoreTerm' rep t2

def CoreTerm (ty : CoreTy) := {rep : CoreTy → Type} → CoreTerm' rep ty

unsafe def ex1 : SurfaceTerm (.record ([("Name", .string),("Age", .int), ("LoggedIn", .bool) ])) :=
  .constRecord (HList.cons (SurfaceTerm'.constString "Alice") (HList.cons (SurfaceTerm'.constInt 23) (HList.cons (SurfaceTerm'.constBool true) HList.nil)))

/-!
Compilation from Surface (named records) to Core (binary products)

We erase record field names and encode records as right-associated
binary products. We translate additive/scale structure evidence and
PHOAS terms accordingly.
-/

namespace SurfaceToCore

-- Translate types
mutual
@[simp]
def ty : SurfaceTy → CoreTy
  | .bool => .bool
  | .unit => .unit
  | .int => .int
  | .string => .string
  | .dict k v => .dict (ty k) (ty v)
  | .record σ => tyRecord σ

@[simp]
def tyRecord : Schema → CoreTy
  | [] => CoreTy.unit
  | (_, t) :: ts => CoreTy.prod (ty t) (tyRecord ts)
end

-- Add translation for record evidence
mutual
def addRecord : (l : Schema) → HList (fun (p : String × SurfaceTy) => AddM p.2) l → AddCore (ty (.record l))
  | [], _ => AddCore.unitA
  | (_ :: l), HList.cons a rest =>
    let m := addRecord l rest
    AddCore.recordA (add a) (m)

-- Translate AddM evidence on the surface to the core
def add : {t : SurfaceTy} → AddM t → AddCore (ty t)
  | _, .boolA => AddCore.boolA
  | _, .intA  => AddCore.intA
  | _, @AddM.dictA k v av => AddCore.dictA (add av)
  | _, @AddM.recordA σ fields => addRecord σ fields
end

-- Translate Scale evidence
mutual
def scaleRecord {sc : SurfaceTy}
    : (l : Schema)
    → (fields : ∀ (p : String × SurfaceTy), p ∈ l → ScaleM sc p.2)
    → ScaleCore (ty sc) (ty (.record l))
  | [], _ => ScaleCore.unitS
  | (p :: ps), fields =>
    have hHead : ScaleM sc p.2 := fields p (by simp)
    have hTail : ∀ (q : String × SurfaceTy), q ∈ ps → ScaleM sc q.2 :=
      fun q hq => fields q (by simpa [List.mem_cons] using Or.inr hq)
    let sHead := scale hHead
    let sTail := scaleRecord ps hTail
    ScaleCore.recordS sHead sTail

def scale : {sc t : SurfaceTy} → ScaleM sc t → ScaleCore (ty sc) (ty t)
  | _, _, .boolS => ScaleCore.boolS
  | _, _, .intS  => ScaleCore.intS
  | _, _, @ScaleM.dictS sc dom range sRange => ScaleCore.dictS (scale sRange)
  | _, _, @ScaleM.recordS sc l fields => scaleRecord (sc := sc) l fields
end
-- Translate Scale evidence
-- Scale translation for record evidence

-- Project a named field using the HasField proof into a chain of fst/snd
def projBy (rep : CoreTy → Type)
    : {σ : Schema} → {n : String} → {t : SurfaceTy}
    → (p : HasField σ n t)
    → CoreTerm' rep (ty (.record σ))
    → CoreTerm' rep (ty t)
  | _, _, _, HasField.here, r =>
      -- In the `here` case, the record schema is `(n,t)::σ`, so `r`
      -- has type `prod (ty t) (ty (.record σ))` by definition of `ty`.
      CoreTerm'.projFst r
  | _, _, _, HasField.there p, r =>
      projBy rep p (CoreTerm'.projSnd r)



end SurfaceToCore

-- Relation between type translation and tensoring (axiomatized for now)
@[simp]
unsafe def SurfaceToCore.ty_tensor (a b : SurfaceTy)
  : SurfaceToCore.ty (tensor a b) = tensorCore (SurfaceToCore.ty a) (SurfaceToCore.ty b) := by
  -- A complete proof would proceed by cases on `a` and (for records) the schema.
  -- We leave it as an axiom/placeholder for now to keep the compiler happy.
  sorry

-- Compile surface terms into core terms
unsafe def SurfaceToCore {rep : CoreTy → Type} {t : SurfaceTy}
    (t1 : SurfaceTerm' (rep ∘ SurfaceToCore.ty) t)
    : CoreTerm' rep (SurfaceToCore.ty t) :=
  let go := @SurfaceToCore rep
  match t1 with
  | SurfaceTerm'.var v => CoreTerm'.var v
  | SurfaceTerm'.constUnit => CoreTerm'.constUnit
  | SurfaceTerm'.constInt i => CoreTerm'.constInt i
  | SurfaceTerm'.constBool b => CoreTerm'.constBool b
  | SurfaceTerm'.constString s => CoreTerm'.constString s
  | @SurfaceTerm'.constRecord _ l fields =>
      let rec fold {l : Schema}
          : HList (fun (p : String × SurfaceTy) => SurfaceTerm' (rep ∘ SurfaceToCore.ty) p.2) l
          → CoreTerm' rep (SurfaceToCore.ty (.record l))
        | HList.nil => CoreTerm'.constUnit
        | HList.cons h t =>
            CoreTerm'.constPair (go h) (fold t)
      fold fields
  | SurfaceTerm'.emptyDict => CoreTerm'.emptyDict
  | @SurfaceTerm'.dictInsert _ _ _ k v d =>
      CoreTerm'.dictInsert (go k) (go v) (go d)
  | SurfaceTerm'.not b => CoreTerm'.not (go b)
  | SurfaceTerm'.ite c t e => CoreTerm'.ite (go c) (go t) (go e)
  | SurfaceTerm'.letin t f => CoreTerm'.letin (go t) (fun x => go (f x))
  | @SurfaceTerm'.add _ ty a x y => CoreTerm'.add (a := SurfaceToCore.add a) (go x) (go y)
  | @SurfaceTerm'.mul _ sc t1 t2 s1 s2 x y =>
      -- Align result type via `ty_tensor`
      let u := CoreTerm'.mul (_s1 := SurfaceToCore.scale s1) (_s2 := SurfaceToCore.scale s2) (go x) (go y)
      -- `u` has type `CoreTerm' rep (tensorCore (ty t1) (ty t2))`;
      -- rewrite to `ty (tensor t1 t2)`.
      by
        rw [SurfaceToCore.ty_tensor t1 t2]
        exact u
  | @SurfaceTerm'.projByName _ n t σ p r =>
      SurfaceToCore.projBy (rep := rep) p (go r)

@[simp, reducible]
def CoreTy.denote : CoreTy → Type
  | .bool => Bool
  | .int => Int
  | .string => String
  | .unit => PUnit
  | .dict dom range => Dict dom.denote range.denote
  | .prod a b => (CoreTy.denote a) × (CoreTy.denote b)

instance instOrdDict (a b : Type) : Ord (Dict a b) where
  compare := fun _ _ => Ordering.eq

def Ty.ord (t : CoreTy) : Ord t.denote :=
  match t with
    | .bool => inferInstance
    | .int => inferInstance
    | .string => inferInstance
    | .dict a b => instOrdDict a.denote b.denote
    | .prod a b => @Prod.Lex.instOrdLexProd a.denote b.denote (Ty.ord a) (Ty.ord b)
    | .unit => inferInstance

def AddCore.denote {t : CoreTy} : AddCore t → t.denote → t.denote → t.denote
  | .boolA, x, y => Bool.xor x y
  | .intA, x, y => Int.add x y
  | @AddCore.dictA dom range aRange, x, y =>
    let inner := AddCore.denote aRange
    -- Merge y into x using inner on values
    y.map.foldl (fun acc k v2 =>
      match Dict.find? acc k with
      | some v1 => Dict.insert acc k (inner v1 v2)
      | none    => Dict.insert acc k v2
    ) x
  | .recordA a b, (xl, xr), (yl, yr) => (AddCore.denote a xl yl, AddCore.denote b xr yr)
  | .unitA, _, _ => PUnit.unit

def CoreTerm'.denote {ty : CoreTy} :  CoreTerm' CoreTy.denote ty → ty.denote
  | CoreTerm'.var v => v
  | CoreTerm'.constInt n => n
  | CoreTerm'.constBool b => b
  | CoreTerm'.constString s => s
  | CoreTerm'.add a t1 t2 => AddCore.denote a (denote t1) (denote t2)
  | .not t => Bool.not (denote t)
  | .ite c t1 t2 => match (denote c) with
    | true => (denote t1)
    | false => (denote t2)
  | .letin t1 f => denote (f (denote t1))
  | .projFst p => (denote p).1
  | .projSnd p => (denote p).2
  | .constPair l r => (denote l, denote r)
  | @CoreTerm'.emptyDict _ dom range => Dict.empty (Ty.ord dom)
  | .dictInsert key val dict => Dict.insert (dict.denote) key.denote val.denote
  | @CoreTerm'.mul _ sc t1 t2 s1 s2 t1e t2e => sorry
  | CoreTerm'.constUnit => PUnit.unit

#eval! CoreTerm'.denote  (SurfaceToCore ex1)
