import Std.Data.TreeMap.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.List.AList
-- import
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
  -- | record : (List (String × SurfaceTy)) → SurfaceTy
  | record (t :  String → Option SurfaceTy) :  SurfaceTy
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


abbrev Schema := List (String × SurfaceTy)

inductive HasField : Schema → String → SurfaceTy → Type where
  | here  {n σ t} : HasField (⟨ n,t ⟩ :: σ) n t
  | there {σ m u n t} (p : HasField σ n t) : HasField (⟨ m, u ⟩ :: σ) n t


inductive AddM : SurfaceTy → Type where
  | boolA : AddM .bool
  | intA  : AddM .int
  | dictA {k v : SurfaceTy} (av : AddM v) : AddM (.dict k v)
  | recordA {σ : String → Option SurfaceTy} : (∀ (s : String), match σ s with
    | .none => Unit
    | .some f => AddM f) →  AddM (.record σ)

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

@[simp]
def tensor (a b : SurfaceTy) : SurfaceTy :=
  match a with
    | .dict dom range => .dict dom (tensor range b)
    | .record l => .record (fun (s : String) => Option.map (fun t => tensor t b) (l s))
    | _ => b
  decreasing_by
     · simp
       grind
     · simp
      --  grind
       sorry
@[simp]
def tensorCore (a b : CoreTy) : CoreTy :=
  match a with
    | .dict dom range => .dict dom (tensorCore range b)
    | .prod x y => .prod (tensorCore x b) (tensorCore y b)
    | _ => b

inductive SurfaceTerm' (rep : SurfaceTy → Type) : SurfaceTy → Type
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

def SurfaceTerm (ty : SurfaceTy) := {rep : SurfaceTy → Type} → SurfaceTerm' rep ty
