import PartIiProject.Term
import PartIiProject.HList
import PartIiProject.Mem

namespace PartIiProject

/-!
Basic *surface* types and evidence.

This module intentionally contains only the shared surface-level language model
(types, builtins, and semimodule evidence). The older PHOAS surface terms/programs
(`STerm'`, `STermLoc'`, `SProg`) have been removed in favor of the DeBruijn-indexed
pipeline in `SurfaceCore2.lean` / `Term2.lean`.
-/

inductive SurfaceTy : Type where
  | bool : SurfaceTy
  | int : SurfaceTy
  | real : SurfaceTy
  | maxProduct : SurfaceTy
  | date : SurfaceTy
  | string : SurfaceTy
  | dict : SurfaceTy → SurfaceTy → SurfaceTy
  | record : List (String × SurfaceTy) → SurfaceTy
  deriving Inhabited, Repr


instance : ToString SurfaceTy := {
  toString := fun s => toString (repr s)
}
abbrev Schema := List (String × SurfaceTy)

/- Field-membership proof with an index extractor (used for dot projection). -/
inductive HasField : Schema → String → SurfaceTy → Type where
  | here  {nm σ t} : HasField (⟨nm, t⟩ :: σ) nm t
  | there {σ nm' t' nm t} (p : HasField σ nm t) : HasField (⟨nm', t'⟩ :: σ) nm t

def HasField.index : {σ : Schema} → {n : String} → {t : SurfaceTy} → HasField σ n t → Nat
  | _, _, _, HasField.here => 0
  | _, _, _, HasField.there p => HasField.index p + 1

/- Surface-level semimodule evidence (mirrors core `AddM`/`ScaleM`). -/
inductive SAdd : SurfaceTy → Type where
  | boolA   : SAdd .bool
  | intA    : SAdd .int
  | realA   : SAdd .real
  | maxProductA : SAdd .maxProduct
  | dateA   : SAdd .date
  | stringA : SAdd .string
  | dictA   {k v : SurfaceTy} (av : SAdd v) : SAdd (.dict k v)
  | recordA {σ : Schema} : HList (fun p => SAdd p.snd) σ → SAdd (.record σ)

inductive SScale : SurfaceTy → SurfaceTy → Type where
  | boolS : SScale .bool .bool
  | intS : SScale .int .int
  | realS : SScale .real .real
  | maxProductS : SScale .maxProduct .maxProduct
  | dictS {sc dom range : SurfaceTy} (sRange : SScale sc range) : SScale sc (.dict dom range)
  | recordS {sc : SurfaceTy} {σ : Schema}
      (fields : (p : String × SurfaceTy) → Mem p σ → SScale sc p.snd) :
      SScale sc (.record σ)

/- Surface tensor shape: type of `e1 * e2` when `e1 : a` and `e2 : b`.
   Marked `unsafe` because Lean's termination checker doesn't see structural decrease. -/
@[simp, reducible]
unsafe def stensor (a b : SurfaceTy) : SurfaceTy :=
  match a with
  | .dict dom range => .dict dom (stensor range b)
  | .record σ => .record (σ.map (fun (n, t) => (n, stensor t b)))
  | _ => b

inductive SBuiltin : SurfaceTy → SurfaceTy → Type where
  | And : SBuiltin (.record [("_1", .bool), ("_2", .bool)]) .bool
  | Or  : SBuiltin (.record [("_1", .bool), ("_2", .bool)]) .bool
  | Eq {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) .bool
  | Leq {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) .bool
  | Lt {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) .bool
  | Sub {t : SurfaceTy} : SBuiltin (.record [("_1", t), ("_2", t)]) t
  | Div : SBuiltin (.record [("_1", .real), ("_2", .real)]) .real
  | StrEndsWith : SBuiltin (.record [("_1", .string), ("_2", .string)]) .bool
  | StrStartsWith : SBuiltin (.record [("_1", .string), ("_2", .string)]) .bool
  | StrContains : SBuiltin (.record [("_1", .string), ("_2", .string)]) .bool
  | FirstIndex : SBuiltin (.record [("_1", .string), ("_2", .string)]) .int
  | LastIndex : SBuiltin (.record [("_1", .string), ("_2", .string)]) .int
  | SubString : SBuiltin (.record [("_1", .string), ("_2", .int), ("_3", .int)]) .string
  | Dom {dom range : SurfaceTy} : SBuiltin (.dict dom range) (.dict dom .bool)
  | Range : SBuiltin .int (.dict .int .bool)
  | Size {dom range : SurfaceTy} : SBuiltin (.dict dom range) .int
  | DateLit (yyyymmdd : Int) : SBuiltin (.record []) .date
  | Year : SBuiltin .date .int
  | Concat (σ1 σ2 : Schema) :
      SBuiltin (.record [("_1", .record σ1), ("_2", .record σ2)]) (.record (σ1 ++ σ2))

end PartIiProject
