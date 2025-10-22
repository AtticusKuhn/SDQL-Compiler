import Std.Data.TreeMap.Basic
import Mathlib.Data.Prod.Lex

structure Dict (α β : Type) where
  cmp : Ord α
  map : Std.TreeMap (cmp := cmp.compare) α β

instance toStringDict (a b : Type) [ToString a] [ToString b] : ToString (Dict a b) where
  toString := fun s =>
    "{" ++ s.map.foldl (fun acc k v => acc ++ s!"{k} -> {v}, ") "" ++ "}"

-- Provide a Repr instance for Dict so #eval can display it using its
-- existing ToString rendering.
instance reprDict (a b : Type) [ToString a] [ToString b] : Repr (Dict a b) where
  reprPrec d _ := repr (toString d)

-- Pretty-printing helpers live below, after `Ty.denote` and `tensor`.

namespace Dict
def empty {α β} (cmp : Ord α) : Dict α β :=
  { cmp := cmp
  , map := Std.TreeMap.empty (α := α) (β := β) (cmp := fun a b => cmp.compare a b)
  }

def insert {α β} (d : Dict α β) (k : α) (v : β) : Dict α β :=
  { d with map := d.map.insert (cmp := fun a b => d.cmp.compare a b) k v }

def find? {α β} (d : Dict α β) (k : α) : Option β :=
  d.map.get? (cmp := fun a b => d.cmp.compare a b) k

-- Map values of a Dict while preserving its ordering
def mapValues {α β γ} (d : Dict α β) (f : β → γ) : Dict α γ :=
  d.map.foldl (fun acc k v => Dict.insert acc k (f v)) (Dict.empty d.cmp)
end Dict
