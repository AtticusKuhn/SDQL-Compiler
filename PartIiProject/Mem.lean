inductive Mem {α : Type} (a : α) : List α → Type
  /-- The head of a list is a member: `a ∈ a :: as`. -/
  | head (as : List α) : Mem a (a::as)
  /-- A member of the tail of a list is a member of the list: `a ∈ l → a ∈ b :: l`. -/
  | tail (b : α) {as : List α} : Mem a as → Mem a (b::as)
