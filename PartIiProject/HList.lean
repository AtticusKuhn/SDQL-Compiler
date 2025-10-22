
inductive HList {α : Type} (β : α → Type) : List α → Type where
  | nil : HList β []
  | cons {x xs} : β x → HList β xs → HList β (x :: xs)


def hmap {T : Type} {l : List T} {ftype : T → Type} {gtype : T → Type} (f : {t : T} → ftype t → gtype t) : HList ftype l  → HList gtype l
  | HList.nil => HList.nil
  | HList.cons t ts => HList.cons (f t) (hmap f ts)


def hmap2 {T : Type} {l : List T} {ftype : T → Type} {gtype : T → Type} {htype : T → Type} (f : {t : T} → ftype t → gtype t → htype t) : HList ftype l  → HList gtype l → HList htype l
  | HList.nil, HList.nil => HList.nil
  | HList.cons fhead ftail, HList.cons ghead gtail => HList.cons (f fhead ghead) (hmap2 f ftail gtail)

def dmap {T : Type} (l : List T) {ftype : T → Type} (f : (t : T) → ftype t) : HList ftype l :=
  match l with
    | [] => HList.nil
    | t :: ts => HList.cons (f t) (dmap ts f)
