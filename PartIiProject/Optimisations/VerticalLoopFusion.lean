import PartIiProject.Optimisations.Apply

open PartIiProject

namespace PartIiProject.Optimisations

open PartIiProject.Optimisations.Term2

private def varMem? {ctx : List Ty} {ty : Ty} (tm : Term2 ctx ty) : Option (Mem ty ctx) :=
  match tm with
  | .var m => some m
  | .constInt _ => none
  | .constReal _ => none
  | .constBool _ => none
  | .constString _ => none
  | .constRecord _ => none
  | .emptyDict => none
  | .dictInsert _ _ _ => none
  | .lookup _ _ _ => none
  | .not _ => none
  | .ite _ _ _ => none
  | .letin _ _ => none
  | .add _ _ _ => none
  | @Term2.mul _ _ _ _ _ _ _ _ _ _ => none
  | .promote _ => none
  | .sum _ _ _ => none
  | @Term2.proj _ _ _ _ _ _ => none
  | .builtin _ _ => none

private def singletonDictInsert?
    {ctx : List Ty} {ty : Ty} (tm : Term2 ctx ty) :
    Option (Σ dom : Ty, Σ range : Ty, TermLoc2 ctx dom × TermLoc2 ctx range) :=
  match tm with
  | @Term2.dictInsert _ dom range k v _d => some ⟨dom, ⟨range, (k, v)⟩⟩
  | .var _ => none
  | .constInt _ => none
  | .constReal _ => none
  | .constBool _ => none
  | .constString _ => none
  | .constRecord _ => none
  | .emptyDict => none
  | .lookup _ _ _ => none
  | .not _ => none
  | .ite _ _ _ => none
  | .letin _ _ => none
  | .add _ _ _ => none
  | @Term2.mul _ _ _ _ _ _ _ _ _ _ => none
  | .promote _ => none
  | .sum _ _ _ => none
  | @Term2.proj _ _ _ _ _ _ => none
  | .builtin _ _ => none

/--
Vertical loop fusion, specialized to the two common "singleton dict" shapes:

1. Key-map fusion:
   `let y = sum(<x,x_v> in e1) { f1(x) -> x_v } in sum(<x,x_v> in y) { f2(x) -> x_v }`
   `↦ sum(<x,x_v> in e1) { f2(f1(x)) -> x_v }`

2. Value-map fusion:
   `let y = sum(<x,x_v> in e1) { x -> f1(x_v) } in sum(<x,x_v> in y) { x -> f2(x_v) }`
   `↦ sum(<x,x_v> in e1) { x -> f2(f1(x_v)) }`
-/
def verticalLoopFusion2 : Optimisation
  := fun {ctx} {ty} t =>
      match t with
    | t@Term2.letin (⟨_,  .sum a dict ⟨ _, .dictInsert x y z⟩  ⟩ ) let_in_body => .some t
    | _ => .none

end PartIiProject.Optimisations
