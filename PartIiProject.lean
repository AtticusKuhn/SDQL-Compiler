import PartIiProject.Term
import PartIiProject.Rust
import PartIiProject.CodegenRust

open PartIiProject
-- import PartIiProject.SurfaceCore

-- Open-term demo: compile a term with one runtime parameter to a Rust function.
-- SDQL term: fun (p : i64) => p + 2
def f1 : Fin 1 → Ty := fun _ => Ty.int
def openAdd2 : Term' (fun _ => String) f1 Ty.int :=
  Term'.add AddM.intA (Term'.freeVariable ⟨0, by decide⟩) (Term'.constInt 2)

def nameEnv1 : Fin 1 → String := fun _ => "p"

-- Demo string generation moved to Tests. Keep library modules clean.
