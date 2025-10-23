import PartIiProject.Term
import PartIiProject.Rust
import PartIiProject.CodegenRust

open PartIiProject

-- Quick demos: compile some existing SDQL terms to Rust-like code strings
#eval renderRust test
#eval renderRust test3
#eval renderRust sum_vals
-- import PartIiProject.SurfaceCore

-- Open-term demo: compile a term with one runtime parameter to a Rust function.
-- SDQL term: fun (p : i64) => p + 2
def f1 : Fin 1 → Ty := fun _ => Ty.int
def openAdd2 : Term' (fun _ => String) f1 Ty.int :=
  Term'.add AddM.intA (Term'.freeVariable ⟨0, by decide⟩) (Term'.constInt 2)

def nameEnv1 : Fin 1 → String := fun _ => "p"

#eval PartIiProject.renderRustFn "add2" nameEnv1 openAdd2
