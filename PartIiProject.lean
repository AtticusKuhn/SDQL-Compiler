import PartIiProject.Term
import PartIiProject.Mem
import PartIiProject.Rust
import PartIiProject.CodegenRust
import PartIiProject.SyntaxSDQL
-- import PartIiProject.SDQLTests.TPCH.Q01

open PartIiProject
-- import PartIiProject.SurfaceCore

-- Open-term demo: compile a term with one runtime parameter to a Rust function.
-- SDQL term: fun (p : i64) => p + 2
def f1 : Fin 1 → Ty := fun _ => Ty.int
def openAdd2 : TermLoc' (fun _ => String) f1 Ty.int :=
  TermLoc'.withUnknownLoc (Term'.add AddM.intA
    (TermLoc'.withUnknownLoc (Term'.freeVariable 0))
    (TermLoc'.withUnknownLoc (Term'.constInt 2)))

def nameEnv1 : Fin 1 → String := fun _ => "p"

-- Demo string generation moved to Tests. Keep library modules clean.
