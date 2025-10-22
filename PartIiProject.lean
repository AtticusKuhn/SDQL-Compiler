import PartIiProject.Term
import PartIiProject.Rust
import PartIiProject.CodegenRust

open PartIiProject

-- Quick demos: compile some existing SDQL terms to Rust-like code strings
#eval renderRust test
#eval renderRust test3
#eval renderRust sum_vals
-- import PartIiProject.SurfaceCore

-- Open-term demo: a function with a free parameter compiled to Rust
def openAdd2 : _root_.OpenTerm _root_.Ty.int :=
  fun {_} => _root_.Term'.add _root_.AddM.intA (_root_.Term'.var "p") (_root_.Term'.constInt 2)

#eval PartIiProject.renderRustFn "add2" [("p", _root_.Ty.int)] (openAdd2 (fvar := fun _ => _root_.Ty.int))
