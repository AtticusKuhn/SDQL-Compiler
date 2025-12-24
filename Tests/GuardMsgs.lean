import PartIiProject.SyntaxSDQLProg

open PartIiProject

/--
error: Type error while typechecking SDQL program
Expected: int
At: true
Type mismatch: expected int, got bool
-/
#guard_msgs in
#check ([SDQLProg2 { int }| true ] : SProg2)

