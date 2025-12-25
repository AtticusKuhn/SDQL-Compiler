import PartIiProject.SurfaceCore2
import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.Infer
import PartIiProject.Untyped.TypeOf
import PartIiProject.Untyped.TypeUtil
import PartIiProject.Untyped.UntypedTerm

open PartIiProject

/-!
Small `#eval` sanity checks for the untyped pipeline (DeBruijn).
-/

/-- Helper to show the result of DeBruijn \ inference -/
unsafe def showResult2 {ctx : List SurfaceTy} (expectedTy : SurfaceTy)
    (result : Except TypeError (STermLoc2 ctx expectedTy)) : String :=
  match result with
  | .ok _ => s!"OK: {tyToString expectedTy}"
  | .error (_, msg) => s!"Error: {msg}"

/-- Helper: create a dummy SourceLocation for testing -/
def dummyStx : SourceLocation := ⟨ 0, 0, ""⟩

/-- Helper: wrap a term with dummy SourceLocation (for closed terms) -/
def withDummy (t : UntypedTerm' 0) : UntypedTermLoc 0 :=
  .mk dummyStx t

-- Test: integer literal
unsafe def test_int : String :=
  let term := withDummy (.constInt 42)
  showResult2 .int (typeinfer2 .int term)

#eval! test_int  -- "OK: int"

-- Test: boolean literal
unsafe def test_bool : String :=
  let term := withDummy (.constBool true)
  showResult2 .bool (typeinfer2 .bool term)

#eval! test_bool  -- "OK: bool"

-- Test: addition
unsafe def test_add : String :=
  let term : UntypedTermLoc 0 := .mk dummyStx (.add
    (.mk dummyStx (.constInt 1))
    (.mk dummyStx (.constInt 2)))
  showResult2 .int (typeinfer2 .int term)

#eval! test_add  -- "OK: int"

-- Test: type error - expected int, got bool
unsafe def test_type_error : String :=
  let term := withDummy (.constBool true)
  showResult2 .int (typeinfer2 .int term)

#eval! test_type_error  -- "Error: Type mismatch: expected int, got bool"

-- Test: empty dict with type annotation
unsafe def test_empty_dict : String :=
  let term := withDummy (.emptyDictAnn .int .bool)
  showResult2 (.dict .int .bool) (typeinfer2 (.dict .int .bool) term)

#eval! test_empty_dict  -- "OK: { int -> bool }"

-- Test: record
unsafe def test_record : String :=
  let fields : UntypedTermFields 0 := .cons "name" (.mk dummyStx (.constString "Alice"))
    (.cons "age" (.mk dummyStx (.constInt 30)) .nil)
  let term : UntypedTermLoc 0 := .mk dummyStx (.constRecord fields)
  showResult2 (.record [("age", .int), ("name", .string)]) (typeinfer2 (.record [("age", .int), ("name", .string)]) term)

#eval! test_record  -- "OK: <age: int, name: string>"

-- Test: field projection
unsafe def test_proj : String :=
  let fields : UntypedTermFields 0 := .cons "name" (.mk dummyStx (.constString "Alice"))
    (.cons "age" (.mk dummyStx (.constInt 30)) .nil)
  let record : UntypedTermLoc 0 := .mk dummyStx (.constRecord fields)
  let term : UntypedTermLoc 0 := .mk dummyStx (.projByName "age" record)
  match typeof2 [] term with
  | .ok ty => showResult2 ty (typeinfer2 ty term)
  | .error (_, msg) => s!"Error: {msg}"

#eval! test_proj  -- "OK: int"

