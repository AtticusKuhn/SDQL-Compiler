import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.Evidence
import PartIiProject.Untyped.ExtractLoads
import PartIiProject.Untyped.Infer
import PartIiProject.Untyped.LoadTerm
import PartIiProject.Untyped.Pipeline
import PartIiProject.Untyped.Tests
import PartIiProject.Untyped.TypeOf
import PartIiProject.Untyped.TypeUtil
import PartIiProject.Untyped.UntypedTerm

/-!
Legacy umbrella module.

`PartIiProject/untyped.lean` used to hold the entire untyped pipeline. It is now
factored into `PartIiProject/Untyped/*` and kept as a stable import target.
-/

