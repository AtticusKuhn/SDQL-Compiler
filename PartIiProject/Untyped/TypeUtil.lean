import PartIiProject.SurfaceCore2
import PartIiProject.Untyped.Errors

open PartIiProject

/-!
Surface-type utilities used by the untyped pipeline.
-/

/-- Check if two SurfaceTy are equal -/
unsafe def tyEq : SurfaceTy → SurfaceTy → Bool
  | .bool, .bool => true
  | .int, .int => true
  | .real, .real => true
  | .maxProduct, .maxProduct => true
  | .date, .date => true
  | .string, .string => true
  | .dict k1 v1, .dict k2 v2 => tyEq k1 k2 && tyEq v1 v2
  | .record σ1, .record σ2 => schemaEq σ1 σ2
  | _, _ => false
where
  schemaEq : Schema → Schema → Bool
    | [], [] => true
    | (n1, t1) :: rest1, (n2, t2) :: rest2 =>
        n1 == n2 && tyEq t1 t2 && schemaEq rest1 rest2
    | _, _ => false

/-- Pretty print a SurfaceTy -/
unsafe def tyToString : SurfaceTy → String
  | .bool => "bool"
  | .int => "int"
  | .real => "real"
  | .maxProduct => "max_prod"
  | .date => "date"
  | .string => "string"
  | .dict k v => s!"\{ {tyToString k} -> {tyToString v} }"
  | .record σ => s!"<{schemaToString σ}>"
where
  schemaToString : Schema → String
    | [] => ""
    | [(n, t)] => s!"{n}: {tyToString t}"
    | (n, t) :: rest => s!"{n}: {tyToString t}, {schemaToString rest}"

/-- Check type equality and produce a term via unsafe cast if equal -/
unsafe def checkTyEq2 {ctx : List SurfaceTy}
    (stx : SourceLocation)
    (ty1 ty2 : SurfaceTy)
    (mkTerm : STermLoc2 ctx ty1)
    : Except TypeError (STermLoc2 ctx ty2) :=
  if tyEq ty1 ty2 then
    pure (unsafeCast (α := STermLoc2 ctx ty1) mkTerm)
  else
    .error (stx, s!"Type mismatch: expected {tyToString ty2}, got {tyToString ty1}")
