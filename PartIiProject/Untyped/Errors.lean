import PartIiProject.Term

/-!
Shared error type for the untyped pipeline.
-/

/-- A type inference error with source location -/
abbrev TypeError := SourceLocation × String

/-- Create a type error with SourceLocation location -/
def typeError (stx : SourceLocation) (msg : String) : TypeError := (stx, msg)

/-- Human-readable location snippet for error messages. -/
def sourceLocWhere (stx : SourceLocation) : String :=
  if stx.substring.isEmpty then
    "unknown location"
  else
    stx.substring
