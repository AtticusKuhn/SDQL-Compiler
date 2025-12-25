import PartIiProject.SurfaceCore
import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.TypeUtil

open PartIiProject

/-!
Evidence synthesis (`SAdd`/`SScale`) and record-field lookup helpers.
-/

-- Synthesize SAdd evidence for a type
mutual
  unsafe def synthSAdd (stx : SourceLocation) (ty : SurfaceTy) : Except TypeError (SAdd ty) :=
    match ty with
    | .bool => pure SAdd.boolA
    | .int => pure SAdd.intA
    | .real => pure SAdd.realA
    | .date => pure SAdd.dateA
    | .string => pure SAdd.stringA
    | .dict _ range => do
        let aRange ← synthSAdd stx range
        pure (SAdd.dictA aRange)
    | .record σ => do
        let hlist ← synthSAddFields stx σ
        pure (SAdd.recordA hlist)

  unsafe def synthSAddFields (stx : SourceLocation) : (σ : Schema) → Except TypeError (HList (fun p => SAdd p.snd) σ)
    | [] => pure HList.nil
    | (_, t) :: rest => do
        let h ← synthSAdd stx t
        let tl ← synthSAddFields stx rest
        pure (HList.cons h tl)
end

/-- Synthesize SScale evidence for scaling type t by scalar sc -/
unsafe def synthSScale (stx : SourceLocation) (sc : SurfaceTy) (t : SurfaceTy) : Except TypeError (SScale sc t) :=
  match sc, t with
  | .bool, .bool => pure SScale.boolS
  | .int, .int => pure SScale.intS
  | .real, .real => pure SScale.realS
  | sc, .dict _ range => do
      let sRange ← synthSScale stx sc range
      pure (SScale.dictS sRange)
  | sc, .record σ => do
      -- Validate all fields can be scaled
      for (_, ft) in σ do
        let _ ← synthSScale stx sc ft
      -- Build the fields function
      let fieldsOk : (p : String × SurfaceTy) → Mem p σ → SScale sc p.snd :=
        fun (_, ft) _ =>
          match synthSScale stx sc ft with
          | .ok s => s
          | .error _ => unsafeCast SScale.intS  -- unreachable: already validated
      pure (SScale.recordS fieldsOk)
  | _, _ => .error (stx, s!"Cannot scale {tyToString t} by {tyToString sc}")

/-- Find a field in a schema and return its type and HasField proof -/
unsafe def findField (stx : SourceLocation) : (σ : Schema) → (name : String)
    → Except TypeError ((t : SurfaceTy) × HasField σ name t)
  | [], name => .error (stx, s!"Field '{name}' not found in record")
  | (n, t) :: rest, name =>
      if h : n = name then
        pure ⟨t, h ▸ HasField.here⟩
      else do
        let ⟨t', pf⟩ ← findField stx rest name
        pure ⟨t', HasField.there pf⟩

/-- Find the `i`th field in a schema and return its type and `HasField` proof.

    Note: supports duplicate names (the proof selects by position). -/
unsafe def findFieldByIndex (stx : SourceLocation) : (σ : Schema) → (i : Nat)
    → Except TypeError (Sigma fun nm : String => Sigma fun t : SurfaceTy => HasField σ nm t)
  | [], i => .error (stx, s!"Record index {i} out of bounds")
  | (nm, t) :: _, 0 => pure ⟨nm, ⟨t, HasField.here⟩⟩
  | _ :: rest, i + 1 => do
      let ⟨nm', ⟨t', pf⟩⟩ ← findFieldByIndex stx rest i
      pure ⟨nm', ⟨t', HasField.there pf⟩⟩

