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
    | .maxProduct => pure SAdd.maxProductA
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
  | .maxProduct, .maxProduct => pure SScale.maxProductS
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




/-- Find the innermost non-dict, non-record scalar type. -/
private unsafe def findLeafScalar : SurfaceTy → SurfaceTy
  | .dict _ V => findLeafScalar V
  | .record ((_, t) :: _) => findLeafScalar t
  | t => t



/-- Strip dict/record layers one at a time from `candidate` and check whether
    the stripped version is a tensor-product square root, i.e. `stensor S S = T`.

    For example, given `T = {int → {int → real}}`:
    - candidate = `{int → {int → real}}`: `stensor` of this with itself ≠ T, peel dict layer
    - candidate = `{int → real}`:          `stensor {int → real} {int → real} = T` ✓ -/
private unsafe def peelForStensorRoot (T : SurfaceTy) (candidate : SurfaceTy) : Option SurfaceTy :=
  if tyEq (stensor candidate candidate) T then
    some candidate
  else
    match candidate with
    | .dict _ V => peelForStensorRoot T V
    | .record σ =>
      match σ with
      | (_, v) :: _ => peelForStensorRoot T v
      | [] => none
    | _ => none

/-- Find `S` such that `stensor S S = T`, by peeling dict/record layers from `T`
    until the remaining type is a valid square root under `stensor`. -/
private unsafe def stensorRoot (T : SurfaceTy) : Option (Σ (S : SurfaceTy), PLift (stensor S S = T)) :=
  match peelForStensorRoot T T with
  | some S => some ⟨S, ⟨unsafeCast (rfl : S = S)⟩⟩
  | none => none

/-- Synthesize SHasMul evidence for semiring multiplication.

    For scalar types (`bool`, `real`) this is immediate. For structured types
    (dicts, records, or tensors thereof), finds the square root `t` under
    `stensor` and synthesises `SScale (leaf t) t` to construct the
    `squareMatrix` evidence. -/
unsafe def synthSHasMul (stx : SourceLocation) (ty : SurfaceTy) : Except TypeError (SHasMul ty) :=
  match ty with
  | .bool => pure SHasMul.boolS
  | .real => pure SHasMul.realS
  | x =>
    match stensorRoot x with
    | .none => .error (stx, s!"*s expects a semiring type (bool, real, or square matrix), got {tyToString ty}")
    | .some ⟨t, ⟨e⟩⟩ =>
      let sc := findLeafScalar t
      let scale : SScale sc t := match synthSScale stx sc t with
        | .ok s => s
        | .error _ => unsafeCast SScale.realS  -- fallback for mixed-scalar records
      .pure (e ▸ SHasMul.squareMatrix scale)

/-- Synthesize SHasClosure evidence for Kleene star. -/
unsafe def synthSHasClosure (stx : SourceLocation) (ty : SurfaceTy) : Except TypeError (SHasClosure ty) :=
  match ty with
  | .bool => pure SHasClosure.boolS
  | .real => pure SHasClosure.realS
  | .dict dom range =>
      match range with
      | .dict dom' inner =>
          if tyEq dom dom' then
            match inner with
            | .bool =>
                let sRange : SScale .bool .bool := SScale.boolS
                let sDict : SScale .bool (.dict dom .bool) := SScale.dictS sRange
                let h := SHasClosure.squareMatrix sDict
                pure (unsafeCast h)
            | .real =>
                let sRange : SScale .real .real := SScale.realS
                let sDict : SScale .real (.dict dom .real) := SScale.dictS sRange
                let h := SHasClosure.squareMatrix sDict
                pure (unsafeCast h)
            | .maxProduct =>
                let sRange : SScale .maxProduct .maxProduct := SScale.maxProductS
                let sDict : SScale .maxProduct (.dict dom .maxProduct) := SScale.dictS sRange
                let h := SHasClosure.squareMatrix sDict
                pure (unsafeCast h)
            | _ =>
                .error (stx, s!"closure expects bool, real, or a square matrix over bool/real/max_prod, got {tyToString ty}")
          else
            .error (stx, s!"closure expects a square matrix (matching domains), got {tyToString ty}")
      | _ =>
          .error (stx, s!"closure expects bool, real, or a square matrix, got {tyToString ty}")
  | _ => .error (stx, s!"closure expects bool, real, or a square matrix, got {tyToString ty}")

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
