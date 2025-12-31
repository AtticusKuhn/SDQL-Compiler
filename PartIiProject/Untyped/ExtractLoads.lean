import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.LoadTerm
import PartIiProject.Untyped.UntypedTerm

open PartIiProject

/-!
Load extraction: `LoadTerm` (PHOAS) → `UntypedTermLoc` (DeBruijn).
-/

/-- Collect all distinct (path, type, SourceLocation) triples from a LoadTerm.
    Sorted alphabetically by path. If the same path appears with different types,
    later occurrences are ignored.
    Note: Uses Nat as rep for PHOAS instantiation during traversal. -/
unsafe def collectLoads (e : LoadTermLoc Unit) : List (String × SurfaceTy × SourceLocation) :=
  let collected := go e []
  let sorted := collected.toArray.qsort (fun (p1, _, _) (p2, _, _) => p1 < p2) |>.toList
  dedup sorted
where
  go : LoadTermLoc Unit → List (String × SurfaceTy × SourceLocation) → List (String × SurfaceTy × SourceLocation)
    | .mk stx inner, acc =>
      match inner with
      | .var _ => acc
      | .constInt _ => acc
      | .constReal _ => acc
      | .constBool _ => acc
      | .constString _ => acc
      | .constRecord fields =>
          fields.foldl (fun acc' (_, e) => go e acc') acc
      | .emptyDict => acc
      | .emptyDictAnn _ _ => acc
      | .dictInsert k v d => go d (go v (go k acc))
      | .not e => go e acc
      | .ite c t f => go f (go t (go c acc))
      | .iteThen c t => go t (go c acc)
      | .letin bound body =>
          let boundLoads := go bound acc
          go (body ()) boundLoads  -- dummy Nat for PHOAS traversal
      | .add e1 e2 => go e2 (go e1 acc)
      | .mul _ e1 e2 => go e2 (go e1 acc)
      | .projByName _ e => go e acc
      | .lookup d k => go k (go d acc)
      | .sum d body =>
          let dLoads := go d acc
          go (body () ()) dLoads  -- dummy Nats for PHOAS traversal
      | .load path ty =>
          if acc.any (fun (p, _, _) => p == path) then acc
          else (path, ty, stx) :: acc
      | .builtinAnd arg => go arg acc
      | .builtinOr arg => go arg acc
      | .builtinEq _ arg => go arg acc
      | .builtinLeq _ arg => go arg acc
      | .builtinLt _ arg => go arg acc
      | .builtinSub _ arg => go arg acc
      | .builtinDiv arg => go arg acc
      | .builtinStrEndsWith arg => go arg acc
      | .builtinStrStartsWith arg => go arg acc
      | .builtinStrContains arg => go arg acc
      | .builtinFirstIndex arg => go arg acc
      | .builtinLastIndex arg => go arg acc
      | .builtinSubString arg => go arg acc
      | .builtinDom _ _ arg => go arg acc
      | .builtinRange arg => go arg acc
      | .builtinSize arg => go arg acc
      | .builtinDateLit _ => acc
      | .builtinYear arg => go arg acc
      | .builtinConcat _ _ arg => go arg acc

  dedup : List (String × SurfaceTy × SourceLocation) → List (String × SurfaceTy × SourceLocation)
    | [] => []
    | [x] => [x]
    | (p1, t1, s1) :: (p2, t2, s2) :: rest =>
        if p1 == p2 then dedup ((p1, t1, s1) :: rest)
        else (p1, t1, s1) :: dedup ((p2, t2, s2) :: rest)

/-- Result of extracting loads from a LoadTerm -/
structure ExtractedLoads2 where
  ctx       : List SurfaceTy        -- Types of loads (the context)
  loadPaths : List String           -- File paths for loads
  term      : UntypedTermLoc ctx.length  -- The transformed DeBruijn term

/-- Convert a LoadTerm (PHOAS) to an UntypedTerm (DeBruijn) by:
    1. Replacing load nodes with variables referencing the context
    2. Converting PHOAS variables to DeBruijn indices

    The transformation uses Nat as rep for PHOAS, where the Nat value
    represents the "level" (depth) at which a variable was bound.
    DeBruijn index = currentDepth - 1 - level.

    Loads are placed at the beginning of the context (indices 0..n-1).
-/
unsafe def extractLoads2 (e : LoadTerm) : Except TypeError ExtractedLoads2 := do
  let eNat : LoadTermLoc Nat := e (rep := Nat)
  let loads := collectLoads e
  let ctx : List SurfaceTy := loads.map (fun (_, ty, _) => ty)
  let loadPaths : List String := loads.map (fun (path, _, _) => path)
  let pathToIndex := zipWithIndex loads
  -- Transform starting with ctx.length as the base depth (loads occupy indices 0..n-1)
  have hlen : ctx.length = loads.length := by simp [ctx]
  let term0 : UntypedTermLoc loads.length ← transform loads.length pathToIndex eNat
  let term : UntypedTermLoc ctx.length := by
    simpa [hlen] using term0
  pure { ctx := ctx, loadPaths := loadPaths, term := term }
where
  zipWithIndex (l : List (String × SurfaceTy × SourceLocation)) : List (String × Nat) :=
    let rec go (l : List (String × SurfaceTy × SourceLocation)) (i : Nat) : List (String × Nat) :=
      match l with
      | [] => []
      | (path, _, _) :: rest => (path, i) :: go rest (i + 1)
    go l 0

  findIndex (pathToIndex : List (String × Nat)) (path : String) : Option Nat :=
    pathToIndex.find? (fun (p, _) => p == path) |>.map (·.2)

  -- Convert PHOAS level to DeBruijn index
  -- In PHOAS with Nat, level is the depth when introduced
  -- DeBruijn index = currentDepth - 1 - level
  -- Note: level < currentDepth invariant holds for well-formed PHOAS terms
  mkFin (stx : SourceLocation) (n i : Nat) : Except TypeError (Fin n) :=
    if h : i < n then
      pure ⟨i, h⟩
    else
      .error (stx, s!"internal error: index {i} out of bounds for context size {n}")

  levelToIndex (stx : SourceLocation) (currentDepth : Nat) (level : Nat) : Except TypeError (Fin currentDepth) := do
    if level < currentDepth then
      mkFin stx currentDepth (currentDepth - 1 - level)
    else
      .error (stx, s!"internal error: ill-scoped PHOAS variable (level={level}, depth={currentDepth})")

  -- Transform LoadTermLoc (PHOAS) to UntypedTermLoc (DeBruijn)
  transform (depth : Nat) (pathToIndex : List (String × Nat))
      : LoadTermLoc Nat → Except TypeError (UntypedTermLoc depth)
    | .mk stx inner => do
      let inner' ← transformInner depth stx pathToIndex inner
      pure (.mk stx inner')

  -- Transform LoadTerm record fields to UntypedTermFields
  transformFields (depth : Nat) (pathToIndex : List (String × Nat))
      : List (String × LoadTermLoc Nat) → Except TypeError (UntypedTermFields depth)
    | [] => pure .nil
    | (name, e) :: rest => do
        let e' ← transform depth pathToIndex e
        let rest' ← transformFields depth pathToIndex rest
        pure (.cons name e' rest')

  transformInner (depth : Nat) (stx : SourceLocation) (pathToIndex : List (String × Nat))
      : LoadTerm' Nat → Except TypeError (UntypedTerm' depth)
    | .var level =>
        -- Convert PHOAS level to DeBruijn index
        return .var (← levelToIndex stx depth level)
    | .constInt i => pure (.constInt i)
    | .constReal r => pure (.constReal r)
    | .constBool b => pure (.constBool b)
    | .constString s => pure (.constString s)
    | .constRecord fields => do
        let fields' ← transformFields depth pathToIndex fields
        pure (.constRecord fields')
    | .emptyDict => pure .emptyDict
    | .emptyDictAnn dom range => pure (.emptyDictAnn dom range)
    | .dictInsert k v d =>
        return .dictInsert (← transform depth pathToIndex k) (← transform depth pathToIndex v) (← transform depth pathToIndex d)
    | .not e => return .not (← transform depth pathToIndex e)
    | .ite c t f =>
        return .ite (← transform depth pathToIndex c) (← transform depth pathToIndex t) (← transform depth pathToIndex f)
    | .iteThen c t =>
        return .iteThen (← transform depth pathToIndex c) (← transform depth pathToIndex t)
    | .letin bound body =>
        -- Increase depth for the body, pass current depth as the PHOAS level
        return .letin (← transform depth pathToIndex bound) (← transform (depth + 1) pathToIndex (body depth))
    | .add e1 e2 =>
        return .add (← transform depth pathToIndex e1) (← transform depth pathToIndex e2)
    | .mul sc e1 e2 =>
        return .mul sc (← transform depth pathToIndex e1) (← transform depth pathToIndex e2)
    | .projByName name e =>
        return .projByName name (← transform depth pathToIndex e)
    | .lookup d k =>
        return .lookup (← transform depth pathToIndex d) (← transform depth pathToIndex k)
    | .sum d body =>
        -- sum binds key and value, so increase depth by 2
        -- In DeBruijn context (dom :: range :: ctx):
        --   Index 0 = key (dom), Index 1 = value (range)
        -- PHOAS body is (fun key value => ...), so we pass:
        --   key gets level (depth + 1) → index 0 at depth (depth + 2)
        --   value gets level depth → index 1 at depth (depth + 2)
        return .sum (← transform depth pathToIndex d) (← transform (depth + 2) pathToIndex (body (depth + 1) depth))
    | .load path _ =>
        -- Load becomes a variable at its index in the context
        match findIndex pathToIndex path with
        | some i =>
            -- Load index i maps to a Fin in the DeBruijn context
            -- At depth d with n loads, load i is at index (d - n + i)
            -- because loads start at indices 0..n-1, then let bindings push them deeper
            let numLoads := pathToIndex.length
            let loadIndex := depth - numLoads + i
            return .var (← mkFin stx depth loadIndex)
        | none => .error (stx, s!"internal error: load path not found in load map: {path}")
    | .builtinAnd arg => return .builtinAnd (← transform depth pathToIndex arg)
    | .builtinOr arg => return .builtinOr (← transform depth pathToIndex arg)
    | .builtinEq t arg => return .builtinEq t (← transform depth pathToIndex arg)
    | .builtinLeq t arg => return .builtinLeq t (← transform depth pathToIndex arg)
    | .builtinLt t arg => return .builtinLt t (← transform depth pathToIndex arg)
    | .builtinSub t arg => return .builtinSub t (← transform depth pathToIndex arg)
    | .builtinDiv arg => return .builtinDiv (← transform depth pathToIndex arg)
    | .builtinStrEndsWith arg => return .builtinStrEndsWith (← transform depth pathToIndex arg)
    | .builtinStrStartsWith arg => return .builtinStrStartsWith (← transform depth pathToIndex arg)
    | .builtinStrContains arg => return .builtinStrContains (← transform depth pathToIndex arg)
    | .builtinFirstIndex arg => return .builtinFirstIndex (← transform depth pathToIndex arg)
    | .builtinLastIndex arg => return .builtinLastIndex (← transform depth pathToIndex arg)
    | .builtinSubString arg => return .builtinSubString (← transform depth pathToIndex arg)
    | .builtinDom dom range arg => return .builtinDom dom range (← transform depth pathToIndex arg)
    | .builtinRange arg => return .builtinRange (← transform depth pathToIndex arg)
    | .builtinSize arg => return .builtinSize (← transform depth pathToIndex arg)
    | .builtinDateLit yyyymmdd => pure (.builtinDateLit yyyymmdd)
    | .builtinYear arg => return .builtinYear (← transform depth pathToIndex arg)
    | .builtinConcat σ1 σ2 arg => return .builtinConcat σ1 σ2 (← transform depth pathToIndex arg)
