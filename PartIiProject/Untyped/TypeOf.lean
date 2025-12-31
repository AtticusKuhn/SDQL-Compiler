import PartIiProject.SurfaceCore2
import PartIiProject.Untyped.Errors
import PartIiProject.Untyped.TypeUtil
import PartIiProject.Untyped.UntypedTerm

open PartIiProject

/-!
Type computation (`typeof2`) for DeBruijn untyped terms.
-/

/-- Get the type at a given index in a context -/
unsafe def getTypeAt (ctx : List SurfaceTy) (i : Fin ctx.length) : SurfaceTy :=
  ctx[i.val]'(by exact i.isLt)

/-- Convert a Fin index to a Mem proof -/
unsafe def finToMem : (ctx : List SurfaceTy) → (i : Fin ctx.length) → Mem (getTypeAt ctx i) ctx
  | [], i => nomatch i
  | t :: ts, ⟨0, _⟩ => Mem.head ts
  | _ :: ts, ⟨n + 1, h⟩ =>
      let i' : Fin ts.length := ⟨n, Nat.lt_of_succ_lt_succ h⟩
      Mem.tail _ (finToMem ts i')

/-- Compute the type of an untyped term in a given context.
    Returns an error with SourceLocation location if the term cannot be typed. -/
unsafe def typeof2 (ctx : List SurfaceTy) (e : UntypedTermLoc ctx.length) : Except TypeError SurfaceTy := do
  match e with
  | .mk stx inner =>
    match inner with
    | .var i => pure (getTypeAt ctx i)
    | .constInt _ => pure .int
    | .constReal _ => pure .real
    | .constBool _ => pure .bool
    | .constString _ => pure .string
    | .constRecord fields => do
        let sortedFields := UntypedTermFields.sortByName fields
        let schema ← typeofFields2 ctx (sortedFields.toList)
        pure (.record schema)
    | .emptyDict =>
        .error (stx, "cannot infer type of unannotated empty dict; use {}_{Tdom, Trange}")
    | .emptyDictAnn domTy rangeTy => pure (.dict domTy rangeTy)
    | .dictInsert k v _ => do
        let domTy ← typeof2 ctx k
        let rangeTy ← typeof2 ctx v
        pure (.dict domTy rangeTy)
    | .not _ => pure .bool
    | .ite _ t _ => typeof2 ctx t
    | .iteThen _ t => typeof2 ctx t
    | .letin bound body => do
        let boundTy ← typeof2 ctx bound
        typeof2 (boundTy :: ctx) body
    | .add e1 _ => typeof2 ctx e1
    | .mul _ e1 e2 => do
        let t1 ← typeof2 ctx e1
        let t2 ← typeof2 ctx e2
        pure (stensor t1 t2)
    | .projByName name inner => do
        let ty ← typeof2 ctx inner
        match ty with
        | .record σ =>
            match σ.find? (fun (n, _) => n == name) with
            | some (_, fieldTy) => pure fieldTy
            | none => .error (stx, s!"Field '{name}' not found in record {σ}")
        | _ => .error (stx, s!"Cannot project from non-record type {tyToString ty}")
    | .lookup d k => do
        let dTy ← typeof2 ctx d
        match dTy with
        | .dict _ rangeTy => pure rangeTy
        | .record σ =>
            -- SDQL sugar: `r(n)` for constant integer `n` means positional projection.
            match k.term with
            | .constInt i =>
                if i < 0 then
                  .error (k.stx, s!"Record projection index must be nonnegative, got {i}")
                else
                  let idx := Int.toNat i
                  match σ.get? idx with
                  | some (_, fieldTy) => pure fieldTy
                  | none => .error (k.stx, s!"Record index {idx} out of bounds for record {tyToString (.record σ)}")
            | _ =>
                .error (k.stx, "Record projection expects a constant integer index")
        | _ =>
            .error (stx, s!"Cannot lookup in non-dictionary type {tyToString dTy}")
    | .sum d body => do
        let dictTy ← typeof2 ctx d
        match dictTy with
        | .dict domTy rangeTy => typeof2 (domTy :: rangeTy :: ctx) body
        | _ => .error (stx, s!"sum expects dictionary, got {tyToString dictTy}")
    | .builtinAnd _ => pure .bool
    | .builtinOr _ => pure .bool
    | .builtinEq _ _ => pure .bool
    | .builtinLeq _ _ => pure .bool
    | .builtinLt _ _ => pure .bool
    | .builtinSub _ arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .record [("_1", t1), ("_2", t2)] =>
            if tyEq t1 t2 then
              pure t1
            else
              .error (stx, s!"- expects both operands to have the same type, got {tyToString t1} and {tyToString t2}")
        | other =>
            .error (stx, s!"- expects a pair record argument, got {tyToString other}")
    | .builtinDiv arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .record [("_1", .real), ("_2", .real)] => pure .real
        | other =>
            .error (stx, s!"/ expects a pair of reals, got {tyToString other}")
    | .builtinStrEndsWith _ => pure .bool
    | .builtinStrStartsWith _ => pure .bool
    | .builtinStrContains _ => pure .bool
    | .builtinFirstIndex _ => pure .int
    | .builtinLastIndex _ => pure .int
    | .builtinSubString _ => pure .string
    | .builtinDom _ _ arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .dict domTy _ => pure (.dict domTy .bool)
        | other => .error (stx, s!"dom expects a dictionary argument, got {tyToString other}")
    | .builtinRange _ => pure (.dict .int .bool)
    | .builtinSize arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .dict _ _ => pure .int
        | other => .error (stx, s!"size expects a dictionary argument, got {tyToString other}")
    | .builtinDateLit _ => pure .date
    | .builtinYear arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .date => pure .int
        | other => .error (stx, s!"year expects a date argument, got {tyToString other}")
    | .builtinConcat _ _ arg => do
        let argTy ← typeof2 ctx arg
        match argTy with
        | .record [("_1", .record σ1), ("_2", .record σ2)] =>
            pure (.record (σ1 ++ σ2))
        | other =>
            .error (stx, s!"concat expects a pair of records, got {tyToString other}")
where
  typeofFields2 (ctx : List SurfaceTy) : List (String × UntypedTermLoc ctx.length) → Except TypeError Schema
    | [] => pure []
    | (name, e) :: rest => do
        let ty ← typeof2 ctx e
        let restSchema ← typeofFields2 ctx rest
        pure ((name, ty) :: restSchema)
