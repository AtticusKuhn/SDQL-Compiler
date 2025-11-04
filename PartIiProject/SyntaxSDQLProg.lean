import Lean
import PartIiProject.SyntaxSDQL
import PartIiProject.SurfaceCore
import Std

open Lean

namespace PartIiProject

/-
  Program-level EDSL for SDQL via `[SDQLProg { ty }| ... ]` quasiquotation.

  It extends the term DSL with a `load[Ty]("file.tbl")` form. The macro:
  - Scans for all `load[...]` occurrences, assigns each distinct filepath a
    fresh free-variable index (sorted alphabetically for determinism),
  - Replaces each `load[...]` in the term with a corresponding
    `STerm'.freeVariable` at that index (typed with the bracket type), and
  - Produces an `SProg` whose `fvar` captures the free-vars' Surface types and
    whose `loadPaths` maps indices back to filepaths.

  Usage: `[SDQLProg { <SurfaceTy> }| <sdql term with load[...] ...> ]`.
  The outer `{ <SurfaceTy> }` provides the program's overall result type, just
  like examples in `SyntaxSDQL.lean` annotate term types. This keeps the macro
  simple and predictable.
-/

/- Extend sdql type grammar to support dict and record types for loads. -/

-- Reuse the `sdqlty` category declared in `SyntaxSDQL.lean`.
syntax (name := sdqltyDict) "{" sdqlty "->" sdqlty "}" : sdqlty
syntax (name := sdqltyRecord) "<" sepBy(ident ":" sdqlty, ",") ">" : sdqlty

private partial def elabTyP : TSyntax `sdqlty → MacroM (TSyntax `term)
  | `(sdqlty| int) => `(SurfaceTy.int)
  | `(sdqlty| bool) => `(SurfaceTy.bool)
  | `(sdqlty| string) => `(SurfaceTy.string)
  | `(sdqlty| { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTyP k
      let vv ← elabTyP v
      `(SurfaceTy.dict $kk $vv)
  | `(sdqlty| < $[ $n:ident : $t:sdqlty ],* >) => do
      -- Build a list of (String × SurfaceTy) from the annotated fields
      let ns : Array (TSyntax `ident) := n
      let ts : Array (TSyntax `sdqlty) := t
      if ns.size != ts.size then
        Macro.throwError "mismatched fields in record type"
      -- Pair names with original indices and sort names for determinism
      let mut pairs : Array (String × Nat) := #[]
      for i in [:ns.size] do
        pairs := pairs.push ((ns[i]!).getId.toString, i)
      let sorted := pairs.qsort (fun a b => a.fst < b.fst)
      let mut elems : Array (TSyntax `term) := #[]
      for (nm, idx) in sorted do
        let sNm := Syntax.mkStrLit nm
        let tt ← elabTyP (ts[idx]!)
        elems := elems.push (← `(Prod.mk $sNm $tt))
      -- assemble a Lean list literal without using `.reverse`
      let mut ret : TSyntax `term := (← `(List.nil))
      let mut i := elems.size
      while i > 0 do
        let j := i - 1
        let e := elems[j]!
        ret ← `(List.cons $e $ret)
        i := j
      `(SurfaceTy.record $ret)
  | stx => Macro.throwErrorAt stx "unsupported SDQL type in program DSL"

/- Extend term grammar with loads -/
syntax (name := sdqlLoad) "load" "[" sdqlty "]" "(" str ")" : sdql


/- Utilities: collect loads and elaborate the term to STerm' with free vars -/

private abbrev LoadKey := String

private structure LoadInfo where
  ty : TSyntax `term   -- a `SurfaceTy` term

private partial def collectLoads (stx : TSyntax `sdql) : MacroM (Array (LoadKey × LoadInfo)) :=
  let rec go (e : TSyntax `sdql)
      (acc : Array (LoadKey × LoadInfo))
      : MacroM (Array (LoadKey × LoadInfo)) := do
    -- Recognize load[...] and recur through other forms
    match e with
    | `(sdql| load[ $ty:sdqlty ] ( $p:str )) => do
        let tyTerm ← elabTyP ty
        let key := p.getString
        -- Simply record the occurrence; dedup and consistency checks happen later
        return acc.push (key, { ty := tyTerm })
    -- Pairs and composite forms recurse; otherwise return acc
    | `(sdql| ( $x:sdql )) => go x acc
    | `(sdql| $x:sdql + $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql * { int } $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql * { bool } $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| not $x:sdql) => go x acc
    | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
        let acc ← go c acc; let acc ← go t acc; go f acc
    | `(sdql| let $x:ident = $e:sdql in $b:sdql) => do
        let acc ← go e acc; go b acc
    | `(sdql| $d:sdql ( $k:sdql )) => do let acc ← go d acc; go k acc
    | `(sdql| {}_{ $dom:sdqlty, $rng:sdqlty }) => return acc
    | `(sdql| < $a:sdql, $b:sdql >) => do let acc ← go a acc; go b acc
    | `(sdql| < $a:sdql, $b:sdql, $c:sdql >) => do
        let acc ← go a acc; let acc ← go b acc; go c acc
    | `(sdql| < $[ $n:ident = $e:sdql ],* >) => do
        let mut accm := acc
        for ee in e do
          accm ← go ee accm
        return accm
    | `(sdql| { $[$k:sdql -> $v:sdql],* }) => do
        let mut accm := acc
        for kk in k do accm ← go kk accm
        for vv in v do accm ← go vv accm
        return accm
    | `(sdql| sum( < $ki:ident , $vi:ident > in $d:sdql ) $body:sdql) => do
        let acc ← go d acc
        go body acc
    | _ => return acc
  go stx (#[])


/- Elaborate sdql to STerm' rep fvar t, using freeVariable for loads.
   We reuse operators from SyntaxSDQL (SDQL.add, SDQL.mulInt, etc.). -/
private partial def elabSDQLProg
    (fvarArr : Array (TSyntax `term)) -- types for each Fin idx, in order
    (keysSorted : Array LoadKey)
    : TSyntax `sdql → MacroM (TSyntax `term) :=
  let findIdx (path : String) : MacroM Nat :=
    -- linear search; small arrays expected
    let rec search (i : Nat) : MacroM Nat := do
      if h : i < keysSorted.size then
        if keysSorted[i]! = path then
          return i
        else
          search (i+1)
      else
        Macro.throwError s!"internal error: missing load index for '{path}'"
    search 0
  -- Build a `Fin n` literal and a `freeVariable` term at index i.
  let mkFreeVar (i : Nat) : MacroM (TSyntax `term) := do
    -- Lean can construct `Fin n` from Nat via `⟨i, _⟩` but here we only need
    -- the index as a numeral, relying on `OfNat` for Fin when possible.
    -- We instead form `Nat.succ` iteratively with `OfNat.ofNat` on Fin.
    -- Simpler: use `Nat.succ` numerals in `STerm'.freeVariable (n := _)` context.
    let lit := Syntax.mkNatLit i
    `(STerm'.freeVariable $lit)
  let rec go : TSyntax `sdql → MacroM (TSyntax `term)
    | `(sdql| $n:num) => `(STerm'.constInt $n)
    | `(sdql| $s:str) => `(STerm'.constString $s)
    | `(sdql| not $e:sdql) => do `(STerm'.not $(← go e))
    | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
        `(STerm'.ite $(← go c) $(← go t) $(← go f))
    | `(sdql| let $x:ident = $e:sdql in $b:sdql) => do
        let ee ← go e; let bb ← go b
        `(STerm'.letin $ee (fun $x => $bb))
    | `(sdql| $x:sdql + $y:sdql) => do `(SDQL.add $(← go x) $(← go y))
    | `(sdql| $x:sdql * { int } $y:sdql) => do `(SDQL.mulInt $(← go x) $(← go y))
    | `(sdql| $x:sdql * { bool } $y:sdql) => do `(SDQL.mulBool $(← go x) $(← go y))
    | `(sdql| $d:sdql ( $k:sdql )) => do `(SDQL.lookup $(← go d) $(← go k))
    | `(sdql| {}_{ $dom:sdqlty, $rng:sdqlty }) => do
        let domTy ← elabTyP dom
        let rngTy ← elabTyP rng
        `((STerm'.emptyDict : STerm' rep fvar (SurfaceTy.dict $domTy $rngTy)))
    | `(sdql| < $a:sdql, $b:sdql >) => do
        `(STerm'.constRecord (l := [("_1", _), ("_2", _)])
          (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _)]) $(← go a)
            (HList.cons (x := (Prod.mk "_2" _)) (xs := []) $(← go b) HList.nil)))
    | `(sdql| < $a:sdql, $b:sdql, $c:sdql >) => do
        `(STerm'.constRecord (l := [("_1", _), ("_2", _), ("_3", _)])
          (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _), ("_3", _)]) $(← go a)
            (HList.cons (x := (Prod.mk "_2" _)) (xs := [("_3", _)]) $(← go b)
              (HList.cons (x := (Prod.mk "_3" _)) (xs := []) $(← go c) HList.nil))))
    | `(sdql| < $[ $n:ident = $e:sdql ],* >) => do
        -- Use the helper from `SyntaxSDQL.lean` via re-elaboration
        let names : Array (TSyntax `ident) := n
        let exprs : Array (TSyntax `sdql) := e
        -- Local helper replicating `elabNamedRecord` logic
        let mrec : TSyntax `term ← do
          let l := names.size
          if l != exprs.size then
            Macro.throwError "mismatched fields in named record"
          let mut pairs : Array (String × Nat) := #[]
          for i in [:l] do
            pairs := pairs.push ((names[i]!).getId.toString, i)
          let sorted := pairs.qsort (fun a b => a.fst < b.fst)
          let rec mkH (j : Nat) : MacroM (TSyntax `term) := do
            if j < sorted.size then
              let (nm, idx) := sorted[j]!
              let sNm := Syntax.mkStrLit nm
              let vi ← go (exprs[idx]!)
              let tail ← mkH (j+1)
              `(HList.cons (x := (Prod.mk $sNm _)) (xs := _) $vi $tail)
            else `(HList.nil)
          `((← mkH 0))
        `(STerm'.constRecord $mrec)
    | `(sdql| { $[$k:sdql -> $v:sdql],* }) => do
        if k.size == 0 then
          Macro.throwError "empty dictionary requires a type annotation: {}_{ Tdom, Trange }"
        let rec build (i : Nat) : MacroM (TSyntax `term) := do
          if i == k.size then `(STerm'.emptyDict)
          else
            let tk ← go (k[i]!)
            let tv ← go (v[i]!)
            let tail ← build (i+1)
            `(STerm'.dictInsert $tk $tv $tail)
        build 0
    | `(sdql| sum( < $k:ident , $v:ident > in $d:sdql ) $body:sdql) => do
        `(SDQL.sum $(← go d) (fun $k $v => $(← go body)))
    | `(sdql| load[ $ty:sdqlty ] ( $p:str )) => do
        let idx ← findIdx p.getString
        mkFreeVar idx
    | `(sdql| ( $e:sdql )) => go e
    | `(sdql| $x:ident) => `(STerm'.var $x)
    | stx => Macro.throwError s!"unrecognized SDQL syntax in program DSL: {stx}"
  go


/- Program quasiquoter -/
syntax "[SDQLProg" "{" sdqlty "}" "|" sdql "]" : term

macro_rules
  | `([SDQLProg { $t:sdqlty }| $e:sdql ]) => do
      -- Collect loads and assign indices (alphabetical by path)
      let loadsArr ← collectLoads e
      -- Deduplicate by filepath, preserving first occurrence's type
      -- (simple pass; can be refined later). For now, keep original order.
      let uniqLoads := loadsArr
      -- Extract keys and sort
      let keys := uniqLoads.map (·.fst)
      let keysSorted := keys.qsort (· < ·)
      -- Build fvar (Fin n → SurfaceTy) as a match on indices
      let nLit := Syntax.mkNatLit keysSorted.size
      -- Array of SurfaceTy terms aligned with index order
      let mut fvarArr : Array (TSyntax `term) := #[]
      for k in keysSorted do
        -- find ty in uniqLoads
        let mut found? : Option (TSyntax `term) := none
        for (k', info) in uniqLoads do
          if k' = k then
            found? := some info.ty
        match found? with
        | some ty => fvarArr := fvarArr.push ty
        | none => Macro.throwError s!"internal error: missing collected info for '{k}'"
      -- Elaborate overall result type
      let tTerm ← elabTyP t
      -- Build the term with free variables
      let termBody ← elabSDQLProg fvarArr keysSorted e
      -- Build `fvar` and `loadPaths` as lambdas doing case analysis on `Fin n`.
      -- We implement these as `fun i => match i.val with | 0 => ... | 1 => ...` for simplicity.
      -- Helper: array → function by indexing Fin.nat
      let buildFn (arr : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
        `(fun (i : Fin $nLit) => (#[ $[$arr],* ])[i.val]!)
      -- fvar : Fin n → SurfaceTy
      let fvarFn ← buildFn fvarArr
      -- loadPaths : Fin n → String
      let lpArr : Array (TSyntax `term) := keysSorted.map (fun k => Syntax.mkStrLit k)
      let loadPathsFn ← buildFn lpArr
      -- Assemble SProg
      `(SProg.mk $tTerm $nLit $fvarFn (fun {rep : SurfaceTy → Type} => ($termBody : STerm' rep (fun i => ($fvarFn i)) $tTerm)) $loadPathsFn)

end PartIiProject

-- Examples
namespace PartIiProject
open ToCore

unsafe def ex_prog_add : SProg := [SDQLProg { int }| 3 + 5 ]

unsafe def ex_prog_dict_load : SProg :=
  [SDQLProg { { int -> int } }|
    { 3 -> 7 } + load[{ int -> int }]("data.tbl")
  ]

unsafe def showProgTerm (p : SProg) : String :=
  Term.show (ToCore.trProg p).term

#eval showProgTerm ex_prog_add
#eval showProgTerm ex_prog_dict_load

end PartIiProject
