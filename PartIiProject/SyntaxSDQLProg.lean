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

/- Extend term grammar with loads and a few extra forms -/
syntax (name := sdqlLoad) "load" "[" sdqlty "]" "(" str ")" : sdql
syntax (name := sdqlSumBind) "sum" "(" "<" ident "," ident ">" "<-" sdql ")" sdql : sdql
syntax:70 sdql:70 "." ident : sdql
syntax (name := sdqlEmptyDict) "{" "}" "_" "{" sdqlty "," sdqlty "}"  : sdql
-- External builtin calls as seen in some SDQL samples, e.g.,
-- ext(`StrEndsWith`, x, y)
-- syntax (name := sdql) "StrEndsWith("  sdql "," sdql ")" : sdql


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
        let tyTerm ← elabTy ty
        let key := p.getString
        -- Simply record the occurrence; dedup and consistency checks happen later
        return acc.push (key, { ty := tyTerm })
    -- Pairs and composite forms recurse; otherwise return acc
    | `(sdql| ( $x:sdql )) => go x acc
    | `(sdql| $x:sdql + $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql * { int } $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql * { bool } $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql && $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql || $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| $x:sdql == $y:sdql) => do let acc ← go x acc; go y acc
    | `(sdql| not $x:sdql) => go x acc
    | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
        let acc ← go c acc; let acc ← go t acc; go f acc
    | `(sdql| let $x:ident = $e:sdql in $b:sdql) => do
        let acc ← go e acc; go b acc
    -- record positional projection r(0): just recurse into receiver
    | `(sdql| $r:sdql ( $i:num )) => go r acc
    | `(sdql| $d:sdql ( $k:sdql )) => do let acc ← go d acc; go k acc
    | `(sdql| dom ( $e:sdql )) => go e acc
    | `(sdql| range ( $e:sdql )) => go e acc
    | `(sdql| endsWith ( $x:sdql , $y:sdql )) => do let acc ← go x acc; go y acc
    -- | `(sdql| ext(` $nm:ident `, $x:sdql, $y:sdql)) => do let acc ← go x acc; go y acc
    | `(sdql| unique ( $e:sdql )) => go e acc
    -- typed empty dict: ignore in load-collection
    | `(sdql| {}_{ $_:sdqlty, $_:sdqlty }) => return acc
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
    | `(sdql| sum( < $ki:ident , $vi:ident > <- $d:sdql ) $body:sdql) => do
        let acc ← go d acc
        go body acc
    | _ => return acc
  go stx (#[])


/- Elaborate sdql to STerm' rep fvar t, using freeVariable for loads.
   We first rewrite the SDQL surface syntax to replace `load` with
   `fvar[...]` placeholders (and desugar a few program-only forms),
   then delegate the actual elaboration to `elabSDQL` from SyntaxSDQL. -/
private partial def elabSDQLProg
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

  -- Build an `sdql` free-variable placeholder at index i.
  let mkFVar (i : Nat) : MacroM (TSyntax `sdql) := do
    let lit := Syntax.mkNumLit (toString i)
    `(sdql| fvar[ $lit ])

  -- helper: build nested let-bindings for each field in a loaded record.
  -- Given a receiver variable `x` and a list of sorted (identifier, index) pairs,
  -- produce `let name_i = x(i) in ...` nesting at the SDQL level.
  let rec mkFieldLets (x : TSyntax `ident)
      (pairs : Array (TSyntax `ident × Nat)) (body : TSyntax `sdql) : MacroM (TSyntax `sdql) := do
    if pairs.isEmpty then
      return body
    else
      let (sNm, idx) := pairs[0]!
      let rest := pairs.extract 1 pairs.size
      let idxLit : TSyntax `num := ⟨Syntax.mkNumLit (toString idx)⟩
      let proj ← `(sdql| $x:ident . $idxLit:num)
      let nextBody ← mkFieldLets x rest body
      `(sdql| let $sNm:ident = $proj in $nextBody)

  -- Rewrite SDQL, replacing loads and program-only sugar.
  let rec go : TSyntax `sdql → MacroM (TSyntax `sdql)
    -- literals
    | stx@`(sdql| $n:num) => pure stx
    | stx@`(sdql| $s:str) => pure stx
    | stx@`(sdql| true)   => pure stx
    | stx@`(sdql| false)  => pure stx
    -- let with record-typed load: expand into a load of a free variable plus
    -- projections binding each field name.
    | `(sdql| let $x:ident = load[ < $[ $n:ident : $t:sdqlty ],* > ] ( $p:str ) in $b:sdql) => do
        let names : Array (TSyntax `ident) := n
        let tys   : Array (TSyntax `sdqlty) := t
        if names.size != tys.size then
          Macro.throwError "mismatched fields in record type"
        -- sort names
        let mut pairs : Array (String × Nat) := #[]
        for i in [:names.size] do
          pairs := pairs.push ((names[i]!).getId.toString, i)
        let sorted := pairs.qsort (fun a b => a.fst < b.fst)
        -- Compute sorted (identifier, position) where position is index in sorted list
        let sortedWithIdx : Array (TSyntax `ident × Nat) := Id.run do
          let mut acc : Array (TSyntax `ident × Nat) := #[]
          let mut j : Nat := 0
          for (_, orig) in sorted do
            acc := acc.push (names[orig]!, j)
            j := j + 1
          acc
        let idx ← findIdx p.getString
        let fv  ← mkFVar idx
        let b'  ← go b
        let withFields ← mkFieldLets x sortedWithIdx b'
        `(sdql| let $x = $fv in $withFields)
    -- generic let
    | `(sdql| let $x:ident = $e:sdql in $b:sdql) => do
        let e' ← go e; let b' ← go b
        `(sdql| let $x = $e' in $b')
    -- binary ops
    | `(sdql| $x:sdql + $y:sdql) => do
        let x' ← go x; let y' ← go y
        `(sdql| $x' + $y')
    | `(sdql| $x:sdql && $y:sdql) => do
        let x' ← go x; let y' ← go y
        `(sdql| $x' && $y')
    | `(sdql| $x:sdql || $y:sdql) => do
        let x' ← go x; let y' ← go y
        `(sdql| $x' || $y')
    | `(sdql| $x:sdql == $y:sdql) => do
        let x' ← go x; let y' ← go y
        `(sdql| $x' == $y')
    | `(sdql| $x:sdql * { int } $y:sdql) => do
        let x' ← go x; let y' ← go y
        `(sdql| $x' * { int } $y')
    | `(sdql| $x:sdql * { bool } $y:sdql) => do
        let x' ← go x; let y' ← go y
        `(sdql| $x' * { bool } $y')
    -- unary
    | `(sdql| not $e:sdql) => do
        let e' ← go e
        `(sdql| not $e')
    | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
        let c' ← go c; let t' ← go t; let f' ← go f
        `(sdql| if $c' then $t' else $f')
    -- lookup / projection
    | `(sdql| $d:sdql ( $k:sdql )) => do
        let d' ← go d; let k' ← go k
        `(sdql| $d' ( $k' ))
    -- builtins
    | `(sdql| dom ( $e:sdql )) => do
        let e' ← go e
        `(sdql| dom ($e'))
    | `(sdql| range ( $e:sdql )) => do
        let e' ← go e
        `(sdql| range ($e'))
    | `(sdql| endsWith ( $x:sdql , $y:sdql )) => do
        let x' ← go x; let y' ← go y
        `(sdql| endsWith ($x', $y'))
    | `(sdql| unique ( $e:sdql )) => do
        let e' ← go e
        `(sdql| unique ($e'))
    -- typed empty dict: no subterms to rewrite
    | stx@`(sdql| {}_{ $domTy:sdqlty, $rngTy:sdqlty}) => pure stx
    -- records and dictionaries
    | `(sdql| < $a:sdql, $b:sdql >) => do
        let a' ← go a; let b' ← go b
        `(sdql| < $a', $b' >)
    | `(sdql| < $a:sdql, $b:sdql, $c:sdql >) => do
        let a' ← go a; let b' ← go b; let c' ← go c
        `(sdql| < $a', $b', $c' >)
    | `(sdql| < $[ $n:ident = $e:sdql ],* >) => do
        let es : Array (TSyntax `sdql) := e
        let mut es' : Array (TSyntax `sdql) := #[]
        for ee in es do
          es' := es'.push (← go ee)
        -- reuse the original field names but with rewritten expressions
        let names : Array (TSyntax `ident) := n
        `(sdql| < $[ $names:ident = $es':sdql ],* >)
    | `(sdql| { $[$k:sdql -> $v:sdql],* }) => do
        let ks : Array (TSyntax `sdql) := k
        let vs : Array (TSyntax `sdql) := v
        let mut ks' : Array (TSyntax `sdql) := #[]
        let mut vs' : Array (TSyntax `sdql) := #[]
        for kk in ks do
          ks' := ks'.push (← go kk)
        for vv in vs do
          vs' := vs'.push (← go vv)
        `(sdql| { $[ $ks':sdql -> $vs':sdql ],* })
    -- sum with "in"
    | `(sdql| sum( < $k:ident , $v:ident > in $d:sdql ) $body:sdql) => do
        let d' ← go d; let body' ← go body
        `(sdql| sum( < $k , $v > in $d' ) $body')
    -- sum with "<-" sugar
    | `(sdql| sum( < $k:ident , $v:ident > <- $d:sdql ) $body:sdql) => do
        let d' ← go d; let body' ← go body
        `(sdql| sum( < $k , $v > in $d' ) $body')
    -- load as expression
    | `(sdql| load[ $ty:sdqlty ] ( $p:str )) => do
        let idx ← findIdx p.getString
        mkFVar idx
    -- dot access becomes simple variable access due to earlier let-expansion
    | `(sdql| $recv:ident . $fname:ident) => do
        -- dot access desugars to the field variable; load-expansion has
        -- already introduced lets binding these field names.
        `(sdql| $fname:ident)
    -- parentheses
    | `(sdql| ( $e:sdql )) => do
        let e' ← go e
        `(sdql| ($e'))
    -- variables and fallback
    | stx@`(sdql| $x:ident) => pure stx
    | stx => pure stx

  fun stx => do
    let rewritten ← go stx
    elabSDQL rewritten


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
      let tTerm ← elabTy t
      -- Build the term with free variables by rewriting loads to `fvar` and
      -- delegating to the core SDQL elaborator.
      let termBody ← elabSDQLProg keysSorted e
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
