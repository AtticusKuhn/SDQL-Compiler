import Lean
import PartIiProject.Term
import PartIiProject.SurfaceCore

open Lean

namespace PartIiProject

/-
  Mini-DSL for SDQL terms via `[SDQL| ... ]` quasiquotation.

  This module defines:
  - Lightweight typeclasses `HasAddM`/`HasScaleM` to infer AddM/ScaleM evidence
    where possible (int, bool, and dictionaries).
  - Helper combinators (`SDQL.add`, `SDQL.mul{Int,Bool}`, `SDQL.lookup` ...)
    so macros can keep terms concise while Lean infers types.
  - A small parser for SDQL-like syntax and macros that elaborate into
    `Term f ty` (i.e., generic in representation `rep`).

  Notes and scope:
  - Records are supported for construction `< e1, e2, ... >`.
  - Field projection is supported via `e . n` (0-based index).
  - Dictionaries support `{ k1 -> v1, ..., kn -> vn }` and typed empty
    `{ }_{ Tdom, Trange }`.
  - Lookup uses `d(k)` and requires `HasAddM` for the value type (provided
    automatically for ints/bools and dictionaries).
  - Addition `e1 + e2` uses `HasAddM`; multiplication requires a scalar tag
    `e1 *{int} e2` or `e1 *{bool} e2` to select the semiring.
  - `sum(<k,v> in d) body` folds with addition; `HasAddM` is used for the
    result type.

  This DSL targets closed terms (`Term f0 ty`) out of the box. Open terms with
  free variables are not yet parsed; they can still be expressed directly via
  `Term'.freeVariable`.
-/

/- Surface-level typeclass wrappers so Lean can infer SAdd/SScale from
   surrounding types (int, bool, dictionaries, and records). -/

-- (no extra opens)

class HasSAdd (ty : SurfaceTy) where
  inst : SAdd ty

class HasSScale (sc : SurfaceTy) (t : SurfaceTy) where
  inst : SScale sc t

namespace HasSAdd

instance : HasSAdd SurfaceTy.int := ⟨SAdd.intA⟩
instance : HasSAdd SurfaceTy.bool := ⟨SAdd.boolA⟩
instance instDict {dom range : SurfaceTy} [h : HasSAdd range] : HasSAdd (SurfaceTy.dict dom range) :=
  ⟨SAdd.dictA h.inst⟩

-- Build SAdd for named records by recursion on the schema
class BuildSAddFields (σ : Schema) where
  inst : HList (fun (_, t) => SAdd t) σ

instance : BuildSAddFields ([] : Schema) := ⟨HList.nil⟩

instance (nm : String) (t : SurfaceTy) (σ : Schema)
    [ht : HasSAdd t] [rest : BuildSAddFields σ]
    : BuildSAddFields ((nm, t) :: σ) :=
  ⟨HList.cons ht.inst rest.inst⟩

instance recRecord {σ : Schema} [BuildSAddFields σ] : HasSAdd (SurfaceTy.record σ) :=
  ⟨SAdd.recordA (BuildSAddFields.inst (σ := σ))⟩

end HasSAdd

namespace HasSScale

instance : HasSScale SurfaceTy.int SurfaceTy.int := ⟨SScale.intS⟩
instance : HasSScale SurfaceTy.bool SurfaceTy.bool := ⟨SScale.boolS⟩
instance instDict {sc dom range : SurfaceTy} [h : HasSScale sc range] : HasSScale sc (SurfaceTy.dict dom range) :=
  ⟨SScale.dictS h.inst⟩

-- Build SScale for named records by recursion on the schema
class BuildSScaleFields (sc : SurfaceTy) (σ : Schema) where
  inst : (p : String × SurfaceTy) → Mem p σ → SScale sc p.snd

instance (sc : SurfaceTy) : BuildSScaleFields sc ([] : Schema) :=
  ⟨fun _ m => by cases m⟩

instance (sc : SurfaceTy) (nm : String) (t : SurfaceTy) (σ : Schema)
    [ht : HasSScale sc t] [rest : BuildSScaleFields sc σ]
    : BuildSScaleFields sc ((nm, t) :: σ) :=
  ⟨fun p m => by
    cases m with
    | head _ =>
        -- In this branch `p` defeq `(nm, t)` so the goal reduces to `SScale sc t`.
        exact ht.inst
    | tail _ m' =>
        exact rest.inst p m'⟩

instance recRecord {sc : SurfaceTy} {σ : Schema} [BuildSScaleFields sc σ]
    : HasSScale sc (SurfaceTy.record σ) :=
  ⟨SScale.recordS (HasSScale.BuildSScaleFields.inst (sc := sc) (σ := σ))⟩

end HasSScale

/- Helper combinators (non-recursive) -/
namespace SDQL

unsafe def add {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy} {ty : SurfaceTy}
    [h : HasSAdd ty]
    (x y : STerm' rep fvar ty) : STerm' rep fvar ty :=
  STerm'.add h.inst x y

unsafe def lookup {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy}
    {dom range : SurfaceTy} [h : HasSAdd range]
    (d : STerm' rep fvar (.dict dom range))
    (k : STerm' rep fvar dom) : STerm' rep fvar range :=
  STerm'.lookup h.inst d k

unsafe def mulInt {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy}
    {t1 t2 : SurfaceTy} [i1 : HasSScale SurfaceTy.int t1] [i2 : HasSScale SurfaceTy.int t2]
    (x : STerm' rep fvar t1) (y : STerm' rep fvar t2)
    : STerm' rep fvar (stensor t1 t2) :=
  STerm'.mul (i1.inst) (i2.inst) x y

unsafe def mulBool {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy}
    {t1 t2 : SurfaceTy} [i1 : HasSScale SurfaceTy.bool t1] [i2 : HasSScale SurfaceTy.bool t2]
    (x : STerm' rep fvar t1) (y : STerm' rep fvar t2)
    : STerm' rep fvar (stensor t1 t2) :=
  STerm'.mul (i1.inst) (i2.inst) x y

unsafe def emptyDict {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy}
    {dom range : SurfaceTy} : STerm' rep fvar (.dict dom range) :=
  STerm'.emptyDict

unsafe def dictSingleton {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy}
    {dom range : SurfaceTy}
    (k : STerm' rep fvar dom) (v : STerm' rep fvar range)
    : STerm' rep fvar (.dict dom range) :=
  STerm'.dictInsert k v STerm'.emptyDict

unsafe def sum {rep : SurfaceTy → Type} {n : Nat} {fvar : Fin n → SurfaceTy}
    {dom range ty : SurfaceTy} [h : HasSAdd ty]
    (d : STerm' rep fvar (.dict dom range))
    (f : rep dom → rep range → STerm' rep fvar ty) : STerm' rep fvar ty :=
  STerm'.sum h.inst d f

end SDQL


/- We keep types Lean-level inside macros to simplify; in surface syntax
   we provide small tokens like `int`/`bool` only where needed (e.g., `*{int}`). -/


/- SDQL term grammar -/
declare_syntax_cat sdql

-- atoms
syntax num                             : sdql
syntax str                             : sdql
syntax ident                          : sdql
syntax (name := sdqlTrue) "true"      : sdql
syntax (name := sdqlFalse) "false"    : sdql
syntax "(" sdql ")"                  : sdql
syntax "<" sdql "," sdql ">"        : sdql
syntax "<" sdql "," sdql "," sdql ">" : sdql
-- named record fields
syntax "<" sepBy(ident "=" sdql, ",") ">" : sdql
syntax "{" sepBy(sdql "->" sdql, ",")  "}"        : sdql

-- lookup (postfix-ish)
syntax:70 sdql:70 "(" sdql ")" : sdql
-- positional record projection via `e . n`
syntax:70 sdql:70 "." num : sdql

-- unary
syntax "not" sdql                     : sdql
syntax "if" sdql "then" sdql "else" sdql : sdql
syntax "let" ident "=" sdql "in" sdql : sdql

-- binary ops (left-assoc precedence)
syntax:60 sdql:60 "+" sdql:61          : sdql
syntax:55 sdql:55 "*" "{" "int" "}" sdql:56  : sdql -- scaled multiply
syntax:55 sdql:55 "*" "{" "bool" "}" sdql:56 : sdql
syntax:58 sdql:58 "&&" sdql:59           : sdql
syntax:57 sdql:57 "||" sdql:58           : sdql
syntax:59 sdql:59 "==" sdql:60           : sdql

-- builtins/functions
syntax "dom" "(" sdql ")"               : sdql
syntax "range" "(" sdql ")"             : sdql
syntax "endsWith" "(" sdql "," sdql ")" : sdql
syntax "unique" "(" sdql ")"            : sdql

-- summation over dictionaries
syntax "sum" "(" "<" ident "," ident ">" "in" sdql ")" sdql : sdql


-- Types used in typed empty dictionary
declare_syntax_cat sdqlty
syntax (name := sdqltyInt) "int" : sdqlty
syntax (name := sdqltyBool) "bool" : sdqlty
syntax (name := sdqltyString) "string" : sdqlty
syntax (name := sdqltyReal) "real" : sdqlty
syntax (name := sdqltyDict) "{" sdqlty "->" sdqlty "}" : sdqlty
syntax (name := sdqltyVec) "@vec" "{" sdqlty "->" sdqlty "}" : sdqlty
syntax (name := sdqltyVarchar) "varchar" "(" num ")" : sdqlty
syntax (name := sdqltyRecord) "<" sepBy(ident ":" sdqlty, ",") ">" : sdqlty

partial def elabTy : TSyntax `sdqlty → MacroM (TSyntax `term)
  | `(sdqlty| int) => `(SurfaceTy.int)
  | `(sdqlty| bool) => `(SurfaceTy.bool)
  | `(sdqlty| string) => `(SurfaceTy.string)
  | `(sdqlty| real) => `(SurfaceTy.real)
  | `(sdqlty| varchar($n:num)) => `(SurfaceTy.string)
  | `(sdqlty| @vec { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTy k
      let vv ← elabTy v
      `(SurfaceTy.dict $kk $vv)
  | `(sdqlty| { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTy k
      let vv ← elabTy v
      `(SurfaceTy.dict $kk $vv)
  | `(sdqlty| < $[ $n:ident : $t:sdqlty ],* >) => do
      -- Build a list of (String × SurfaceTy) from the annotated fields,
      -- sorting by field name for a canonical schema.
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
        let tt ← elabTy (ts[idx]!)
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
  | stx => Macro.throwErrorAt stx "unsupported SDQL type in this DSL"

-- typed empty dictionary: {}_{ Tdom, Trange }
syntax "{" "}" "_" "{" sdqlty "," sdqlty "}" : sdql

-- free variable placeholder, used by the program DSL
syntax (name := sdqlFVar) "fvar" "[" num "]" : sdql

/- Elaboration helpers to build HLists and sdql → term -/
mutual
  -- Helper to elaborate named record literals
  partial def elabNamedRecord (ns : Array (TSyntax `ident)) (es : Array (TSyntax `sdql)) : MacroM (TSyntax `term) := do
    let n := ns.size
    if n != es.size then
      Macro.throwError "mismatched fields in named record"
    -- Pair up field names with their original indices, then sort by name.
    let mut pairs : Array (String × Nat) := #[]
    for i in [:n] do
      let nm := (ns[i]!).getId.toString
      pairs := pairs.push (nm, i)
    let sorted := pairs.qsort (fun a b => a.fst < b.fst)
    let sortedList := sorted.toList
    -- Build the HList in sorted order of field names. This makes
    -- the record literal independent of the input order of fields.
    let rec mkH (j : Nat) : MacroM (TSyntax `term) := do
      if j < sorted.size then
        let entry := sortedList.get! j
        let nm := entry.fst
        let idx := entry.snd
        let sNm := Syntax.mkStrLit nm
        let vi ← elabSDQL (es[idx]!)
        let tail ← mkH (j+1)
        `(HList.cons (x := (Prod.mk $sNm _)) (xs := _) $vi $tail)
      else
        `(HList.nil)
    let hl ← mkH 0
    `(STerm'.constRecord $hl)

  partial def elabSDQL : TSyntax `sdql → MacroM (TSyntax `term)
  -- atoms and parentheses
  | `(sdql| $n:num) => `(STerm'.constInt $n)
  | `(sdql| $s:str) => `(STerm'.constString $s)
  | `(sdql| fvar[ $i:num ]) => `(STerm'.freeVariable $i)
  -- positional record projection r.0
  | `(sdql| $r:sdql . $i:num) => do
      let rr ← elabSDQL r
      `(STerm'.projIndex $rr $i)
  -- dictionary lookup d(k)
  | `(sdql| $d:sdql ( $k:sdql )) => do
      let dd ← elabSDQL d; let kk ← elabSDQL k
      `(SDQL.lookup $dd $kk)
  | `(sdql| not $e:sdql) => do
      let ee ← elabSDQL e
      `(STerm'.not $ee)
  | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
      let cc ← elabSDQL c; let tt ← elabSDQL t; let ff ← elabSDQL f
      `(STerm'.ite $cc $tt $ff)
  | `(sdql| let $x:ident = $e:sdql in $b:sdql) => do
      let ee ← elabSDQL e; let bb ← elabSDQL b
      `(STerm'.letin $ee (fun $x => $bb))
  | `(sdql| $x:sdql + $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      `(SDQL.add $xx $yy)
  | `(sdql| $x:sdql && $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      let recArg ← `(
        STerm'.constRecord (l := [("_1", _), ("_2", _)])
          (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _)]) $xx
            (HList.cons (x := (Prod.mk "_2" _)) (xs := []) $yy HList.nil))
      )
      `(STerm'.builtin PartIiProject.SBuiltin.And $recArg)
  | `(sdql| $x:sdql || $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      let recArg ← `(
        STerm'.constRecord (l := [("_1", _), ("_2", _)])
          (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _)]) $xx
            (HList.cons (x := (Prod.mk "_2" _)) (xs := []) $yy HList.nil))
      )
      `(STerm'.builtin PartIiProject.SBuiltin.Or $recArg)
  | `(sdql| $x:sdql == $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      let recArg ← `(
        STerm'.constRecord (l := [("_1", _), ("_2", _)])
          (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _)]) $xx
            (HList.cons (x := (Prod.mk "_2" _)) (xs := []) $yy HList.nil))
      )
      `(STerm'.builtin (PartIiProject.SBuiltin.Eq) $recArg)
  | `(sdql| $x:sdql * { int } $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      `(SDQL.mulInt $xx $yy)
  | `(sdql| $x:sdql * { bool } $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      `(SDQL.mulBool $xx $yy)
  | `(sdql| dom ( $e:sdql )) => do
      `(STerm'.builtin (PartIiProject.SBuiltin.Dom) $(← elabSDQL e))
  | `(sdql| range ( $e:sdql )) => do
      `(STerm'.builtin PartIiProject.SBuiltin.Range $(← elabSDQL e))
  | `(sdql| endsWith ( $x:sdql , $y:sdql )) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      let recArg ← `(
        STerm'.constRecord (l := [("_1", _), ("_2", _)])
          (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _)]) $xx
            (HList.cons (x := (Prod.mk "_2" _)) (xs := []) $yy HList.nil))
      )
      `(STerm'.builtin PartIiProject.SBuiltin.StrEndsWith $recArg)
  | `(sdql| unique ( $e:sdql )) => do
      elabSDQL e
  | `(sdql| sum( < $k:ident , $v:ident > in $d:sdql ) $body:sdql) => do
      let dd ← elabSDQL d; let bb ← elabSDQL body
      `(SDQL.sum $dd (fun $k $v => $bb))
  | stx =>
      if stx.raw.getKind == `PartIiProject.sdqlTrue then
        `(STerm'.constBool Bool.true)
      else if stx.raw.getKind == `PartIiProject.sdqlFalse then
        `(STerm'.constBool Bool.false)
      else match stx with
        -- typed empty dict
        | `(sdql| {}_{ $domTy:sdqlty, $rngTy:sdqlty }) => do
            let d ← elabTy domTy
            let r ← elabTy rngTy
            `((STerm'.emptyDict (domain := $d) (ran := $r)))
        | `(sdql| $x:ident) => `(STerm'.var $x)
        | `(sdql| ( $e:sdql )) => elabSDQL e
        | `(sdql| < $a:sdql, $b:sdql >) => do
            let ta ← elabSDQL a; let tb ← elabSDQL b
            -- positional record: assign placeholder names
            `(STerm'.constRecord (l := [("_1", _), ("_2", _)])
                (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _)]) $ta
                  (HList.cons (x := (Prod.mk "_2" _)) (xs := []) $tb HList.nil)))
        | `(sdql| < $a:sdql, $b:sdql, $c:sdql >) => do
            let ta ← elabSDQL a; let tb ← elabSDQL b; let tc ← elabSDQL c
            `(STerm'.constRecord (l := [("_1", _), ("_2", _), ("_3", _)])
                (HList.cons (x := (Prod.mk "_1" _)) (xs := [("_2", _), ("_3", _)]) $ta
                  (HList.cons (x := (Prod.mk "_2" _)) (xs := [("_3", _)]) $tb
                    (HList.cons (x := (Prod.mk "_3" _)) (xs := []) $tc HList.nil))))
        | `(sdql| < $[ $n:ident = $e:sdql ],* >) => do
            elabNamedRecord n e
        -- n-ary dictionary literal: { k1 -> v1, ..., kn -> vn }
        | `(sdql| { $[$k:sdql -> $v:sdql],* }) => do
            let ks : Array (TSyntax `sdql) := k
            let vs : Array (TSyntax `sdql) := v
            elabDictPairs ks vs
        | `(sdql| { $k:sdql -> $v:sdql }) => do
            let tk ← elabSDQL k; let tv ← elabSDQL v
            `(STerm'.dictInsert $tk $tv STerm'.emptyDict)
        | _ => Macro.throwError s!"unrecognized SDQL syntax: {stx}"

  partial def elabDictPairs (ks : Array (TSyntax `sdql)) (vs : Array (TSyntax `sdql)) : MacroM (TSyntax `term) := do
    let n := ks.size
    if n == 0 then
      Macro.throwError "empty dictionary requires a type annotation: {}_{ Tdom, Trange }"
    else if n != vs.size then
      Macro.throwError "mismatched key/value pairs in dictionary literal"
    else
      let rec mk (i : Nat) : MacroM (TSyntax `term) := do
        if i == n then
          `(STerm'.emptyDict)
        else
          let tk ← elabSDQL (ks[i]!)
          let tv ← elabSDQL (vs[i]!)
          let tail ← mk (i + 1)
          `(STerm'.dictInsert $tk $tv $tail)
      mk 0
end
/- Quasiquoter entry point: elaborates to an `STerm f ty` function
   (`rep`-polymorphic). -/
syntax "[SDQL|" sdql "]" : term

macro_rules
  | `([SDQL| $e:sdql ]) => do
      let te ← elabSDQL e
      `(fun {rep : SurfaceTy → Type} => ($te : STerm' rep f0 _))


/- Simple examples to exercise the DSL. -/
-- open SDQL

-- 1) integers: 3 + 5
unsafe def ex_add : STerm f0 SurfaceTy.int := [SDQL| 3 + 5 ]

-- 2) boolean example (requires boolean tokens in the parser) -- postponed
-- def ex_bool : Term f0 Ty.bool := [SDQL| not (true + false) ]

-- 3) named record
unsafe def ex_record : STerm f0 (SurfaceTy.record [("a", .int), ("b", .int)]) :=
  [SDQL| < a = 10 , b = 20 > ]

unsafe def ex_record_2 : STerm f0 (SurfaceTy.record [("a", .int), ("b", .int)]) :=
  [SDQL| < b = 20 , a = 10 > ]

/- Quick `#eval` checks -/
open ToCore
unsafe def env0 : (s : Fin 0) → (ToCore.ty (f0 s)).denote := fun s => nomatch s


-- 4) dictionary singleton and lookup
unsafe def ex_dict_lookup : STerm f0 SurfaceTy.int := [SDQL| { 3 -> 7 , 5 -> 1 + 1} (3) ]

-- 5) typed empty dictionary
-- unsafe def ex_empty : STerm f0 (SurfaceTy.dict .int .int) := [SDQL| {}_{ int, int } ]

-- 6) sum over dictionary
unsafe def ex_sum : STerm f0 SurfaceTy.int := [SDQL| sum( <k, v> in { 1 -> 10 } ) k ]

-- Show via surface→core translation
unsafe def showCore {t} (e : STerm f0 t) : String :=
  Term'.show (ToCore.tr e (rep := fun _ => String))

#eval showCore ex_add
-- #eval showCore ex_empty
#eval showCore ex_record
#eval showCore ex_record_2
#eval showCore ex_sum
#eval showCore ex_dict_lookup

end PartIiProject
