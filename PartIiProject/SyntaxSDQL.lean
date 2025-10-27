import Lean
import PartIiProject.Term

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

/- Typeclass wrappers so Lean can infer AddM and ScaleM from the surrounding
   term types. We provide instances for ints/bools and dictionaries. -/
class HasAddM (ty : Ty) where
  inst : AddM ty

class HasScaleM (sc : Ty) (t : Ty) where
  inst : ScaleM sc t

namespace HasAddM

instance : HasAddM Ty.int := ⟨AddM.intA⟩
instance : HasAddM Ty.bool := ⟨AddM.boolA⟩
instance instDict {dom range : Ty} [h : HasAddM range] : HasAddM (Ty.dict dom range) :=
  ⟨AddM.dictA h.inst⟩

end HasAddM

namespace HasScaleM

instance : HasScaleM Ty.int Ty.int := ⟨ScaleM.intS⟩
instance : HasScaleM Ty.bool Ty.bool := ⟨ScaleM.boolS⟩
instance instDict {sc dom range : Ty} [h : HasScaleM sc range] : HasScaleM sc (Ty.dict dom range) :=
  ⟨ScaleM.dictS h.inst⟩

end HasScaleM

/- Helper combinators (non-recursive) -/
namespace SDQL

def add {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty} {ty : Ty}
    [h : HasAddM ty]
    (x y : Term' rep fvar ty) : Term' rep fvar ty :=
  Term'.add h.inst x y

def lookup {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {dom range : Ty} [h : HasAddM range]
    (d : Term' rep fvar (.dict dom range))
    (k : Term' rep fvar dom) : Term' rep fvar range :=
  Term'.lookup h.inst d k

def mulInt {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {t1 t2 : Ty} [i1 : HasScaleM Ty.int t1] [i2 : HasScaleM Ty.int t2]
    (x : Term' rep fvar t1) (y : Term' rep fvar t2)
    : Term' rep fvar (tensor t1 t2) :=
  Term'.mul (i1.inst) (i2.inst) x y

def mulBool {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {t1 t2 : Ty} [i1 : HasScaleM Ty.bool t1] [i2 : HasScaleM Ty.bool t2]
    (x : Term' rep fvar t1) (y : Term' rep fvar t2)
    : Term' rep fvar (tensor t1 t2) :=
  Term'.mul (i1.inst) (i2.inst) x y

def proj' {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {l : List Ty}
    (e : Term' rep fvar (.record l)) (i : Nat)
    : Term' rep fvar (l.getD i Ty.int) :=
  Term'.proj l e i

def emptyDict {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {dom range : Ty} : Term' rep fvar (.dict dom range) :=
  Term'.emptyDict

def dictSingleton {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {dom range : Ty}
    (k : Term' rep fvar dom) (v : Term' rep fvar range)
    : Term' rep fvar (.dict dom range) :=
  Term'.dictInsert k v Term'.emptyDict

def sum {rep : Ty → Type} {n : Nat} {fvar : Fin n → Ty}
    {dom range ty : Ty} [h : HasAddM ty]
    (d : Term' rep fvar (.dict dom range))
    (f : rep dom → rep range → Term' rep fvar ty) : Term' rep fvar ty :=
  Term'.sum h.inst d f

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
syntax "{" sdql "->" sdql "}"        : sdql

-- field projection and lookup (postfix-ish)
syntax:70 sdql:70 "." num : sdql
syntax:70 sdql:70 "(" sdql ")" : sdql

-- unary
syntax "not" sdql                     : sdql
syntax "if" sdql "then" sdql "else" sdql : sdql
syntax "let" ident "=" sdql "in" sdql : sdql

-- binary ops (left-assoc precedence)
syntax:60 sdql:60 "+" sdql:61          : sdql
syntax:55 sdql:55 "*" "{" "int" "}" sdql:56  : sdql -- scaled multiply
syntax:55 sdql:55 "*" "{" "bool" "}" sdql:56 : sdql

-- summation over dictionaries
syntax "sum" "(" "<" ident "," ident ">" "in" sdql ")" sdql : sdql


-- Types used in typed empty dictionary
declare_syntax_cat sdqlty
syntax (name := sdqltyInt) "int" : sdqlty
syntax (name := sdqltyBool) "bool" : sdqlty
syntax (name := sdqltyString) "string" : sdqlty

private def elabTy : TSyntax `sdqlty → MacroM (TSyntax `term)
  | `(sdqlty| int) => `(Ty.int)
  | `(sdqlty| bool) => `(Ty.bool)
  | `(sdqlty| string) => `(Ty.string)
  | stx => Macro.throwErrorAt stx "unsupported SDQL type in this DSL"

-- typed empty dictionary: {}_{ Tdom, Trange }
syntax "{" "}" "_" "{" sdqlty "," sdqlty "}" : sdql

/- Elaboration helpers to build HLists and sdql → term -/
mutual
  partial def elabSDQL : TSyntax `sdql → MacroM (TSyntax `term)
  -- atoms and parentheses
  | `(sdql| $n:num) => `(Term'.constInt $n)
  | `(sdql| $s:str) => `(Term'.constString $s)
  | `(sdql| $e:sdql . $i:num) => do
      let ee ← elabSDQL e
      `(SDQL.proj' $ee $i)
  | `(sdql| $d:sdql ( $k:sdql )) => do
      let dd ← elabSDQL d; let kk ← elabSDQL k
      `(SDQL.lookup $dd $kk)
  | `(sdql| not $e:sdql) => do
      let ee ← elabSDQL e
      `(Term'.not $ee)
  | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
      let cc ← elabSDQL c; let tt ← elabSDQL t; let ff ← elabSDQL f
      `(Term'.ite $cc $tt $ff)
  | `(sdql| let $x:ident = $e:sdql in $b:sdql) => do
      let ee ← elabSDQL e; let bb ← elabSDQL b
      `(Term'.letin $ee (fun $x => $bb))
  | `(sdql| $x:sdql + $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      `(SDQL.add $xx $yy)
  | `(sdql| $x:sdql * { int } $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      `(SDQL.mulInt $xx $yy)
  | `(sdql| $x:sdql * { bool } $y:sdql) => do
      let xx ← elabSDQL x; let yy ← elabSDQL y
      `(SDQL.mulBool $xx $yy)
  | `(sdql| sum( < $k:ident , $v:ident > in $d:sdql ) $body:sdql) => do
      let dd ← elabSDQL d; let bb ← elabSDQL body
      `(SDQL.sum $dd (fun $k $v => $bb))
  | stx =>
      if stx.raw.getKind == `PartIiProject.sdqlTrue then
        `(Term'.constBool Bool.true)
      else if stx.raw.getKind == `PartIiProject.sdqlFalse then
        `(Term'.constBool Bool.false)
      else match stx with
        | `(sdql| {}_{ $dom:sdqlty, $rng:sdqlty }) => do
            let domTy ← elabTy dom
            let rngTy ← elabTy rng
            `((Term'.emptyDict : Term' rep f0 (Ty.dict $domTy $rngTy)))
        | `(sdql| $x:ident) => `(Term'.var $x)
        | `(sdql| ( $e:sdql )) => elabSDQL e
        | `(sdql| < $a:sdql, $b:sdql >) => do
            let ta ← elabSDQL a; let tb ← elabSDQL b
            `(Term'.constRecord (HList.cons $ta (HList.cons $tb HList.nil)))
        | `(sdql| < $a:sdql, $b:sdql, $c:sdql >) => do
            let ta ← elabSDQL a; let tb ← elabSDQL b; let tc ← elabSDQL c
            `(Term'.constRecord (HList.cons $ta (HList.cons $tb (HList.cons $tc HList.nil))))
        | `(sdql| { $k:sdql -> $v:sdql }) => do
            let tk ← elabSDQL k; let tv ← elabSDQL v
            `(Term'.dictInsert $tk $tv Term'.emptyDict)
        | _ => Macro.throwError s!"unrecognized SDQL syntax: {stx}"

end
/- Quasiquoter entry point: elaborates to a `Term f ty` function
   (`rep`-polymorphic). -/
syntax "[SDQL|" sdql "]" : term

macro_rules
  | `([SDQL| $e:sdql ]) => do
      let te ← elabSDQL e
      `(fun {rep : Ty → Type} => ($te : Term' rep f0 _))


/- Simple examples to exercise the DSL. -/
-- open SDQL

-- 1) integers: 3 + 5
def ex_add : Term f0 Ty.int := [SDQL| 3 + 5 ]

-- 2) boolean example (requires boolean tokens in the parser) -- postponed
-- def ex_bool : Term f0 Ty.bool := [SDQL| not (true + false) ]

-- 3) records and projection: < 10, 20 >.1
def ex_proj : Term f0 Ty.int := [SDQL| < 10, 20 >.1 ]

/- Quick `#eval` checks -/
unsafe def env0 : (s : Fin 0) → (f0 s).denote := fun s => nomatch s


-- 4) dictionary singleton and lookup
def ex_dict_lookup : Term f0 Ty.int := [SDQL| { 3 -> 7 }(3) ]

-- 5) typed empty dictionary
def ex_empty : Term f0 (Ty.dict Ty.int Ty.int) := [SDQL| {}_{ int, int } ]

-- 6) sum over dictionary
def ex_sum : Term f0 Ty.int := [SDQL| sum( <k, v> in { 1 -> 10 } ) k ]

#eval Term'.show ex_add
#eval Term'.show ex_empty
#eval Term'.show ex_proj
#eval Term'.show ex_sum
#eval Term'.show ex_dict_lookup

end PartIiProject
