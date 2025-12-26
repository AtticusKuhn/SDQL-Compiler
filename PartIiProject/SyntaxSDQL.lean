import Lean
import PartIiProject.SurfaceCore
import PartIiProject.untyped

open Lean

namespace PartIiProject

/-!
SDQL syntax + parser macros.

The parser elaborates SDQL source into a `LoadTerm` (`PartIiProject.untyped`).
The rest of the pipeline is:

`LoadTerm` → load-extraction → `UntypedTermLoc` → type inference → `STermLoc2`.

This file intentionally does *not* elaborate directly to typed surface/core terms.
-/

/- SDQL term grammar -/
declare_syntax_cat sdql

/- SDQL identifiers

Lean reserves `_` as a hole, but SDQL allows `_` as an identifier.
We parse SDQL identifiers into a separate syntax category and map `_` to a
valid Lean binder identifier when building the HOAS `LoadTermLoc` AST.
-/
declare_syntax_cat sdqlident
syntax ident : sdqlident
syntax "_"   : sdqlident

-- atoms
syntax num                              : sdql
syntax scientific                       : sdql
syntax str                              : sdql
syntax sdqlident                        : sdql
syntax (name := sdqlTrue) "true"        : sdql
syntax (name := sdqlFalse) "false"      : sdql
syntax "(" sdql ")"                     : sdql
syntax "<" sdql "," sdql ">"            : sdql
syntax "<" sdql "," sdql "," sdql ">"   : sdql
syntax "<" sepBy(sdqlident "=" sdql, ",") ">" : sdql
syntax "{" sepBy(sdql "->" sdql, ",")  "}" : sdql

syntax "date(" num ")" : sdql
syntax "year(" sdql ")" : sdql

-- lookup and projection
syntax:70 sdql:70 "(" sdql ")" : sdql
syntax:70 sdql:70 "." sdqlident : sdql

-- unary / control
syntax "not" sdql : sdql
syntax "if" sdql "then" sdql "else" sdql : sdql
syntax "if" sdql "then" sdql : sdql
syntax "let" sdqlident "=" sdql "in" sdql : sdql

-- binary ops (left-assoc precedence)
syntax:60 sdql:60 "+" sdql:61 : sdql
syntax:60 sdql:60 "-" sdql:61 : sdql
syntax:55 sdql:55 "*" sdql:56 : sdql
syntax:55 sdql:55 "*" "{" "int" "}" sdql:56 : sdql
syntax:55 sdql:55 "*" "{" "bool" "}" sdql:56 : sdql
syntax:55 sdql:55 "*" "{" "real" "}" sdql:56 : sdql
syntax:58 sdql:58 "&&" sdql:59 : sdql
syntax:57 sdql:57 "||" sdql:58 : sdql
syntax:59 sdql:59 "==" sdql:60 : sdql
syntax:59 sdql:59 "<=" sdql:60 : sdql
syntax:59 sdql:59 "<" sdql:60 : sdql

-- builtins/functions
syntax "dom" "(" sdql ")" : sdql
syntax "range" "(" sdql ")" : sdql
syntax "endsWith" "(" sdql "," sdql ")" : sdql
syntax "unique" "(" sdql ")" : sdql
syntax "concat" "(" sdql "," sdql ")" : sdql

-- summation over dictionaries
syntax "sum" "(" "<" sdqlident "," sdqlident ">" "in" sdql ")" sdql : sdql
syntax "sum" "(" "<" sdqlident "," sdqlident ">" "<-" sdql ")" sdql : sdql

-- types
declare_syntax_cat sdqlty
syntax (name := sdqltyInt) "int" : sdqlty
syntax (name := sdqltyBool) "bool" : sdqlty
syntax (name := sdqltyString) "string" : sdqlty
syntax (name := sdqltyReal) "real" : sdqlty
syntax (name := sdqltyDate) "date" : sdqlty
syntax (name := sdqltyDict) "{" sdqlty "->" sdqlty "}" : sdqlty
syntax (name := sdqltyVec) "@vec" "{" sdqlty "->" sdqlty "}" : sdqlty
syntax (name := sdqltyVarchar) "varchar" "(" num ")" : sdqlty
syntax (name := sdqltyRecord) "<" sepBy(sdqlident ":" sdqlty, ",") ">" : sdqlty

-- typed empty dictionary: {}_{ Tdom, Trange }
syntax "{" "}" "_" "{" sdqlty "," sdqlty "}" : sdql

-- load expressions
syntax (name := sdqlLoad) "load" "[" sdqlty "]" "(" str ")" : sdql

/-- SDQL identifier `_` is a hole in Lean; map it to a safe binder identifier. -/
private def sdqlBlankBinderName : Name :=
  Name.mkSimple "_sdql_blank"

private def sdqlIdentToLeanIdent (x : TSyntax `sdqlident) : MacroM (TSyntax `ident) := do
  match x with
  | `(sdqlident| $i:ident) => pure i
  | `(sdqlident| _) => pure <| mkIdentFrom x sdqlBlankBinderName
  | _ => Macro.throwErrorAt x "unexpected SDQL identifier"

private def sdqlIdentToString (x : TSyntax `sdqlident) : MacroM String := do
  match x with
  | `(sdqlident| $i:ident) => pure i.getId.toString
  | `(sdqlident| _) => pure "_"
  | _ => Macro.throwErrorAt x "unexpected SDQL identifier"

/-- Helper to elaborate a record type with a given field ordering. -/
partial def elabRecordTy (stx : TSyntax `sdqlty) (ns : Array (TSyntax `sdqlident)) (ts : Array (TSyntax `sdqlty))
    (sortFields : Bool) (elabField : TSyntax `sdqlty → MacroM (TSyntax `term)) : MacroM (TSyntax `term) := do
  if ns.size != ts.size then
    Macro.throwErrorAt stx "mismatched fields in record type"
  let mut pairs : Array (String × Nat) := #[]
  for i in [:ns.size] do
    pairs := pairs.push ((← sdqlIdentToString (ns[i]!)), i)
  let orderedPairs := if sortFields then pairs.qsort (fun a b => a.fst < b.fst) else pairs
  let mut elems : Array (TSyntax `term) := #[]
  for (nm, idx) in orderedPairs do
    let sNm := Syntax.mkStrLit nm
    let tt ← elabField (ts[idx]!)
    elems := elems.push (← `(Prod.mk $sNm $tt))
  let mut ret : TSyntax `term := (← `(List.nil))
  let mut i := elems.size
  while i > 0 do
    let j := i - 1
    let e := elems[j]!
    ret ← `(List.cons $e $ret)
    i := j
  `(SurfaceTy.record $ret)

/-- Elaborate an SDQL type to a `SurfaceTy` term (with alphabetically sorted record fields). -/
partial def elabTy : TSyntax `sdqlty → MacroM (TSyntax `term)
  | `(sdqlty| int) => `(SurfaceTy.int)
  | `(sdqlty| bool) => `(SurfaceTy.bool)
  | `(sdqlty| string) => `(SurfaceTy.string)
  | `(sdqlty| real) => `(SurfaceTy.real)
  | `(sdqlty| date) => `(SurfaceTy.date)
  | `(sdqlty| varchar($n:num)) => `(SurfaceTy.string)
  | `(sdqlty| @vec { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTy k
      let vv ← elabTy v
      `(SurfaceTy.dict $kk $vv)
  | `(sdqlty| { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTy k
      let vv ← elabTy v
      `(SurfaceTy.dict $kk $vv)
  | stx@`(sdqlty| < $[ $n:sdqlident : $t:sdqlty ],* >) =>
      elabRecordTy stx n t Bool.true elabTy
  | stx => Macro.throwErrorAt stx "unsupported SDQL type"

/-- Elaborate an SDQL type preserving declaration order for record fields.
    Used for table load schemas where field order must match TBL column order. -/
partial def elabTyPreserveOrder : TSyntax `sdqlty → MacroM (TSyntax `term)
  | `(sdqlty| int) => `(SurfaceTy.int)
  | `(sdqlty| bool) => `(SurfaceTy.bool)
  | `(sdqlty| string) => `(SurfaceTy.string)
  | `(sdqlty| real) => `(SurfaceTy.real)
  | `(sdqlty| date) => `(SurfaceTy.date)
  | `(sdqlty| varchar($n:num)) => `(SurfaceTy.string)
  | `(sdqlty| @vec { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTyPreserveOrder k
      let vv ← elabTyPreserveOrder v
      `(SurfaceTy.dict $kk $vv)
  | `(sdqlty| { $k:sdqlty -> $v:sdqlty }) => do
      let kk ← elabTyPreserveOrder k
      let vv ← elabTyPreserveOrder v
      `(SurfaceTy.dict $kk $vv)
  | stx@`(sdqlty| < $[ $n:sdqlident : $t:sdqlty ],* >) =>
      elabRecordTy stx n t Bool.false elabTyPreserveOrder
  | stx => Macro.throwErrorAt stx "unsupported SDQL type"

/-- Extract source location from syntax, returning a term that constructs a `SourceLocation`. -/
def mkSourceLoc (stx : Syntax) : MacroM (TSyntax `term) := do
  let fallbackStr : String :=
    match stx.reprint with
    | some s => s
    | none => ""
  match stx.getRange?, stx.getSubstring? with
  | some r, some s =>
      let startLit := Syntax.mkNumLit (toString r.start.byteIdx)
      let endLit := Syntax.mkNumLit (toString r.stop.byteIdx)
      let strLit : StrLit := Syntax.mkStrLit (s.toString)
      `(SourceLocation.mk $startLit $endLit $strLit)
  | some r, none =>
      let startLit := Syntax.mkNumLit (toString r.start.byteIdx)
      let endLit := Syntax.mkNumLit (toString r.stop.byteIdx)
      let strLit : StrLit := Syntax.mkStrLit fallbackStr
      `(SourceLocation.mk $startLit $endLit $strLit)
  | none, some s =>
      let strLit : StrLit := Syntax.mkStrLit (s.toString)
      `(SourceLocation.mk 0 0 $strLit)
  | none, none =>
      if fallbackStr.isEmpty then
        `(SourceLocation.unknown)
      else
        let strLit : StrLit := Syntax.mkStrLit fallbackStr
        `(SourceLocation.mk 0 0 $strLit)

/-- Wrap a `LoadTerm'` node with a `SourceLocation` computed from the parsed syntax. -/
def wrapLoadWithStx (stx : TSyntax `sdql) (inner : TSyntax `term) : MacroM (TSyntax `term) := do
  let location ← mkSourceLoc stx
  `(LoadTermLoc.mk (stx := $location) $inner)

mutual
  /-- Elaborate a named record literal to `LoadTermLoc`. -/
  partial def elabNamedRecordToLoad (stx : TSyntax `sdql) (ns : Array (TSyntax `sdqlident))
      (es : Array (TSyntax `sdql)) : MacroM (TSyntax `term) := do
    withRef stx do
      let n := ns.size
      if n != es.size then
        Macro.throwErrorAt stx "mismatched fields in named record"
      let mut pairs : Array (TSyntax `term) := #[]
      for i in [:n] do
        let nm := Syntax.mkStrLit (← sdqlIdentToString (ns[i]!))
        let ei ← elabSDQLToLoad (es[i]!)
        pairs := pairs.push (← `(Prod.mk $nm $ei))
      let mut pairList : TSyntax `term := (← `(List.nil))
      let mut j := pairs.size
      while j > 0 do
        let k := j - 1
        let p := pairs[k]!
        pairList ← `(List.cons $p $pairList)
        j := k
      let inner ← `(LoadTerm'.constRecord $pairList)
      wrapLoadWithStx stx inner

  /-- Elaborate SDQL syntax to `LoadTermLoc` (parser output for the pipeline). -/
  partial def elabSDQLToLoad (stx : TSyntax `sdql) : MacroM (TSyntax `term) :=
    withRef stx do
      match stx with
      | `(sdql| $n:num) => wrapLoadWithStx stx (← `(LoadTerm'.constInt $n))
      | `(sdql| $r:scientific) => wrapLoadWithStx stx (← `(LoadTerm'.constReal $r))
      | `(sdql| $s:str) => wrapLoadWithStx stx (← `(LoadTerm'.constString $s))
      | `(sdql| true) => wrapLoadWithStx stx (← `(LoadTerm'.constBool Bool.true))
      | `(sdql| false) => wrapLoadWithStx stx (← `(LoadTerm'.constBool Bool.false))

      -- variable / dotted variable path (e.g. `r.field.subfield`)
      | `(sdql| $x:sdqlident) => do
          let xIdent ← sdqlIdentToLeanIdent x
          let name := xIdent.getId
          let components := name.componentsRev.reverse
          if components.length > 1 then
            let baseIdent := mkIdentFrom xIdent (Name.mkSimple components[0]!.toString)
            let mut result ← wrapLoadWithStx stx (← `(LoadTerm'.var $baseIdent))
            for i in [1:components.length] do
              let fieldName := Syntax.mkStrLit components[i]!.toString
              result ← wrapLoadWithStx stx (← `(LoadTerm'.projByName $fieldName $result))
            return result
          else
            wrapLoadWithStx stx (← `(LoadTerm'.var $xIdent))

      | `(sdql| ( $e:sdql )) => elabSDQLToLoad e

      -- record literals
      | `(sdql| < $a:sdql , $b:sdql >) => do
          let ta ← elabSDQLToLoad a
          let tb ← elabSDQLToLoad b
          wrapLoadWithStx stx (← `(LoadTerm'.constRecord [("_1", $ta), ("_2", $tb)]))
      | `(sdql| < $a:sdql , $b:sdql , $c:sdql >) => do
          let ta ← elabSDQLToLoad a
          let tb ← elabSDQLToLoad b
          let tc ← elabSDQLToLoad c
          wrapLoadWithStx stx (← `(LoadTerm'.constRecord [("_1", $ta), ("_2", $tb), ("_3", $tc)]))
      | stx@`(sdql| < $[ $n:sdqlident = $e:sdql ],* >) =>
          elabNamedRecordToLoad stx n e

      -- dictionary literals (syntactic sugar over inserts)
      | `(sdql| { $[$ks:sdql -> $vs:sdql],* }) => do
          -- build from the end using unannotated emptyDict
          let loc ← mkSourceLoc stx
          let mut tail : TSyntax `term := (← `(LoadTermLoc.mk (stx := $loc) LoadTerm'.emptyDict))
          for i in [0:ks.size] do
            let tk ← elabSDQLToLoad (ks[ks.size - 1 - i]!)
            let tv ← elabSDQLToLoad (vs[vs.size - 1 - i]!)
            tail ← wrapLoadWithStx stx (← `(LoadTerm'.dictInsert $tk $tv $tail))
          return tail

      -- typed empty dict
      | `(sdql| {}_{ $d:sdqlty , $r:sdqlty }) => do
          let dd ← elabTy d
          let rr ← elabTy r
          wrapLoadWithStx stx (← `(LoadTerm'.emptyDictAnn $dd $rr))

      -- projection / lookup
      | `(sdql| $r:sdql . $fname:sdqlident) => do
          let rr ← elabSDQLToLoad r
          let fieldName := Syntax.mkStrLit (← sdqlIdentToString fname)
          wrapLoadWithStx stx (← `(LoadTerm'.projByName $fieldName $rr))
      | `(sdql| $d:sdql ( $k:sdql )) => do
          let dd ← elabSDQLToLoad d
          let kk ← elabSDQLToLoad k
          wrapLoadWithStx stx (← `(LoadTerm'.lookup $dd $kk))

      -- control
      | `(sdql| not $e:sdql) =>
          wrapLoadWithStx stx (← `(LoadTerm'.not $(← elabSDQLToLoad e)))
      | `(sdql| if $c:sdql then $t:sdql else $f:sdql) => do
          let cc ← elabSDQLToLoad c
          let tt ← elabSDQLToLoad t
          let ff ← elabSDQLToLoad f
          wrapLoadWithStx stx (← `(LoadTerm'.ite $cc $tt $ff))
      | `(sdql| if $c:sdql then $t:sdql) => do
          let cc ← elabSDQLToLoad c
          let tt ← elabSDQLToLoad t
          wrapLoadWithStx stx (← `(LoadTerm'.iteThen $cc $tt))
      | `(sdql| let $x:sdqlident = $e:sdql in $b:sdql) => do
          let ee ← elabSDQLToLoad e
          let bb ← elabSDQLToLoad b
          let xIdent ← sdqlIdentToLeanIdent x
          wrapLoadWithStx stx (← `(LoadTerm'.letin $ee (fun $xIdent => $bb)))

      -- arithmetic / boolean ops
      | `(sdql| $x:sdql + $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          wrapLoadWithStx stx (← `(LoadTerm'.add $xx $yy))
      | `(sdql| $x:sdql - $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          wrapLoadWithStx stx (← `(LoadTerm'.builtinSub SurfaceTy.int (LoadTermLoc.mk (stx := $(← mkSourceLoc stx))
            (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)]))))
      | `(sdql| $x:sdql * $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          wrapLoadWithStx stx (← `(LoadTerm'.mul none $xx $yy))
      | `(sdql| $x:sdql *{int} $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          wrapLoadWithStx stx (← `(LoadTerm'.mul (some SurfaceTy.int) $xx $yy))
      | `(sdql| $x:sdql *{bool} $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          wrapLoadWithStx stx (← `(LoadTerm'.mul (some SurfaceTy.bool) $xx $yy))
      | `(sdql| $x:sdql *{real} $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          wrapLoadWithStx stx (← `(LoadTerm'.mul (some SurfaceTy.real) $xx $yy))
      | `(sdql| $x:sdql && $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinAnd $arg))
      | `(sdql| $x:sdql || $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinOr $arg))
      | `(sdql| $x:sdql == $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinEq SurfaceTy.int $arg))
      | `(sdql| $x:sdql <= $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinLeq SurfaceTy.int $arg))
      | `(sdql| $x:sdql < $y:sdql) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinLt SurfaceTy.int $arg))

      -- builtins
      | `(sdql| dom($e:sdql)) => do
          let ee ← elabSDQLToLoad e
          wrapLoadWithStx stx (← `(LoadTerm'.builtinDom SurfaceTy.int SurfaceTy.int $ee))
      | `(sdql| range($e:sdql)) => do
          let ee ← elabSDQLToLoad e
          wrapLoadWithStx stx (← `(LoadTerm'.builtinRange $ee))
      | `(sdql| endsWith($x:sdql, $y:sdql)) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinStrEndsWith $arg))
      | `(sdql| unique($e:sdql)) => elabSDQLToLoad e
      | `(sdql| date($n:num)) =>
          wrapLoadWithStx stx (← `(LoadTerm'.builtinDateLit $n))
      | `(sdql| year($e:sdql)) => do
          let ee ← elabSDQLToLoad e
          wrapLoadWithStx stx (← `(LoadTerm'.builtinYear $ee))
      | `(sdql| concat($x:sdql, $y:sdql)) => do
          let xx ← elabSDQLToLoad x
          let yy ← elabSDQLToLoad y
          let loc ← mkSourceLoc stx
          let arg := (← `(LoadTermLoc.mk (stx := $loc) (LoadTerm'.constRecord [("_1", $xx), ("_2", $yy)])))
          wrapLoadWithStx stx (← `(LoadTerm'.builtinConcat [] [] $arg))

      -- summation
      | `(sdql| sum(<$k:sdqlident, $v:sdqlident> in $d:sdql) $body:sdql) => do
          let dd ← elabSDQLToLoad d
          let bb ← elabSDQLToLoad body
          let kIdent ← sdqlIdentToLeanIdent k
          let vIdent ← sdqlIdentToLeanIdent v
          wrapLoadWithStx stx (← `(LoadTerm'.sum $dd (fun $kIdent => fun $vIdent => $bb)))
      | `(sdql| sum(<$k:sdqlident, $v:sdqlident> <- $d:sdql) $body:sdql) =>
          elabSDQLToLoad (← `(sdql| sum(<$k, $v> in $d) $body))

      -- load
      | `(sdql| load[$t:sdqlty]($p:str)) => do
          let tt ← elabTyPreserveOrder t
          wrapLoadWithStx stx (← `(LoadTerm'.load $p $tt))

      | _ =>
          Macro.throwErrorAt stx "unsupported SDQL syntax"
end

end PartIiProject
