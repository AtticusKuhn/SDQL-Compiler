import PartIiProject.Bench.Common
import PartIiProject.Bench.Table
import PartIiProject.Optimisations
import PartIiProject.SyntaxSDQLProg
import Lean
import Std

open PartIiProject
open PartIiProject.Optimisations
open System

namespace OptimisationPerformanceComparison

def outDir : FilePath := FilePath.mk ".sdql-opt-perf-out"
def runtimeSrc : FilePath := FilePath.mk "sdql_runtime.rs"

def iters : Nat := 3
def dictN : Int := 200000
def memoN : Int := 100000
def memoM : Int := 1000

unsafe structure BenchCase where
  name : String
  prog : SProg2
  opts : List Optimisation
  env : List (String × String) := []

structure Reading where
  name : String
  unoptMs : Nat
  optMs : Nat

def meanNat (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ =>
      let total := xs.foldl (fun s x => s + x) 0
      total / xs.length

def timeBinaryAvgMs (binPath : FilePath) (iters : Nat) (env : List (String × String)) :
    IO (Except String Nat) := do
  if iters == 0 then
    return .error "iters must be > 0"
  let mut acc : List Nat := []
  for _ in [0:iters] do
    match ← PartIiProject.Bench.timeBinaryMs binPath env with
    | .ok ms => acc := ms :: acc
    | .error e => return .error e
  return .ok (meanNat acc)

unsafe def runCase (b : BenchCase) : IO (Except String Reading) := do
  let baseCp := ToCore2.trProg2 b.prog
  let optTerm := applyOptimisationsLoc b.opts baseCp.term
  let optCp : Prog2 := { baseCp with term := optTerm }

  let unoptBin ←
    match ← PartIiProject.Bench.compileProg2ToBin outDir runtimeSrc s!"{b.name}_unopt" baseCp with
    | .ok p => pure p
    | .error e => return .error s!"Unoptimised compile failed:\n{e}"

  let optBin ←
    match ← PartIiProject.Bench.compileProg2ToBin outDir runtimeSrc s!"{b.name}_opt" optCp with
    | .ok p => pure p
    | .error e => return .error s!"Optimised compile failed:\n{e}"

  let unoptMs ←
    match ← timeBinaryAvgMs unoptBin iters b.env with
    | .ok ms => pure ms
    | .error e => return .error s!"Unoptimised run failed:\n{e}"

  let optMs ←
    match ← timeBinaryAvgMs optBin iters b.env with
    | .ok ms => pure ms
    | .error e => return .error s!"Optimised run failed:\n{e}"

  return .ok { name := b.name, unoptMs := unoptMs, optMs := optMs }

unsafe def p_vertical_loop_fusion_key_map : SProg2 :=
  [SDQLProg2 { { int -> int } }|
    let dictN = 200000 in
    let d = sum( <i, _> <- range(dictN) ) { i -> i } in
    let y = sum( <x, x_v> <- d ) { x + 1 -> x_v } in
    sum( <x, x_v> <- y ) { x + 2 -> x_v }
  ]

unsafe def p_vertical_loop_fusion_value_map : SProg2 :=
  [SDQLProg2 { { int -> int } }|
    let dictN = 200000 in
    let d = sum( <i, _> <- range(dictN) ) { i -> i } in
    let y = sum( <x, x_v> <- d ) { x -> x_v + 1 } in
    sum( <x, x_v> <- y ) { x -> x_v + 2 }
  ]

unsafe def p_horizontal_loop_fusion : SProg2 :=
  [SDQLProg2 { int }|
    let dictN = 200000 in
    let d = sum( <i, _> <- range(dictN) ) { i -> i } in
    let y1 = sum( <_, v> <- d ) v in
    let y2 = sum( <_, v> <- d ) (v + 1) in
    y1 + y2
  ]

unsafe def p_loop_factorization_left : SProg2 :=
  [SDQLProg2 { int }|
    let dictN = 200000 in
    let d = sum( <i, _> <- range(dictN) ) { i -> i } in
    sum( <_, v> <- d ) (2 * v)
  ]

unsafe def p_loop_factorization_right : SProg2 :=
  [SDQLProg2 { int }|
    let dictN = 200000 in
    let d = sum( <i, _> <- range(dictN) ) { i -> i } in
    sum( <_, v> <- d ) (v * 2)
  ]

unsafe def p_loop_invariant_code_motion : SProg2 :=
  [SDQLProg2 { int }|
    let dictN = 200000 in
    let d = sum( <i, _> <- range(dictN) ) { i -> i } in
    sum( <_, v> <- d ) (let y = 5 in v + y)
  ]

-- Memoization lookup + hoisting: without hoisting this is not a win; include code motion.
unsafe def p_loop_memoization_lookup : SProg2 :=
  [SDQLProg2 { int }|
    let memoN = 100000 in
    let memoM = 1000 in
    let d = sum( <i, _> <- range(memoN) ) { i -> i } in
    sum( <i, _> <- range(memoM) ) (sum( <k, v> <- d ) (if k == i then v))
  ]

-- Partition + hoisting: then-branch depends on `i`, so lookup-memoization cannot hoist `f`.
unsafe def p_loop_memoization_partition : SProg2 :=
  [SDQLProg2 { int }|
    let memoN = 100000 in
    let memoM = 1000 in
    let d = sum( <i, _> <- range(memoN) ) { i -> i } in
    sum( <i, _> <- range(memoM) ) (sum( <k, v> <- d ) (if k == i then v + i))
  ]

unsafe def mkCases : List BenchCase :=
  [ { name := "vertical_loop_fusion_key_map"
      prog := p_vertical_loop_fusion_key_map
      opts := [verticalLoopFusionKeyMap2, verticalLoopFusionValueMap2]
    }
  , { name := "vertical_loop_fusion_value_map"
      prog := p_vertical_loop_fusion_value_map
      opts := [verticalLoopFusionKeyMap2, verticalLoopFusionValueMap2]
    }
  , { name := "horizontal_loop_fusion"
      prog := p_horizontal_loop_fusion
      opts := [horizontalLoopFusion2]
    }
  , { name := "loop_factorization_left"
      prog := p_loop_factorization_left
      opts := [loopFactorizationLeft2]
    }
  , { name := "loop_factorization_right"
      prog := p_loop_factorization_right
      opts := [loopFactorizationRight2]
    }
  , { name := "loop_invariant_code_motion"
      prog := p_loop_invariant_code_motion
      opts := [loopInvariantCodeMotion2]
    }
  , { name := "loop_memoization_lookup"
      prog := p_loop_memoization_lookup
      opts := [loopMemoizationLookup2, loopInvariantCodeMotion2]
    }
  , { name := "loop_memoization_partition"
      prog := p_loop_memoization_partition
      opts := [loopMemoizationPartition2, loopInvariantCodeMotion2]
    }
  ]

unsafe def main (_args : List String) : IO UInt32 := do
  if (← outDir.pathExists) then
    IO.FS.removeDirAll outDir
  IO.FS.createDirAll outDir

  let mut readings : List Reading := []
  let mut failures : List (String × String) := []

  for b in mkCases do
    match ← runCase b with
    | .ok r => readings := readings.concat r
    | .error e => failures := failures.concat (b.name, e)

  PartIiProject.Bench.printMsComparisonTable
    s!"SDQL optimisation performance comparison (mean of {iters} run(s); wall-clock ms)"
    "unopt" "opt" "opt/unopt"
    (readings.map fun r =>
      { name := r.name, leftMs := r.unoptMs, rightMs := r.optMs })
    (preamble := [s!"Params: dictN={dictN}, memoN={memoN}, memoM={memoM}"])

  if !failures.isEmpty then
    IO.eprintln ""
    IO.eprintln "Failures:"
    for (nm, err) in failures do
      IO.eprintln s!"- {nm}: {err}"
    return 1
  return 0

end OptimisationPerformanceComparison

unsafe def main (args : List String) : IO UInt32 :=
  OptimisationPerformanceComparison.main args
