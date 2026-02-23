import PartIiProject.CodegenRust
import PartIiProject.Bench.Common
import PartIiProject.Bench.Table
import PartIiProject.SyntaxSDQLProg
import Lean
import Std

open PartIiProject
open PartIiProject.Bench
open System

namespace GraphPerformance

/-!
# Graph Performance Benchmark

Tests the performance of SDQL as a graph database by measuring `closure(e)` on
graphs of increasing size across multiple topologies. Two problems are benchmarked:

1. **Graph reachability** (transitive closure): `closure` over `bool` adjacency
2. **Viterbi** (most probable path): `closure` over `max_prod` adjacency

Topologies tested:
- **Chain**: 0 → 1 → 2 → ... → (n-1)
- **Cycle**: 0 → 1 → ... → (n-1) → 0
- **Star** (outward): 0 → {1, 2, ..., n-1}

For each graph, the script:
- Compiles the SDQL program to a Rust binary and measures execution time.
- Runs the equivalent Python reference script and compares outputs for correctness.
-/

def outDir : FilePath := FilePath.mk ".sdql-graph-perf-out"
def runtimeSrc : FilePath := FilePath.mk "sdql_runtime.rs"

-- ============================================================================
-- Graph generation helpers (JSON for Python reference scripts)
-- ============================================================================

/-- JSON for a chain graph (bool adjacency): 0→1, 1→2, ..., (n-2)→(n-1). -/
def chainGraphBoolJson (n : Nat) : String :=
  let entries := (List.range (n - 1)).map fun i =>
    "\"" ++ toString i ++ "\": [" ++ toString (i + 1) ++ "]"
  "{" ++ String.intercalate ", " entries ++ "}"

/-- JSON for a chain graph (Viterbi/weighted): 0→1, ..., (n-2)→(n-1) with weight w. -/
def chainGraphViterbiJson (n : Nat) (w : Float) : String :=
  let entries := (List.range (n - 1)).map fun i =>
    "\"" ++ toString i ++ "\": {\"" ++ toString (i + 1) ++ "\": " ++ toString w ++ "}"
  "{" ++ String.intercalate ", " entries ++ "}"

/-- JSON for a cycle graph (bool adjacency): 0→1, ..., (n-2)→(n-1), (n-1)→0. -/
def cycleGraphBoolJson (n : Nat) : String :=
  let entries := (List.range n).map fun i =>
    let next := if i == n - 1 then 0 else i + 1
    "\"" ++ toString i ++ "\": [" ++ toString next ++ "]"
  "{" ++ String.intercalate ", " entries ++ "}"

/-- JSON for a cycle graph (Viterbi/weighted) with weight w. -/
def cycleGraphViterbiJson (n : Nat) (w : Float) : String :=
  let entries := (List.range n).map fun i =>
    let next := if i == n - 1 then 0 else i + 1
    "\"" ++ toString i ++ "\": {\"" ++ toString next ++ "\": " ++ toString w ++ "}"
  "{" ++ String.intercalate ", " entries ++ "}"

/-- JSON for a star graph (bool adjacency): 0→1, 0→2, ..., 0→(n-1). -/
def starGraphBoolJson (n : Nat) : String :=
  let succs := (List.range (n - 1)).map fun i => toString (i + 1)
  "{\"0\": [" ++ String.intercalate ", " succs ++ "]}"

/-- JSON for a star graph (Viterbi/weighted) with weight w. -/
def starGraphViterbiJson (n : Nat) (w : Float) : String :=
  let succs := (List.range (n - 1)).map fun i =>
    "\"" ++ toString (i + 1) ++ "\": " ++ toString w
  "{\"0\": {" ++ String.intercalate ", " succs ++ "}}"

-- ============================================================================
-- SDQL programs: Chain topology (reachability)
-- ============================================================================

unsafe def reachability_chain_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(4)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_chain_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(9)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_chain_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(19)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_chain_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(49)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_chain_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(99)) { i -> { i + 1 -> true } }) ]

-- ============================================================================
-- SDQL programs: Cycle topology (reachability)
-- Back-edge is included in the sum body; idempotent bool addition ensures
-- the graph is correct (true + true = true).
-- ============================================================================

unsafe def reachability_cycle_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(4)) { i -> { i + 1 -> true } } + { 4 -> { 0 -> true } }) ]

unsafe def reachability_cycle_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(9)) { i -> { i + 1 -> true } } + { 9 -> { 0 -> true } }) ]

unsafe def reachability_cycle_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(19)) { i -> { i + 1 -> true } } + { 19 -> { 0 -> true } }) ]

unsafe def reachability_cycle_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(49)) { i -> { i + 1 -> true } } + { 49 -> { 0 -> true } }) ]

unsafe def reachability_cycle_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(99)) { i -> { i + 1 -> true } } + { 99 -> { 0 -> true } }) ]

-- ============================================================================
-- SDQL programs: Star topology (reachability)
-- Centre node 0 has edges to all other nodes.
-- ============================================================================

unsafe def reachability_star_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(4)) { 0 -> { i + 1 -> true } }) ]

unsafe def reachability_star_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(9)) { 0 -> { i + 1 -> true } }) ]

unsafe def reachability_star_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(19)) { 0 -> { i + 1 -> true } }) ]

unsafe def reachability_star_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(49)) { 0 -> { i + 1 -> true } }) ]

unsafe def reachability_star_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(99)) { 0 -> { i + 1 -> true } }) ]

-- ============================================================================
-- SDQL programs: Chain topology (Viterbi / max_prod)
-- ============================================================================

unsafe def viterbi_chain_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(4)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_chain_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(9)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_chain_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(19)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_chain_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(49)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_chain_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(99)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

-- ============================================================================
-- SDQL programs: Cycle topology (Viterbi / max_prod)
-- ============================================================================

unsafe def viterbi_cycle_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(4)) { i -> { i + 1 -> promote[max_prod](0.5) } }
      + { 4 -> { 0 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_cycle_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(9)) { i -> { i + 1 -> promote[max_prod](0.5) } }
      + { 9 -> { 0 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_cycle_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(19)) { i -> { i + 1 -> promote[max_prod](0.5) } }
      + { 19 -> { 0 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_cycle_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(49)) { i -> { i + 1 -> promote[max_prod](0.5) } }
      + { 49 -> { 0 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_cycle_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(99)) { i -> { i + 1 -> promote[max_prod](0.5) } }
      + { 99 -> { 0 -> promote[max_prod](0.5) } }) ]

-- ============================================================================
-- SDQL programs: Star topology (Viterbi / max_prod)
-- ============================================================================

unsafe def viterbi_star_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(4)) { 0 -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_star_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(9)) { 0 -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_star_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(19)) { 0 -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_star_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(49)) { 0 -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_star_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(99)) { 0 -> { i + 1 -> promote[max_prod](0.5) } }) ]

-- ============================================================================
-- Benchmark infrastructure
-- ============================================================================

unsafe structure GraphBenchCase where
  name : String
  n : Nat
  topology : String
  prog : SProg2
  pythonScript : FilePath
  jsonInput : String
  /-- If true, output mismatch is a hard failure; if false, just a warning. -/
  strictCompare : Bool := Bool.true

structure TimingResult where
  name : String
  n : Nat
  sdqlMs : Nat
  pythonMs : Nat

/-- Run an SDQL binary and capture its stdout. -/
def runBinaryCapture (binPath : FilePath) : IO (Except String (Nat × String)) := do
  let start ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := binPath.toString,
    args := #[],
    inheritEnv := Bool.true,
  }
  let stop ← IO.monoMsNow
  if out.exitCode != 0 then
    return .error s!"Non-zero exit code {out.exitCode} for {binPath.toString}:\n{out.stderr}"
  return .ok (stop - start, out.stdout.trim)

/-- Run a Python script with JSON input via a temp file, capture stdout. -/
def runPythonCapture (script : FilePath) (jsonInput : String) : IO (Except String (Nat × String)) := do
  -- Write JSON to a temp file to avoid stdin pipe deadlock
  let tmpFile := outDir / "python_input.json"
  IO.FS.writeFile tmpFile jsonInput
  let start ← IO.monoMsNow
  let out ← IO.Process.output {
    cmd := "python3",
    args := #[script.toString, tmpFile.toString],
    inheritEnv := Bool.true,
  }
  let stop ← IO.monoMsNow
  if out.exitCode != 0 then
    return .error s!"Python script failed (exit {out.exitCode}):\n{out.stderr}"
  return .ok (stop - start, out.stdout.trim)

/-- Run a single graph benchmark case. -/
unsafe def runGraphBenchCase (b : GraphBenchCase) : IO (Except String TimingResult) := do
  IO.println s!"  Compiling {b.name} (n={b.n})..."

  -- Compile SDQL program to binary
  let binPath ←
    match ← compileSProg2ToBin outDir runtimeSrc b.name b.prog with
    | .ok p => pure p
    | .error e => return .error s!"Compilation failed for {b.name}:\n{e}"

  IO.println s!"  Running SDQL binary..."
  let (sdqlMs, sdqlOutput) ←
    match ← runBinaryCapture binPath with
    | .ok r => pure r
    | .error e => return .error s!"SDQL run failed for {b.name}:\n{e}"

  IO.println s!"  Running Python reference ({b.pythonScript})..."
  let (pythonMs, pythonOutput) ←
    match ← runPythonCapture b.pythonScript b.jsonInput with
    | .ok r => pure r
    | .error e => return .error s!"Python run failed for {b.name}:\n{e}"

  -- Correctness check: use numerical comparison to handle float formatting
  -- differences between Rust (no scientific notation) and Python (scientific
  -- notation for small values, different last-digit rounding).
  let sdqlFile := outDir / (b.name ++ "_sdql_out.txt")
  let pyFile := outDir / (b.name ++ "_py_out.txt")
  IO.FS.writeFile sdqlFile sdqlOutput
  IO.FS.writeFile pyFile pythonOutput
  let cmpResult ← IO.Process.output {
    cmd := "python3",
    args := #["scripts/compare_sdql_output.py", sdqlFile.toString, pyFile.toString],
    inheritEnv := Bool.true,
  }
  if cmpResult.exitCode != 0 then
    IO.eprintln s!"  WARNING: Output mismatch for {b.name}!"
    IO.eprintln s!"    SDQL output   (first 200 chars): {sdqlOutput.take 200}"
    IO.eprintln s!"    Python output  (first 200 chars): {pythonOutput.take 200}"
    IO.eprintln s!"    {cmpResult.stderr.trim}"
    if b.strictCompare then
      return .error s!"Output mismatch for {b.name}"
    else
      IO.eprintln s!"    (non-strict mode: continuing despite mismatch)"
  else
    IO.println s!"  OK (outputs match, SDQL={sdqlMs}ms, Python={pythonMs}ms)"

  return .ok {
    name := b.name
    n := b.n
    sdqlMs := sdqlMs
    pythonMs := pythonMs
  }

-- ============================================================================
-- Benchmark case lists
-- ============================================================================

unsafe def reachabilityChainCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/transitive_closure.py"
  [ { name := "reach_chain_5",    n := 5,    topology := "chain",
      prog := reachability_chain_5,   pythonScript := script, jsonInput := chainGraphBoolJson 5 }
  , { name := "reach_chain_10",   n := 10,   topology := "chain",
      prog := reachability_chain_10,  pythonScript := script, jsonInput := chainGraphBoolJson 10 }
  , { name := "reach_chain_20",   n := 20,   topology := "chain",
      prog := reachability_chain_20,  pythonScript := script, jsonInput := chainGraphBoolJson 20 }
  , { name := "reach_chain_50",   n := 50,   topology := "chain",
      prog := reachability_chain_50,  pythonScript := script, jsonInput := chainGraphBoolJson 50 }
  , { name := "reach_chain_100",  n := 100,  topology := "chain",
      prog := reachability_chain_100, pythonScript := script, jsonInput := chainGraphBoolJson 100 }
  ]

unsafe def reachabilityCycleCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/transitive_closure.py"
  [ { name := "reach_cycle_5",    n := 5,    topology := "cycle",
      prog := reachability_cycle_5,   pythonScript := script, jsonInput := cycleGraphBoolJson 5 }
  , { name := "reach_cycle_10",   n := 10,   topology := "cycle",
      prog := reachability_cycle_10,  pythonScript := script, jsonInput := cycleGraphBoolJson 10 }
  , { name := "reach_cycle_20",   n := 20,   topology := "cycle",
      prog := reachability_cycle_20,  pythonScript := script, jsonInput := cycleGraphBoolJson 20 }
  , { name := "reach_cycle_50",   n := 50,   topology := "cycle",
      prog := reachability_cycle_50,  pythonScript := script, jsonInput := cycleGraphBoolJson 50 }
  , { name := "reach_cycle_100",  n := 100,  topology := "cycle",
      prog := reachability_cycle_100, pythonScript := script, jsonInput := cycleGraphBoolJson 100 }
  ]

unsafe def reachabilityStarCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/transitive_closure.py"
  [ { name := "reach_star_5",    n := 5,    topology := "star",
      prog := reachability_star_5,   pythonScript := script, jsonInput := starGraphBoolJson 5 }
  , { name := "reach_star_10",   n := 10,   topology := "star",
      prog := reachability_star_10,  pythonScript := script, jsonInput := starGraphBoolJson 10 }
  , { name := "reach_star_20",   n := 20,   topology := "star",
      prog := reachability_star_20,  pythonScript := script, jsonInput := starGraphBoolJson 20 }
  , { name := "reach_star_50",   n := 50,   topology := "star",
      prog := reachability_star_50,  pythonScript := script, jsonInput := starGraphBoolJson 50 }
  , { name := "reach_star_100",  n := 100,  topology := "star",
      prog := reachability_star_100, pythonScript := script, jsonInput := starGraphBoolJson 100 }
  ]

unsafe def viterbiChainCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/viterbi.py"
  let w : Float := 0.5
  [ { name := "viterbi_chain_5",    n := 5,    topology := "chain",
      prog := viterbi_chain_5,   pythonScript := script,
      jsonInput := chainGraphViterbiJson 5 w, strictCompare := Bool.true }
  , { name := "viterbi_chain_10",   n := 10,   topology := "chain",
      prog := viterbi_chain_10,  pythonScript := script,
      jsonInput := chainGraphViterbiJson 10 w, strictCompare := Bool.true }
  , { name := "viterbi_chain_20",   n := 20,   topology := "chain",
      prog := viterbi_chain_20,  pythonScript := script,
      jsonInput := chainGraphViterbiJson 20 w, strictCompare := Bool.true }
  , { name := "viterbi_chain_50",   n := 50,   topology := "chain",
      prog := viterbi_chain_50,  pythonScript := script,
      jsonInput := chainGraphViterbiJson 50 w, strictCompare := Bool.true }
  , { name := "viterbi_chain_100",  n := 100,  topology := "chain",
      prog := viterbi_chain_100, pythonScript := script,
      jsonInput := chainGraphViterbiJson 100 w, strictCompare := Bool.true }
  ]

unsafe def viterbiCycleCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/viterbi.py"
  let w : Float := 0.5
  [ { name := "viterbi_cycle_5",    n := 5,    topology := "cycle",
      prog := viterbi_cycle_5,   pythonScript := script,
      jsonInput := cycleGraphViterbiJson 5 w, strictCompare := Bool.true }
  , { name := "viterbi_cycle_10",   n := 10,   topology := "cycle",
      prog := viterbi_cycle_10,  pythonScript := script,
      jsonInput := cycleGraphViterbiJson 10 w, strictCompare := Bool.true }
  , { name := "viterbi_cycle_20",   n := 20,   topology := "cycle",
      prog := viterbi_cycle_20,  pythonScript := script,
      jsonInput := cycleGraphViterbiJson 20 w, strictCompare := Bool.true }
  , { name := "viterbi_cycle_50",   n := 50,   topology := "cycle",
      prog := viterbi_cycle_50,  pythonScript := script,
      jsonInput := cycleGraphViterbiJson 50 w, strictCompare := Bool.true }
  , { name := "viterbi_cycle_100",  n := 100,  topology := "cycle",
      prog := viterbi_cycle_100, pythonScript := script,
      jsonInput := cycleGraphViterbiJson 100 w, strictCompare := Bool.true }
  ]

unsafe def viterbiStarCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/viterbi.py"
  let w : Float := 0.5
  [ { name := "viterbi_star_5",    n := 5,    topology := "star",
      prog := viterbi_star_5,   pythonScript := script,
      jsonInput := starGraphViterbiJson 5 w, strictCompare := Bool.true }
  , { name := "viterbi_star_10",   n := 10,   topology := "star",
      prog := viterbi_star_10,  pythonScript := script,
      jsonInput := starGraphViterbiJson 10 w, strictCompare := Bool.true }
  , { name := "viterbi_star_20",   n := 20,   topology := "star",
      prog := viterbi_star_20,  pythonScript := script,
      jsonInput := starGraphViterbiJson 20 w, strictCompare := Bool.true }
  , { name := "viterbi_star_50",   n := 50,   topology := "star",
      prog := viterbi_star_50,  pythonScript := script,
      jsonInput := starGraphViterbiJson 50 w, strictCompare := Bool.true }
  , { name := "viterbi_star_100",  n := 100,  topology := "star",
      prog := viterbi_star_100, pythonScript := script,
      jsonInput := starGraphViterbiJson 100 w, strictCompare := Bool.true }
  ]

-- ============================================================================
-- Main
-- ============================================================================

/-- Run a list of benchmark cases and collect results and failures. -/
unsafe def runBenchSuite (label : String) (desc : String) (cases : List GraphBenchCase) :
    IO (List TimingResult × List (String × String)) := do
  IO.println s!"--- {label} ---"
  IO.println s!"  {desc}"
  IO.println ""
  let mut readings : List TimingResult := []
  let mut failures : List (String × String) := []
  for b in cases do
    match ← runGraphBenchCase b with
    | .ok r => readings := readings.concat r
    | .error e => failures := failures.concat (b.name, e)
  IO.println ""
  return (readings, failures)

unsafe def main (_args : List String) : IO UInt32 := do
  if (← outDir.pathExists) then
    IO.FS.removeDirAll outDir
  IO.FS.createDirAll outDir

  let mut allReachReadings : List TimingResult := []
  let mut allViterbiReadings : List TimingResult := []
  let mut failures : List (String × String) := []

  -- === Reachability benchmarks ===
  IO.println "=== Graph Reachability (transitive closure over bool) ==="
  IO.println ""

  let (r, f) ← runBenchSuite "Chain" "0 → 1 → 2 → ... → (n-1)" reachabilityChainCases
  allReachReadings := allReachReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Cycle" "0 → 1 → ... → (n-1) → 0" reachabilityCycleCases
  allReachReadings := allReachReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Star" "0 → {1, 2, ..., n-1}" reachabilityStarCases
  allReachReadings := allReachReadings ++ r; failures := failures ++ f

  -- === Viterbi benchmarks ===
  IO.println "=== Viterbi (most probable path, max_prod closure) ==="
  IO.println ""

  let (r, f) ← runBenchSuite "Chain (w=0.5)" "0 → 1 → ... → (n-1)" viterbiChainCases
  allViterbiReadings := allViterbiReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Cycle (w=0.5)" "0 → 1 → ... → (n-1) → 0" viterbiCycleCases
  allViterbiReadings := allViterbiReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Star (w=0.5)" "0 → {1, 2, ..., n-1}" viterbiStarCases
  allViterbiReadings := allViterbiReadings ++ r; failures := failures ++ f

  -- === Summary tables ===
  IO.println "============================================================"
  IO.println ""

  printMsComparisonTable
    "Graph Reachability: SDQL vs Python (wall-clock ms)"
    "SDQL" "Python" "SDQL/Python"
    (allReachReadings.map fun r =>
      { name := r.name ++ " (n=" ++ toString r.n ++ ")", leftMs := r.sdqlMs, rightMs := r.pythonMs })

  IO.println ""

  printMsComparisonTable
    "Viterbi (max-product closure): SDQL vs Python (wall-clock ms)"
    "SDQL" "Python" "SDQL/Python"
    (allViterbiReadings.map fun r =>
      { name := r.name ++ " (n=" ++ toString r.n ++ ")", leftMs := r.sdqlMs, rightMs := r.pythonMs })

  if !failures.isEmpty then
    IO.eprintln ""
    IO.eprintln "Failures:"
    for (nm, err) in failures do
      IO.eprintln s!"- {nm}: {err}"
    return 1

  return 0

end GraphPerformance

unsafe def main (args : List String) : IO UInt32 :=
  GraphPerformance.main args
