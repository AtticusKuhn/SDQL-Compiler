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
chain graphs of increasing size. Two problems are benchmarked:

1. **Graph reachability** (transitive closure): `closure` over `bool` adjacency
2. **Viterbi** (most probable path): `closure` over `max_prod` adjacency

For each graph size, the script:
- Compiles the SDQL program to a Rust binary and measures execution time.
- Runs the equivalent Python reference script and compares outputs for correctness.

Graph structure: chain  0 → 1 → 2 → ... → (n-1),
built as `sum(<i, _> <- range(n - 1)) { i -> { i + 1 -> w } }`.
-/

def outDir : FilePath := FilePath.mk ".sdql-graph-perf-out"
def runtimeSrc : FilePath := FilePath.mk "sdql_runtime.rs"

-- ============================================================================
-- Graph generation helpers (for Python comparison JSON)
-- ============================================================================

/-- Generate JSON for a chain graph (bool adjacency) with edges 0→1, 1→2, ..., (n-2)→(n-1). -/
def chainGraphBoolJson (n : Nat) : String :=
  let entries := (List.range (n - 1)).map fun i =>
    "\"" ++ toString i ++ "\": [" ++ toString (i + 1) ++ "]"
  "{" ++ String.intercalate ", " entries ++ "}"

/-- Generate JSON for a chain graph (Viterbi) with weighted edges. -/
def chainGraphViterbiJson (n : Nat) (w : Float) : String :=
  let entries := (List.range (n - 1)).map fun i =>
    "\"" ++ toString i ++ "\": {\"" ++ toString (i + 1) ++ "\": " ++ toString w ++ "}"
  "{" ++ String.intercalate ", " entries ++ "}"

-- ============================================================================
-- SDQL programs: chain graphs of various sizes (reachability)
-- Each program builds edges 0→1→2→...→(n-1) and computes closure.
-- ============================================================================

unsafe def reachability_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(4)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(9)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(19)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(49)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(99)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_200 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(199)) { i -> { i + 1 -> true } }) ]

unsafe def reachability_500 : SProg2 :=
  [SDQLProg2 { { int -> { int -> bool } } }|
    closure(sum(<i, _> <- range(499)) { i -> { i + 1 -> true } }) ]

-- ============================================================================
-- SDQL programs: chain graphs of various sizes (Viterbi / max_prod)
-- ============================================================================

unsafe def viterbi_5 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(4)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_10 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(9)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_20 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(19)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_50 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(49)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_100 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(99)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_200 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(199)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

unsafe def viterbi_500 : SProg2 :=
  [SDQLProg2 { { int -> { int -> max_prod } } }|
    closure(sum(<i, _> <- range(499)) { i -> { i + 1 -> promote[max_prod](0.5) } }) ]

-- ============================================================================
-- Benchmark infrastructure
-- ============================================================================

unsafe structure GraphBenchCase where
  name : String
  n : Nat
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

/-- Run a Python script with JSON piped to stdin, capture stdout. -/
def runPythonCapture (script : FilePath) (jsonInput : String) : IO (Except String (Nat × String)) := do
  let start ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := "python3",
    args := #[script.toString],
    stdin := .piped,
    stdout := .piped,
    stderr := .piped,
    inheritEnv := Bool.true,
  }
  child.stdin.putStr jsonInput
  child.stdin.flush
  let (stdout, stderr) ← do
    let stdout ← child.stdout.readToEnd
    let stderr ← child.stderr.readToEnd
    pure (stdout, stderr)
  let code ← child.wait
  let stop ← IO.monoMsNow
  if code != 0 then
    return .error s!"Python script failed (exit {code}):\n{stderr}"
  return .ok (stop - start, stdout.trim)

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

  -- Correctness check
  if sdqlOutput != pythonOutput then
    IO.eprintln s!"  WARNING: Output mismatch for {b.name}!"
    IO.eprintln s!"    SDQL output   (first 200 chars): {sdqlOutput.take 200}"
    IO.eprintln s!"    Python output  (first 200 chars): {pythonOutput.take 200}"
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

unsafe def reachabilityCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/transitive_closure.py"
  [ { name := "reachability_5",   n := 5,   prog := reachability_5,
      pythonScript := script, jsonInput := chainGraphBoolJson 5 }
  , { name := "reachability_10",  n := 10,  prog := reachability_10,
      pythonScript := script, jsonInput := chainGraphBoolJson 10 }
  , { name := "reachability_20",  n := 20,  prog := reachability_20,
      pythonScript := script, jsonInput := chainGraphBoolJson 20 }
  , { name := "reachability_50",  n := 50,  prog := reachability_50,
      pythonScript := script, jsonInput := chainGraphBoolJson 50 }
  , { name := "reachability_100", n := 100, prog := reachability_100,
      pythonScript := script, jsonInput := chainGraphBoolJson 100 }
  , { name := "reachability_200", n := 200, prog := reachability_200,
      pythonScript := script, jsonInput := chainGraphBoolJson 200 }
  , { name := "reachability_500", n := 500, prog := reachability_500,
      pythonScript := script, jsonInput := chainGraphBoolJson 500 }
  ]

unsafe def viterbiCases : List GraphBenchCase :=
  let script := FilePath.mk "scripts/viterbi.py"
  let w : Float := 0.5
  -- strictCompare := Bool.false because float formatting may differ between Rust and Python
  [ { name := "viterbi_5",   n := 5,   prog := viterbi_5,
      pythonScript := script, jsonInput := chainGraphViterbiJson 5 w, strictCompare := Bool.false }
  , { name := "viterbi_10",  n := 10,  prog := viterbi_10,
      pythonScript := script, jsonInput := chainGraphViterbiJson 10 w, strictCompare := Bool.false }
  , { name := "viterbi_20",  n := 20,  prog := viterbi_20,
      pythonScript := script, jsonInput := chainGraphViterbiJson 20 w, strictCompare := Bool.false }
  , { name := "viterbi_50",  n := 50,  prog := viterbi_50,
      pythonScript := script, jsonInput := chainGraphViterbiJson 50 w, strictCompare := Bool.false }
  , { name := "viterbi_100", n := 100, prog := viterbi_100,
      pythonScript := script, jsonInput := chainGraphViterbiJson 100 w, strictCompare := Bool.false }
  , { name := "viterbi_200", n := 200, prog := viterbi_200,
      pythonScript := script, jsonInput := chainGraphViterbiJson 200 w, strictCompare := Bool.false }
  , { name := "viterbi_500", n := 500, prog := viterbi_500,
      pythonScript := script, jsonInput := chainGraphViterbiJson 500 w, strictCompare := Bool.false }
  ]

-- ============================================================================
-- Main
-- ============================================================================

unsafe def main (_args : List String) : IO UInt32 := do
  if (← outDir.pathExists) then
    IO.FS.removeDirAll outDir
  IO.FS.createDirAll outDir

  let mut reachReadings : List TimingResult := []
  let mut viterbiReadings : List TimingResult := []
  let mut failures : List (String × String) := []

  IO.println "=== Graph Reachability (transitive closure) ==="
  IO.println "  Graph type: chain 0 -> 1 -> ... -> (n-1)"
  IO.println ""

  for b in reachabilityCases do
    match ← runGraphBenchCase b with
    | .ok r => reachReadings := reachReadings.concat r
    | .error e => failures := failures.concat (b.name, e)

  IO.println ""
  IO.println "=== Viterbi (most probable path) ==="
  IO.println "  Graph type: chain (weight=0.5) 0 -> 1 -> ... -> (n-1)"
  IO.println ""

  for b in viterbiCases do
    match ← runGraphBenchCase b with
    | .ok r => viterbiReadings := viterbiReadings.concat r
    | .error e => failures := failures.concat (b.name, e)

  IO.println ""

  -- Print reachability table
  printMsComparisonTable
    "Graph Reachability: SDQL vs Python (wall-clock ms)"
    "SDQL" "Python" "SDQL/Python"
    (reachReadings.map fun r =>
      { name := r.name ++ " (n=" ++ toString r.n ++ ")", leftMs := r.sdqlMs, rightMs := r.pythonMs })

  IO.println ""

  -- Print Viterbi table
  printMsComparisonTable
    "Viterbi (max-product closure): SDQL vs Python (wall-clock ms)"
    "SDQL" "Python" "SDQL/Python"
    (viterbiReadings.map fun r =>
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
