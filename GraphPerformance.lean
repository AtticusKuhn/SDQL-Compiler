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
-- Parameterised SDQL program builders
-- ============================================================================

inductive GraphTopology where
  | chain | cycle | star

inductive GraphProblem where
  | reachability
  | viterbi (w : Float)

/-- Wrap a `LoadTerm'` with an unknown source location. -/
private def mkLoc {rep : Type} (t : LoadTerm' rep) : LoadTermLoc rep :=
  LoadTermLoc.mk SourceLocation.unknown t

/-- Build an SDQL `closure(...)` program for the given topology, problem type and
    graph size `n` (number of nodes).

- `chain n`: closure of 0 → 1 → ... → (n-1)
- `cycle n`: closure of 0 → 1 → ... → (n-1) → 0
- `star  n`: closure of 0 → {1, ..., n-1}

For `reachability`, edges carry `true : bool`.
For `viterbi w`, edges carry `promote[max_prod](w)`. -/
unsafe def mkGraphProg (topo : GraphTopology) (prob : GraphProblem) (n : Nat) : SProg2 :=
  let valTy : SurfaceTy := match prob with
    | .reachability => .bool
    | .viterbi _    => .maxProduct
  let term : LoadTerm := fun {rep} =>
    let val : LoadTermLoc rep := match prob with
      | .reachability => mkLoc (.constBool Bool.true)
      | .viterbi w    => mkLoc (.promote .maxProduct (mkLoc (.constReal w)))
    let edgeBody : rep → rep → LoadTermLoc rep := fun i _v =>
      let src : LoadTermLoc rep := match topo with
        | .star => mkLoc (.constInt 0)
        | _     => mkLoc (.var i)
      let tgt := mkLoc (.add (mkLoc (.var i)) (mkLoc (.constInt 1)))
      mkLoc (.dictInsert src
        (mkLoc (.dictInsert tgt val (mkLoc .emptyDict)))
        (mkLoc .emptyDict))
    let sumExpr := mkLoc (.sum
      (mkLoc (.builtinRange (mkLoc (.constInt (n - 1)))))
      edgeBody)
    let graphExpr : LoadTermLoc rep := match topo with
      | .cycle =>
        let backEdge := mkLoc (.dictInsert
          (mkLoc (.constInt (n - 1)))
          (mkLoc (.dictInsert (mkLoc (.constInt 0)) val (mkLoc .emptyDict)))
          (mkLoc .emptyDict))
        mkLoc (.add sumExpr backEdge)
      | _ => sumExpr
    mkLoc (.closure graphExpr)
  loadTermToSProg2 (.dict .int (.dict .int valTy)) term

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
    return .error s!"Output mismatch for {b.name}"
  else
    IO.println s!"  OK (outputs match, SDQL={sdqlMs}ms, Python={pythonMs}ms)"

  return .ok {
    name := b.name
    n := b.n
    sdqlMs := sdqlMs
    pythonMs := pythonMs
  }

-- ============================================================================
-- Case list builder
-- ============================================================================

/-- Build a list of benchmark cases for one (topology, problem) combination. -/
unsafe def mkCases (probName topoName : String) (topo : GraphTopology) (prob : GraphProblem)
    (script : FilePath) (mkJson : Nat → String) (sizes : List Nat) : List GraphBenchCase :=
  sizes.map fun n => {
    name := s!"{probName}_{topoName}_{n}"
    n := n
    topology := topoName
    prog := mkGraphProg topo prob n
    pythonScript := script
    jsonInput := mkJson n
  }

-- ============================================================================
-- Main
-- ============================================================================

/-- Run a list of benchmark cases and collect results and failures. -/
unsafe def runBenchSuite (label desc : String) (cases : List GraphBenchCase) :
    IO (List TimingResult × List (String × String)) := do
  IO.println s!"--- {label} ---"
  IO.println s!"  {desc}"
  IO.println ""
  let mut readings : List TimingResult := []
  let mut failures : List (String × String) := []
  for b in cases do
    match ← runGraphBenchCase b with
    | .ok r => readings := readings ++ [r]
    | .error e => failures := failures ++ [(b.name, e)]
  IO.println ""
  return (readings, failures)

unsafe def main (_args : List String) : IO UInt32 := do
  if (← outDir.pathExists) then
    IO.FS.removeDirAll outDir
  IO.FS.createDirAll outDir

  let sizes := [10, 50, 100, 200, 500]
  let w : Float := 0.5
  let reachScript := FilePath.mk "scripts/transitive_closure.py"
  let viterbiScript := FilePath.mk "scripts/viterbi.py"

  let mut allReachReadings : List TimingResult := []
  let mut allViterbiReadings : List TimingResult := []
  let mut failures : List (String × String) := []

  -- === Reachability benchmarks ===
  IO.println "=== Graph Reachability (transitive closure over bool) ==="
  IO.println ""

  let (r, f) ← runBenchSuite "Chain" "0 → 1 → 2 → ... → (n-1)"
    (mkCases "reach" "chain" .chain .reachability reachScript (chainGraphBoolJson ·) sizes)
  allReachReadings := allReachReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Cycle" "0 → 1 → ... → (n-1) → 0"
    (mkCases "reach" "cycle" .cycle .reachability reachScript (cycleGraphBoolJson ·) sizes)
  allReachReadings := allReachReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Star" "0 → {1, 2, ..., n-1}"
    (mkCases "reach" "star" .star .reachability reachScript (starGraphBoolJson ·) sizes)
  allReachReadings := allReachReadings ++ r; failures := failures ++ f

  -- === Viterbi benchmarks ===
  IO.println "=== Viterbi (most probable path, max_prod closure) ==="
  IO.println ""

  let (r, f) ← runBenchSuite "Chain (w=0.5)" "0 → 1 → ... → (n-1)"
    (mkCases "viterbi" "chain" .chain (.viterbi w) viterbiScript (chainGraphViterbiJson · w) sizes)
  allViterbiReadings := allViterbiReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Cycle (w=0.5)" "0 → 1 → ... → (n-1) → 0"
    (mkCases "viterbi" "cycle" .cycle (.viterbi w) viterbiScript (cycleGraphViterbiJson · w) sizes)
  allViterbiReadings := allViterbiReadings ++ r; failures := failures ++ f

  let (r, f) ← runBenchSuite "Star (w=0.5)" "0 → {1, 2, ..., n-1}"
    (mkCases "viterbi" "star" .star (.viterbi w) viterbiScript (starGraphViterbiJson · w) sizes)
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
