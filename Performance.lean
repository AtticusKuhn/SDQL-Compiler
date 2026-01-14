import PartIiProject.CodegenRust
import PartIiProject.Bench.Common
import PartIiProject.Bench.Table
import PartIiProject.SyntaxSDQLProg
import Tests.Cases
import Lean
import Std

open PartIiProject
open PartIiProject.Bench
open System

namespace Performance

/-
This runner compares runtime (single-run, wall-clock milliseconds) between:
- `sdql-rs` reference binaries (or binaries compiled by `sdql-rs` from a provided SDQL source), and
- our Lean→Rust generated binaries compiled via `rustc`.

It intentionally does *not* check output equality; correctness is covered by `Tests/Cases.lean`.
-/

def outDir : FilePath := FilePath.mk ".sdql-perf-out"
def runtimeSrc : FilePath := FilePath.mk "sdql_runtime.rs"

def sdqlRsTargetDir : FilePath := outDir / "sdql-rs-target"

def lastPathComponent (p : String) : String :=
  match (p.splitOn "/").getLast? with
  | some c => c
  | none => p

def ensureSdqlRsRefBin (refBinPath : String) : IO (Except String Unit) := do
  let refBin := FilePath.mk refBinPath
  let refBinExists ← refBin.pathExists
  if refBinExists then
    return .ok ()
  let isSdqlRsTarget := refBinPath.startsWith "sdql-rs/target/release/"
  if !isSdqlRsTarget then
    return .error s!"Reference binary not found: {refBinPath}"
  let binName := lastPathComponent refBinPath
  let srcPath := FilePath.mk s!"sdql-rs/src/bin/{binName}.rs"
  let srcExists ← srcPath.pathExists
  if !srcExists then
    return .error s!"Reference binary missing and no source found at {srcPath.toString}"
  let (code, _out, err) ← PartIiProject.Bench.runProc "cargo" #["build", "--release", "--bin", binName]
    (cwd? := some (FilePath.mk "sdql-rs"))
    (envVars := [("RUSTFLAGS", "-C target-cpu=native")])
  if code != 0 then
    return .error s!"Failed to build reference binary {binName}:\n{err}"
  let refBinExistsAfter ← refBin.pathExists
  if refBinExistsAfter then
    return .ok ()
  else
    return .error s!"Reference binary still missing after build: {refBinPath}"

def listReleaseBins (releaseDir : FilePath) : IO (List String) := do
  if !(← releaseDir.pathExists) then
    return []
  let entries ← releaseDir.readDir
  let mut acc : List String := []
  for e in entries do
    let p := e.path
    let md ← p.metadata
    if md.type == .file && p.extension.isNone then
      match p.fileName with
      | some n =>
          if n.startsWith "." then
            pure ()
          else
            acc := n :: acc
      | none => pure ()
  return acc

def discoverNewSdqlRsBin (releaseDir : FilePath) (before after : List String) : Except String FilePath :=
  let newOnes := after.filter (fun n => n != "main" && !(before.contains n))
  match newOnes with
  | [n] => .ok (releaseDir / n)
  | [] => .error "sdql-rs compilation produced no new binary (try cleaning the perf output directory)"
  | ns => .error s!"sdql-rs compilation produced multiple new binaries: {ns}"

def ensureSdqlRsBinFromSdql (sdqlSrc : String) : IO (Except String FilePath) := do
  let absOutDir ← PartIiProject.Bench.absPath outDir
  let cargoTargetDir := absOutDir / "sdql-rs-target"
  let releaseDir := cargoTargetDir / "release"

  IO.FS.createDirAll absOutDir
  IO.FS.createDirAll cargoTargetDir

  let before ← listReleaseBins releaseDir
  let sdqlPath := absOutDir / "sdqlrs_micro.sdql"
  PartIiProject.Bench.writeFile sdqlPath sdqlSrc

  let (code, err) ← PartIiProject.Bench.runProcDiscardStdout "cargo"
    #["run", "--release", "--quiet", "--bin", "main", sdqlPath.toString]
    (cwd? := some (FilePath.mk "sdql-rs"))
    (envVars := [("RUSTFLAGS", "-C target-cpu=native"), ("CARGO_TARGET_DIR", cargoTargetDir.toString)])

  if code != 0 then
    return .error s!"sdql-rs failed to compile/run SDQL source:\n{err}"

  let after ← listReleaseBins releaseDir
  let e := discoverNewSdqlRsBin releaseDir before after
  match e with
    | Except.ok p => IO.print s!"path = {p}"
    | Except.error e => IO.print s!"error = {e}"
  return e

unsafe structure Benchmark where
  name : String
  prog : SProg2
  sdqlRsBin : IO (Except String FilePath)
  env : List (String × String) := []

structure Reading where
  name : String
  sdqlRsMs : Nat
  leanMs : Nat
  ratioMilli : Nat

unsafe def runBenchmark (b : Benchmark) : IO (Except String Reading) := do
  let refPath ← b.sdqlRsBin
  let refBinPath ←
    match refPath with
    | .ok p => pure p
    | .error e => return .error e

  let leanBinPath ←
    match ← PartIiProject.Bench.compileSProg2ToBin outDir runtimeSrc s!"{b.name}_lean" b.prog with
    | .ok p => pure p
    | .error e => return .error s!"Lean→Rust compile failed for {b.name}:\n{e}"

  let sdqlMs ←
    match ← PartIiProject.Bench.timeBinaryMs refBinPath b.env with
    | .ok ms => pure ms
    | .error e => return .error s!"sdql-rs run failed for {b.name} ({refBinPath.toString}):\n{e}"

  let leanMs ←
    match ← PartIiProject.Bench.timeBinaryMs leanBinPath b.env with
    | .ok ms => pure ms
    | .error e => return .error s!"Lean-generated run failed for {b.name} ({leanBinPath.toString}):\n{e}"

  return .ok {
    name := b.name
    sdqlRsMs := sdqlMs
    leanMs := leanMs
    ratioMilli := PartIiProject.Bench.ratioMilli leanMs sdqlMs
  }

unsafe def microBenchmarks : List Benchmark :=
  let pAdd : SProg2 :=
    [SDQLProg2 { int }| sum( <_, _> <- range(2000000) ) 1 ]
  let pDict : SProg2 :=
    [SDQLProg2 { { int -> int } }| sum( <i, _> <- range(400000) ) { i -> 1 } ]
  let pLookup : SProg2 :=
    [SDQLProg2 { int }|
      let d = sum( <i, _> <- range(200000) ) { i -> i } in
      sum( <i, _> <- range(200000) ) d(i)
    ]

  -- sdql-rs uses `<-` for summation binders; use our `SProg2`→String printer, which emits sdql-rs syntax.
  let sAdd : String := toString pAdd
  let sDict : String := toString pDict
  let sLookup : String := toString pLookup

  [ { name := "micro_sum_range_add"
      prog := pAdd
      sdqlRsBin := do ensureSdqlRsBinFromSdql sAdd
    }
  , { name := "micro_sum_range_dict_build"
      prog := pDict
      sdqlRsBin := do ensureSdqlRsBinFromSdql sDict
    }
  , { name := "micro_sum_range_lookup"
      prog := pLookup
      sdqlRsBin := do ensureSdqlRsBinFromSdql sLookup
    }
  ]

unsafe def tpchBenchmarks : List Benchmark :=
  let mk (name : String) (p : SProg2) (refBinPath : String) (envVars : List (String × String)) : Benchmark :=
    { name := name
      prog := p
      sdqlRsBin := do
        match ← ensureSdqlRsRefBin refBinPath with
        | .ok () => return .ok (FilePath.mk refBinPath)
        | .error e => return .error e
      env := envVars
    }
  let collect (cs : List Tests.Cases.TestCase) : List Benchmark :=
    cs.foldr (fun c acc =>
      match c with
      | .programRef name p refBinPath envVars => mk name p refBinPath envVars :: acc
      | _ => acc
    ) []
  collect Tests.Cases.tpchCases ++ collect Tests.Cases.tpchCasesSF001

unsafe def main (_args : List String) : IO UInt32 := do
  if (← outDir.pathExists) then
    IO.FS.removeDirAll outDir
  IO.FS.createDirAll outDir

  let mut readings : List Reading := []
  let mut failures : List (String × String) := []

  let benches := microBenchmarks ++ tpchBenchmarks
  for b in benches do
    match ← runBenchmark b with
    | .ok r =>
        readings := readings.concat r
    | .error e =>
        failures := failures.concat (b.name, e)

  PartIiProject.Bench.printMsComparisonTable
    "SDQL performance comparison (single run; wall-clock ms)"
    "sdql-rs" "lean-gen" "lean/sdql"
    (readings.map fun r =>
      { name := r.name, leftMs := r.sdqlRsMs, rightMs := r.leanMs })

  if !failures.isEmpty then
    IO.eprintln ""
    IO.eprintln "Failures:"
    for (nm, err) in failures do
      IO.eprintln s!"- {nm}: {err}"
    return 1

  return 0

end Performance

unsafe def main (args : List String) : IO UInt32 :=
  Performance.main args
