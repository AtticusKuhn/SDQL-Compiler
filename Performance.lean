import PartIiProject.CodegenRust
import PartIiProject.SyntaxSDQLProg
import Tests.Cases
import Lean
import Std

open PartIiProject
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

def writeFile (p : FilePath) (s : String) : IO Unit :=
  IO.FS.writeFile p s

def copyFile (src dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readFile src
  IO.FS.writeFile dst contents

def absPath (p : FilePath) : IO FilePath := do
  let cwd ← IO.currentDir
  pure (cwd / p)

def runProc (cmd : String) (args : Array String) (cwd? : Option FilePath := none)
    (envVars : List (String × String) := []) : IO (Nat × String × String) := do
  let env : Array (String × Option String) := envVars.toArray.map (fun (k, v) => (k, some v))
  let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd?, env := env, inheritEnv := Bool.true }
  return (out.exitCode.toNat, out.stdout, out.stderr)

def runProcDiscardStdout (cmd : String) (args : Array String) (cwd? : Option FilePath := none)
    (envVars : List (String × String) := []) : IO (Nat × String) := do
  let env : Array (String × Option String) := envVars.toArray.map (fun (k, v) => (k, some v))
  let child ← IO.Process.spawn {
    cmd := cmd,
    args := args,
    cwd := cwd?,
    env := env,
    inheritEnv := Bool.true,
    stdout := .null,
    stderr := .piped,
  }
  let code := (← child.wait).toNat
  let err ← child.stderr.readToEnd
  return (code, err)

def runTimedMs (cmd : String) (args : Array String) (cwd? : Option FilePath := none)
    (envVars : List (String × String) := []) : IO (Nat × Nat) := do
  let env : Array (String × Option String) := envVars.toArray.map (fun (k, v) => (k, some v))
  let start ← IO.monoMsNow
  let child ← IO.Process.spawn {
    cmd := cmd,
    args := args,
    cwd := cwd?,
    env := env,
    stdout := .null,
    stderr := .null,
  }
  let code := (← child.wait).toNat
  let stop ← IO.monoMsNow
  return (code, stop - start)

def lastPathComponent (p : String) : String :=
  match (p.splitOn "/").getLast? with
  | some c => c
  | none => p

def compileRust (rsPath binPath : FilePath) : IO (Except String Unit) := do
  let (code, _out, err) ← runProc "rustc"
    #["-O", "-C", "target-cpu=native", "-o", binPath.toString, rsPath.toString]
  if code != 0 then
    return .error err
  return .ok ()

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
  let (code, _out, err) ← runProc "cargo" #["build", "--release", "--bin", binName]
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
  let absOutDir ← absPath outDir
  let cargoTargetDir := absOutDir / "sdql-rs-target"
  let releaseDir := cargoTargetDir / "release"

  IO.FS.createDirAll absOutDir
  IO.FS.createDirAll cargoTargetDir

  let before ← listReleaseBins releaseDir
  let sdqlPath := absOutDir / "sdqlrs_micro.sdql"
  writeFile sdqlPath sdqlSrc

  let (code, err) ← runProcDiscardStdout "cargo"
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

def padLeft (width : Nat) (s : String) : String :=
  if s.length >= width then s else String.mk (List.replicate (width - s.length) ' ') ++ s

def padRight (width : Nat) (s : String) : String :=
  if s.length >= width then s else s ++ String.mk (List.replicate (width - s.length) ' ')

def pad3 (n : Nat) : String :=
  let s := toString n
  if s.length >= 3 then s else String.mk (List.replicate (3 - s.length) '0') ++ s

def ratioMilli (numer denom : Nat) : Nat :=
  if denom == 0 then 0 else (numer * 1000) / denom

def ratioString (numer denom : Nat) : String :=
  if denom == 0 then "n/a"
  else
    let rm := ratioMilli numer denom
    let whole := rm / 1000
    let frac := rm % 1000
    s!"{whole}.{pad3 frac}×"

unsafe def compileLeanGeneratedBin (name : String) (sp : SProg2) : IO (Except String FilePath) := do
  IO.FS.createDirAll outDir
  copyFile runtimeSrc (outDir / "sdql_runtime.rs")
  let cp := ToCore2.trProg2 sp
  let rs := PartIiProject.renderRustProg2Shown cp
  let rsPath := outDir / s!"{name}_lean.rs"
  let binPath := outDir / s!"{name}_lean.bin"
  writeFile rsPath rs
  match ← compileRust rsPath binPath with
  | .error err => return .error err
  | .ok () => return .ok binPath

def timeBinary (binPath : FilePath) (envVars : List (String × String)) : IO (Except String Nat) := do
  let (code, ms) ← runTimedMs binPath.toString #[] (cwd? := none) (envVars := envVars)
  if code != 0 then
    return .error s!"Non-zero exit code {code} for {binPath.toString}"
  return .ok ms

unsafe def runBenchmark (b : Benchmark) : IO (Except String Reading) := do
  let refPath ← b.sdqlRsBin
  let refBinPath ←
    match refPath with
    | .ok p => pure p
    | .error e => return .error e

  let leanBinPath ←
    match ← compileLeanGeneratedBin b.name b.prog with
    | .ok p => pure p
    | .error e => return .error s!"Lean→Rust compile failed for {b.name}:\n{e}"

  let sdqlMs ←
    match ← timeBinary refBinPath b.env with
    | .ok ms => pure ms
    | .error e => return .error s!"sdql-rs run failed for {b.name} ({refBinPath.toString}):\n{e}"

  let leanMs ←
    match ← timeBinary leanBinPath b.env with
    | .ok ms => pure ms
    | .error e => return .error s!"Lean-generated run failed for {b.name} ({leanBinPath.toString}):\n{e}"

  return .ok {
    name := b.name
    sdqlRsMs := sdqlMs
    leanMs := leanMs
    ratioMilli := ratioMilli leanMs sdqlMs
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

def printTable (readings : List Reading) : IO Unit := do
  if readings.isEmpty then
    IO.println "No benchmarks ran."
    return

  let nameW := readings.foldl (fun w r => max w r.name.length) 4
  let colW := 12

  IO.println "SDQL performance comparison (single run; wall-clock ms)"
  IO.println (padRight nameW "case" ++ "  " ++
    padLeft colW "sdql-rs" ++ "  " ++
    padLeft colW "lean-gen" ++ "  " ++
    padLeft colW "lean/sdql")
  IO.println (String.mk (List.replicate (nameW + 2 + colW*3 + 4) '-'))

  for r in readings do
    IO.println (padRight nameW r.name ++ "  " ++
      padLeft colW s!"{r.sdqlRsMs}ms" ++ "  " ++
      padLeft colW s!"{r.leanMs}ms" ++ "  " ++
      padLeft colW (ratioString r.leanMs r.sdqlRsMs))

  let totalSdql := readings.foldl (fun s r => s + r.sdqlRsMs) 0
  let totalLean := readings.foldl (fun s r => s + r.leanMs) 0
  IO.println (String.mk (List.replicate (nameW + 2 + colW*3 + 4) '-'))
  IO.println (padRight nameW "TOTAL" ++ "  " ++
    padLeft colW s!"{totalSdql}ms" ++ "  " ++
    padLeft colW s!"{totalLean}ms" ++ "  " ++
    padLeft colW (ratioString totalLean totalSdql))

def compileRust2 (rsPath binPath : FilePath) : IO (Nat × String) := do
  let (code, _out, err) ← runProc "rustc" #["-O", "-o", binPath.toString, rsPath.toString]
  return (code, err)
unsafe def compileProgram (name : String) (sp : SProg2) :
  IO (Except String FilePath) := do
    let cp := ToCore2.trProg2 sp
    -- Generate Rust code with source location comments for debugging
    let rs := PartIiProject.renderRustProg2Shown cp
    let rsPath := outDir / s!"{name}.rs"
    let binPath := outDir / s!"{name}.bin"
    writeFile rsPath rs
    let (ccode, cerr) ← compileRust2 rsPath binPath
    if ccode != 0 then
      return .error cerr
    return .ok binPath
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

  printTable readings

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
