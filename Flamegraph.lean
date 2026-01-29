import PartIiProject.CodegenRust
import PartIiProject.Bench.Common
import PartIiProject.SyntaxSDQLProg
import Tests.Cases
import Lean
import Std

open PartIiProject
open PartIiProject.Bench
open System

namespace Flamegraph

def outDir : FilePath := FilePath.mk ".sdql-flamegraph-out"
def runtimeSrcRel : FilePath := FilePath.mk "sdql_runtime.rs"

unsafe structure Benchmark where
  name : String
  prog : SProg2
  env : List (String × String)

unsafe def benchmarkFromCase : Tests.Cases.TestCase -> Option Benchmark
  | .programRef name p _ env => some { name := name, prog := p, env := env }
  | _ => none

unsafe def collectBenchmarks (cs : List Tests.Cases.TestCase) : List Benchmark :=
  cs.foldr (fun c acc =>
    match benchmarkFromCase c with
    | some b => b :: acc
    | none => acc) []

unsafe def tpchBenchmarks : List Benchmark :=
  collectBenchmarks Tests.Cases.tpchCases ++
  collectBenchmarks Tests.Cases.tpchCasesSF001

structure Paths where
  rootDir : FilePath
  baseDir : FilePath
  cargoDir : FilePath
  cargoBinDir : FilePath
  cargoTargetDir : FilePath
  manifestPath : FilePath
  flamegraphDir : FilePath
  runtimeSrc : FilePath
  runtimeDst : FilePath

def mkPaths (rootDir : FilePath) : Paths :=
  let baseDir := rootDir / outDir
  let cargoDir := baseDir / "cargo"
  let cargoBinDir := cargoDir / "src" / "bin"
  let cargoTargetDir := baseDir / "cargo-target"
  let manifestPath := cargoDir / "Cargo.toml"
  let flamegraphDir := baseDir / "svgs"
  let runtimeSrc := rootDir / runtimeSrcRel
  let runtimeDst := cargoBinDir / "sdql_runtime.rs"
  { rootDir := rootDir
    baseDir := baseDir
    cargoDir := cargoDir
    cargoBinDir := cargoBinDir
    cargoTargetDir := cargoTargetDir
    manifestPath := manifestPath
    flamegraphDir := flamegraphDir
    runtimeSrc := runtimeSrc
    runtimeDst := runtimeDst
  }

def absolutizeTpchEnv (rootDir : FilePath) (env : List (String × String)) : List (String × String) :=
  env.map (fun (k, v) =>
    if k == "TPCH_DATASET_PATH" then
      let path := FilePath.mk v
      if path.isAbsolute then
        (k, v)
      else
        (k, (rootDir / path).toString)
    else
      (k, v))

def rewriteLoadPathForFlamegraph (rootDir : FilePath) (path : String) : String :=
  if path.startsWith "datasets/tpch/" then
    path
  else
    let fp := FilePath.mk path
    if fp.isAbsolute then path else (rootDir / fp).toString

unsafe def rewriteLoadPathsForFlamegraph (rootDir : FilePath) (p : SProg2) : SProg2 :=
  { p with loadPaths := p.loadPaths.map (rewriteLoadPathForFlamegraph rootDir) }

def renderCargoToml (binNames : List String) : String :=
  let header := String.intercalate "\n"
    [ "[package]"
    , "name = \"sdql_flamegraphs\""
    , "version = \"0.1.0\""
    , "edition = \"2021\""
    , "autobins = false"
    , ""
    , "[profile.release]"
    , "debug = true"
    ]
  let mkBin (name : String) : String :=
    String.intercalate "\n"
      [ "[[bin]]"
      , s!"name = \"{name}\""
      , s!"path = \"src/bin/{name}.rs\""
      ]
  let bins := binNames.map mkBin
  String.intercalate "\n\n" (header :: bins)

unsafe def writeCargoProject (paths : Paths) (bins : List Benchmark) : IO Unit := do
  IO.FS.createDirAll paths.cargoBinDir
  IO.FS.createDirAll paths.flamegraphDir
  PartIiProject.Bench.copyFile paths.runtimeSrc paths.runtimeDst
  let manifest := renderCargoToml (bins.map (fun b => b.name))
  PartIiProject.Bench.writeFile paths.manifestPath manifest
  for b in bins do
    let prog := rewriteLoadPathsForFlamegraph paths.rootDir b.prog
    let rs := PartIiProject.renderRustProg2Shown (ToCore2.trProg2 prog)
    let rsPath := paths.cargoBinDir / s!"{b.name}.rs"
    PartIiProject.Bench.writeFile rsPath rs

unsafe def runFlamegraph (paths : Paths) (b : Benchmark) : IO (Except String Unit) := do
  let svgPath := paths.flamegraphDir / s!"{b.name}.svg"
  let env :=
    absolutizeTpchEnv paths.rootDir b.env ++
    [ ("CARGO_TARGET_DIR", paths.cargoTargetDir.toString)
    , ("CARGO_PROFILE_RELEASE_DEBUG", "true")
    ]
  let args :=
    #[ "flamegraph"
     , "--bin", b.name
     , "--manifest-path", paths.manifestPath.toString
     , "-o", svgPath.toString
     ]
  let (code, out, err) ← PartIiProject.Bench.runProc "cargo" args (cwd? := some paths.cargoDir)
    (envVars := env)
  if code != 0 then
    return .error s!"cargo flamegraph failed for {b.name}:\n{out}\n{err}"
  return .ok ()

unsafe def main (_args : List String) : IO UInt32 := do
  let rootDir ← IO.currentDir
  let paths := mkPaths rootDir

  if (← paths.baseDir.pathExists) then
    IO.FS.removeDirAll paths.baseDir
  IO.FS.createDirAll paths.baseDir

  let benches := tpchBenchmarks
  writeCargoProject paths benches

  let mut failures : List (String × String) := []
  for b in benches do
    let res ← runFlamegraph paths b
    match res with
    | .ok () => pure ()
    | .error e => failures := failures.concat (b.name, e)

  if !failures.isEmpty then
    IO.eprintln ""
    IO.eprintln "Failures:"
    for (nm, err) in failures do
      IO.eprintln s!"- {nm}: {err}"
    return 1

  return 0

end Flamegraph

unsafe def main (args : List String) : IO UInt32 :=
  Flamegraph.main args
