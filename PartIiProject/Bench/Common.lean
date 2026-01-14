import PartIiProject.CodegenRust
import PartIiProject.SyntaxSDQLProg
import Lean
import Std

open PartIiProject
open System

namespace PartIiProject.Bench

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

def compileRust (rsPath binPath : FilePath) : IO (Except String Unit) := do
  let (code, _out, err) ← runProc "rustc"
    #["-O", "-C", "target-cpu=native", "-o", binPath.toString, rsPath.toString]
  if code != 0 then
    return .error err
  return .ok ()

def copyRuntime (runtimeSrc outDir : FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  copyFile runtimeSrc (outDir / "sdql_runtime.rs")

unsafe def compileProg2ToBin (outDir runtimeSrc : FilePath) (name : String) (cp : Prog2) :
    IO (Except String FilePath) := do
  copyRuntime runtimeSrc outDir
  let rs := PartIiProject.renderRustProg2Shown cp
  let rsPath := outDir / s!"{name}.rs"
  let binPath := outDir / s!"{name}.bin"
  writeFile rsPath rs
  match ← compileRust rsPath binPath with
  | .ok () => return .ok binPath
  | .error err => return .error err

unsafe def compileSProg2ToBin (outDir runtimeSrc : FilePath) (name : String) (sp : SProg2) :
    IO (Except String FilePath) := do
  compileProg2ToBin outDir runtimeSrc name (ToCore2.trProg2 sp)

def timeBinaryMs (binPath : FilePath) (envVars : List (String × String) := []) : IO (Except String Nat) := do
  let (code, ms) ← runTimedMs binPath.toString #[] (cwd? := none) (envVars := envVars)
  if code != 0 then
    return .error s!"Non-zero exit code {code} for {binPath.toString}"
  return .ok ms

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

end PartIiProject.Bench
