import PartIiProject.CodegenRust
import Tests.Cases
import Lean

open PartIiProject
open System

structure TestResult where
  name : String
  expected : Int
  got : Option Int
  stderr : Option String := none
  deriving Inhabited

def outDir : FilePath := FilePath.mk ".sdql-test-out"

def writeFile (p : FilePath) (s : String) : IO Unit :=
  IO.FS.writeFile p s

def runProc (cmd : String) (args : Array String) (cwd? : Option FilePath := none) : IO (Nat × String × String) := do
  let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd? }
  let code := out.exitCode.toNat
  return (code, out.stdout, out.stderr)

def compileRust (rsPath binPath : FilePath) : IO (Nat × String) := do
  let (code, _out, err) ← runProc "rustc" #["-O", "-o", binPath.toString, rsPath.toString]
  return (code, err)

def runBinary (binPath : FilePath) : IO (Nat × String × String) := do
  runProc binPath.toString #[]

def runCase (c : Tests.Cases.TestCase) : IO TestResult := do
  IO.FS.createDirAll outDir
  match c with
  | .mk name t expected =>
      let rs := PartIiProject.renderRustMeasured t
      let rsPath := outDir / s!"{name}.rs"
      let binPath := outDir / s!"{name}.bin"
      writeFile rsPath rs
      let (ccode, cerr) ← compileRust rsPath binPath
      if ccode != 0 then
        return { name, expected, got := none, stderr := some cerr }
      let (rcode, rout, rerr) ← runBinary binPath
      if rcode != 0 then
        return { name, expected, got := none, stderr := some rerr }
      let outStr := rout.trim
      match outStr.toInt? with
      | some n =>
          return { name, expected, got := some n }
      | none =>
          return { name, expected, got := none, stderr := some s!"Non-integer output: {outStr}" }

def formatResult (r : TestResult) : String :=
  match r.got with
  | some n => if n == r.expected then s!"[PASS] {r.name}" else s!"[FAIL] {r.name}: expected {r.expected}, got {n}"
  | none => s!"[ERROR] {r.name}: {r.stderr.getD "unknown error"}"

def anyFailures (rs : List TestResult) : Bool :=
  rs.any (fun r => match r.got with
                   | some n => n != r.expected
                   | none => true)

unsafe def main (_args : List String) : IO UInt32 := do
  let mut results : List TestResult := []
  for c in Tests.Cases.cases do
    let r ← runCase c
    IO.println (formatResult r)
    results := results.concat r
  if anyFailures results then
    return 1
  else
    return 0
