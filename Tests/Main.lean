import PartIiProject.CodegenRust
import Tests.Cases
import PartIiProject.SurfaceCore
import Lean

open PartIiProject
open System

structure TestResult where
  name : String
  expected : String
  got : Option String
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

/- Render Rust literals for runtime arguments -/
mutual
private unsafe def rustLitHList : {l : List Ty} → HList Ty.denote l → List String
  | [], .nil => []
  | _ :: ts, .cons h t => rustLit h :: rustLitHList t

private unsafe def rustLit : {t : Ty} → t.denote → String
  | .int, n => toString n
  | .bool, b => if b then "true" else "false"
  | .real, n => toString n
  | .string, s => s!"String::from(\"{s}\")"
  | .record l, r =>
      let parts := rustLitHList r
      "(" ++ String.intercalate ", " parts ++ ")"
  | .dict kTy vTy, d =>
      let start := "std::collections::BTreeMap::new()"
      d.map.foldl (fun acc k v => s!"map_insert({acc}, {rustLit (t := kTy) k}, {rustLit (t := vTy) v})") start
end

unsafe def runCase (c : Tests.Cases.TestCase) : IO TestResult := do
  IO.FS.createDirAll outDir
  match c with
  | .program name sp expected =>
      -- Lower to core program and render via program-level codegen
      let cp := PartIiProject.ToCore.trProg sp
      let rs := PartIiProject.renderRustProgShown cp
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
      return { name, expected, got := some outStr }

def formatResult (r : TestResult) : String :=
  match r.got with
  | some s => if s == r.expected then s!"[PASS] {r.name}" else s!"[FAIL] {r.name}: expected {r.expected}, got {s}"
  | none => s!"[ERROR] {r.name}: {r.stderr.getD "unknown error"}"

def anyFailures (rs : List TestResult) : Bool :=
  rs.any (fun r => match r.got with
                   | some s => s != r.expected
                   | none => Bool.true)

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
