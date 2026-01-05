import PartIiProject.CodegenRust
import PartIiProject.Rust
import PartIiProject.Term2
import Tests.Cases
import Lean

open PartIiProject
open PartIiProject.Rust (withLocComments)
open System

inductive TestKind where
  | compileOnly
  | expectOutput
  | expectRefMatch
  deriving Inhabited

structure TestResult where
  name : String
  kind : TestKind
  expected? : Option String := none
  got? : Option String := none
  stderr? : Option String := none
  refBin? : Option String := none  -- Path to reference binary (for expectRefMatch)
  deriving Inhabited

def outDir : FilePath := FilePath.mk ".sdql-test-out"

/-- Path to the shared SDQL runtime file. -/
def runtimeSrc : FilePath := FilePath.mk "sdql_runtime.rs"

def writeFile (p : FilePath) (s : String) : IO Unit :=
  IO.FS.writeFile p s

/-- Copy a file from src to dst. -/
def copyFile (src dst : FilePath) : IO Unit := do
  let contents ← IO.FS.readFile src
  IO.FS.writeFile dst contents

def runProc (cmd : String) (args : Array String) (cwd? : Option FilePath := none) : IO (Nat × String × String) := do
  let out ← IO.Process.output { cmd := cmd, args := args, cwd := cwd? }
  let code := out.exitCode.toNat
  return (code, out.stdout, out.stderr)

def lastPathComponent (p : String) : String :=
  match (p.splitOn "/").getLast? with
  | some c => c
  | none => p

def ensureSdqlRsRefBin (refBinPath : String) : IO (Except String Unit) := do
  let refBin := FilePath.mk refBinPath
  let refBinExists ← refBin.pathExists
  if refBinExists then
    return .ok ()
  else
    let isSdqlRsTarget := refBinPath.startsWith "sdql-rs/target/release/"
    if isSdqlRsTarget then
      let binName := lastPathComponent refBinPath
      let srcPath := FilePath.mk s!"sdql-rs/src/bin/{binName}.rs"
      let srcExists ← srcPath.pathExists
      if srcExists then
        let (code, _out, err) ← runProc "cargo" #["build", "--release", "--bin", binName]
          (cwd? := some (FilePath.mk "sdql-rs"))
        if code != 0 then
          return .error s!"Failed to build reference binary {binName}:\n{err}"
        else
          let refBinExistsAfter ← refBin.pathExists
          if refBinExistsAfter then
            return .ok ()
          else
            return .error s!"Reference binary still missing after build: {refBinPath}"
      else
        return .error s!"Reference binary missing and no source found at {srcPath.toString}"
    else
      return .error s!"Reference binary not found: {refBinPath}"

def compileRust (rsPath binPath : FilePath) : IO (Nat × String) := do
  let (code, _out, err) ← runProc "rustc" #["-O", "-o", binPath.toString, rsPath.toString]
  return (code, err)

def runBinary (binPath : FilePath) : IO (Nat × String × String) := do
  runProc binPath.toString #[]

def runBinaryWithEnv (binPath : FilePath) (envVars : List (String × String)) : IO (Nat × String × String) := do
  -- Build environment array from envVars list
  let envArray := envVars.map (fun (k, v) => s!"{k}={v}")
  -- Use sh -c to set environment variables and run the binary
  let envPrefix := String.intercalate " " envArray
  let cmd := if envVars.isEmpty then binPath.toString else s!"{envPrefix} {binPath.toString}"
  let out ← IO.Process.output { cmd := "sh", args := #["-c", cmd] }
  let code := out.exitCode.toNat
  return (code, out.stdout, out.stderr)

/- Render Rust literals for runtime arguments -/
mutual
private unsafe def rustLitHList : {l : List Ty} → HList Ty.denote l → List String
  | [], .nil => []
  | _ :: ts, .cons h t => rustLit h :: rustLitHList t

private unsafe def rustLit : {t : Ty} → t.denote → String
  | .int, n => toString n
  | .bool, b => if b then "true" else "false"
  | .real, n => s!"Real::new({n})"
  | .maxProduct, n => s!"promote_max_product(Real::new({n}))"
  | .date, d => s!"Date::new({d.yyyymmdd})"
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
  -- Copy the shared runtime file to the output directory
  copyFile runtimeSrc (outDir / "sdql_runtime.rs")
  let compileProgram (name : String) (sp : SProg2) :
      IO (Except String FilePath) := do
        let cp := ToCore2.trProg2 sp
        -- Generate Rust code with source location comments for debugging
        let rs := PartIiProject.renderRustProg2Shown cp withLocComments
        let rsPath := outDir / s!"{name}.rs"
        let binPath := outDir / s!"{name}.bin"
        writeFile rsPath rs
        let (ccode, cerr) ← compileRust rsPath binPath
        if ccode != 0 then
          return .error cerr
        return .ok binPath
  match c with
  | .program name sp expected => do
      match ← compileProgram name sp with
      | .error err =>
          return { name, kind := .expectOutput, expected? := some expected, stderr? := some err }
      | .ok binPath =>
          let (rcode, rout, rerr) ← runBinary binPath
          if rcode != 0 then
            return { name, kind := .expectOutput, expected? := some expected, stderr? := some rerr }
          let outStr := rout.trim
          return { name, kind := .expectOutput, expected? := some expected, got? := some outStr }
  | .compileOnly name sp => do
      match ← compileProgram name sp with
      | .error err =>
          return { name, kind := .compileOnly, stderr? := some err }
      | .ok _ =>
          return { name, kind := .compileOnly }
  | .programRef name sp refBinPath envVars => do
      match ← ensureSdqlRsRefBin refBinPath with
      | .error err =>
          return { name, kind := .expectRefMatch, refBin? := some refBinPath, stderr? := some err }
      | .ok () => pure ()
      -- First, run the reference binary to get expected output
      let (refCode, refOut, refErr) ← runBinaryWithEnv (FilePath.mk refBinPath) envVars
      if refCode != 0 then
        return { name, kind := .expectRefMatch, refBin? := some refBinPath,
                 stderr? := some s!"Reference binary failed: {refErr}" }
      let expected := refOut.trim
      -- Then compile and run our generated code
      match ← compileProgram name sp with
      | .error err =>
          return { name, kind := .expectRefMatch, expected? := some expected,
                   refBin? := some refBinPath, stderr? := some err }
      | .ok binPath =>
          let (rcode, rout, rerr) ← runBinaryWithEnv binPath envVars
          if rcode != 0 then
            return { name, kind := .expectRefMatch, expected? := some expected,
                     refBin? := some refBinPath, stderr? := some rerr }
          let outStr := rout.trim
          return { name, kind := .expectRefMatch, expected? := some expected,
                   got? := some outStr, refBin? := some refBinPath }

def formatResult (r : TestResult) : String :=
  match r.stderr? with
  | some err => s!"[ERROR] {r.name}: {err}"
  | none =>
      match r.kind with
      | .compileOnly => s!"[PASS] {r.name} (compiled)"
      | .expectOutput =>
          match r.expected?, r.got? with
          | some expected, some got =>
              if got == expected then
                s!"[PASS] {r.name}"
              else
                s!"[FAIL] {r.name}: expected {expected}, got {got}"
          | _, _ => s!"[ERROR] {r.name}: missing output"
      | .expectRefMatch =>
          match r.expected?, r.got?, r.refBin? with
          | some expected, some got, some refBin =>
              if got == expected then
                s!"[PASS] {r.name} (matches {refBin})"
              else
                s!"[FAIL] {r.name}: expected (from {refBin}):\n  {expected}\ngot:\n  {got}"
          | _, _, _ => s!"[ERROR] {r.name}: missing output"

def anyFailures (rs : List TestResult) : Bool :=
  rs.any (fun r =>
    match r.kind with
    | .compileOnly =>
        r.stderr?.isSome
    | .expectOutput =>
        match r.stderr? with
        | some _ => Bool.true
        | none =>
            match r.expected?, r.got? with
            | some expected, some got => got != expected
            | _, _ => Bool.true
    | .expectRefMatch =>
        match r.stderr? with
        | some _ => Bool.true
        | none =>
            match r.expected?, r.got? with
            | some expected, some got => got != expected
            | _, _ => Bool.true)

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
