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

/- Render Rust literals for runtime arguments -/
mutual
private unsafe def rustLitHList : {l : List Ty} → HList Ty.denote l → List String
  | [], .nil => []
  | _ :: ts, .cons h t => rustLit h :: rustLitHList t

private unsafe def rustLit : {t : Ty} → t.denote → String
  | .int, n => toString n
  | .bool, b => if b then "true" else "false"
  | .string, s => s!"String::from(\"{s}\")"
  | .record l, r =>
      let parts := rustLitHList r
      "(" ++ String.intercalate ", " parts ++ ")"
  | .dict dom range, d =>
      let start := "std::collections::BTreeMap::new()"
      d.map.foldl (fun acc k v => s!"map_insert({acc}, {rustLit (t := dom) k}, {rustLit (t := range) v})") start
end

unsafe def runCase (c : Tests.Cases.TestCase) : IO TestResult := do
  IO.FS.createDirAll outDir
  match c with
  | .closed name t expected =>
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
  | .openCase (n := n) (fvar := fvar) name _ termCode args expected =>
      -- Build a Rust program with a function for the open term and a main that calls it with concrete args
      -- Parameter naming convention must match Codegen for free variables
      let paramName : (i : Fin n) → String := fun i => s!"arg{i.val}"
      let fnSrc := PartIiProject.renderRustFn name paramName termCode
      -- Build main with concrete values
      let paramDecls : List String :=
        (List.finRange n).map (fun i => s!"let {paramName i} = {rustLit (t := fvar i) (args i)};")
      let callArgs := (List.finRange n).map (fun i => paramName i)
      let callArgsStr := String.intercalate ", " callArgs
      let mainBody :=
        "fn main() {\n" ++
        String.intercalate "\n" (paramDecls.map (fun s => "  " ++ s)) ++ "\n  " ++
        "let result = " ++ name ++ "(" ++ callArgsStr ++ ");\n  println!(\"{}\", SDQLMeasure::measure(&result));\n}\n"
      let rs := PartIiProject.rustRuntimeHeader ++ fnSrc ++ mainBody
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
      | some n => return { name, expected, got := some n }
      | none => return { name, expected, got := none, stderr := some s!"Non-integer output: {outStr}" }

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
