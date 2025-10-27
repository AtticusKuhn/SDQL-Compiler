import PartIiProject.Term
import PartIiProject.Rust

-- set_option linter.style.longLine false

namespace PartIiProject

open Rust

/- Type translation ------------------------------------------------------- -/
def coreTyToRustTy : _root_.Ty → Rust.Ty
  | .bool => .bool
  | .int => .i64
  | .string => .str
  | .dict k v => .map (coreTyToRustTy k) (coreTyToRustTy v)
  | .record l => .tuple (l.map coreTyToRustTy)

/- Zeros for additive monoids (used for lookup defaults and sum inits). -/
mutual
  def zerosForHList : {l : List _root_.Ty} → _root_.HList _root_.AddM l → List Rust.Expr
    | [], .nil => []
    | _ :: ts, .cons h t => zeroOfAddM h :: zerosForHList t

  def zeroOfAddM : {t : _root_.Ty} → _root_.AddM t → Rust.Expr
    | .bool, .boolA => .litBool false
    | .int, .intA => .litInt 0
    | .dict _ _, @_root_.AddM.dictA _ _ _ => .mapEmpty
    | .record _, @_root_.AddM.recordA _ fields => .tuple (zerosForHList fields)
end

/- Compilation from core terms to Rust simplified AST -------------------- -/
namespace Compile

mutual
  /- Compile an SDQL term into a Rust simplified AST expression.
     `nameEnv` maps each runtime parameter (free variable) index to its Rust identifier. -/
  def compile {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
      (nameEnv : Fin n → String)
      : _root_.Term' (fun _ => String) fvar ty → Rust.Expr
  | .var v => .var v
  | .freeVariable i => .var (nameEnv i)
  | .constInt n => .litInt n
  | .constBool b => .litBool b
  | .constString s => .litString s
  | .constRecord fields => .tuple (compileRecordFields nameEnv fields)
  | .emptyDict => .mapEmpty
  | .dictInsert k v d => .mapInsert (compile nameEnv d) (compile nameEnv k) (compile nameEnv v)
  | .not t => .not (compile nameEnv t)
  | .ite c t f => .ite (compile nameEnv c) (compile nameEnv t) (compile nameEnv f)
  | .letin t1 f =>
      -- Use a conventional binder name "x" as in the pretty-printer
      let xName := "x"
      .block
        [ .letDecl false xName (some (compile nameEnv t1)) ]
        (compile nameEnv (f xName))
  | .add a t1 t2 =>
      match a with
      | .boolA => .binop .bitXor (compile nameEnv t1) (compile nameEnv t2)
      | .intA => .binop .add (compile nameEnv t1) (compile nameEnv t2)
      | @_root_.AddM.dictA dom range aRange => .call "dict_add" [compile nameEnv t1, compile nameEnv t2]
      | @_root_.AddM.recordA l fields => .call "tuple_add" [compile nameEnv t1, compile nameEnv t2]
  | .mul _ _ e1 e2 =>
      -- We surface SDQL's shape-directed multiply as a helper call.
      .call "sdql_mul" [compile nameEnv e1, compile nameEnv e2]
  | .lookup aRange d k =>
      let deflt := zeroOfAddM aRange
      .lookupOrDefault (compile nameEnv d) (compile nameEnv k) deflt
  | .sum a d f =>
      -- Emit a block with an accumulator and a for-loop over (k,v) in d
      let accName := "acc"
      let kName := "k"
      let vName := "v"
      let accInit := zeroOfAddM a
      let bodyStmt : Rust.Stmt :=
        let bodyExpr := compile nameEnv (f kName vName)
        let updated :=
          match a with
          | .boolA => .binop .bitXor (.var accName) bodyExpr
          | .intA => .binop .add (.var accName) bodyExpr
          | @_root_.AddM.dictA dom range aRange => .call "dict_add" [.var accName, bodyExpr]
          | @_root_.AddM.recordA l fields => .call "tuple_add" [.var accName, bodyExpr]
        Rust.Stmt.assign accName updated
      .block
        [ .letDecl true accName (some accInit)
        , Rust.Stmt.forKV kName vName (compile nameEnv d) [bodyStmt]
        ]
        (.var accName)
  | .proj l r i => .call "proj" [compile nameEnv r, .litInt (Int.ofNat i)]

  /- Compile a record literal represented as an HList of sub-terms. -/
  def compileRecordFields {n : Nat} {fvar : Fin n → _root_.Ty}
    (nameEnv : Fin n → String)
    : {l : List _root_.Ty} → _root_.HList (_root_.Term' (fun _ => String) fvar) l → List Rust.Expr
    | _, .nil => []
    | _, .cons h t => compile nameEnv h :: compileRecordFields nameEnv t
end

end Compile

/- Entry points ---------------------------------------------------------- -/

def compileToRustExpr {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.Term fvar ty) : Rust.Expr :=
  -- Closed-term compilation: there are no free variables, so the `nameEnv` is unused.
  -- We still provide a total function for completeness.
  Compile.compile (fun i => s!"arg{i.val}") (t (rep := fun _ => String))

def renderRust {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.Term fvar ty) : String :=
  Rust.wrapAsMain (compileToRustExpr t)

/- Render a standalone Rust program that computes the compiled expression
   and prints a simple numeric "measure" of the result for comparison
   against Lean's evaluator. This avoids full pretty-printing of nested
   dictionaries/records while still catching semantic regressions. -/
/-- Shared Rust runtime header used by test executables. -/
def rustRuntimeHeader : String :=
  "use std::collections::BTreeMap;\n" ++
  "\n" ++
  "// Minimal runtime helpers used by generated code\n" ++
  "fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {\n" ++
  "    m.insert(k, v);\n" ++
  "    m\n" ++
  "}\n" ++
  "fn lookup_or_default<K: Ord, V: Clone>(m: BTreeMap<K, V>, k: K, default: V) -> V {\n" ++
  "    match m.get(&k) {\n" ++
  "        Some(v) => v.clone(),\n" ++
  "        None => default,\n" ++
  "    }\n" ++
  "}\n" ++
  "\n" ++
  "// Pretty-printing for SDQL values (mirrors Lean showValue)\n" ++
  "pub trait SDQLShow { fn show(&self) -> String; }\n" ++
  "impl SDQLShow for i64 { fn show(&self) -> String { self.to_string() } }\n" ++
  "impl SDQLShow for bool { fn show(&self) -> String { self.to_string() } }\n" ++
  "impl SDQLShow for String { fn show(&self) -> String { self.clone() } }\n" ++
  "impl<K: Ord + SDQLShow, V: SDQLShow> SDQLShow for BTreeMap<K, V> {\n" ++
  "    fn show(&self) -> String {\n" ++
  "        let mut s = String::new();\n" ++
  "        s.push('{');\n" ++
  "        for (k, v) in self.iter() {\n" ++
  "            s.push_str(&format!(\"{} -> {}, \", k.show(), v.show()));\n" ++
  "        }\n" ++
  "        s.push('}');\n" ++
  "        s\n" ++
  "    }\n" ++
  "}\n" ++
  "\n" ++
  "// Tuple/record pretty-printing for small arities\n" ++
  "impl<T1: SDQLShow> SDQLShow for (T1,) { fn show(&self) -> String { format!(\"<{}>\", self.0.show()) } }\n" ++
  "impl<T1: SDQLShow, T2: SDQLShow> SDQLShow for (T1, T2) { fn show(&self) -> String { format!(\"<{}, {}>\", self.0.show(), self.1.show()) } }\n" ++
  "impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow> SDQLShow for (T1, T2, T3) { fn show(&self) -> String { format!(\"<{}, {}, {}>\", self.0.show(), self.1.show(), self.2.show()) } }\n" ++
  "impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow> SDQLShow for (T1, T2, T3, T4) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show()) } }\n" ++
  "impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show()) } }\n" ++
  "\n"

def renderRustShown {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.Term fvar ty) : String :=
  let expr := compileToRustExpr t
  let header := rustRuntimeHeader
  let body :=
    let e := Rust.showExpr expr 1
    "fn main() {\n  let result = " ++ e ++ ";\n  println!(\"{}\", SDQLShow::show(&result));\n}\n"
  header ++ body

/- Open-term compilation helpers. --------------------------------------- -/

/-- Compile an open term (with runtime parameters) to a Rust AST, given a naming environment. -/
def compileOpenToRustExpr {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (nameEnv : Fin n → String)
    (t : _root_.Term' (fun _ => String) fvar ty) : Rust.Expr :=
  Compile.compile nameEnv t

/-- Render a Rust function `fn <name>(params...) -> Ret { <expr> }` for an open term. -/
def renderRustFn {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (name : String)
    (paramNames : Fin n → String)
    (t : _root_.Term' (fun _ => String) fvar ty)
    : String :=
  -- Build the parameter list from `paramNames` and `fvar`'s compile-time types.
  let paramDecls : List String :=
    (List.finRange n).map (fun i => s!"{paramNames i}: {Rust.showTy (coreTyToRustTy (fvar i))}")
  let paramsStr := String.intercalate ", " paramDecls
  let retStr := Rust.showTy (coreTyToRustTy (ty))
  let body := Rust.showExpr (compileOpenToRustExpr paramNames t) 1
  let header := "pub fn " ++ name ++ "(" ++ paramsStr ++ ") -> " ++ retStr ++ " {\n"
  let footer := "\n}\n"
  header ++ "  " ++ body ++ footer

end PartIiProject
