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
      | @_root_.AddM.recordA l fields =>
          let fname := match l.length with
                        | 0 => "tuple_add0"
                        | 1 => "tuple_add"
                        | 2 => "tuple_add2"
                        | 3 => "tuple_add3"
                        | 4 => "tuple_add4"
                        | _ => "tuple_add5" -- fallback for 5+
          .call fname [compile nameEnv t1, compile nameEnv t2]
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
   and prints the result using a tiny runtime library for SDQL values. -/
/-- Shared Rust runtime header used by test executables and program codegen.
    This defines a small `sdql_runtime` module and re-exports its items so
    generated code can call helpers directly or as `sdql_runtime::...`. -/
def rustRuntimeHeader : String :=
  String.intercalate "\n"
  [ "use std::collections::BTreeMap;"
  , "\n// Minimal runtime helpers used by generated code"
  , "pub mod sdql_runtime {"
  , "    use std::collections::BTreeMap;"
  , "    use std::ops::Add;"
  , "\n    // Insert without mutation at the call-site"
  , "    pub fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {"
  , "        m.insert(k, v);"
  , "        m"
  , "    }"
  , "\n    pub fn lookup_or_default<K: Ord, V: Clone>(m: BTreeMap<K, V>, k: K, default: V) -> V {"
  , "        match m.get(&k) {"
  , "            Some(v) => v.clone(),"
  , "            None => default,"
  , "        }"
  , "    }"
  , "\n    // Dictionary addition merges keys with value addition"
  , "    pub fn dict_add<K: Ord + Clone, V: Add<Output = V> + Clone>(a: BTreeMap<K, V>, b: BTreeMap<K, V>) -> BTreeMap<K, V> {"
  , "        let mut acc = a;"
  , "        for (k, v2) in b.into_iter() {"
  , "            if let Some(v1) = acc.get(&k).cloned() {"
  , "                acc.insert(k, v1 + v2);"
  , "            } else {"
  , "                acc.insert(k, v2);"
  , "            }"
  , "        }"
  , "        acc"
  , "    }"
  , "\n    // Tuple/record addition for small arities"
  , "    pub fn tuple_add0(a: (), _b: ()) -> () { a }"
  , "    pub fn tuple_add<T1: Add<Output = T1>>(a: (T1,), b: (T1,)) -> (T1,) { (a.0 + b.0,) }"
  , "    pub fn tuple_add2<T1: Add<Output = T1>, T2: Add<Output = T2>>(a: (T1, T2), b: (T1, T2)) -> (T1, T2) { (a.0 + b.0, a.1 + b.1) }"
  , "    pub fn tuple_add3<T1: Add<Output = T1>, T2: Add<Output = T2>, T3: Add<Output = T3>>(a: (T1, T2, T3), b: (T1, T2, T3)) -> (T1, T2, T3) { (a.0 + b.0, a.1 + b.1, a.2 + b.2) }"
  , "    pub fn tuple_add4<T1: Add<Output = T1>, T2: Add<Output = T2>, T3: Add<Output = T3>, T4: Add<Output = T4>>(a: (T1, T2, T3, T4), b: (T1, T2, T3, T4)) -> (T1, T2, T3, T4) { (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3) }"
  , "    pub fn tuple_add5<T1: Add<Output = T1>, T2: Add<Output = T2>, T3: Add<Output = T3>, T4: Add<Output = T4>, T5: Add<Output = T5>>(a: (T1, T2, T3, T4, T5), b: (T1, T2, T3, T4, T5)) -> (T1, T2, T3, T4, T5) { (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4) }"
  , "\n    // Generic stub loader: returns Default::default() and prints path"
  , "    pub fn load<T: Default>(_path: &str) -> T {"
  , "        // TODO: parse from file at runtime"
  , "        Default::default()"
  , "    }"
  , "\n    // Pretty-printing for SDQL values (mirrors Lean showValue)"
  , "    pub trait SDQLShow { fn show(&self) -> String; }"
  , "    impl SDQLShow for i64 { fn show(&self) -> String { self.to_string() } }"
  , "    impl SDQLShow for bool { fn show(&self) -> String { self.to_string() } }"
  , "    impl SDQLShow for String { fn show(&self) -> String { self.clone() } }"
  , "    impl<K: Ord + SDQLShow, V: SDQLShow> SDQLShow for BTreeMap<K, V> {"
  , "        fn show(&self) -> String {"
  , "            let mut s = String::new();"
  , "            s.push('{');"
  , "            for (k, v) in self.iter() {"
  , "                s.push_str(&format!(\"{} -> {}, \", k.show(), v.show()));"
  , "            }"
  , "            s.push('}');"
  , "            s"
  , "        }"
  , "    }"
  , "\n    // Tuple/record pretty-printing for small arities"
  , "    impl<T1: SDQLShow> SDQLShow for (T1,) { fn show(&self) -> String { format!(\"<{}>\", self.0.show()) } }"
  , "    impl<T1: SDQLShow, T2: SDQLShow> SDQLShow for (T1, T2) { fn show(&self) -> String { format!(\"<{}, {}>\", self.0.show(), self.1.show()) } }"
  , "    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow> SDQLShow for (T1, T2, T3) { fn show(&self) -> String { format!(\"<{}, {}, {}>\", self.0.show(), self.1.show(), self.2.show()) } }"
  , "    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow> SDQLShow for (T1, T2, T3, T4) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show()) } }"
  , "    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show()) } }"
  , "} // end module sdql_runtime"
  , "\n// Re-export runtime helpers at crate root for convenience"
  , "use sdql_runtime::*;"
  , "\n"
  ]

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

/- Program-level codegen ------------------------------------------------- -/

/-- Render a Rust program from a `Prog`. The generated program:
    - defines and re-exports a tiny runtime library (`sdql_runtime`),
    - loads each free variable from the provided file path via a stub `load`,
    - evaluates the compiled term, and
    - prints the pretty-printed result. -/
def renderRustProgShown (p : _root_.Prog) : String :=
  let header := rustRuntimeHeader
  -- Parameter names for free variables
  let paramName : (i : Fin p.n) → String := fun i => s!"arg{i.val}"
  -- Emit `let arg<i> : <Ty> = sdql_runtime::load::<Ty>("path");`
  let idxs := (List.finRange p.n)
  let paramDecls : List String := idxs.map (fun i =>
    let tyStr := Rust.showTy (coreTyToRustTy (p.fvar i))
    let nm := paramName i
    -- escape Rust string literal – here we assume paths are well-formed; add minimal escaping
    let path := (p.loadPaths i)
    let lit := path.replace "\\" "\\\\" |>.replace "\"" "\\\""
    s!"let {nm}: {tyStr} = sdql_runtime::load::<{tyStr}>(\"{lit}\");"
  )
  -- Compile the open term with the chosen names
  let expr := compileOpenToRustExpr paramName (p.term (rep := fun _ => String))
  let bodyExpr := Rust.showExpr expr 1
  let loadsStr := String.intercalate "\n" (paramDecls.map (fun s => "  " ++ s))
  let mainBody :=
    "fn main() {\n" ++
    loadsStr ++ "\n  " ++
    "let result = " ++ bodyExpr ++ ";\n  println!(\"{}\", SDQLShow::show(&result));\n}\n"
  header ++ mainBody

end PartIiProject
