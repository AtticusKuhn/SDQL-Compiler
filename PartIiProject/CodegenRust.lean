import PartIiProject.Term
import PartIiProject.Rust

-- set_option linter.style.longLine false

namespace PartIiProject

open Rust

/- Type translation ------------------------------------------------------- -/
def coreTyToRustTy : _root_.Ty → Rust.Ty
  | .bool => .bool
  | .real => .real
  | .date => .date
  | .int => .i64
  | .string => .str
  | .dict k v => .map (coreTyToRustTy k) (coreTyToRustTy v)
  | .record l => .tuple (l.map coreTyToRustTy)

/- Zeros for additive monoids (used for lookup defaults and sum inits). -/
mutual
  def zerosForHListLoc : {l : List _root_.Ty} → _root_.HList _root_.AddM l → List Rust.ExprLoc
    | [], .nil => []
    | _ :: _, .cons h t => zeroOfAddMLoc h :: zerosForHListLoc t

  def zeroOfAddMLoc : {t : _root_.Ty} → _root_.AddM t → Rust.ExprLoc
    | .bool, .boolA => ExprLoc.withUnknownLoc (.litBool false)
    | .real, .realA => ExprLoc.withUnknownLoc (.litReal 0.0)
    | .date, .dateA => ExprLoc.withUnknownLoc (.litDate 10101)  -- dummy date (0001-01-01)
    | .int, .intA => ExprLoc.withUnknownLoc (.litInt 0)
    | .string, .stringA => ExprLoc.withUnknownLoc (.litString "")
    | .dict _ _, @_root_.AddM.dictA _ _ _ => ExprLoc.withUnknownLoc .mapEmpty
    | .record _, @_root_.AddM.recordA _ fields => ExprLoc.withUnknownLoc (.tuple (zerosForHListLoc fields))
end

/- Compilation from core terms to Rust simplified AST -------------------- -/
namespace Compile

/-- State monad for fresh name generation. -/
abbrev FreshM := StateM Nat

/-- Get a fresh identifier suffix, incrementing the counter. -/
def fresh : FreshM Nat := modifyGet fun n => (n, n + 1)

/-- Generate a fresh variable name with the given prefix. -/
def freshName (pfx : String) : FreshM String := do
  let n ← fresh
  return s!"{pfx}{n}"

/-- Compile addition based on the additive monoid evidence. -/
def compileAdd {ty : _root_.Ty} (a : _root_.AddM ty) (lhs rhs : Rust.ExprLoc) : Rust.Expr :=
  match a with
  | .boolA => .binop .bitXor lhs rhs
  | .realA => .binop .add lhs rhs
  | .dateA => rhs.expr  -- date "addition" just takes rhs (overwrite)
  | .intA => .binop .add lhs rhs
  | .stringA => .binop .add lhs rhs
  | @_root_.AddM.dictA _ _ _ => .call "dict_add" [lhs, rhs]
  | @_root_.AddM.recordA l _ =>
      let fname := match l.length with
        | 0 => "tuple_add0" | 1 => "tuple_add" | 2 => "tuple_add2"
        | 3 => "tuple_add3" | 4 => "tuple_add4" | _ => "tuple_add5"
      .call fname [lhs, rhs]

/-- Compile a builtin function application. -/
def compileBuiltin {argTy resTy : _root_.Ty} (b : _root_.BuiltinFn argTy resTy) (argExpr : Rust.ExprLoc) : Rust.Expr :=
  match b with
  | .And => .call "ext_and" [argExpr]
  | .Or => .call "ext_or" [argExpr]
  | .Eq _ => .call "ext_eq" [argExpr]
  | .Leq _ => .call "ext_leq" [argExpr]
  | .Sub _ => .call "ext_sub" [argExpr]
  | .StrEndsWith => .call "ext_str_ends_with" [argExpr]
  | .Dom => .call "ext_dom" [ExprLoc.withUnknownLoc (Rust.Expr.borrow argExpr)]
  | .Range => .call "ext_range" [argExpr]
  | .DateLit yyyymmdd => .litDate yyyymmdd

mutual
  /-- Compile an SDQL located term into a Rust located expression.
      `nameEnv` maps each runtime parameter (free variable) index to its Rust identifier.
      Source locations are propagated from the SDQL term to the Rust expression. -/
  def compileLoc' {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
      (nameEnv : Fin n → String)
      (t : _root_.TermLoc' (fun _ => String) fvar ty) : FreshM Rust.ExprLoc := do
    let ⟨loc, inner⟩ := t
    let expr ← compile' nameEnv loc inner
    return Rust.ExprLoc.mk loc expr

  /-- Compile an SDQL term into a Rust expression.
      `nameEnv` maps each runtime parameter (free variable) index to its Rust identifier.
      `loc` is the source location from the parent TermLoc' wrapper. -/
  def compile' {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
      (nameEnv : Fin n → String) (loc : SourceLocation)
      (t : _root_.Term' (fun _ => String) fvar ty) : FreshM Rust.Expr := do
    match t with
    | .var v => return .var v
    | .freeVariable i => return .var (nameEnv i)
    | .constInt n => return .litInt n
    | .constReal r => return .litReal r
    | .constBool b => return .litBool b
    | .constString s => return .litString s
    | .constRecord fields => return .tuple (← compileRecordFields' nameEnv fields)
    | .emptyDict => return .mapEmpty
    | .dictInsert k v d =>
        return .mapInsert (← compileLoc' nameEnv d) (← compileLoc' nameEnv k) (← compileLoc' nameEnv v)
    | .not t => return .not (← compileLoc' nameEnv t)
    | .ite c t f => return .ite (← compileLoc' nameEnv c) (← compileLoc' nameEnv t) (← compileLoc' nameEnv f)
    | .letin t1 f =>
        let t1Expr ← compileLoc' nameEnv t1
        let binderName ← freshName "x"
        let bodyExpr ← compileLoc' nameEnv (f binderName)
        return .block [Rust.StmtLoc.mk loc (.letDecl false binderName (some t1Expr))] bodyExpr
    | .add a t1 t2 =>
        let lhs ← compileLoc' nameEnv t1
        let rhs ← compileLoc' nameEnv t2
        return compileAdd a lhs rhs
    | .mul _ _ e1 e2 =>
        return .call "sdql_mul" [← compileLoc' nameEnv e1, ← compileLoc' nameEnv e2]
    | .lookup aRange d k =>
        return .lookupOrDefault (← compileLoc' nameEnv d) (← compileLoc' nameEnv k) (zeroOfAddMLoc aRange)
    | .sum a d f =>
        let de ← compileLoc' nameEnv d
        let accName ← freshName "acc"
        let kName ← freshName "k"
        let vName ← freshName "v"
        let bodyExpr ← compileLoc' nameEnv (f kName vName)
        let accVar := ExprLoc.withUnknownLoc (.var accName)
        let updated := compileAdd a accVar bodyExpr
        let loop := Rust.StmtLoc.mk loc (.forKV kName vName de [Rust.StmtLoc.mk loc (.assign accName (ExprLoc.withUnknownLoc updated))])
        return .block
          [ Rust.StmtLoc.mk loc (.letDecl true accName (some (zeroOfAddMLoc a)))
          , loop ]
          (ExprLoc.withUnknownLoc (.var accName))
    | .proj _ r i => return .tupleProj (← compileLoc' nameEnv r) i
    | .builtin b a =>
        let argExpr ← compileLoc' nameEnv a
        return compileBuiltin b argExpr

  /-- Compile a record literal represented as an HList of located sub-terms. -/
  def compileRecordFields' {n : Nat} {fvar : Fin n → _root_.Ty}
      (nameEnv : Fin n → String)
      : {l : List _root_.Ty} → _root_.HList (_root_.TermLoc' (fun _ => String) fvar) l → FreshM (List Rust.ExprLoc)
    | _, .nil => return []
    | _, .cons h t => return (← compileLoc' nameEnv h) :: (← compileRecordFields' nameEnv t)
end

/-- Compile a located term to a located Rust expression. -/
def compileLoc {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (nameEnv : Fin n → String)
    (t : _root_.TermLoc' (fun _ => String) fvar ty) : Rust.ExprLoc :=
  (compileLoc' nameEnv t).run' 0

end Compile

/- Entry points ---------------------------------------------------------- -/

/-- Compile a closed located term to a located Rust expression -/
def compileToRustExprLoc {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.TermLoc fvar ty) : Rust.ExprLoc :=
  -- Closed-term compilation: there are no free variables, so the `nameEnv` is unused.
  -- We still provide a total function for completeness.
  Compile.compileLoc (fun i => s!"arg{i.val}") (t (rep := fun _ => String))

def renderRust {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.TermLoc fvar ty) (config : Rust.ShowConfig := Rust.defaultConfig) : String :=
  Rust.wrapAsMainLoc (compileToRustExprLoc t) config

/- Render a standalone Rust program that computes the compiled expression
   and prints the result using a tiny runtime library for SDQL values. -/
/-- Rust import header that references the external sdql_runtime.rs file.
    The runtime file must be present in the same directory as the generated .rs file.
    This keeps generated files small and readable. -/
def rustRuntimeHeader : String :=
  String.intercalate "\n"
  [ "// Import the SDQL runtime library from external file"
  , "#[path = \"sdql_runtime.rs\"]"
  , "mod sdql_runtime;"
  , ""
  , "use std::collections::BTreeMap;"
  , "use sdql_runtime::*;"
  , ""
  ]

def renderRustShown {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.TermLoc fvar ty) (config : Rust.ShowConfig := Rust.defaultConfig) : String :=
  let expr := compileToRustExprLoc t
  let header := rustRuntimeHeader
  let body :=
    let e := Rust.showExprLoc expr 1 config
    "fn main() {\n  let result = " ++ e ++ ";\n  println!(\"{}\", SDQLShow::show(&result));\n}\n"
  header ++ body

/- Open-term compilation helpers. --------------------------------------- -/

/-- Compile an open located term (with runtime parameters) to a located Rust expression, given a naming environment. -/
def compileOpenToRustExprLoc {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (nameEnv : Fin n → String)
    (t : _root_.TermLoc' (fun _ => String) fvar ty) : Rust.ExprLoc :=
  Compile.compileLoc nameEnv t

/-- Render a Rust function `fn <name>(params...) -> Ret { <expr> }` for an open located term. -/
def renderRustFn {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (name : String)
    (paramNames : Fin n → String)
    (t : _root_.TermLoc' (fun _ => String) fvar ty)
    (config : Rust.ShowConfig := Rust.defaultConfig)
    : String :=
  -- Build the parameter list from `paramNames` and `fvar`'s compile-time types.
  let paramDecls : List String :=
    (List.finRange n).map (fun i => s!"{paramNames i}: {Rust.showTy (coreTyToRustTy (fvar i))}")
  let paramsStr := String.intercalate ", " paramDecls
  let retStr := Rust.showTy (coreTyToRustTy (ty))
  let body := Rust.showExprLoc (compileOpenToRustExprLoc paramNames t) 1 config
  let header := "pub fn " ++ name ++ "(" ++ paramsStr ++ ") -> " ++ retStr ++ " {\n"
  let footer := "\n}\n"
  header ++ "  " ++ body ++ footer

/- Program-level codegen ------------------------------------------------- -/

/- Table loader generation:
   A table type is expected to be a record (tuple) where:
   - Most fields are `dict int T` (columnar vectors), compiled to `BTreeMap<i64, T>`
   - The last field is typically `int` (size), compiled to `i64`

   For each `dict int T` field at position i, we emit:
     `sdql_runtime::build_col::<RustTy>(&rows, i)`
   For `int` fields (typically the size), we emit:
     `size`
-/

/-- Generate the Rust expression for a single field in a table loader. -/
def genFieldLoader (fieldTy : _root_.Ty) (colIdx : Nat) : String :=
  match fieldTy with
  | .dict .int valTy =>
    -- Columnar vector: build_col with the value type
    let valRustTy := Rust.showTy (coreTyToRustTy valTy)
    s!"sdql_runtime::build_col::<{valRustTy}>(&rows, {colIdx})"
  | .int =>
    -- Size field: use the size variable directly
    "size"
  | other =>
    -- Fallback for other types (shouldn't happen in well-formed table schemas)
    let rustTy := Rust.showTy (coreTyToRustTy other)
    s!"/* unsupported field type {rustTy} */ Default::default()"

/-- Generate indexed field loader expressions for a list of field types. -/
def genFieldLoaders (fields : List _root_.Ty) : List String :=
  let rec go (fs : List _root_.Ty) (idx : Nat) : List String :=
    match fs with
    | [] => []
    | f :: rest => genFieldLoader f idx :: go rest (idx + 1)
  go fields 0

def genTableLoader (ty : _root_.Ty) (path : String) : String :=
  let lit := path.replace "\\" "\\\\" |>.replace "\"" "\\\""
  match ty with
  | .record fields =>
    -- Generate build_col calls for each field
    let colExprs := genFieldLoaders fields
    -- Wrap in a block that loads the TBL file
    let tupleBody := String.intercalate ", " colExprs
    "{\n      let (rows, size) = sdql_runtime::load_tbl(\"" ++ lit ++ "\");\n      (" ++ tupleBody ++ ")\n    }"
  | _ =>
    -- Non-record types: fall back to a placeholder (shouldn't happen for tables)
    let rustTy := Rust.showTy (coreTyToRustTy ty)
    s!"/* cannot load non-record type {rustTy} */ Default::default()"

/-- Render a Rust program from a `Prog`. The generated program:
    - defines and re-exports a tiny runtime library (`sdql_runtime`),
    - loads each free variable from the provided file path using generic loaders,
    - evaluates the compiled term, and
    - prints the pretty-printed result.
    The `config` parameter controls whether source location comments are emitted. -/
def renderRustProgShown (p : _root_.Prog) (config : Rust.ShowConfig := Rust.defaultConfig) : String :=
  let header := rustRuntimeHeader
  -- Parameter names for free variables
  let paramName : (i : Fin p.n) → String := fun i => s!"arg{i.val}"
  -- Generate inline loaders for each table parameter
  let idxs := (List.finRange p.n)
  let paramDecls : List String := idxs.map (fun i =>
    let ty := p.fvar i
    let tyStr := Rust.showTy (coreTyToRustTy ty)
    let nm := paramName i
    let path := p.loadPaths i
    let loaderExpr := genTableLoader ty path
    s!"let {nm}: {tyStr} = {loaderExpr};"
  )
  -- Compile the open located term with the chosen names
  let expr := compileOpenToRustExprLoc paramName (p.term (rep := fun _ => String))
  let bodyExpr := Rust.showExprLoc expr 1 config
  let loadsStr := String.intercalate "\n" (paramDecls.map (fun s => "  " ++ s))
  let mainBody :=
    "fn main() {\n" ++
    loadsStr ++ "\n  " ++
    "let result = " ++ bodyExpr ++ ";\n  println!(\"{}\", SDQLShow::show(&result));\n}\n"
  header ++ mainBody

end PartIiProject
