import PartIiProject.Term
import PartIiProject.Term2
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
  | .Lt _ => .call "ext_lt" [argExpr]
  | .Sub _ => .call "ext_sub" [argExpr]
  | .StrEndsWith => .call "ext_str_ends_with" [argExpr]
  | .Dom => .call "ext_dom" [ExprLoc.withUnknownLoc (Rust.Expr.borrow argExpr)]
  | .Range => .call "ext_range" [argExpr]
  | .DateLit yyyymmdd => .litDate yyyymmdd
  | .Year => .call "ext_year" [argExpr]
  | .Concat l1 l2 => .call "ext_concat" [argExpr]
end Compile

/- Entry points ---------------------------------------------------------- -/
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

/- ========================================================================
   DeBruijn Compilation (Term2 → Rust)
   ======================================================================== -/

namespace Compile2

/-- A name environment for DeBruijn terms: a list of Rust variable names,
    indexed from most recent binding (head) to oldest (tail). -/
abbrev NameEnv := List String

/-- Look up the Rust variable name for a DeBruijn Mem proof by computing the index -/
def lookupMem {ty : _root_.Ty} {ctx : List _root_.Ty} (m : Mem ty ctx) (env : NameEnv) : String :=
  let idx := memIdx m
  env.getD idx "???"
where
  memIdx : {ty : _root_.Ty} → {ctx : List _root_.Ty} → Mem ty ctx → Nat
    | _, _ :: _, .head _ => 0
    | _, _ :: _, .tail _ m' => memIdx m' + 1

mutual
  /-- Compile a DeBruijn located term into a Rust located expression. -/
  def compileLoc2 {ctx : List _root_.Ty} {ty : _root_.Ty}
      (env : NameEnv)
      (t : TermLoc2 ctx ty) : Compile.FreshM Rust.ExprLoc := do
    let ⟨loc, inner⟩ := t
    let expr ← compile2 env loc inner
    return Rust.ExprLoc.mk loc expr

  /-- Compile a DeBruijn term into a Rust expression. -/
  def compile2 {ctx : List _root_.Ty} {ty : _root_.Ty}
      (env : NameEnv) (loc : SourceLocation)
      (t : Term2 ctx ty) : Compile.FreshM Rust.Expr := do
    match t with
    | .var m => return .var (lookupMem m env)
    | .constInt n => return .litInt n
    | .constReal r => return .litReal r
    | .constBool b => return .litBool b
    | .constString s => return .litString s
    | .constRecord fields => return .tuple (← compileFields2 env fields)
    | .emptyDict => return .mapEmpty
    | .dictInsert k v d =>
        return .mapInsert (← compileLoc2 env d) (← compileLoc2 env k) (← compileLoc2 env v)
    | .not t => return .not (← compileLoc2 env t)
    | .ite c t f => return .ite (← compileLoc2 env c) (← compileLoc2 env t) (← compileLoc2 env f)
    | @Term2.letin _ ty₁ _ bound body =>
        let boundExpr ← compileLoc2 env bound
        let binderName ← Compile.freshName "x"
        let extEnv := binderName :: env
        let bodyExpr ← compileLoc2 extEnv body
        return .block [Rust.StmtLoc.mk loc (.letDecl false binderName (some boundExpr))] bodyExpr
    | .add a t1 t2 =>
        let lhs ← compileLoc2 env t1
        let rhs ← compileLoc2 env t2
        return Compile.compileAdd a lhs rhs
    | @Term2.mul _ _ _ _ s1 s2 e1 e2 =>
        let lhs ← compileLoc2 env e1
        let rhs ← compileLoc2 env e2
        match s1, s2 with
        | .realS, .realS => return .binop .mul lhs rhs
        | .intS, .intS => return .binop .mul lhs rhs
        | .boolS, .boolS =>
            let arg := ExprLoc.withUnknownLoc (.tuple [lhs, rhs])
            return .call "ext_and" [arg]
        | _, _ =>
            return .call "sdql_mul" [lhs, rhs]
    | .lookup aRange d k =>
        return .lookupOrDefault (← compileLoc2 env d) (← compileLoc2 env k) (zeroOfAddMLoc aRange)
    | @Term2.sum _ dom range _ a d body =>
        let de ← compileLoc2 env d
        let accName ← Compile.freshName "acc"
        let kName ← Compile.freshName "k"
        let vName ← Compile.freshName "v"
        -- Extend environment for sum body: dom :: range :: ctx
        -- DeBruijn: first bound variable (dom/key) has index 0, second (range/val) has index 1
        let extEnv := kName :: vName :: env
        let bodyExpr ← compileLoc2 extEnv body
        let accVar := ExprLoc.withUnknownLoc (.var accName)
        let updated := Compile.compileAdd a accVar bodyExpr
        let loop := Rust.StmtLoc.mk loc (.forKV kName vName de [Rust.StmtLoc.mk loc (.assign accName (ExprLoc.withUnknownLoc updated))])
        return .block
          [ Rust.StmtLoc.mk loc (.letDecl true accName (some (zeroOfAddMLoc a)))
          , loop ]
          (ExprLoc.withUnknownLoc (.var accName))
    | .proj _ r i => return .tupleProj (← compileLoc2 env r) i
    | .builtin b a =>
        let argExpr ← compileLoc2 env a
        return Compile.compileBuiltin b argExpr

  /-- Compile DeBruijn record fields to a list of Rust expressions. -/
  def compileFields2 {ctx : List _root_.Ty}
      (env : NameEnv)
      : {l : List _root_.Ty} → TermFields2 ctx l → Compile.FreshM (List Rust.ExprLoc)
    | [], .nil => return []
    | _, .cons h t => return (← compileLoc2 env h) :: (← compileFields2 env t)
end

/-- Compile a DeBruijn term to a Rust expression (runs the state monad). -/
def compileLocRun {ctx : List _root_.Ty} {ty : _root_.Ty}
    (env : NameEnv)
    (t : TermLoc2 ctx ty) : Rust.ExprLoc :=
  (compileLoc2 env t).run' 0

end Compile2

/- Program-level codegen (PHOAS - kept for compatibility) ---------------- -/

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

/- DeBruijn Program-level codegen ---------------------------------------- -/

/-- Build a name environment from a context.
    Each position in the context gets a name like "arg0", "arg1", etc. -/
def mkLoadEnv (ctx : List _root_.Ty) : Compile2.NameEnv :=
  (List.range ctx.length).map (fun i => s!"arg{i}")

/-- Render a Rust program from a `Prog2` (DeBruijn indexed).
    The generated program:
    - imports the sdql_runtime module,
    - loads each context variable from the provided file path,
    - evaluates the compiled term, and
    - prints the result.
-/
def renderRustProg2Shown (p : Prog2) (config : Rust.ShowConfig := Rust.defaultConfig) : String :=
  let header := rustRuntimeHeader
  -- Build name environment for context variables
  let env := mkLoadEnv p.ctx
  -- Generate inline loaders for each context variable
  let rec genLoaders (ctx : List _root_.Ty) (paths : List String) (idx : Nat)
      : List String :=
    match ctx, paths with
    | [], [] => []
    | ty :: restCtx, path :: restPaths =>
        let tyStr := Rust.showTy (coreTyToRustTy ty)
        let nm := s!"arg{idx}"
        let loaderExpr := genTableLoader ty path
        s!"let {nm}: {tyStr} = {loaderExpr};" :: genLoaders restCtx restPaths (idx + 1)
    | _, _ => []  -- Mismatched lengths, shouldn't happen
  let paramDecls := genLoaders p.ctx p.loadPaths 0
  -- Compile the term with the name environment
  let expr := Compile2.compileLocRun env p.term
  let bodyExpr := Rust.showExprLoc expr 1 config
  let loadsStr := String.intercalate "\n" (paramDecls.map (fun s => "  " ++ s))
  let mainBody :=
    "fn main() {\n" ++
    loadsStr ++ "\n  " ++
    "let result = " ++ bodyExpr ++ ";\n  println!(\"{}\", SDQLShow::show(&result));\n}\n"
  header ++ mainBody

end PartIiProject
