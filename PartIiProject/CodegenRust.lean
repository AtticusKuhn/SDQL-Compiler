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
  | .maxProduct => .maxProduct
  | .date => .date
  | .int => .i64
  | .string => .str
  | .dict k v => .map (coreTyToRustTy k) (coreTyToRustTy v)
  | .record l => .tuple (l.map coreTyToRustTy)

/- Zeros for additive monoids (used for lookup defaults and sum inits). -/
mutual
  def zerosForHListLoc {ctx : Nat} : {l : List _root_.Ty} → _root_.HList _root_.AddM l → Rust.Exprs ctx
    | [], .nil => .nil
    | _ :: _, .cons h t =>
        .cons (zeroOfAddMLoc (ctx := ctx) h) (zerosForHListLoc (ctx := ctx) t)

  def zeroOfAddMLoc {ctx : Nat} : {t : _root_.Ty} → _root_.AddM t → Rust.ExprLoc ctx
    | .bool, .boolA => ExprLoc.withUnknownLoc (.litBool false)
    | .real, .realA => ExprLoc.withUnknownLoc (.litReal 0.0)
    | .maxProduct, .maxProductA =>
        ExprLoc.withUnknownLoc (.callRuntimeFn .promoteMaxProduct (Rust.Exprs.singleton (ExprLoc.withUnknownLoc (.litReal 0.0))))
    | .date, .dateA => ExprLoc.withUnknownLoc (.litDate 10101)  -- dummy date (0001-01-01)
    | .int, .intA => ExprLoc.withUnknownLoc (.litInt 0)
    | .string, .stringA => ExprLoc.withUnknownLoc (.litString "")
    | .dict _ _, @_root_.AddM.dictA _ _ _ => ExprLoc.withUnknownLoc .mapEmpty
    | .record _, @_root_.AddM.recordA _ fields => ExprLoc.withUnknownLoc (.tuple (zerosForHListLoc (ctx := ctx) fields))
end

/- Compilation from core terms to Rust simplified AST -------------------- -/
namespace Compile

/-- Compile addition based on the additive monoid evidence. -/
def compileAdd {ctx : Nat} {ty : _root_.Ty} (a : _root_.AddM ty) (lhs rhs : Rust.ExprLoc ctx) : Rust.Expr ctx :=
  match a with
  | .boolA => .binop .bitOr lhs rhs
  | .realA => .binop .add lhs rhs
  | .maxProductA => .callRuntimeFn .maxProductAdd (Rust.Exprs.ofList [lhs, rhs])
  | .dateA => rhs.expr  -- date "addition" just takes rhs (overwrite)
  | .intA => .binop .add lhs rhs
  | .stringA => .binop .add lhs rhs
  | @_root_.AddM.dictA _ _ _ => .callRuntimeFn .dictAdd (Rust.Exprs.ofList [lhs, rhs])
  | @_root_.AddM.recordA l _ => .callRuntimeFn (.tupleAdd l.length) (Rust.Exprs.ofList [lhs, rhs])

/-- Compile a builtin function application. -/
def compileBuiltin {ctx : Nat} {argTy resTy : _root_.Ty} (b : _root_.BuiltinFn argTy resTy) (argExpr : Rust.ExprLoc ctx) : Rust.Expr ctx :=
  match b with
  | .And => .callRuntimeFn .extAnd (Rust.Exprs.singleton argExpr)
  | .Or => .callRuntimeFn .extOr (Rust.Exprs.singleton argExpr)
  | .Eq _ => .callRuntimeFn .extEq (Rust.Exprs.singleton argExpr)
  | .Leq _ => .callRuntimeFn .extLeq (Rust.Exprs.singleton argExpr)
  | .Lt _ => .callRuntimeFn .extLt (Rust.Exprs.singleton argExpr)
  | .Sub _ => .callRuntimeFn .extSub (Rust.Exprs.singleton argExpr)
  | .Div => .callRuntimeFn .extDiv (Rust.Exprs.singleton argExpr)
  | .StrEndsWith => .callRuntimeFn .extStrEndsWith (Rust.Exprs.singleton argExpr)
  | .StrStartsWith => .callRuntimeFn .extStrStartsWith (Rust.Exprs.singleton argExpr)
  | .StrContains => .callRuntimeFn .extStrContains (Rust.Exprs.singleton argExpr)
  | .FirstIndex => .callRuntimeFn .extFirstIndex (Rust.Exprs.singleton argExpr)
  | .LastIndex => .callRuntimeFn .extLastIndex (Rust.Exprs.singleton argExpr)
  | .SubString => .callRuntimeFn .extSubString (Rust.Exprs.singleton argExpr)
  | .Dom => .callRuntimeFn .extDom (Rust.Exprs.singleton (ExprLoc.withUnknownLoc (Rust.Expr.borrow argExpr)))
  | .Range => .callRuntimeFn .extRange (Rust.Exprs.singleton argExpr)
  | .Size => .callRuntimeFn .extSize (Rust.Exprs.singleton (ExprLoc.withUnknownLoc (Rust.Expr.borrow argExpr)))
  | .DateLit yyyymmdd => .litDate yyyymmdd
  | .Year => .callRuntimeFn .extYear (Rust.Exprs.singleton argExpr)
  | .Concat l1 l2 => .callRuntimeFn .extConcat (Rust.Exprs.singleton argExpr)
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

def memIdx {α : Type} {a : α} {ctx : List α} : Mem a ctx → Nat
  | .head _ => 0
  | .tail _ m => memIdx m + 1

theorem memIdx_lt_length {α : Type} {a : α} {ctx : List α} (m : Mem a ctx) : memIdx m < ctx.length := by
  induction m with
  | head as =>
      simp [memIdx]
  | tail b m ih =>
      simpa [memIdx] using Nat.succ_lt_succ ih

def memToFin {α : Type} {a : α} {ctx : List α} (m : Mem a ctx) : Fin ctx.length :=
  ⟨memIdx m, memIdx_lt_length m⟩

mutual
  /-- Compile a DeBruijn located term into a Rust located expression. -/
  def compileLoc2 {ctx : List _root_.Ty} {ty : _root_.Ty}
      (t : TermLoc2 ctx ty) : Rust.ExprLoc ctx.length :=
    let ⟨loc, inner⟩ := t
    Rust.ExprLoc.mk loc (compile2 loc inner)

  /-- Compile a DeBruijn term into a Rust expression. -/
  def compile2 {ctx : List _root_.Ty} {ty : _root_.Ty}
      (loc : SourceLocation)
      (t : Term2 ctx ty) : Rust.Expr ctx.length :=
    match t with
    | .var m => .var (memToFin m)
    | .constInt n => .litInt n
    | .constReal r => .litReal r
    | .constBool b => .litBool b
    | .constString s => .litString s
    | .constRecord fields => .tuple (compileFields2 fields)
    | .emptyDict => .mapEmpty
    | .dictInsert k v d =>
        .mapInsert (compileLoc2 d) (compileLoc2 k) (compileLoc2 v)
    | .not t => .not (compileLoc2 t)
    | .ite c t f => .ite (compileLoc2 c) (compileLoc2 t) (compileLoc2 f)
    | @Term2.letin _ ty₁ _ bound body =>
        .letIn (compileLoc2 bound) (compileLoc2 body)
    | .add a t1 t2 =>
        Compile.compileAdd a (compileLoc2 t1) (compileLoc2 t2)
    | @Term2.mul _ _ _ _ s1 s2 e1 e2 =>
        let lhs := compileLoc2 e1
        let rhs := compileLoc2 e2
        match s1, s2 with
        | .realS, .realS => .binop .mul lhs rhs
        | .maxProductS, .maxProductS => .binop .mul lhs rhs
        | .intS, .intS => .binop .mul lhs rhs
        | .boolS, .boolS =>
            let arg := ExprLoc.withUnknownLoc (.tuple (Rust.Exprs.ofList [lhs, rhs]))
            .callRuntimeFn .extAnd (Rust.Exprs.singleton arg)
        | _, _ =>
            .callRuntimeFn .sdqlMul (Rust.Exprs.ofList [lhs, rhs])
    | @Term2.promote _ fromType toType e =>
        let inner := compileLoc2 e
        match fromType, toType with
        | .int, .real => .callRuntimeFn .promoteIntToReal (Rust.Exprs.singleton inner)
        | .int, .maxProduct => .callRuntimeFn .promoteIntToMaxProduct (Rust.Exprs.singleton inner)
        | .real, .maxProduct => .callRuntimeFn .promoteMaxProduct (Rust.Exprs.singleton inner)
        | .maxProduct, .real => .callRuntimeFn .demoteMaxProduct (Rust.Exprs.singleton inner)
        | _, _ => inner.expr
    | .lookup aRange d k =>
        .lookupOrDefault (compileLoc2 d) (compileLoc2 k) (zeroOfAddMLoc (ctx := ctx.length) aRange)
    | @Term2.sum _ dom range _ a d body =>
        let n := ctx.length
        let accInit : Rust.ExprLoc n := zeroOfAddMLoc (ctx := n) a
        let accDecl : Rust.StmtLoc n (n+1) := Rust.StmtLoc.mk loc (.letDecl true (.some accInit))
        let de : Rust.ExprLoc (n+1) :=
          Rust.Rename1.exprLoc (ctx := n) Fin.succ (compileLoc2 d)

        let shiftAfter2 : Fin (n + 2) → Fin (n + 3) := fun i =>
          if h : i.1 < 2 then
            ⟨i.1, by omega⟩
          else
            ⟨i.1 + 1, by omega⟩

        let bodyDomRange : Rust.ExprLoc (n+2) := compileLoc2 body
        let bodyLoop : Rust.ExprLoc (n+3) :=
          Rust.Rename1.exprLoc (ctx := n+2) shiftAfter2 bodyDomRange

        let accIdx : Fin (n + 3) :=
          ⟨2, by omega⟩
        -- let accIdx : Fin (n + 3) :=

        let accVar : Rust.ExprLoc (n+3) := Rust.ExprLoc.withUnknownLoc (.var accIdx)
        let updated : Rust.Expr (n+3) := Compile.compileAdd a accVar bodyLoop
        let assignAcc : Rust.StmtLoc (n+3) (n+3) :=
          Rust.StmtLoc.mk loc (.assign accIdx (Rust.ExprLoc.withUnknownLoc updated))

        let loopBody : Rust.StmtSeq (n+3) (n+3) :=
          Rust.StmtSeq.cons assignAcc Rust.StmtSeq.nil
        let loopStmt : Rust.StmtLoc (n+1) (n+1) := Rust.StmtLoc.mk loc (.forKV de loopBody)

        let stmts : Rust.StmtSeq n (n+1) :=
          Rust.StmtSeq.cons accDecl (Rust.StmtSeq.cons loopStmt Rust.StmtSeq.nil)
        let accResult : Rust.ExprLoc (n+1) :=
          Rust.ExprLoc.withUnknownLoc (.var ⟨0, Nat.succ_pos n⟩)
        .block stmts accResult
    | .proj _ r i => .tupleProj (compileLoc2 r) i
    | .builtin b a =>
        Compile.compileBuiltin b (compileLoc2 a)

  /-- Compile DeBruijn record fields to a list of Rust expressions. -/
  def compileFields2 {ctx : List _root_.Ty}
      : {l : List _root_.Ty} → TermFields2 ctx l → Rust.Exprs ctx.length
    | [], .nil => .nil
    | _, .cons h t => .cons (compileLoc2 h) (compileFields2 t)
end

#check Fin.succ
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
def mkLoadEnv (ctx : List _root_.Ty) : Rust.NameEnv :=
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
  -- Compile the term to a DeBruijn-indexed Rust AST, and pretty-print using `env`
  let expr := Compile2.compileLoc2 p.term
  let bodyExpr := Rust.showExprLocRun env expr 1 config
  let loadsStr := String.intercalate "\n" (paramDecls.map (fun s => "  " ++ s))
  let mainBody :=
    "fn main() {\n" ++
    loadsStr ++ "\n  " ++
    "let result = " ++ bodyExpr ++ ";\n  println!(\"{}\", SDQLShow::show(&result));\n}\n"
  header ++ mainBody

end PartIiProject
