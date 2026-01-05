import PartIiProject.Term

namespace PartIiProject

/-!
  A very small, simplified Rust AST and pretty-printer.
  This is intentionally minimal – just enough to express the codegen
  patterns we need for SDQL terms (expressions, let blocks, ifs, simple
  function calls, and loops for dictionary iteration).

  The AST includes source location tracking from the original SDQL code,
  using a mutually inductive pattern similar to Term'/TermLoc'.
-/

namespace Rust

inductive Ty : Type where
  | bool : Ty
  | i64 : Ty
  | real : Ty  -- SDQL real, maps to an Ord-capable f64 wrapper
  | maxProduct : Ty  -- SDQL max-product semiring over reals
  | date : Ty  -- SDQL date, represented as YYYYMMDD integer
  | str : Ty
  | tuple : List Ty → Ty
  | map : Ty → Ty → Ty
  deriving Inhabited, BEq, Repr

inductive BinOp : Type where
  | add | sub | mul | div | bitXor | bitAnd | bitOr | eq | lt | gt | leq
  deriving Inhabited, BEq, Repr

/- Calls to the external SDQL Rust runtime (no stringly-typed function names). -/
inductive RuntimeFn : Type where
  | dictAdd : RuntimeFn
  | tupleAdd : (arity : Nat) → RuntimeFn
  | sdqlMul : RuntimeFn
  | maxProductAdd : RuntimeFn
  | promoteMaxProduct : RuntimeFn
  | demoteMaxProduct : RuntimeFn
  | promoteIntToReal : RuntimeFn
  | promoteIntToMaxProduct : RuntimeFn
  | extAnd : RuntimeFn
  | extOr : RuntimeFn
  | extEq : RuntimeFn
  | extLeq : RuntimeFn
  | extLt : RuntimeFn
  | extSub : RuntimeFn
  | extDiv : RuntimeFn
  | extStrEndsWith : RuntimeFn
  | extStrStartsWith : RuntimeFn
  | extStrContains : RuntimeFn
  | extFirstIndex : RuntimeFn
  | extLastIndex : RuntimeFn
  | extSubString : RuntimeFn
  | extDom : RuntimeFn
  | extRange : RuntimeFn
  | extSize : RuntimeFn
  | extYear : RuntimeFn
  | extConcat : RuntimeFn
  deriving Inhabited, BEq, Repr

def runtimeFnName : RuntimeFn → String
  | .dictAdd => "dict_add"
  | .tupleAdd arity =>
      match arity with
      | 0 => "tuple_add0"
      | 1 => "tuple_add"
      | 2 => "tuple_add2"
      | 3 => "tuple_add3"
      | 4 => "tuple_add4"
      | _ => "tuple_add5"
  | .sdqlMul => "sdql_mul"
  | .maxProductAdd => "max_product_add"
  | .promoteMaxProduct => "promote_max_product"
  | .demoteMaxProduct => "demote_max_product"
  | .promoteIntToReal => "promote_int_to_real"
  | .promoteIntToMaxProduct => "promote_int_to_max_product"
  | .extAnd => "ext_and"
  | .extOr => "ext_or"
  | .extEq => "ext_eq"
  | .extLeq => "ext_leq"
  | .extLt => "ext_lt"
  | .extSub => "ext_sub"
  | .extDiv => "ext_div"
  | .extStrEndsWith => "ext_str_ends_with"
  | .extStrStartsWith => "ext_str_starts_with"
  | .extStrContains => "ext_str_contains"
  | .extFirstIndex => "ext_first_index"
  | .extLastIndex => "ext_last_index"
  | .extSubString => "ext_sub_string"
  | .extDom => "ext_dom"
  | .extRange => "ext_range"
  | .extSize => "ext_size"
  | .extYear => "ext_year"
  | .extConcat => "ext_concat"

/-
  Rust AST with source location tracking.

  `ExprLoc` pairs an expression with its source location from the original SDQL code.
  `Expr` is the underlying expression structure.
  `StmtLoc` pairs a statement with its source location.
  `Stmt` is the underlying statement structure.

  These are mutually inductive to allow recursive structures to carry locations.
-/
mutual
  /-- An expression paired with its source location from SDQL -/
  inductive ExprLoc  : (ctx : Nat)  →  Type where
    | mk : {ctx : Nat} → (loc : SourceLocation) → Expr ctx  → ExprLoc ctx
    deriving Repr

  /-- A small list type for expressions in a fixed DeBruijn context.
      We avoid `List (ExprLoc ctx)` inside indexed inductives due to kernel restrictions. -/
  inductive Exprs : (ctx : Nat) → Type where
    | nil : {ctx : Nat} → Exprs ctx
    | cons : {ctx : Nat} → ExprLoc ctx → Exprs ctx → Exprs ctx
    deriving Repr

  /-- Optional initializer for `let` declarations (avoids `Option (ExprLoc ctx)` in indexed inductives). -/
  inductive OptExprLoc : (ctx : Nat) → Type where
    | none : {ctx : Nat} → OptExprLoc ctx
    | some : {ctx : Nat} → ExprLoc ctx → OptExprLoc ctx
    deriving Repr

  /-- Rust expression constructors -/
  inductive Expr : (ctx : Nat) → Type where
    | var : {ctx : Nat} → Fin ctx → Expr  ctx
    | litInt : {ctx : Nat} → Int → Expr ctx
    | litReal : {ctx : Nat} → Float → Expr ctx  -- produces Real::new(value)
    | litDate : {ctx : Nat} → Int → Expr  ctx  -- produces date!(YYYYMMDD)
    | litBool : {ctx : Nat} → Bool → Expr ctx
    | litString : {ctx : Nat} → String → Expr ctx
    | tuple : {ctx : Nat} → Exprs ctx → Expr ctx
    | tupleProj : {ctx : Nat} →  ExprLoc ctx → Nat → Expr ctx
    | borrow : {ctx : Nat} →  ExprLoc ctx → Expr ctx
    | mapEmpty : {ctx : Nat} → Expr ctx
    | mapInsert : {ctx : Nat} → ExprLoc ctx → ExprLoc ctx → ExprLoc ctx → Expr ctx
    | binop : {ctx : Nat} → BinOp → ExprLoc ctx → ExprLoc ctx → Expr ctx
    | not : {ctx : Nat} → ExprLoc ctx → Expr ctx
    | ite : {ctx : Nat} → ExprLoc ctx → ExprLoc ctx → ExprLoc ctx → Expr ctx
    | letIn : {ctx : Nat} → ExprLoc ctx → ExprLoc ctx.succ → Expr ctx
    | callRuntimeFn : {ctx : Nat} → RuntimeFn → Exprs ctx → Expr ctx
    | block : {ctx : Nat} → {ctxOut : Nat} → StmtSeq ctx ctxOut → ExprLoc ctxOut → Expr ctx
    | lookupOrDefault : {ctx : Nat} → ExprLoc ctx → ExprLoc ctx → ExprLoc ctx → Expr ctx
    deriving Repr

  /-- A statement paired with its source location from SDQL -/
  inductive StmtLoc : (ctxIn ctxOut : Nat) → Type where
    | mk : {ctxIn ctxOut : Nat} → (loc : SourceLocation) → Stmt ctxIn ctxOut → StmtLoc ctxIn ctxOut
    deriving Repr

  /-- A sequential statement list with context growth (via `letDecl`). -/
  inductive StmtSeq : (ctxIn ctxOut : Nat) → Type where
    | nil : {ctx : Nat} → StmtSeq ctx ctx
    | cons : {ctxIn ctxMid ctxOut : Nat} → StmtLoc ctxIn ctxMid → StmtSeq ctxMid ctxOut → StmtSeq ctxIn ctxOut
    deriving Repr

  /- A very small statement sublanguage to support loops and mutations. -/
  inductive Stmt : (ctxIn ctxOut : Nat) → Type where
    | letDecl : {ctx : Nat} → (mutable : Bool) → (init? : OptExprLoc ctx) → Stmt ctx ctx.succ
    | assign : {ctx : Nat} → (target : Fin ctx) → (rhs : ExprLoc ctx) → Stmt ctx ctx
    | expr : {ctx : Nat} → ExprLoc ctx → Stmt ctx ctx
    | forKV : {ctx : Nat} → (map : ExprLoc ctx) → (body : StmtSeq (ctx + 2) (ctx + 2)) → Stmt ctx ctx
    deriving Repr
end

-- Inhabited instances for the mutual types (defined after the mutual block)
mutual
  partial def Expr.default (ctx : Nat) : Expr ctx := .litBool false
  partial def ExprLoc.default (ctx : Nat) : ExprLoc ctx := .mk SourceLocation.unknown (Expr.default ctx)
  partial def Stmt.default (ctx : Nat) : Stmt ctx ctx := .expr (ExprLoc.default ctx)
  partial def StmtLoc.default (ctx : Nat) : StmtLoc ctx ctx := .mk SourceLocation.unknown (Stmt.default ctx)
end

instance (ctx : Nat) : Inhabited (Expr ctx) := ⟨Expr.default ctx⟩
instance (ctx : Nat) : Inhabited (ExprLoc ctx) := ⟨ExprLoc.default ctx⟩
instance (ctx : Nat) : Inhabited (Stmt ctx ctx) := ⟨Stmt.default ctx⟩
instance (ctx : Nat) : Inhabited (StmtLoc ctx ctx) := ⟨StmtLoc.default ctx⟩

namespace ExprLoc
  /-- Extract the source location from a located expression -/
  def loc {ctx : Nat} : ExprLoc ctx → SourceLocation
    | .mk l _ => l

  /-- Extract the underlying expression from a located expression -/
  def expr {ctx : Nat} : ExprLoc ctx → Expr ctx
    | .mk _ e => e

  /-- Create a located expression with an unknown location -/
  def withUnknownLoc {ctx : Nat} (e : Expr ctx) : ExprLoc ctx :=
    .mk SourceLocation.unknown e
end ExprLoc

namespace Exprs
  def toList {ctx : Nat} : Exprs ctx → List (ExprLoc ctx)
    | .nil => []
    | .cons h t => h :: toList t

  def ofList {ctx : Nat} : List (ExprLoc ctx) → Exprs ctx
    | [] => .nil
    | h :: t => .cons h (ofList t)

  def singleton {ctx : Nat} (e : ExprLoc ctx) : Exprs ctx :=
    .cons e .nil

  def map {ctx ctx' : Nat} (f : ExprLoc ctx → ExprLoc ctx') : Exprs ctx → Exprs ctx'
    | .nil => .nil
    | .cons h t => .cons (f h) (map f t)
end Exprs

namespace StmtLoc
  /-- Extract the source location from a located statement -/
  def loc {ctxIn ctxOut : Nat} : StmtLoc ctxIn ctxOut → SourceLocation
    | .mk l _ => l

  /-- Extract the underlying statement from a located statement -/
  def stmt {ctxIn ctxOut : Nat} : StmtLoc ctxIn ctxOut → Stmt ctxIn ctxOut
    | .mk _ s => s

  /-- Create a located statement with an unknown location -/
  def withUnknownLoc {ctxIn ctxOut : Nat} (s : Stmt ctxIn ctxOut) : StmtLoc ctxIn ctxOut :=
    .mk SourceLocation.unknown s
end StmtLoc

/- Pretty-printing -------------------------------------------------------- -/

private def indentStr : Nat → String
  | 0 => ""
  | n+1 => indentStr n ++ "  "

private def paren (s : String) : String := s!"({s})"

def showBinOp : BinOp → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .bitXor => "^"
  | .bitAnd => "&"
  | .bitOr => "|"
  | .eq => "=="
  | .lt => "<"
  | .gt => ">"
  | .leq => "<="

partial def showTy : Ty → String
  | .bool => "bool"
  | .i64 => "i64"
  | .real => "Real"  -- Uses our Ord-capable f64 wrapper
  | .maxProduct => "MaxProduct"
  | .date => "Date"  -- SDQL Date wrapper
  | .str => "String"
  | .tuple ts =>
      match ts with
      | [] => "()"
      | [t] => s!"({showTy t},)"
      | _  => paren <| String.intercalate ", " (ts.map showTy)
  | .map k v => s!"std::collections::BTreeMap<{showTy k}, {showTy v}>"

/-- Escape potentially-problematic substrings for embedding in a Rust block comment. -/
def escapeForBlockComment (s : String) : String :=
  -- Avoid prematurely closing the comment and keep the output single-line.
  s.replace "*/" "* /"
   |>.replace "\r" " "
   |>.replace "\n" " "

/-- Format a source location as a Rust comment.
    Uses `SourceLocation.substring` (not byte ranges) since some pipelines only populate the substring. -/
def formatLocComment (loc : SourceLocation) : String :=
  let snippet := loc.substring.trim
  if snippet.isEmpty then
    ""  -- Don't emit comment for unknown locations
  else
    s!"/* {escapeForBlockComment snippet} */ "

/-- Configuration for whether to emit source location comments -/
structure ShowConfig where
  /-- Whether to emit SDQL source location comments -/
  emitLocComments : Bool := false
  deriving Inhabited

/-- Default configuration (no location comments) -/
def defaultConfig : ShowConfig := ⟨false⟩

/-- Configuration that emits location comments -/
def withLocComments : ShowConfig := ⟨true⟩

 /-- Name environment, indexed from most recent binder (head) to oldest (tail). -/
abbrev NameEnv := List String

 /-- State used to generate fresh Rust variable names during pretty-printing. -/
abbrev ShowM := StateM Nat

private def freshName (pfx : String) : ShowM String := do
  let n ← get
  set (n + 1)
  return s!"{pfx}{n}"

private def lookupVar {ctx : Nat} (env : NameEnv) (v : Fin ctx) : String :=
  env.getD v.1 s!"v{v.1}"

mutual
  /-- Show a located expression, optionally emitting source location comments -/
  partial def showExprLoc {ctx : Nat} (env : NameEnv) (e : ExprLoc ctx)
      (indent := 0) (config : ShowConfig := defaultConfig) : ShowM String := do
    let locComment := if config.emitLocComments then formatLocComment e.loc else ""
    let inner ← showExpr env e.expr indent config
    return locComment ++ inner

  partial def showExpr {ctx : Nat} (env : NameEnv) (e : Expr ctx)
      (indent := 0) (config : ShowConfig := defaultConfig) : ShowM String := do
    match e with
    | .var v => return lookupVar env v
    | .litInt n => return toString n
    | .litReal f => return s!"Real::new({f})"
    | .litDate d => return s!"date!({d})"
    | .litBool b => return (if b then "true" else "false")
    | .litString s => return s!"String::from(\"{s}\")"
    | .tuple es =>
        let es := Exprs.toList es
        match es with
        | [] => return "()"
        | [e] =>
            let se ← showExprLoc env e indent config
            return s!"({se},)"
        | _ =>
            let parts ← es.mapM (fun e => showExprLoc env e indent config)
            return paren <| String.intercalate ", " parts
    | .tupleProj e idx =>
        let se ← showExprLoc env e indent config
        return s!"({se}).{idx}"
    | .borrow e =>
        let se ← showExprLoc env e indent config
        return s!"&{paren se}"
    | .mapEmpty => return "std::collections::BTreeMap::new()"
    | .mapInsert m k v =>
        let sm ← showExprLoc env m indent config
        let sk ← showExprLoc env k indent config
        let sv ← showExprLoc env v indent config
        return s!"map_insert({sm}, {sk}, {sv})"
    -- Always parenthesize binary operator operands to avoid Rust precedence pitfalls
    -- (e.g. `x * (1.0 + y)` must not render as `x * 1.0 + y`).
    | .binop op a b =>
        let sa ← showExprLoc env a indent config
        let sb ← showExprLoc env b indent config
        return s!"{paren sa} {showBinOp op} {paren sb}"
    | .not a =>
        let sa ← showExprLoc env a indent config
        return s!"!{paren sa}"
    | .ite c t f => do
        let ci ← showExprLoc env c indent config
        let ti ← showExprLoc env t (indent+1) config
        let fi ← showExprLoc env f (indent+1) config
        return (
          "if " ++ ci ++ " {\n" ++
          indentStr (indent+1) ++ ti ++ "\n" ++ indentStr indent ++ "} else {\n" ++
          indentStr (indent+1) ++ fi ++ "\n" ++ indentStr indent ++ "}"
        )
    | .letIn v body => do
        let name ← freshName "x"
        let vi ← showExprLoc env v indent config
        let bi ← showExprLoc (name :: env) body indent config
        return "{" ++ " let " ++ name ++ " = " ++ vi ++ "; " ++ bi ++ " }"
    | .callRuntimeFn f args =>
        let argsStr ← (Exprs.toList args).mapM (fun a => showExprLoc env a indent config)
        return s!"{runtimeFnName f}({String.intercalate ", " argsStr})"
    | .block ss result =>
        let (bodyStr, envOut) ← showStmtSeq env ss (indent+1) config
        let ri ← showExprLoc envOut result (indent+1) config
        let bodyPrefix := if bodyStr.isEmpty then "" else bodyStr ++ "\n"
        return "{" ++ "\n" ++ bodyPrefix ++ indentStr (indent+1) ++ ri ++ "\n" ++ indentStr indent ++ "}"
    | .lookupOrDefault m k d => do
        let sm ← showExprLoc env m indent config
        let sk ← showExprLoc env k indent config
        let sd ← showExprLoc env d indent config
        return s!"lookup_or_default(&{sm}, {sk}, {sd})"

  /-- Show a located statement, optionally emitting source location comments -/
  partial def showStmtLoc {ctxIn ctxOut : Nat} (env : NameEnv) (s : StmtLoc ctxIn ctxOut)
      (indent : Nat) (config : ShowConfig := defaultConfig) : ShowM (String × NameEnv) := do
    let locComment := if config.emitLocComments then formatLocComment s.loc else ""
    -- For statements, emit the comment at the start of the line
    let (line, envOut) ← showStmt env s.stmt indent config
    let rendered :=
      if locComment.isEmpty then line
      else indentStr indent ++ locComment ++ line.trimLeft
    return (rendered, envOut)

  partial def showStmt {ctxIn ctxOut : Nat} (env : NameEnv) (s : Stmt ctxIn ctxOut)
      (indent : Nat) (config : ShowConfig := defaultConfig) : ShowM (String × NameEnv) := do
    match s with
    | .letDecl isMut initOpt =>
        let nm ← freshName "x"
        let kw := if isMut then "let mut" else "let"
        let initStr ←
          match initOpt with
          | .none => pure ""
          | .some e => do
              let se ← showExprLoc env e indent config
              pure s!" = {se}"
        return (s!"{indentStr indent}{kw} {nm}{initStr};", nm :: env)
    | .assign tgt rhs => do
        let n := lookupVar env tgt
        let se ← showExprLoc env rhs indent config
        return (s!"{indentStr indent}{n} = {se};", env)
    | .expr e => do
        let se ← showExprLoc env e indent config
        return (s!"{indentStr indent}{se};", env)
    | .forKV m body => do
        let k ← freshName "k"
        let v ← freshName "v"
        let sm ← showExprLoc env m indent config
        let head := indentStr indent ++ "for (" ++ k ++ ", " ++ v ++ ") in " ++ sm ++ ".clone().into_iter() {"
        let (inner, _envOut) ← showStmtSeq (k :: v :: env) body (indent+1) config
        let tail := "\n" ++ indentStr indent ++ "}"
        let mid := if inner = "" then "" else "\n" ++ inner
        return (head ++ mid ++ tail, env)

  partial def showStmtSeq {ctxIn ctxOut : Nat} (env : NameEnv) (ss : StmtSeq ctxIn ctxOut)
      (indent : Nat) (config : ShowConfig := defaultConfig) : ShowM (String × NameEnv) := do
    match ss with
    | .nil => return ("", env)
    | .cons s rest => do
        let (line, env1) ← showStmtLoc env s indent config
        let (tail, env2) ← showStmtSeq env1 rest indent config
        let out := if tail.isEmpty then line else line ++ "\n" ++ tail
        return (out, env2)
end

def showExprLocRun {ctx : Nat} (env : NameEnv) (e : ExprLoc ctx)
    (indent := 0) (config : ShowConfig := defaultConfig) : String :=
  (showExprLoc env e indent config).run' 0

def showExprRun {ctx : Nat} (env : NameEnv) (e : Expr ctx)
    (indent := 0) (config : ShowConfig := defaultConfig) : String :=
  (showExpr env e indent config).run' 0

/- Small helper to wrap an expression into a main function as a string. -/
def wrapAsMain (e : Expr 0) (config : ShowConfig := defaultConfig) : String :=
  let exprStr := showExprRun (env := []) e 1 config
  "fn main() {\n  let result = " ++ exprStr ++ ";\n}\n"

/-- Wrap a located expression into a main function -/
def wrapAsMainLoc (e : ExprLoc 0) (config : ShowConfig := defaultConfig) : String :=
  let exprStr := showExprLocRun (env := []) e 1 config
  "fn main() {\n  let result = " ++ exprStr ++ ";\n}\n"

namespace Rename1
  /-- Lift a renaming `ctx → ctx+1` under a binder: `(ctx+1) → (ctx+2)`. -/
  def lift {ctx : Nat} (f : Fin ctx → Fin (ctx + 1)) : Fin (ctx + 1) → Fin (ctx + 2)
    | ⟨0, _h⟩ => ⟨0, Nat.succ_pos _⟩
    | ⟨Nat.succ i, h⟩ =>
        have hi : i < ctx := Nat.lt_of_succ_lt_succ (by
          -- `Nat.succ i < ctx + 1` and `ctx + 1 = Nat.succ ctx`
          simpa using h)
        let fi := f ⟨i, hi⟩
        ⟨Nat.succ fi.1, Nat.succ_lt_succ fi.2⟩

  /-- Lift a renaming under `n` binders. -/
  def liftN {ctx : Nat} (n : Nat) (f : Fin ctx → Fin (ctx + 1))
      : Fin (ctx + n) → Fin (ctx + n + 1) :=
    Nat.rec (motive := fun n => Fin (ctx + n) → Fin (ctx + n + 1))
      f
      (fun _ g => lift g)
      n

  mutual
    /-- Rename a located expression by inserting one new variable in the context. -/
    def exprLoc {ctx : Nat} (f : Fin ctx → Fin (ctx + 1)) : ExprLoc ctx → ExprLoc (ctx + 1)
      | .mk loc e => .mk loc (expr f e)

    /-- Rename a list of located expressions. -/
    def exprs {ctx : Nat} (f : Fin ctx → Fin (ctx + 1)) : Exprs ctx → Exprs (ctx + 1)
      | .nil => .nil
      | .cons h t => .cons (exprLoc f h) (exprs f t)

    /-- Rename an expression by inserting one new variable in the context. -/
    def expr {ctx : Nat} (f : Fin ctx → Fin (ctx + 1)) : Expr ctx → Expr (ctx + 1)
      | .var v => .var (f v)
      | .litInt n => .litInt n
      | .litReal r => .litReal r
      | .litDate d => .litDate d
      | .litBool b => .litBool b
      | .litString s => .litString s
      | .tuple es => .tuple (exprs f es)
      | .tupleProj e i => .tupleProj (exprLoc f e) i
      | .borrow e => .borrow (exprLoc f e)
      | .mapEmpty => .mapEmpty
      | .mapInsert m k v => .mapInsert (exprLoc f m) (exprLoc f k) (exprLoc f v)
      | .binop op a b => .binop op (exprLoc f a) (exprLoc f b)
      | .not a => .not (exprLoc f a)
      | .ite c t e => .ite (exprLoc f c) (exprLoc f t) (exprLoc f e)
      | .letIn v body => .letIn (exprLoc f v) (exprLoc (lift f) body)
      | .callRuntimeFn fn args => .callRuntimeFn fn (exprs f args)
      | .block ss result =>
          let (ss', fOut) := stmtSeq f ss
          .block ss' (exprLoc fOut result)
      | .lookupOrDefault m k d => .lookupOrDefault (exprLoc f m) (exprLoc f k) (exprLoc f d)

    /-- Rename a located statement by inserting one new variable in the context. -/
    def stmtLoc {ctxIn ctxOut : Nat} (f : Fin ctxIn → Fin (ctxIn + 1))
        : StmtLoc ctxIn ctxOut → StmtLoc (ctxIn + 1) (ctxOut + 1)
      | .mk loc s => .mk loc (stmt f s)

    /-- Rename a statement by inserting one new variable in the context. -/
    def stmt {ctxIn ctxOut : Nat} (f : Fin ctxIn → Fin (ctxIn + 1))
        : Stmt ctxIn ctxOut → Stmt (ctxIn + 1) (ctxOut + 1)
      | .letDecl isMut init? =>
          let init' :=
            match init? with
            | .none => .none
            | .some e => .some (exprLoc f e)
          .letDecl isMut init'
      | .assign tgt rhs =>
          .assign (f tgt) (exprLoc f rhs)
      | .expr e =>
          .expr (exprLoc f e)
      | .forKV m body =>
          -- Body sees two additional binders (k,v) that are unaffected by the renaming.
          let (body', _fOut) := stmtSeq (liftN 2 f) body
          .forKV (exprLoc f m) body'

    /-- Rename a statement sequence by inserting one new variable in the context.
        Returns both the renamed sequence and the induced renaming on the final context. -/
    def stmtSeq {ctxIn ctxOut : Nat} (f : Fin ctxIn → Fin (ctxIn + 1))
        : StmtSeq ctxIn ctxOut → StmtSeq (ctxIn + 1) (ctxOut + 1) × (Fin ctxOut → Fin (ctxOut + 1))
      | .nil => (.nil, f)
      | .cons s rest =>
          match s with
          | .mk loc st =>
              let s' := stmtLoc f (.mk loc st)
              let fNext :=
                match st with
                | .letDecl .. => lift f
                | .assign .. => f
                | .expr .. => f
                | .forKV .. => f
              let (rest', fOut) := stmtSeq fNext rest
              (.cons s' rest', fOut)
  end
end Rename1

end Rust

end PartIiProject
