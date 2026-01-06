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
  | .tupleAdd arity => s!"tuple_add{arity}"
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

/-- Format a source location as a Rust comment.
    Uses `SourceLocation.substring` (not byte ranges) since some pipelines only populate the substring. -/
def formatLocComment (loc : SourceLocation) : String :=
  let snippet := loc.substring.trim
  if snippet.isEmpty then
    ""  -- Don't emit comment for unknown locations
  else
    s!"\n/* {snippet} */\n"

/-- Configuration for whether to emit source location comments -/
structure ShowConfig where
  /-- Whether to emit SDQL source location comments -/
  emitLocComments : Bool := false
  deriving Inhabited

/-- Default configuration (no location comments) -/
def defaultConfig : ShowConfig := ⟨false⟩

/-- Configuration that emits location comments -/
def withLocComments : ShowConfig := ⟨true⟩

/-- Convert a DeBruijn variable index (0 = most recent binder) into a stable Rust name.
    We name variables by *absolute* position in the context (0 = oldest binder),
    so printed names don't shift under binders. -/
private def varName {ctx : Nat} (v : Fin ctx) : String :=
  -- `v.1 < ctx`, so `ctx - 1 - v.1` is the "absolute" index from the oldest binder.
  s!"x{ctx - 1 - v.1}"

mutual
  /-- Show a located expression, optionally emitting source location comments -/
  partial def showExprLoc {ctx : Nat} (e : ExprLoc ctx)
      (indent := 0) (config : ShowConfig := defaultConfig) : String :=
    let locComment := if config.emitLocComments then formatLocComment e.loc else ""
    let inner := showExpr e.expr indent config
    locComment ++ inner

  partial def showExpr {ctx : Nat} (e : Expr ctx)
      (indent := 0) (config : ShowConfig := defaultConfig) : String :=
    match e with
    | .var v => varName v
    | .litInt n =>  toString n
    | .litReal f =>  s!"Real::new({f})"
    | .litDate d =>  s!"date!({d})"
    | .litBool b =>  (if b then "true" else "false")
    | .litString s =>  s!"String::from(\"{s}\")"
    | .tuple es =>
        let es := Exprs.toList es
        match es with
        | [] =>  "()"
        | [e] =>
            let se := showExprLoc e indent config
            s!"({se},)"
        | _ =>
            let parts := es.map (fun e => showExprLoc e indent config)
            paren <| String.intercalate ", " parts
    | .tupleProj e idx =>
        let se := showExprLoc e indent config
        s!"({se}).{idx}"
    | .borrow e =>
        let se :=  showExprLoc e indent config
        s!"&{paren se}"
    | .mapEmpty => "std::collections::BTreeMap::new()"
    | .mapInsert m k v =>
        let sm :=  showExprLoc m indent config
        let sk :=  showExprLoc k indent config
        let sv :=  showExprLoc v indent config
        s!"map_insert({sm}, {sk}, {sv})"
    -- Always parenthesize binary operator operands to avoid Rust precedence pitfalls
    -- (e.g. `x * (1.0 + y)` must not render as `x * 1.0 + y`).
    | .binop op a b =>
        let sa  :=  showExprLoc a indent config
        let sb  :=  showExprLoc b indent config
        s!"{paren sa} {showBinOp op} {paren sb}"
    | .not a =>
        let sa  :=  showExprLoc a indent config
        s!"!{paren sa}"
    | .ite c t f =>
        let ci := showExprLoc c indent config
        let ti := showExprLoc t (indent+1) config
        let fi := showExprLoc f (indent+1) config
        (
          "if " ++ ci ++ " {\n" ++
          indentStr (indent+1) ++ ti ++ "\n" ++ indentStr indent ++ "} else {\n" ++
          indentStr (indent+1) ++ fi ++ "\n" ++ indentStr indent ++ "}"
        )
    | .letIn (ctx := ctx) v body =>
        let name  :=  s!"x{ctx}"
        let vi  :=  showExprLoc v indent config
        let bi  :=  showExprLoc body indent config
        "{" ++ " let " ++ name ++ " = " ++ vi ++ "; " ++ bi ++ " }"
    | .callRuntimeFn f args =>
        let argsStr  :=  (Exprs.toList args).map (fun a => showExprLoc a indent config)
        s!"{runtimeFnName f}({String.intercalate ", " argsStr})"
    | .block ss result =>
        let (bodyStr)  :=  showStmtSeq ss (indent+1) config
        let ri  :=  showExprLoc result (indent+1) config
        let bodyPrefix := if bodyStr.isEmpty then "" else bodyStr ++ "\n"
        "{" ++ "\n" ++ bodyPrefix ++ indentStr (indent+1) ++ ri ++ "\n" ++ indentStr indent ++ "}"
    | .lookupOrDefault m k d =>
        let sm := showExprLoc m indent config
        let sk := showExprLoc k indent config
        let sd := showExprLoc d indent config
        s!"lookup_or_default(&{sm}, {sk}, {sd})"

  /-- Show a located statement, optionally emitting source location comments -/
  partial def showStmtLoc {ctxIn ctxOut : Nat} (s : StmtLoc ctxIn ctxOut)
      (indent : Nat) (config : ShowConfig := defaultConfig) : String  :=
    let locComment := if config.emitLocComments then formatLocComment s.loc else ""
    -- For statements, emit the comment at the start of the line
    let (line) := showStmt s.stmt indent config
    let rendered :=
      if locComment.isEmpty then line
      else indentStr indent ++ locComment ++ line.trimLeft
    (rendered)

  partial def showStmt {ctxIn ctxOut : Nat}  (s : Stmt ctxIn ctxOut)
      (indent : Nat) (config : ShowConfig := defaultConfig) :  (String) :=
    match s with
    | .letDecl isMut initOpt =>
        let nm :=  s!"x{ctxIn}"
        let kw := if isMut then "let mut" else "let"
        let initStr :=
          match initOpt with
          | .none =>  ""
          | .some e =>
              let se := showExprLoc e indent config
              s!" = {se}"
        (s!"{indentStr indent}{kw} {nm}{initStr};")
    | .assign tgt rhs =>
        let n := varName tgt
        let se := showExprLoc rhs indent config
        (s!"{indentStr indent}{n} = {se};")
    | .expr e =>
        let se := showExprLoc e indent config
        (s!"{indentStr indent}{se};")
    | .forKV (ctx := ctx) m body =>
        -- The loop body context is `ctx + 2` (two fresh DeBruijn binders at indices 0 and 1).
        -- Under `varName`, binder index 0 must print as `x{ctx+1}` and binder index 1 as `x{ctx}`.
        let k :=  s!"x{ctx + 1}"
        let v := s!"x{ctx}"
        let sm := showExprLoc m indent config
        let head := indentStr indent ++ "for (" ++ k ++ ", " ++ v ++ ") in " ++ sm ++ ".clone().into_iter() {"
        let (inner ) := showStmtSeq body (indent+1) config
        let tail := "\n" ++ indentStr indent ++ "}"
        let mid := if inner = "" then "" else "\n" ++ inner
        (head ++ mid ++ tail)

  partial def showStmtSeq {ctxIn ctxOut : Nat} (ss : StmtSeq ctxIn ctxOut)
      (indent : Nat) (config : ShowConfig := defaultConfig) : (String ) :=
    match ss with
    | .nil => ("")
    | .cons s rest =>
        let (line) := showStmtLoc s indent config
        let (tail) := showStmtSeq rest indent config
        let out := if tail.isEmpty then line else line ++ "\n" ++ tail
        (out)
end

def showExprLocRun {ctx : Nat}  (e : ExprLoc ctx)
    (indent := 0) (config : ShowConfig := defaultConfig) : String :=
  (showExprLoc e indent config)

def showExprRun {ctx : Nat} (e : Expr ctx)
    (indent := 0) (config : ShowConfig := defaultConfig) : String :=
  (showExpr e indent config)

/- Small helper to wrap an expression into a main function as a string. -/
def wrapAsMain (e : Expr 0) (config : ShowConfig := defaultConfig) : String :=
  let exprStr := showExprRun e 1 config
  "fn main() {\n  let result = " ++ exprStr ++ ";\n}\n"

/-- Wrap a located expression into a main function -/
def wrapAsMainLoc (e : ExprLoc 0) (config : ShowConfig := defaultConfig) : String :=
  let exprStr := showExprLocRun e 1 config
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
