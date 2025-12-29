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
  | date : Ty  -- SDQL date, represented as YYYYMMDD integer
  | str : Ty
  | tuple : List Ty → Ty
  | map : Ty → Ty → Ty
  deriving Inhabited, BEq, Repr

inductive BinOp : Type where
  | add | sub | mul | div | bitXor | bitAnd | bitOr | eq | lt | gt | leq
  deriving Inhabited, BEq, Repr

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
  inductive ExprLoc : Type where
    | mk : (loc : SourceLocation) → Expr → ExprLoc
    deriving Repr

  /-- Rust expression constructors -/
  inductive Expr : Type where
    | var : String → Expr
    | litInt : Int → Expr
    | litReal : Float → Expr  -- produces Real::new(value)
    | litDate : Int → Expr    -- produces date!(YYYYMMDD)
    | litBool : Bool → Expr
    | litString : String → Expr
    | tuple : List ExprLoc → Expr
    | tupleProj : ExprLoc → Nat → Expr
    | borrow : ExprLoc → Expr
    | mapEmpty : Expr
    | mapInsert : ExprLoc → ExprLoc → ExprLoc → Expr
    | binop : BinOp → ExprLoc → ExprLoc → Expr
    | not : ExprLoc → Expr
    | ite : ExprLoc → ExprLoc → ExprLoc → Expr
    | letIn : String → ExprLoc → ExprLoc → Expr
    | call : String → List ExprLoc → Expr
    | block : List StmtLoc → ExprLoc → Expr
    | lookupOrDefault : ExprLoc → ExprLoc → ExprLoc → Expr
    deriving Repr

  /-- A statement paired with its source location from SDQL -/
  inductive StmtLoc : Type where
    | mk : (loc : SourceLocation) → Stmt → StmtLoc
    deriving Repr

  /- A very small statement sublanguage to support loops and mutations. -/
  inductive Stmt : Type where
    | letDecl : (mutable : Bool) → (name : String) → (init? : Option ExprLoc) → Stmt
    | assign : (name : String) → (rhs : ExprLoc) → Stmt
    | expr : ExprLoc → Stmt
    | forKV : (k v : String) → (map : ExprLoc) → (body : List StmtLoc) → Stmt
    deriving Repr
end

-- Inhabited instances for the mutual types (defined after the mutual block)
mutual
  partial def Expr.default : Expr := .litBool false
  partial def ExprLoc.default : ExprLoc := .mk SourceLocation.unknown Expr.default
  partial def Stmt.default : Stmt := .expr ExprLoc.default
  partial def StmtLoc.default : StmtLoc := .mk SourceLocation.unknown Stmt.default
end

instance : Inhabited Expr := ⟨Expr.default⟩
instance : Inhabited ExprLoc := ⟨ExprLoc.default⟩
instance : Inhabited Stmt := ⟨Stmt.default⟩
instance : Inhabited StmtLoc := ⟨StmtLoc.default⟩

namespace ExprLoc
  /-- Extract the source location from a located expression -/
  def loc : ExprLoc → SourceLocation
    | mk l _ => l

  /-- Extract the underlying expression from a located expression -/
  def expr : ExprLoc → Expr
    | mk _ e => e

  /-- Create a located expression with an unknown location -/
  def withUnknownLoc (e : Expr) : ExprLoc :=
    mk SourceLocation.unknown e
end ExprLoc

namespace StmtLoc
  /-- Extract the source location from a located statement -/
  def loc : StmtLoc → SourceLocation
    | mk l _ => l

  /-- Extract the underlying statement from a located statement -/
  def stmt : StmtLoc → Stmt
    | mk _ s => s

  /-- Create a located statement with an unknown location -/
  def withUnknownLoc (s : Stmt) : StmtLoc :=
    mk SourceLocation.unknown s
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

mutual
  /-- Show a located expression, optionally emitting source location comments -/
  partial def showExprLoc (e : ExprLoc) (indent := 0) (config : ShowConfig := defaultConfig) : String :=
    let locComment := if config.emitLocComments then formatLocComment e.loc else ""
    locComment ++ showExpr e.expr indent config

  partial def showExpr (e : Expr) (indent := 0) (config : ShowConfig := defaultConfig) : String :=
    match e with
    | .var s => s
    | .litInt n => toString n
    | .litReal f => s!"Real::new({f})"
    | .litDate d => s!"date!({d})"
    | .litBool b => if b then "true" else "false"
    | .litString s => s!"String::from(\"{s}\")"
    | .tuple es =>
        match es with
        | [] => "()"
        | [e] => s!"({showExprLoc e indent config},)"
        | _ => paren <| String.intercalate ", " (es.map (fun e => showExprLoc e indent config))
    | .tupleProj e idx => s!"({showExprLoc e indent config}).{idx}"
    | .borrow e => s!"&{paren (showExprLoc e indent config)}"
    | .mapEmpty => "std::collections::BTreeMap::new()"
    | .mapInsert m k v => s!"map_insert({showExprLoc m indent config}, {showExprLoc k indent config}, {showExprLoc v indent config})"
    -- Always parenthesize binary operator operands to avoid Rust precedence pitfalls
    -- (e.g. `x * (1.0 + y)` must not render as `x * 1.0 + y`).
    | .binop op a b => s!"{paren (showExprLoc a indent config)} {showBinOp op} {paren (showExprLoc b indent config)}"
    | .not a => s!"!{paren (showExprLoc a indent config)}"
    | .ite c t f =>
        let ci := showExprLoc c indent config
        let ti := showExprLoc t (indent+1) config
        let fi := showExprLoc f (indent+1) config
        "if " ++ ci ++ " {\n" ++
        indentStr (indent+1) ++ ti ++ "\n" ++ indentStr indent ++ "} else {\n" ++
        indentStr (indent+1) ++ fi ++ "\n" ++ indentStr indent ++ "}"
    | .letIn name v body =>
        let vi := showExprLoc v indent config
        let bi := showExprLoc body indent config
        "{" ++ " let " ++ name ++ " = " ++ vi ++ "; " ++ bi ++ " }"
    | .call f args => s!"{f}({String.intercalate ", " (args.map (fun a => showExprLoc a indent config))})"
    | .block ss result =>
        let body := String.intercalate "\n" (ss.map (fun s => showStmtLoc s (indent+1) config))
        let ri := showExprLoc result (indent+1) config
        "{" ++ "\n" ++ body ++ "\n" ++ indentStr (indent+1) ++ ri ++ "\n" ++ indentStr indent ++ "}"
    | .lookupOrDefault m k d => s!"lookup_or_default(&{showExprLoc m indent config}, {showExprLoc k indent config}, {showExprLoc d indent config})"

  /-- Show a located statement, optionally emitting source location comments -/
  partial def showStmtLoc (s : StmtLoc) (indent : Nat) (config : ShowConfig := defaultConfig) : String :=
    let locComment := if config.emitLocComments then formatLocComment s.loc else ""
    -- For statements, emit the comment at the start of the line
    if locComment.isEmpty then
      showStmt s.stmt indent config
    else
      indentStr indent ++ locComment ++ (showStmt s.stmt indent config).trimLeft

  partial def showStmt (s : Stmt) (indent : Nat) (config : ShowConfig := defaultConfig) : String :=
    match s with
    | .letDecl isMut n initOpt =>
        let kw := if isMut then "let mut" else "let"
        let initStr := match initOpt with
          | none => ""
          | some e => s!" = {showExprLoc e indent config}"
        s!"{indentStr indent}{kw} {n}{initStr};"
    | .assign n e => s!"{indentStr indent}{n} = {showExprLoc e indent config};"
    | .expr e => s!"{indentStr indent}{showExprLoc e indent config};"
    | .forKV k v m body =>
        let head := indentStr indent ++ "for (" ++ k ++ ", " ++ v ++ ") in " ++ showExprLoc m indent config ++ ".into_iter() {"
        let inner := String.intercalate "\n" (body.map (fun s => showStmtLoc s (indent+1) config))
        let tail := "\n" ++ indentStr indent ++ "}"
        head ++ (if inner = "" then "" else "\n" ++ inner) ++ tail
end

/- Small helper to wrap an expression into a main function as a string. -/
def wrapAsMain (e : Expr) (config : ShowConfig := defaultConfig) : String :=
  let exprStr := showExpr e 1 config
  "fn main() {\n  let result = " ++ exprStr ++ ";\n}\n"

/-- Wrap a located expression into a main function -/
def wrapAsMainLoc (e : ExprLoc) (config : ShowConfig := defaultConfig) : String :=
  let exprStr := showExprLoc e 1 config
  "fn main() {\n  let result = " ++ exprStr ++ ";\n}\n"

end Rust

end PartIiProject
