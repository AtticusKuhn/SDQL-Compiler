namespace PartIiProject

/-!
  A very small, simplified Rust AST and pretty-printer.
  This is intentionally minimal – just enough to express the codegen
  patterns we need for SDQL terms (expressions, let blocks, ifs, simple
  function calls, and loops for dictionary iteration).
-/

namespace Rust

inductive Ty : Type where
  | bool : Ty
  | i64 : Ty
  | str : Ty
  | tuple : List Ty → Ty
  | map : Ty → Ty → Ty
  deriving Inhabited, BEq, Repr

inductive BinOp : Type where
  | add | sub | mul | div | bitXor | bitAnd | bitOr | eq | lt | gt
  deriving Inhabited, BEq, Repr

mutual
  inductive Expr : Type where
    | var : String → Expr
    | litInt : Int → Expr
    | litBool : Bool → Expr
    | litString : String → Expr
    | tuple : List Expr → Expr
    | mapEmpty : Expr
    | mapInsert : Expr → Expr → Expr → Expr
    | binop : BinOp → Expr → Expr → Expr
    | not : Expr → Expr
    | ite : Expr → Expr → Expr → Expr
    | letIn : String → Expr → Expr → Expr
    | call : String → List Expr → Expr
    | block : List Stmt → Expr → Expr
    | lookupOrDefault : Expr → Expr → Expr → Expr
    deriving Inhabited, Repr

  /- A very small statement sublanguage to support loops and mutations. -/
  inductive Stmt : Type where
    | letDecl : (mutable : Bool) → (name : String) → (init? : Option Expr) → Stmt
    | assign : (name : String) → (rhs : Expr) → Stmt
    | expr : Expr → Stmt
    | forKV : (k v : String) → (map : Expr) → (body : List Stmt) → Stmt
    deriving Inhabited, Repr
end

/- Pretty-printing -------------------------------------------------------- -/

private def indentStr : Nat → String
  | 0 => ""
  | n+1 => indentStr n ++ "  "

private def paren (s : String) : String := s!"({s})"

partial def showBinOp : BinOp → String
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

partial def showTy : Ty → String
  | .bool => "bool"
  | .i64 => "i64"
  | .str => "String"
  | .tuple ts =>
      match ts with
      | [] => "()"
      | _  => paren <| String.intercalate ", " (ts.map showTy)
  | .map k v => s!"std::collections::BTreeMap<{showTy k}, {showTy v}>"

mutual
  partial def showExpr (e : Expr) (indent := 0) : String :=
    match e with
    | .var s => s
    | .litInt n => toString n
    | .litBool b => if b then "true" else "false"
    | .litString s => s!"\"{s}\""
    | .tuple es => paren <| String.intercalate ", " (es.map (fun e => showExpr e indent))
    | .mapEmpty => "std::collections::BTreeMap::new()"
    | .mapInsert m k v => s!"map_insert({showExpr m indent}, {showExpr k indent}, {showExpr v indent})"
    | .binop op a b => s!"{showExpr a indent} {showBinOp op} {showExpr b indent}"
    | .not a => s!"!{showExpr a indent}"
    | .ite c t f =>
        let ci := showExpr c indent
        let ti := showExpr t (indent+1)
        let fi := showExpr f (indent+1)
        "if " ++ ci ++ " {\n" ++
        indentStr (indent+1) ++ ti ++ "\n" ++ indentStr indent ++ "} else {\n" ++
        indentStr (indent+1) ++ fi ++ "\n" ++ indentStr indent ++ "}"
    | .letIn name v body =>
        let vi := showExpr v indent
        let bi := showExpr body indent
        "{" ++ " let " ++ name ++ " = " ++ vi ++ "; " ++ bi ++ " }"
    | .call f args => s!"{f}({String.intercalate ", " (args.map (fun a => showExpr a indent))})"
    | .block ss result =>
        let body := String.intercalate "\n" (ss.map (fun s => showStmt s (indent+1)))
        let ri := showExpr result (indent+1)
        "{" ++ "\n" ++ body ++ "\n" ++ indentStr (indent+1) ++ ri ++ "\n" ++ indentStr indent ++ "}"
    | .lookupOrDefault m k d => s!"lookup_or_default({showExpr m indent}, {showExpr k indent}, {showExpr d indent})"

  partial def showStmt : Stmt → Nat → String
    | .letDecl isMut n initOpt, indent =>
        let kw := if isMut then "let mut" else "let"
        let initStr := match initOpt with
          | none => ""
          | some e => s!" = {showExpr e indent}"
        s!"{indentStr indent}{kw} {n}{initStr};"
    | .assign n e, indent => s!"{indentStr indent}{n} = {showExpr e indent};"
    | .expr e, indent => s!"{indentStr indent}{showExpr e indent};"
    | .forKV k v m body, indent =>
        let head := indentStr indent ++ "for (" ++ k ++ ", " ++ v ++ ") in " ++ showExpr m indent ++ ".into_iter() {"
        let inner := String.intercalate "\n" (body.map (fun s => showStmt s (indent+1)))
        let tail := "\n" ++ indentStr indent ++ "}"
        head ++ (if inner = "" then "" else "\n" ++ inner) ++ tail
end

/- Small helper to wrap an expression into a main function as a string. -/
def wrapAsMain (e : Expr) : String :=
  let exprStr := showExpr e 1
  "fn main() {\n  let result = " ++ exprStr ++ ";\n}\n"

end Rust

end PartIiProject
