import PartIiProject.Term
import PartIiProject.Rust

set_option linter.style.longLine false

namespace PartIiProject

open Rust

/- Type translation ------------------------------------------------------- -/
partial def coreTyToRustTy : _root_.Ty → Rust.Ty
  | .bool => .bool
  | .int => .i64
  | .string => .str
  | .dict k v => .map (coreTyToRustTy k) (coreTyToRustTy v)
  | .record l => .tuple (l.map coreTyToRustTy)

/- Zeros for additive monoids (used for lookup defaults and sum inits). -/
mutual
  partial def zerosForHList : {l : List _root_.Ty} → _root_.HList _root_.AddM l → List Rust.Expr
    | [], .nil => []
    | _ :: ts, .cons h t => zeroOfAddM h :: zerosForHList t

  partial def zeroOfAddM : {t : _root_.Ty} → _root_.AddM t → Rust.Expr
    | .bool, .boolA => .litBool false
    | .int, .intA => .litInt 0
    | .dict _ _, @_root_.AddM.dictA _ _ _ => .mapEmpty
    | .record _, @_root_.AddM.recordA _ fields => .tuple (zerosForHList fields)
end

/- Compilation from core terms to Rust simplified AST -------------------- -/
namespace Compile

mutual
  /- Compile an SDQL term into a Rust simplified AST expression. -/
  partial def compile {fvar : String → _root_.Ty} {ty : _root_.Ty} : _root_.Term' (fun _ => String) fvar ty → Rust.Expr
  | .var v => .var v
  | .freeVariable s => .var s
  | .constInt n => .litInt n
  | .constBool b => .litBool b
  | .constString s => .litString s
  | .constRecord fields => .tuple (compileRecordFields fields)
  | .emptyDict => .mapEmpty
  | .dictInsert k v d => .mapInsert (compile d) (compile k) (compile v)
  | .not t => .not (compile t)
  | .ite c t f => .ite (compile c) (compile t) (compile f)
  | .letin t1 f =>
      -- Use a conventional binder name "x" as in the pretty-printer
      let xName := "x"
      .block
        [ .letDecl false xName (some (compile t1)) ]
        (compile (f xName))
  | .add a t1 t2 =>
      match a with
      | .boolA => .binop .bitXor (compile t1) (compile t2)
      | .intA => .binop .add (compile t1) (compile t2)
      | @_root_.AddM.dictA dom range aRange => .call "dict_add" [compile t1, compile t2]
      | @_root_.AddM.recordA l fields => .call "tuple_add" [compile t1, compile t2]
  | .mul _ _ e1 e2 =>
      -- We surface SDQL's shape-directed multiply as a helper call.
      .call "sdql_mul" [compile e1, compile e2]
  | .lookup aRange d k =>
      let deflt := zeroOfAddM aRange
      .lookupOrDefault (compile d) (compile k) deflt
  | .sum a d f =>
      -- Emit a block with an accumulator and a for-loop over (k,v) in d
      let accName := "acc"
      let kName := "k"
      let vName := "v"
      let accInit := zeroOfAddM a
      let bodyStmt : Rust.Stmt :=
        let bodyExpr := compile (f kName vName)
        let updated :=
          match a with
          | .boolA => .binop .bitXor (.var accName) bodyExpr
          | .intA => .binop .add (.var accName) bodyExpr
          | @_root_.AddM.dictA dom range aRange => .call "dict_add" [.var accName, bodyExpr]
          | @_root_.AddM.recordA l fields => .call "tuple_add" [.var accName, bodyExpr]
        Rust.Stmt.assign accName updated
      .block
        [ .letDecl true accName (some accInit)
        , Rust.Stmt.forKV kName vName (compile d) [bodyStmt]
        ]
        (.var accName)
  | .proj l r i => .call "proj" [compile r, .litInt (Int.ofNat i)]

  /- Compile a record literal represented as an HList of sub-terms. -/
  partial def compileRecordFields {fvar : String → _root_.Ty}
    : {l : List _root_.Ty} → _root_.HList (_root_.Term' (fun _ => String) fvar) l → List Rust.Expr
    | _, .nil => []
    | _, .cons h t => compile h :: compileRecordFields t
end

end Compile

/- Entry points ---------------------------------------------------------- -/

def compileToRustExpr {ty : _root_.Ty} (t : _root_.Term ty) : Rust.Expr :=
  Compile.compile (t (rep := fun _ => String) (fvar := fun _ => _root_.Ty.int))

def renderRust {ty : _root_.Ty} (t : _root_.Term ty) : String :=
  Rust.wrapAsMain (compileToRustExpr t)

/- Open-term compilation helpers. --------------------------------------- -/

/-- Compile an open term (with free variables named as `String`s) to a Rust AST. -/
def compileOpenToRustExpr {fvar : String → _root_.Ty} {ty : _root_.Ty} (t : _root_.Term' (fun _ => String) fvar ty) : Rust.Expr :=
  Compile.compile t

/-- Render a Rust function `fn <name>(params...) -> Ret { <expr> }` for an open term. -/
def renderRustFn (name : String)
    (params : List (String × _root_.Ty))
    {fvar : String → _root_.Ty} {ty : _root_.Ty}
    (t : _root_.Term' (fun _ => String) fvar ty)
    : String :=
  let paramsStr := String.intercalate ", " <|
    params.map (fun (n, ty) => s!"{n}: {Rust.showTy (coreTyToRustTy ty)}")
  let retStr := Rust.showTy (coreTyToRustTy (ty))
  let body := Rust.showExpr (compileOpenToRustExpr t) 1
  let header := "pub fn " ++ name ++ "(" ++ paramsStr ++ ") -> " ++ retStr ++ " {\n"
  let footer := "\n}\n"
  header ++ "  " ++ body ++ ";" ++ footer

end PartIiProject
