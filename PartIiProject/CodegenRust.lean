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
  /- Compile an SDQL term into a Rust simplified AST expression.
     `nameEnv` maps each runtime parameter (free variable) index to its Rust identifier. -/
  partial def compile {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
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
  partial def compileRecordFields {n : Nat} {fvar : Fin n → _root_.Ty}
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
  header ++ "  " ++ body ++ ";" ++ footer

end PartIiProject
