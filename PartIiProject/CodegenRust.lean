import PartIiProject.Term
import PartIiProject.Rust

-- set_option linter.style.longLine false

namespace PartIiProject

open Rust

/- Type translation ------------------------------------------------------- -/
def coreTyToRustTy : _root_.Ty → Rust.Ty
  | .bool => .bool
  | .real => .real
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
    | .real, .realA => .litReal 0.0
    | .int, .intA => .litInt 0
    | .string, .stringA => .litString ""
    | .dict _ _, @_root_.AddM.dictA _ _ _ => .mapEmpty
    | .record _, @_root_.AddM.recordA _ fields => .tuple (zerosForHList fields)
end

/- Compilation from core terms to Rust simplified AST -------------------- -/
namespace Compile

mutual
  /- Compile an SDQL term into a Rust expression while threading a fresh-name counter.
     `nameEnv` maps each runtime parameter (free variable) index to its Rust identifier. -/
  def compileWithFresh {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
      (nameEnv : Fin n → String)
      (fresh : Nat)
      : _root_.Term' (fun _ => String) fvar ty → (Rust.Expr × Nat)
  | .var v => (.var v, fresh)
  | .freeVariable i => (.var (nameEnv i), fresh)
  | .constInt n => (.litInt n, fresh)
  | .constBool b => (.litBool b, fresh)
  | .constString s => (.litString s, fresh)
  | .constRecord fields =>
      let (es, fresh') := compileRecordFieldsWithFresh nameEnv fields fresh
      (.tuple es, fresh')
  | .emptyDict => (.mapEmpty, fresh)
  | .dictInsert k v d =>
      let (dExpr, fresh1) := compileWithFresh nameEnv fresh d
      let (kExpr, fresh2) := compileWithFresh nameEnv fresh1 k
      let (vExpr, fresh3) := compileWithFresh nameEnv fresh2 v
      (.mapInsert dExpr kExpr vExpr, fresh3)
  | .not t =>
      let (te, fresh') := compileWithFresh nameEnv fresh t
      (.not te, fresh')
  | .ite c t f =>
      let (ce, fresh1) := compileWithFresh nameEnv fresh c
      let (te, fresh2) := compileWithFresh nameEnv fresh1 t
      let (fe, fresh3) := compileWithFresh nameEnv fresh2 f
      (.ite ce te fe, fresh3)
  | .letin t1 f =>
      let (t1Expr, fresh1) := compileWithFresh nameEnv fresh t1
      let binderName := s!"x{fresh1}"
      let (bodyExpr, fresh2) := compileWithFresh nameEnv (fresh1 + 1) (f binderName)
      (.block
        [ .letDecl false binderName (some t1Expr) ]
        bodyExpr, fresh2)
  | .add a t1 t2 =>
      let (lhs, fresh1) := compileWithFresh nameEnv fresh t1
      let (rhs, fresh2) := compileWithFresh nameEnv fresh1 t2
      let expr :=
        match a with
        | .boolA => .binop .bitXor lhs rhs
        | .realA => .binop .add lhs rhs
        | .intA => .binop .add lhs rhs
        | .stringA => .binop .add lhs rhs
        | @_root_.AddM.dictA dom range aRange => .call "dict_add" [lhs, rhs]
        | @_root_.AddM.recordA l fields =>
            let fname := match l.length with
                          | 0 => "tuple_add0"
                          | 1 => "tuple_add"
                          | 2 => "tuple_add2"
                          | 3 => "tuple_add3"
                          | 4 => "tuple_add4"
                          | _ => "tuple_add5" -- fallback for 5+
            .call fname [lhs, rhs]
      (expr, fresh2)
  | .mul _ _ e1 e2 =>
      let (lhs, fresh1) := compileWithFresh nameEnv fresh e1
      let (rhs, fresh2) := compileWithFresh nameEnv fresh1 e2
      (.call "sdql_mul" [lhs, rhs], fresh2)
  | .lookup aRange d k =>
      let (de, fresh1) := compileWithFresh nameEnv fresh d
      let (ke, fresh2) := compileWithFresh nameEnv fresh1 k
      let deflt := zeroOfAddM aRange
      (.lookupOrDefault de ke deflt, fresh2)
  | .sum a d f =>
      let (de, fresh1) := compileWithFresh nameEnv fresh d
      let accName := s!"acc{fresh1}"
      let kName := s!"k{fresh1}"
      let vName := s!"v{fresh1}"
      let accInit := zeroOfAddM a
      let (bodyExpr, fresh2) := compileWithFresh nameEnv (fresh1 + 1) (f kName vName)
      let updated :=
        match a with
        | .boolA => .binop .bitXor (.var accName) bodyExpr
        | .realA => .binop .add (.var accName) bodyExpr
        | .intA => .binop .add (.var accName) bodyExpr
        | .stringA => .binop .add (.var accName) bodyExpr
        | @_root_.AddM.dictA dom range aRange => .call "dict_add" [.var accName, bodyExpr]
        | @_root_.AddM.recordA l fields => .call "tuple_add" [.var accName, bodyExpr]
      let loop :=
        Rust.Stmt.forKV kName vName de [Rust.Stmt.assign accName updated]
      (.block
        [ .letDecl true accName (some accInit)
        , loop
        ]
        (.var accName), fresh2)
  | .proj l r i =>
      let (re, fresh') := compileWithFresh nameEnv fresh r
      (.tupleProj re i, fresh')
  | .builtin b a =>
      let (argExpr, fresh') := compileWithFresh nameEnv fresh a
      let expr :=
        match b with
        | .And => .call "ext_and" [argExpr]
        | .Or => .call "ext_or" [argExpr]
        | .Eq _ => .call "ext_eq" [argExpr]
        | .StrEndsWith => .call "ext_str_ends_with" [argExpr]
        | .Dom => .call "ext_dom" [Rust.Expr.borrow argExpr]
        | .Range => .call "ext_range" [argExpr]
      (expr, fresh')

  /- Compile a record literal represented as an HList of sub-terms. -/
  def compileRecordFieldsWithFresh {n : Nat} {fvar : Fin n → _root_.Ty}
    (nameEnv : Fin n → String)
    : {l : List _root_.Ty} →
        _root_.HList (_root_.Term' (fun _ => String) fvar) l →
        Nat → (List Rust.Expr × Nat)
    | _, .nil, fresh => ([], fresh)
    | _, .cons h t, fresh =>
        let (he, fresh1) := compileWithFresh nameEnv fresh h
        let (te, fresh2) := compileRecordFieldsWithFresh nameEnv t fresh1
        (he :: te, fresh2)
end

def compile {n : Nat} {fvar : Fin n → _root_.Ty} {ty : _root_.Ty}
    (nameEnv : Fin n → String)
    (t : _root_.Term' (fun _ => String) fvar ty) : Rust.Expr :=
  (compileWithFresh nameEnv 0 t).fst

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
  , "    use std::cmp::Ordering;"
  , "\n    // Ord-capable f64 wrapper for SDQL real type"
  , "    #[derive(Debug, Clone, Copy, Default)]"
  , "    pub struct Real(pub f64);"
  , "    impl Real { pub fn new(v: f64) -> Self { Real(v) } }"
  , "    impl PartialEq for Real { fn eq(&self, other: &Self) -> bool { self.0 == other.0 || (self.0.is_nan() && other.0.is_nan()) } }"
  , "    impl Eq for Real {}"
  , "    impl PartialOrd for Real { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }"
  , "    impl Ord for Real {"
  , "        fn cmp(&self, other: &Self) -> Ordering {"
  , "            self.0.partial_cmp(&other.0).unwrap_or_else(|| {"
  , "                if self.0.is_nan() && other.0.is_nan() { Ordering::Equal }"
  , "                else if self.0.is_nan() { Ordering::Greater }"
  , "                else { Ordering::Less }"
  , "            })"
  , "        }"
  , "    }"
  , "    impl Add for Real { type Output = Self; fn add(self, rhs: Self) -> Self { Real(self.0 + rhs.0) } }"
  , "\n    pub trait SdqlAdd { fn sdql_add(&self, other: &Self) -> Self; }"
  , "    impl SdqlAdd for bool { fn sdql_add(&self, other: &Self) -> Self { *self ^ *other } }"
  , "    impl SdqlAdd for i64 { fn sdql_add(&self, other: &Self) -> Self { *self + *other } }"
  , "    impl SdqlAdd for Real { fn sdql_add(&self, other: &Self) -> Self { Real(self.0 + other.0) } }"
  , "    impl SdqlAdd for String {"
  , "        fn sdql_add(&self, other: &Self) -> Self {"
  , "            let mut s = self.clone();"
  , "            s.push_str(other);"
  , "            s"
  , "        }"
  , "    }"
  , "    impl<K: Ord + Clone, V: SdqlAdd + Clone> SdqlAdd for BTreeMap<K, V> {"
  , "        fn sdql_add(&self, other: &Self) -> Self {"
  , "            dict_add(self.clone(), other.clone())"
  , "        }"
  , "    }"
  , "    impl<T1: SdqlAdd> SdqlAdd for (T1,) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0),) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd> SdqlAdd for (T1, T2) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1)) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd> SdqlAdd for (T1, T2, T3) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2)) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd> SdqlAdd for (T1, T2, T3, T4) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3)) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4)) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5)) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd, T7: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6, T7) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5), self.6.sdql_add(&other.6)) } }"
  , "    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd, T7: SdqlAdd, T8: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6, T7, T8) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5), self.6.sdql_add(&other.6), self.7.sdql_add(&other.7)) } }"
  , "\n    // Insert without mutation at the call-site"
  , "    pub fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {"
  , "        m.insert(k, v);"
  , "        m"
  , "    }"
  , "\n    pub fn lookup_or_default<K: Ord, V: Clone>(m: &BTreeMap<K, V>, k: K, default: V) -> V {"
  , "        match m.get(&k) {"
  , "            Some(v) => v.clone(),"
  , "            None => default,"
  , "        }"
  , "    }"
  , "\n    // Dictionary addition merges keys with value addition"
  , "    pub fn dict_add<K: Ord + Clone, V: SdqlAdd + Clone>(a: BTreeMap<K, V>, b: BTreeMap<K, V>) -> BTreeMap<K, V> {"
  , "        let mut acc = a;"
  , "        for (k, v2) in b.into_iter() {"
  , "            if let Some(v1) = acc.get(&k) {"
  , "                let new_v = v1.sdql_add(&v2);"
  , "                acc.insert(k.clone(), new_v);"
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
  , "\n    pub fn ext_and(args: (bool, bool)) -> bool { args.0 && args.1 }"
  , "    pub fn ext_or(args: (bool, bool)) -> bool { args.0 || args.1 }"
  , "    pub fn ext_eq<T: PartialEq>(args: (T, T)) -> bool { args.0 == args.1 }"
  , "    pub fn ext_str_ends_with(args: (String, String)) -> bool {"
  , "        let (s, suf) = args;"
  , "        s.ends_with(&suf)"
  , "    }"
  , "    pub fn ext_dom<K: Ord + Clone, V>(m: &BTreeMap<K, V>) -> BTreeMap<K, bool> {"
  , "        let mut out = BTreeMap::new();"
  , "        for k in m.keys() {"
  , "            out.insert(k.clone(), true);"
  , "        }"
  , "        out"
  , "    }"
  , "    pub fn ext_range(n: i64) -> BTreeMap<i64, bool> {"
  , "        let mut out = BTreeMap::new();"
  , "        let mut i = 0;"
  , "        while i < n {"
  , "            out.insert(i, true);"
  , "            i += 1;"
  , "        }"
  , "        out"
  , "    }"
  , "\n    // TBL file loader for TPCH columnar tables"
  , "    // Parses pipe-delimited files and builds columnar BTreeMaps"
  , "    use std::io::{BufRead, BufReader};"
  , "    use std::fs::File;"
  , ""
  , "    fn parse_tbl_lines(path: &str) -> Vec<Vec<String>> {"
  , "        let file = File::open(path).expect(&format!(\"Failed to open {}\", path));"
  , "        let reader = BufReader::new(file);"
  , "        let mut rows = Vec::new();"
  , "        for line in reader.lines() {"
  , "            let line = line.expect(\"Failed to read line\");"
  , "            // TBL format: field1|field2|...|fieldN|  (trailing pipe)"
  , "            let fields: Vec<String> = line.trim_end_matches('|').split('|').map(|s| s.to_string()).collect();"
  , "            rows.push(fields);"
  , "        }"
  , "        rows"
  , "    }"
  , ""
  , "    // Helper to build columnar maps from rows"
  , "    fn build_string_col(rows: &[Vec<String>], col: usize) -> BTreeMap<i64, String> {"
  , "        let mut m = BTreeMap::new();"
  , "        for (i, row) in rows.iter().enumerate() {"
  , "            m.insert(i as i64, row.get(col).cloned().unwrap_or_default());"
  , "        }"
  , "        m"
  , "    }"
  , ""
  , "    fn build_int_col(rows: &[Vec<String>], col: usize) -> BTreeMap<i64, i64> {"
  , "        let mut m = BTreeMap::new();"
  , "        for (i, row) in rows.iter().enumerate() {"
  , "            let v = row.get(col).and_then(|s| s.parse::<i64>().ok()).unwrap_or(0);"
  , "            m.insert(i as i64, v);"
  , "        }"
  , "        m"
  , "    }"
  , ""
  , "    fn build_real_col(rows: &[Vec<String>], col: usize) -> BTreeMap<i64, Real> {"
  , "        let mut m = BTreeMap::new();"
  , "        for (i, row) in rows.iter().enumerate() {"
  , "            let v = row.get(col).and_then(|s| s.parse::<f64>().ok()).unwrap_or(0.0);"
  , "            m.insert(i as i64, Real::new(v));"
  , "        }"
  , "        m"
  , "    }"
  , ""
  , "    // TPCH table loaders - fields are sorted alphabetically by field name!"
  , "    // nation: n_comment, n_name, n_nationkey, n_regionkey, size"
  , "    // TBL columns: 0=nationkey, 1=name, 2=regionkey, 3=comment"
  , "    pub type NationTable = (BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, i64>, BTreeMap<i64, i64>, i64);"
  , "    fn load_nation(path: &str) -> NationTable {"
  , "        let rows = parse_tbl_lines(path);"
  , "        let size = rows.len() as i64;"
  , "        (build_string_col(&rows, 3), build_string_col(&rows, 1), build_int_col(&rows, 0), build_int_col(&rows, 2), size)"
  , "    }"
  , ""
  , "    // part: p_brand, p_comment, p_container, p_mfgr, p_name, p_partkey, p_retailprice, p_size, p_type, size"
  , "    // TBL columns: 0=partkey, 1=name, 2=mfgr, 3=brand, 4=type, 5=size, 6=container, 7=retailprice, 8=comment"
  , "    pub type PartTable = (BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, i64>, BTreeMap<i64, Real>, BTreeMap<i64, i64>, BTreeMap<i64, String>, i64);"
  , "    fn load_part(path: &str) -> PartTable {"
  , "        let rows = parse_tbl_lines(path);"
  , "        let size = rows.len() as i64;"
  , "        (build_string_col(&rows, 3), build_string_col(&rows, 8), build_string_col(&rows, 6), build_string_col(&rows, 2), build_string_col(&rows, 1), build_int_col(&rows, 0), build_real_col(&rows, 7), build_int_col(&rows, 5), build_string_col(&rows, 4), size)"
  , "    }"
  , ""
  , "    // partsupp: ps_availqty, ps_comment, ps_partkey, ps_suppkey, ps_supplycost, size"
  , "    // TBL columns: 0=partkey, 1=suppkey, 2=availqty, 3=supplycost, 4=comment"
  , "    pub type PartsuppTable = (BTreeMap<i64, Real>, BTreeMap<i64, String>, BTreeMap<i64, i64>, BTreeMap<i64, i64>, BTreeMap<i64, Real>, i64);"
  , "    fn load_partsupp(path: &str) -> PartsuppTable {"
  , "        let rows = parse_tbl_lines(path);"
  , "        let size = rows.len() as i64;"
  , "        (build_real_col(&rows, 2), build_string_col(&rows, 4), build_int_col(&rows, 0), build_int_col(&rows, 1), build_real_col(&rows, 3), size)"
  , "    }"
  , ""
  , "    // region: r_comment, r_name, r_regionkey, size"
  , "    // TBL columns: 0=regionkey, 1=name, 2=comment"
  , "    pub type RegionTable = (BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, i64>, i64);"
  , "    fn load_region(path: &str) -> RegionTable {"
  , "        let rows = parse_tbl_lines(path);"
  , "        let size = rows.len() as i64;"
  , "        (build_string_col(&rows, 2), build_string_col(&rows, 1), build_int_col(&rows, 0), size)"
  , "    }"
  , ""
  , "    // supplier: s_acctbal, s_address, s_comment, s_name, s_nationkey, s_phone, s_suppkey, size"
  , "    // TBL columns: 0=suppkey, 1=name, 2=address, 3=nationkey, 4=phone, 5=acctbal, 6=comment"
  , "    pub type SupplierTable = (BTreeMap<i64, Real>, BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, String>, BTreeMap<i64, i64>, BTreeMap<i64, String>, BTreeMap<i64, i64>, i64);"
  , "    fn load_supplier(path: &str) -> SupplierTable {"
  , "        let rows = parse_tbl_lines(path);"
  , "        let size = rows.len() as i64;"
  , "        (build_real_col(&rows, 5), build_string_col(&rows, 2), build_string_col(&rows, 6), build_string_col(&rows, 1), build_int_col(&rows, 3), build_string_col(&rows, 4), build_int_col(&rows, 0), size)"
  , "    }"
  , ""
  , "    // Generic load interface - dispatches based on type_name"
  , "    // Uses a trait-based approach to avoid unsafe transmutes"
  , "    pub trait LoadTable: Sized { fn load_from(path: &str) -> Self; }"
  , ""
  , "    impl LoadTable for NationTable {"
  , "        fn load_from(path: &str) -> Self { load_nation(path) }"
  , "    }"
  , "    impl LoadTable for PartTable {"
  , "        fn load_from(path: &str) -> Self { load_part(path) }"
  , "    }"
  , "    impl LoadTable for PartsuppTable {"
  , "        fn load_from(path: &str) -> Self { load_partsupp(path) }"
  , "    }"
  , "    impl LoadTable for RegionTable {"
  , "        fn load_from(path: &str) -> Self { load_region(path) }"
  , "    }"
  , "    impl LoadTable for SupplierTable {"
  , "        fn load_from(path: &str) -> Self { load_supplier(path) }"
  , "    }"
  , ""
  , "    pub fn load<T: LoadTable>(path: &str) -> T {"
  , "        T::load_from(path)"
  , "    }"
  , "\n    // Pretty-printing for SDQL values (mirrors Lean showValue)"
  , "    pub trait SDQLShow { fn show(&self) -> String; }"
  , "    impl SDQLShow for i64 { fn show(&self) -> String { self.to_string() } }"
  , "    impl SDQLShow for Real { fn show(&self) -> String { self.0.to_string() } }"
  , "    impl SDQLShow for bool { fn show(&self) -> String { self.to_string() } }"
  , "    impl SDQLShow for String { fn show(&self) -> String { format!(\"\\\"{}\\\"\", self) } }"
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
  , "    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show()) } }"
  , "    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow, T7: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6, T7) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show(), self.6.show()) } }"
  , "    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow, T7: SDQLShow, T8: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6, T7, T8) { fn show(&self) -> String { format!(\"<{}, {}, {}, {}, {}, {}, {}, {}>\", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show(), self.6.show(), self.7.show()) } }"
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
