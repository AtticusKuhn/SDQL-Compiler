use std::collections::BTreeMap;

// Minimal runtime helpers used by generated code
pub mod sdql_runtime {
    use std::collections::BTreeMap;
    use std::ops::Add;
    use std::cmp::Ordering;

    // Ord-capable f64 wrapper for SDQL real type
    #[derive(Debug, Clone, Copy, Default)]
    pub struct Real(pub f64);
    impl Real { pub fn new(v: f64) -> Self { Real(v) } }
    impl PartialEq for Real { fn eq(&self, other: &Self) -> bool { self.0 == other.0 || (self.0.is_nan() && other.0.is_nan()) } }
    impl Eq for Real {}
    impl PartialOrd for Real { fn partial_cmp(&self, other: &Self) -> Option<Ordering> { Some(self.cmp(other)) } }
    impl Ord for Real {
        fn cmp(&self, other: &Self) -> Ordering {
            self.0.partial_cmp(&other.0).unwrap_or_else(|| {
                if self.0.is_nan() && other.0.is_nan() { Ordering::Equal }
                else if self.0.is_nan() { Ordering::Greater }
                else { Ordering::Less }
            })
        }
    }
    impl Add for Real { type Output = Self; fn add(self, rhs: Self) -> Self { Real(self.0 + rhs.0) } }

    // SDQL Date type: stored as YYYYMMDD integer for ordering
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
    pub struct Date(pub i64);
    impl Date { pub fn new(yyyymmdd: i64) -> Self { Date(yyyymmdd) } }
    impl Add for Date { type Output = Self; fn add(self, rhs: Self) -> Self { rhs } }
    #[macro_export]
    macro_rules! date {
        ($yyyymmdd:literal) => {{ Date::new($yyyymmdd) }};
    }

    pub trait SdqlAdd { fn sdql_add(&self, other: &Self) -> Self; }
    impl SdqlAdd for bool { fn sdql_add(&self, other: &Self) -> Self { *self ^ *other } }
    impl SdqlAdd for i64 { fn sdql_add(&self, other: &Self) -> Self { *self + *other } }
    impl SdqlAdd for Real { fn sdql_add(&self, other: &Self) -> Self { Real(self.0 + other.0) } }
    impl SdqlAdd for Date { fn sdql_add(&self, other: &Self) -> Self { *other } }
    impl SdqlAdd for String {
        fn sdql_add(&self, other: &Self) -> Self {
            let mut s = self.clone();
            s.push_str(other);
            s
        }
    }
    impl<K: Ord + Clone, V: SdqlAdd + Clone> SdqlAdd for BTreeMap<K, V> {
        fn sdql_add(&self, other: &Self) -> Self {
            dict_add(self.clone(), other.clone())
        }
    }
    impl<T1: SdqlAdd> SdqlAdd for (T1,) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0),) } }
    impl<T1: SdqlAdd, T2: SdqlAdd> SdqlAdd for (T1, T2) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1)) } }
    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd> SdqlAdd for (T1, T2, T3) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2)) } }
    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd> SdqlAdd for (T1, T2, T3, T4) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3)) } }
    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4)) } }
    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5)) } }
    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd, T7: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6, T7) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5), self.6.sdql_add(&other.6)) } }
    impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd, T7: SdqlAdd, T8: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6, T7, T8) { fn sdql_add(&self, other: &Self) -> Self { (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5), self.6.sdql_add(&other.6), self.7.sdql_add(&other.7)) } }

    // Insert without mutation at the call-site
    pub fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {
        m.insert(k, v);
        m
    }

    pub fn lookup_or_default<K: Ord, V: Clone>(m: &BTreeMap<K, V>, k: K, default: V) -> V {
        match m.get(&k) {
            Some(v) => v.clone(),
            None => default,
        }
    }

    // Dictionary addition merges keys with value addition
    pub fn dict_add<K: Ord + Clone, V: SdqlAdd + Clone>(a: BTreeMap<K, V>, b: BTreeMap<K, V>) -> BTreeMap<K, V> {
        let mut acc = a;
        for (k, v2) in b.into_iter() {
            if let Some(v1) = acc.get(&k) {
                let new_v = v1.sdql_add(&v2);
                acc.insert(k.clone(), new_v);
            } else {
                acc.insert(k, v2);
            }
        }
        acc
    }

    // Tuple/record addition for small arities
    pub fn tuple_add0(a: (), _b: ()) -> () { a }
    pub fn tuple_add<T1: Add<Output = T1>>(a: (T1,), b: (T1,)) -> (T1,) { (a.0 + b.0,) }
    pub fn tuple_add2<T1: Add<Output = T1>, T2: Add<Output = T2>>(a: (T1, T2), b: (T1, T2)) -> (T1, T2) { (a.0 + b.0, a.1 + b.1) }
    pub fn tuple_add3<T1: Add<Output = T1>, T2: Add<Output = T2>, T3: Add<Output = T3>>(a: (T1, T2, T3), b: (T1, T2, T3)) -> (T1, T2, T3) { (a.0 + b.0, a.1 + b.1, a.2 + b.2) }
    pub fn tuple_add4<T1: Add<Output = T1>, T2: Add<Output = T2>, T3: Add<Output = T3>, T4: Add<Output = T4>>(a: (T1, T2, T3, T4), b: (T1, T2, T3, T4)) -> (T1, T2, T3, T4) { (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3) }
    pub fn tuple_add5<T1: Add<Output = T1>, T2: Add<Output = T2>, T3: Add<Output = T3>, T4: Add<Output = T4>, T5: Add<Output = T5>>(a: (T1, T2, T3, T4, T5), b: (T1, T2, T3, T4, T5)) -> (T1, T2, T3, T4, T5) { (a.0 + b.0, a.1 + b.1, a.2 + b.2, a.3 + b.3, a.4 + b.4) }

    pub fn ext_and(args: (bool, bool)) -> bool { args.0 && args.1 }
    pub fn ext_or(args: (bool, bool)) -> bool { args.0 || args.1 }
    pub fn ext_eq<T: PartialEq>(args: (T, T)) -> bool { args.0 == args.1 }
    pub fn ext_leq<T: PartialOrd>(args: (T, T)) -> bool { args.0 <= args.1 }
    pub fn ext_sub<T: std::ops::Sub<Output = T>>(args: (T, T)) -> T { args.0 - args.1 }
    pub fn ext_str_ends_with(args: (String, String)) -> bool {
        let (s, suf) = args;
        s.ends_with(&suf)
    }
    pub fn ext_dom<K: Ord + Clone, V>(m: &BTreeMap<K, V>) -> BTreeMap<K, bool> {
        let mut out = BTreeMap::new();
        for k in m.keys() {
            out.insert(k.clone(), true);
        }
        out
    }
    pub fn ext_range(n: i64) -> BTreeMap<i64, bool> {
        let mut out = BTreeMap::new();
        let mut i = 0;
        while i < n {
            out.insert(i, true);
            i += 1;
        }
        out
    }

    // Generic TBL file loader for columnar tables
    // Parses pipe-delimited files and builds columnar BTreeMaps
    use std::io::{BufRead, BufReader};
    use std::fs::File;

    /// Trait for parsing a TBL field string into a typed value.
    pub trait FromTblField: Sized + Default {
        fn from_tbl_field(s: &str) -> Self;
    }

    impl FromTblField for i64 {
        fn from_tbl_field(s: &str) -> Self { s.parse().unwrap_or(0) }
    }

    impl FromTblField for String {
        fn from_tbl_field(s: &str) -> Self { s.to_string() }
    }

    impl FromTblField for Real {
        fn from_tbl_field(s: &str) -> Self { Real::new(s.parse().unwrap_or(0.0)) }
    }

    impl FromTblField for bool {
        fn from_tbl_field(s: &str) -> Self { s == "true" || s == "1" }
    }

    impl FromTblField for Date {
        fn from_tbl_field(s: &str) -> Self {
            // Parse date in format YYYY-MM-DD to YYYYMMDD
            let parts: Vec<&str> = s.split('-').collect();
            if parts.len() == 3 {
                let y: i64 = parts[0].parse().unwrap_or(0);
                let m: i64 = parts[1].parse().unwrap_or(0);
                let d: i64 = parts[2].parse().unwrap_or(0);
                Date::new(y * 10000 + m * 100 + d)
            } else {
                // Try parsing as YYYYMMDD directly
                Date::new(s.parse().unwrap_or(0))
            }
        }
    }

    /// Parses a TBL file into rows of string fields.
    fn parse_tbl_lines(path: &str) -> Vec<Vec<String>> {
        let file = File::open(path).unwrap_or_else(|_| panic!("Failed to open {}", path));
        let reader = BufReader::new(file);
        let mut rows = Vec::new();
        for line in reader.lines() {
            let line = line.expect("Failed to read line");
            // TBL format: field1|field2|...|fieldN|  (trailing pipe)
            let fields: Vec<String> = line.trim_end_matches('|').split('|').map(|s| s.to_string()).collect();
            rows.push(fields);
        }
        rows
    }

    /// Generic column builder: parses column `col` from each row into a BTreeMap<i64, T>.
    pub fn build_col<T: FromTblField>(rows: &[Vec<String>], col: usize) -> BTreeMap<i64, T> {
        let mut m = BTreeMap::new();
        for (i, row) in rows.iter().enumerate() {
            let v = row.get(col).map(|s| T::from_tbl_field(s)).unwrap_or_default();
            m.insert(i as i64, v);
        }
        m
    }

    /// Generic TBL loader: parses a TBL file and returns (rows, size).
    /// Callers use build_col to extract typed columns.
    pub fn load_tbl(path: &str) -> (Vec<Vec<String>>, i64) {
        let rows = parse_tbl_lines(path);
        let size = rows.len() as i64;
        (rows, size)
    }

    // Pretty-printing for SDQL values (mirrors Lean showValue)
    pub trait SDQLShow { fn show(&self) -> String; }
    impl SDQLShow for i64 { fn show(&self) -> String { self.to_string() } }
    impl SDQLShow for Real { fn show(&self) -> String { self.0.to_string() } }
    impl SDQLShow for Date { fn show(&self) -> String { format!("date({})", self.0) } }
    impl SDQLShow for bool { fn show(&self) -> String { self.to_string() } }
    impl SDQLShow for String { fn show(&self) -> String { format!("\"{}\"", self) } }
    impl<K: Ord + SDQLShow, V: SDQLShow> SDQLShow for BTreeMap<K, V> {
        fn show(&self) -> String {
            let mut s = String::new();
            s.push('{');
            for (k, v) in self.iter() {
                s.push_str(&format!("{} -> {}, ", k.show(), v.show()));
            }
            s.push('}');
            s
        }
    }

    // Tuple/record pretty-printing for small arities
    impl<T1: SDQLShow> SDQLShow for (T1,) { fn show(&self) -> String { format!("<{}>", self.0.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow> SDQLShow for (T1, T2) { fn show(&self) -> String { format!("<{}, {}>", self.0.show(), self.1.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow> SDQLShow for (T1, T2, T3) { fn show(&self) -> String { format!("<{}, {}, {}>", self.0.show(), self.1.show(), self.2.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow> SDQLShow for (T1, T2, T3, T4) { fn show(&self) -> String { format!("<{}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5) { fn show(&self) -> String { format!("<{}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6) { fn show(&self) -> String { format!("<{}, {}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow, T7: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6, T7) { fn show(&self) -> String { format!("<{}, {}, {}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show(), self.6.show()) } }
    impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow, T7: SDQLShow, T8: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6, T7, T8) { fn show(&self) -> String { format!("<{}, {}, {}, {}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show(), self.6.show(), self.7.show()) } }
} // end module sdql_runtime

// Re-export runtime helpers at crate root for convenience
use sdql_runtime::*;

fn main() {

  let result = 3 + 5;
  println!("{}", SDQLShow::show(&result));
}
