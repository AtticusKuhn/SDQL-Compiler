use std::collections::BTreeMap;

// Minimal runtime helpers used by generated code
pub mod sdql_runtime {
    use std::collections::BTreeMap;
    use std::ops::Add;

    // Insert without mutation at the call-site
    pub fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {
        m.insert(k, v);
        m
    }

    pub fn lookup_or_default<K: Ord, V: Clone>(m: BTreeMap<K, V>, k: K, default: V) -> V {
        match m.get(&k) {
            Some(v) => v.clone(),
            None => default,
        }
    }

    // Dictionary addition merges keys with value addition
    pub fn dict_add<K: Ord + Clone, V: Add<Output = V> + Clone>(a: BTreeMap<K, V>, b: BTreeMap<K, V>) -> BTreeMap<K, V> {
        let mut acc = a;
        for (k, v2) in b.into_iter() {
            if let Some(v1) = acc.get(&k).cloned() {
                acc.insert(k, v1 + v2);
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

    // Generic stub loader: returns Default::default() and prints path
    pub fn load<T: Default>(_path: &str) -> T {
        // TODO: parse from file at runtime
        Default::default()
    }

    // Pretty-printing for SDQL values (mirrors Lean showValue)
    pub trait SDQLShow { fn show(&self) -> String; }
    impl SDQLShow for i64 { fn show(&self) -> String { self.to_string() } }
    impl SDQLShow for bool { fn show(&self) -> String { self.to_string() } }
    impl SDQLShow for String { fn show(&self) -> String { self.clone() } }
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
} // end module sdql_runtime

// Re-export runtime helpers at crate root for convenience
use sdql_runtime::*;

fn main() {

  let result = lookup_or_default(map_insert(map_insert(std::collections::BTreeMap::new(), 3, 4), 1, 2), 1, 0);
  println!("{}", SDQLShow::show(&result));
}
