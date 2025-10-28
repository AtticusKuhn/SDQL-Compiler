use std::collections::BTreeMap;

// Minimal runtime helpers used by generated code
fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {
    m.insert(k, v);
    m
}
fn lookup_or_default<K: Ord, V: Clone>(m: BTreeMap<K, V>, k: K, default: V) -> V {
    match m.get(&k) {
        Some(v) => v.clone(),
        None => default,
    }
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

fn main() {
  let result = true ^ false;
  println!("{}", SDQLShow::show(&result));
}
