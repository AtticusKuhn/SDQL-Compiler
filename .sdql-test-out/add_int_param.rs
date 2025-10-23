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

// A simple structural measure used for output comparison in tests
trait SDQLMeasure { fn measure(&self) -> i64; }
impl SDQLMeasure for i64 { fn measure(&self) -> i64 { *self } }
impl SDQLMeasure for bool { fn measure(&self) -> i64 { if *self {1} else {0} } }
impl SDQLMeasure for String { fn measure(&self) -> i64 { self.len() as i64 } }
impl<K: Ord + SDQLMeasure, V: SDQLMeasure> SDQLMeasure for BTreeMap<K, V> {
    fn measure(&self) -> i64 {
        let mut acc: i64 = 0;
        for (k, v) in self.iter() {
            acc += 31 * k.measure() + v.measure();
        }
        acc
    }
}

pub fn add_int_param(arg0: i64) -> i64 {
  arg0 + 5
}
fn main() {
  let arg0 = 7;
  let result = add_int_param(arg0);
  println!("{}", SDQLMeasure::measure(&result));
}
