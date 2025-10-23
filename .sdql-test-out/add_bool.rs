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

fn main() {
  let result = true ^ false;
  println!("{}", SDQLMeasure::measure(&result));
}
