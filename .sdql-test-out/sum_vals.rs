// Import the SDQL runtime library from external file
#[path = "sdql_runtime.rs"]
mod sdql_runtime;

use std::collections::BTreeMap;
use sdql_runtime::*;
fn main() {

  let result = /* sdql:1429..1487 */ {
    /* sdql:1429..1487 */ let mut acc0 = 0;
    /* sdql:1429..1487 */ for (k1, v2) in /* sdql:1429..1487 */ map_insert(/* sdql:1429..1487 */ map_insert(/* sdql:1429..1487 */ std::collections::BTreeMap::new(), /* sdql:1473..1474 */ 5, /* sdql:1478..1479 */ 6), /* sdql:1465..1466 */ 3, /* sdql:1470..1471 */ 4).into_iter() {
      /* sdql:1429..1487 */ acc0 = acc0 + /* sdql:1484..1485 */ v2;
    }
    acc0
  };
  println!("{}", SDQLShow::show(&result));
}
