// Import the SDQL runtime library from external file
#[path = "sdql_runtime.rs"]
mod sdql_runtime;

use std::collections::BTreeMap;
use sdql_runtime::*;
fn main() {

  let result = /* sdql:1238..1281 */ lookup_or_default(&/* sdql:1238..1281 */ map_insert(/* sdql:1238..1281 */ map_insert(/* sdql:1238..1281 */ std::collections::BTreeMap::new(), /* sdql:1267..1268 */ 3, /* sdql:1272..1273 */ 4), /* sdql:1259..1260 */ 1, /* sdql:1264..1265 */ 2), /* sdql:1277..1278 */ 1, 0);
  println!("{}", SDQLShow::show(&result));
}
