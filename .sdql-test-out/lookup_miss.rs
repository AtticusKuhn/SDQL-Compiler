// Import the SDQL runtime library from external file
#[path = "sdql_runtime.rs"]
mod sdql_runtime;

use std::collections::BTreeMap;
use sdql_runtime::*;
fn main() {

  let result = /* sdql:1335..1378 */ lookup_or_default(&/* sdql:1335..1378 */ map_insert(/* sdql:1335..1378 */ map_insert(/* sdql:1335..1378 */ std::collections::BTreeMap::new(), /* sdql:1364..1365 */ 3, /* sdql:1369..1370 */ 4), /* sdql:1356..1357 */ 1, /* sdql:1361..1362 */ 2), /* sdql:1374..1375 */ 0, 0);
  println!("{}", SDQLShow::show(&result));
}
