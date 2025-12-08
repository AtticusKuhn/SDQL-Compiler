// Import the SDQL runtime library from external file
#[path = "sdql_runtime.rs"]
mod sdql_runtime;

use std::collections::BTreeMap;
use sdql_runtime::*;
fn main() {

  let result = /* sdql:1036..1085 */ map_insert(/* sdql:1036..1085 */ std::collections::BTreeMap::new(), /* sdql:1071..1072 */ 1, /* sdql:1076..1081 */ String::from("one"));
  println!("{}", SDQLShow::show(&result));
}
