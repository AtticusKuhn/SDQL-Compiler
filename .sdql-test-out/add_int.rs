// Import the SDQL runtime library from external file
#[path = "sdql_runtime.rs"]
mod sdql_runtime;

use std::collections::BTreeMap;
use sdql_runtime::*;
fn main() {

  let result = /* sdql:959..985 */ /* sdql:978..979 */ 3 + /* sdql:982..983 */ 5;
  println!("{}", SDQLShow::show(&result));
}
