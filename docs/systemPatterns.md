# System Patterns

Architecture overview:

- Core types (`PartIiProject/Term.lean`):
  - `Ty`: `bool | int | string | record (List Ty) | dict Ty Ty`.
  - `Ty.denote`: maps to Lean types; `Dict` wraps `Std.TreeMap` for finite maps.
  - `tensor : Ty → Ty → Ty`: dictionary nests the right type; record maps fields; scalars act as left units.
- Semimodule structure:
  - `AddM t`: additive monoid witness for `t`. Current boolean addition uses XOR; integer uses `+`; dict and record are pointwise/fieldwise. `AddM.zero` gives additive identities and is used for lookup defaults and `sum` inits.
  - `ScaleM sc t`: scalar action of `sc` on `t`. Booleans act via AND; integers via multiplication; extends through dict and record.
- Terms and evaluation:
  - `Term' rep fvar ty`: PHOAS terms with vars, constants, records, dicts (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, and `sum`. `proj` is positional projection (index-based) on records.
  - `Term'.denote`: definitional interpreter using `AddM`/`ScaleM`. `lookup` falls back to `AddM.zero` on misses; `sum` folds with `AddM.denote`.
- Utilities:
  - `HList`: heterogeneous lists with `hmap`, `hmap2`, `dmap` helpers.
  - `Dict`: wrapper with `empty/insert/find?/mapValues` and `Ord` plumbed via a stored comparator.
  - Pretty-printers for records and dicts for clean `#eval` output.

Testing infrastructure:

- Lean test runner:
- `Tests/Cases.lean`: defines SDQL terms and computes expected results using the Lean evaluator’s pretty-printer (`showValue`).
  - `Tests/Main.lean`: compiles each term to a standalone Rust program via `renderRustMeasured`, writes sources to `.sdql-test-out/`, builds with `rustc`, runs binaries, and compares integer outputs.
  - Lake executable target `sdql-tests` drives execution: `lake build sdql-tests` and `lake exe sdql-tests`.

- Rust runtime shims (embedded in generated sources):
- `map_insert`, `lookup_or_default` helpers for maps; `SDQLShow` trait for ints, bools, strings, tuples (limited arities), and `BTreeMap`.
  - The Rust AST printer emits `map_insert(...)` and iterates maps with `.into_iter()` to match the shim.

Code generation integration:

- `renderRustShown` emits a complete Rust `main` that prints the result via the `SDQLShow` trait for comparison with Lean’s `showValue`.
- Current tests avoid `sdql_mul` and complex tuple ops in Rust; those remain placeholders to expand later.

Code generation:

- `PartIiProject/Rust.lean`: a tiny Rust-like AST (`Expr`, `Stmt`, `Ty`) and pretty-printer.
- `PartIiProject/CodegenRust.lean`: compiles core `Term'` to this AST.
  - Maps basic ops (`+`, `^` for bool XOR, `not`, `if`, `let`).
  - `lookup` compiles to `lookup_or_default(m,k,zero)`; `sum` becomes a block with an accumulator and `for (k,v) in map.iter()` loop.
  - `mul` emits a placeholder call `sdql_mul(e1, e2)`; record/dict addition use helper calls `tuple_add` and `dict_add`.
  - Open-term support: `renderRustFn` renders a `fn` with parameter types derived from the core types.

Notable patterns:

- Shape-directed multiply is implemented at the interpreter level via `ScaleM.mulDenote`, ensuring compile-time result shape `tensor t1 t2`.
- Addition and scaling are encoded as explicit evidence, guiding both typing and evaluation.
- Lookups and sums rely on the additive identity of the result to stay total and align with sparse semantics.
- Tests compare Lean vs. Rust by printing values on both sides and checking string equality. Rust programs use `SDQLShow::show(&result)`; Lean uses `showValue`.

Legacy/experiments:

- Earlier surface/named-record experiments (`SurfaceCore.lean`, `surface2.lean`) are archived under `old/` and are not part of the active core.
