# System Patterns

Architecture overview:

- Core types (`PartIiProject/Term.lean`):
  - `Ty`: `bool | int | real | string | record (List Ty) | dict Ty Ty`.
  - `Ty.denote`: maps to Lean types; `Dict` wraps `Std.TreeMap` for finite maps.
  - `tensor : Ty → Ty → Ty`: dictionary nests the right type; record maps fields; scalars act as left units.
- Semimodule structure:
  - `AddM t`: additive monoid witness for `t`. Current boolean addition uses XOR; integer uses `+`; dict and record are pointwise/fieldwise. `AddM.zero` gives additive identities and is used for lookup defaults and `sum` inits.
- Real scalars: `AddM.realA` (0.0, `+`) and `ScaleM.realS` (`*`).
- `ScaleM sc t`: scalar action of `sc` on `t`. Booleans act via AND; integers via multiplication; extends through dict and record. Record scaling uses a typed list‑membership predicate `Mem` in `ScaleM.recordS` to select per‑field scaling evidence in a way that supports structural recursion and definitional equalities.
- Terms and evaluation:
  - `Term' rep fvar ty`: PHOAS terms with vars, constants, records, dicts (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, and `sum`. `proj` is positional projection (index-based) on records.
  - Builtins: `BuiltinFn` provides `And`, `Or`, `Eq`, `StrEndsWith`, `Dom` (key set), and `Range` (0..n-1). Applied via `Term'.builtin`.
  - `Term'.denote`: definitional interpreter using `AddM`/`ScaleM` plus builtin semantics. `lookup` falls back to `AddM.zero` on misses; `sum` folds with `AddM.denote`.
- Utilities:
  - `HList`: heterogeneous lists with `hmap`, `hmap2`, `dmap` helpers.
  - `Dict`: wrapper with `empty/insert/find?/mapValues` and `Ord` plumbed via a stored comparator.
- Pretty-printers for records and dicts for clean `#eval` output.

Surface syntax (mini‑DSL):

- `PartIiProject/SyntaxSDQL.lean` defines a `[SDQL| ... ]` quasiquoter that elaborates to surface `STerm'` (from `SurfaceCore`) instead of directly to core `Term'`:
  - Literals: ints, bools, strings.
  - Records: positional `< e1, e2 >`, `< e1, e2, e3 >`, and named `< a = e1, b = e2, ... >` literals.
  - Dicts: singleton `{ k -> v }` and multi‑entry literals. (Typed empty dict moved to the program DSL.)
  - Lookup: `d(k)`; `sum`: `sum( <k, v> in d ) body`.
  - Algebra: `e1 + e2`, `e1 *{int} e2`, `e1 *{bool} e2`; `if`, `not`, `let x = e1 in e2`.
  - Boolean/builtin ops: `x && y`, `x || y`, `x == y`, `dom(e)`, `range(e)`, `endsWith(x,y)`.
- The DSL uses surface wrapper typeclasses `HasSAdd`/`HasSScale` and helpers `SDQL.add`, `SDQL.mulInt/Bool`, `SDQL.lookup`, `SDQL.sum` to infer `SAdd`/`SScale` evidence (ints, bools, dictionaries, and records via recursive builders).
- Type elaboration: `elabTy` sorts record fields alphabetically for canonical type representation. `elabTyPreserveOrder` preserves declaration order for load schemas, ensuring field positions match TBL column indices.
- To run or print, use `SurfaceCore.ToCore.tr` to translate `STerm'` to core `Term'`.

Surface layer with named records:

- `PartIiProject/SurfaceCore.lean` defines an explicit “surface” representation with names:
  - `SurfaceTy`: mirrors core types but `record` carries a `List (String × SurfaceTy)`.
  - `SAdd` and `SScale`: surface-side evidence for addition and scaling. Scaling covers scalars, dictionaries, and records via `SScale.recordS`, which accepts a function producing per-field scale evidence from a typed list‑membership proof `Mem`.
  - `STerm'`: surface terms featuring `constRecord` and `projByName` using a `HasField` proof to locate a field by name; plus `add`, `mul`, `lookup`, `sum`, `let`, `if`, `not`, `dict` empty/insert, and `builtin` nodes (`SBuiltin` for And/Or/Eq/StrEndsWith/Dom/Range). A surface tensor shape `stensor` matches the core shape at erased types.
  - `ToCore.tr`: translation erases names to positional records (`Ty.record (tyFields …)`), translates `SAdd`/`SScale` to core `AddM`/`ScaleM`, compiles named projection to positional `proj` via an index computed from `HasField` and the lemma `HasField.index_getD_ty`, and emits core `mul` while rewriting the result type using lemmas `ty_stensor_eq` and `tyFields_map_stensor` to align `stensor` with core `tensor`.

Testing infrastructure:

- Lean test runner:
  - `Tests/Cases.lean`: defines SDQL test cases with two variants:
    - `TestCase.program`: compares output against a hardcoded expected string
    - `TestCase.programRef`: dynamically compares against a reference binary (sdql-rs)
  - `Tests/Main.lean`: compiles each term to a standalone Rust program via `renderRustProgShown`, writes sources to `.sdql-test-out/`, builds with `rustc`, runs binaries, and compares outputs. For `programRef` tests, first runs the reference binary to get expected output.
  - Lake executable target `sdql-tests` drives execution: `lake build sdql-tests && lake exe sdql-tests`.
  - Nix wrapper `sdql-tests-with-ref` builds sdql-rs reference binary if needed and runs tests: `nix run`.

- Rust runtime shims (embedded in generated sources):
  - `map_insert`, `lookup_or_default` helpers for maps; `SDQLShow` trait for ints, bools, strings (quoted), tuples (limited arities), and `BTreeMap`.
  - Generic TBL loaders: `FromTblField` trait for type-directed parsing (i64, String, Real, bool), `build_col<T>` for extracting typed columns, `load_tbl` for parsing pipe-delimited TBL files.
  - The Rust AST printer emits `map_insert(...)` and iterates maps with `.into_iter()` to match the shim.
  - Table loading: `genTableLoader` generates inline loader code for each table parameter, using `load_tbl` and `build_col` with column indices derived from the table schema type.

Code generation integration:

- `renderRustShown` emits a complete Rust `main` that prints the result via the `SDQLShow` trait for comparison with Lean’s `showValue`.
- Current tests avoid `sdql_mul` and complex tuple ops in Rust; those remain placeholders to expand later.

Code generation:

- `PartIiProject/Rust.lean`: a tiny Rust-like AST (`Expr`, `Stmt`, `Ty`) and pretty-printer.
- `PartIiProject/CodegenRust.lean`: compiles core `Term'` to this AST.
  - Maps basic ops (`+`, `^` for bool XOR, `not`, `if`, `let`).
  - `lookup` compiles to `lookup_or_default(m,k,zero)`; `sum` becomes a block with an accumulator and `for (k,v) in map.iter()` loop.
  - `mul` emits a placeholder call `sdql_mul(e1, e2)`; record/dict addition use helper calls `tuple_add` and `dict_add`.
  - Builtins compile to external helpers: `ext_and`, `ext_or`, `ext_eq`, `ext_str_ends_with`, `ext_dom`, `ext_range`. Real zeros/addition are supported alongside ints.
  - Open-term support: `renderRustFn` renders a `fn` with parameter types derived from the core types.

Notable patterns:

- Shape-directed multiply is implemented at the interpreter level via `ScaleM.mulDenote`, ensuring compile-time result shape `tensor t1 t2`. On the surface, an unsafe `stensor` is related to core `tensor` by rewrite lemmas to justify emitting `mul` during translation.
- Addition and scaling are encoded as explicit evidence, guiding both typing and evaluation.
- Lookups and sums rely on the additive identity of the result to stay total and align with sparse semantics.
- Tests compare Lean vs. Rust by printing values on both sides and checking string equality. Rust programs use `SDQLShow::show(&result)`; Lean uses `showValue`.

Legacy/experiments:

- Earlier surface/named-record experiments (`SurfaceCore.lean`, `surface2.lean`) are archived under `old/` and are not part of the active core.
