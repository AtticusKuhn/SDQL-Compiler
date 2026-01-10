# System Patterns

Architecture overview:

- Core types (`PartIiProject/Term.lean`):
  - `Ty`: `bool | int | real | date | string | record (List Ty) | dict Ty Ty`.
  - `Ty.maxProduct`: scalar semiring over reals where addition is `max` (used via `promote[max_prod](...)`).
  - `Ty.denote`: maps to Lean types; `Dict` wraps `Std.TreeMap` for finite maps.
  - `tensor : Ty → Ty → Ty`: dictionary nests the right type; record maps fields; scalars act as left units.
- Source locations:
  - `SourceLocation` (in `PartIiProject/Term.lean`) tracks byte offsets and a substring for better error reporting/debugging.
- Semimodule structure:
  - `AddM t`: additive monoid witness for `t`. Boolean addition uses OR; integer uses `+`; dict and record are pointwise/fieldwise. `AddM.zero` gives additive identities and is used for lookup defaults and `sum` inits.
  - `AddM.maxProductA`: uses `max` as addition (identity currently `0.0`).
- Real scalars: `AddM.realA` (0.0, `+`) and `ScaleM.realS` (`*`).
- `ScaleM sc t`: scalar action of `sc` on `t`. Booleans act via AND; integers via multiplication; extends through dict and record. Record scaling uses a typed list‑membership predicate `Mem` in `ScaleM.recordS` to select per‑field scaling evidence in a way that supports structural recursion and definitional equalities.
  - `ScaleM.maxProductS`: multiplication for `maxProduct` scalars (uses `*`).
- Terms:
  - Core (DeBruijn): `TermLoc2`/`Term2` in `PartIiProject/Term2.lean`, indexed by `ctx : List Ty` and using `Mem ty ctx` for variables; includes records/dicts, `not`, `if`, `let`, `add`, `mul`, `sum`, `lookup`, and positional record projection `proj`.
  - Surface (DeBruijn): `STermLoc2`/`STerm2` in `PartIiProject/SurfaceCore2.lean`, with named record projection via `HasField`.
  - Builtins: `BuiltinFn` (core) and `SBuiltin` (surface) cover `And`, `Or`, `Eq`, `Leq`, `Sub`, `Div`, `StrEndsWith`, `StrStartsWith`, `StrContains`, `FirstIndex`, `LastIndex`, `SubString`, `Dom`, `Range`, `Size`, `DateLit`, `Year`, and `Concat`.
- Utilities:
  - `HList`: heterogeneous lists with `hmap`, `hmap2`, `dmap` helpers.
  - `Dict`: wrapper with `empty/insert/find?/mapValues` and `Ord` plumbed via a stored comparator.
- Pretty-printers for records and dicts for clean `#eval` output.

DeBruijn program pipeline (new):

- Untyped pipeline + type inference (`PartIiProject/untyped.lean`):
  - Parser output: `LoadTermLoc` (higher-order binders, includes `load` nodes, carries `SourceLocation`).
  - Load extraction: `LoadTermLoc → UntypedTermLoc` (DeBruijn indices; ctx is just a `Nat`).
  - Type inference: `UntypedTermLoc → STermLoc2` (typed DeBruijn surface terms in `SurfaceCore2.lean`).
  - Program packaging: `SProg2` carries `(t, ctx, term, loadPaths)` with `ctx : List SurfaceTy`.
- Typed DeBruijn surface/core (`PartIiProject/SurfaceCore2.lean`, `PartIiProject/Term2.lean`):
  - `STerm2`/`STermLoc2`: typed DeBruijn surface terms, variables via `Mem ty ctx`.
  - `Term2`/`TermLoc2`: typed DeBruijn core terms, variables via `Mem ty ctx`.
  - `ToCore2.trProg2 : SProg2 → Prog2`: erases surface names and lowers to core.

Surface syntax (mini‑DSL):

- `PartIiProject/SyntaxSDQL.lean` defines:
  - `[SDQL| ... ]`: elaborates to `LoadTermLoc` (the front-end pipeline input).
  - `elabSDQLToLoad`: elaborates SDQL syntax to `LoadTermLoc`.
  - Literals: ints, bools, strings.
  - Records: positional `< e1, e2 >`, `< e1, e2, e3 >`, and named `< a = e1, b = e2, ... >` literals.
  - Dicts: singleton `{ k -> v }` and multi‑entry literals. (Typed empty dict moved to the program DSL.)
  - Lookup: `d(k)`; `sum`: `sum( <k, v> in d ) body`.
  - Algebra: `e1 + e2`, `e1 * e2` (scalar inferred, with optional `*{bool|int|real}` for disambiguation); `if`, `not`, `let x = e1 in e2`.
  - Scalar promotion: `promote[max_prod](e)`; multiplication can be annotated as `*{max_prod}`.
  - Boolean/builtin ops: `x && y`, `x || y`, `x == y`, `x <= y`, `x - y`, `dom(e)`, `range(e)`, `size(d)`, `endsWith(x,y)`, `date(n)`, `year(e)`, plus record `concat`.
- Type elaboration: `elabTy` sorts record fields alphabetically for canonical type representation (stable for duplicate names like `_`). `elabTyPreserveOrder` preserves declaration order for load schemas, ensuring field positions match TBL column indices.
- To build a typed program, use `[SDQLProg2 { T }| ... ]` (see `SyntaxSDQLProg.lean`) which runs the full pipeline to produce an `SProg2`.

Surface layer with named records:

- `PartIiProject/SurfaceCore.lean` defines surface *types* (`SurfaceTy`), field lookup proofs (`HasField`), and surface semimodule evidence (`SAdd`/`SScale`), plus a surface tensor shape `stensor`.
- `PartIiProject/SurfaceCore2.lean` defines DeBruijn-indexed surface terms (`STermLoc2`/`STerm2`) including `constRecord` and `projByName` via `HasField`.
- `PartIiProject/Term2.lean` lowers surface terms to core terms via `ToCore2` (erasing names to positional records).

Testing infrastructure:

- Lean test runner:
  - `Tests/Cases.lean`: defines SDQL test cases with two variants:
    - `TestCase.program`: compares output against a hardcoded expected string
    - `TestCase.programRef`: dynamically compares against a reference binary (sdql-rs)
  - `Tests/Main.lean`: compiles each program (`SProg2`) to a standalone Rust program via `renderRustProg2Shown (ToCore2.trProg2 ...)`, writes sources to `.sdql-test-out/`, builds with `rustc`, runs binaries, and compares outputs. For `programRef` tests, first runs the reference binary to get expected output.
  - Lake executable target `sdql-tests` drives execution: `lake build sdql-tests && lake exe sdql-tests`.
  - Reference binaries are built on-demand: if a `programRef` uses a path under `sdql-rs/target/release/`, the test runner will invoke `cargo build --release --bin <name>` from `sdql-rs/` when the binary is missing.
  - Nix wrapper `sdql-tests-with-ref` (invoked by `nix run`) sets up datasets and runs the Lean test runner; it no longer prebuilds sdql-rs binaries.

- Rust runtime (`sdql_runtime.rs`):
  - Standalone file imported via `#[path = "sdql_runtime.rs"] mod sdql_runtime;`
  - Core types: `Real` (Ord-capable f64 wrapper), `Date` (YYYYMMDD integer)
  - Semimodule trait: `SdqlAdd` with implementations for bool (OR), i64, Real, Date, String, BTreeMap, and tuples up to arity 8
  - Helpers: `map_insert`, `lookup_or_default`, `dict_add`, `tuple_add!` (record/tuple addition via `SdqlAdd`, used as `tuple_add!(N)(a,b)`)
  - Extension functions: `ext_and`, `ext_or`, `ext_eq`, `ext_leq`, `ext_lt`, `ext_sub`, `ext_div`, `ext_str_ends_with`, `ext_str_starts_with`, `ext_str_contains`, `ext_first_index`, `ext_last_index`, `ext_sub_string`, `ext_dom`, `ext_range`, `ext_size`, `ext_year`
  - TBL loaders: `FromTblField` trait for type-directed parsing (i64, String, Real, bool, Date), `build_col<T>` for extracting typed columns, `load_tbl` for parsing pipe-delimited TBL files
  - TPCH dataset path override: `load_tbl` rewrites paths under `datasets/tpch/` using `TPCH_DATASET_PATH` (e.g. pointing to `datasets/tpch-tiny`) so SDQL sources can keep upstream paths while tests swap datasets.
  - Printing: `SDQLShow` trait for ints, bools, strings (quoted), tuples (up to arity 8), and `BTreeMap`
  - The Rust AST printer emits `map_insert(...)` and iterates maps with `.clone().into_iter()` to avoid moving maps that are reused later
  - Table loading: `genTableLoader` generates inline loader code for each table parameter, using `load_tbl` and `build_col` with column indices derived from the table schema type
  - Test runner copies `sdql_runtime.rs` to the output directory (`.sdql-test-out/`) before compiling

Code generation integration:

- `renderRustProg2Shown` emits a complete Rust `main` that prints the result via the `SDQLShow` trait.
- Current tests avoid `sdql_mul` and complex tuple ops in Rust; those remain placeholders to expand later.
  - Max-product support is implemented via a dedicated runtime scalar type `MaxProduct`, plus `max_product_add` and `promote_*` helpers.

Code generation:

- `PartIiProject/Rust.lean`: a tiny Rust-like AST (`Expr`, `Stmt`, `Ty`) with DeBruijn indexing:
  - `Expr : (ctx : Nat) → Type` and `Stmt : (ctxIn ctxOut : Nat) → Type`
  - variables are `Fin ctx` (no stringly-typed variable names)
  - block sequencing uses `StmtSeq` to track context growth via `letDecl`
  - runtime calls go through `RuntimeFn` (no stringly-typed function names)
  - loops: `forKV` for `BTreeMap` iteration and `forRange` for `range(n)` iteration without allocating a map
  - pretty-printer takes an initial `NameEnv` for free vars and generates fresh binder names for `letDecl` / `forKV` / `forRange`
- `PartIiProject/CodegenRust.lean`: compiles core terms/programs to this AST.
  - Maps basic ops (`+`, `|` for bool OR, `not`, `if`, `let`).
  - `lookup` compiles to `lookup_or_default(m,k,zero)`; `sum` becomes a block with an accumulator and a `for (k,v) in map.clone().into_iter()` loop.
  - Optimization: `sum(<k,v> in range(N)) ...` compiles to `forRange N ...` (rendered as `for k in 0..N { let v = true; ... }`) to avoid constructing a `BTreeMap` just to iterate `0..N`.
  - `mul` emits a placeholder call `sdql_mul(e1, e2)`; record/dict addition use helper calls `tuple_add` and `dict_add`.
  - Builtins compile to external helpers: `ext_and`, `ext_or`, `ext_eq`, `ext_leq`, `ext_sub`, `ext_div`, `ext_str_ends_with`, `ext_str_starts_with`, `ext_str_contains`, `ext_first_index`, `ext_last_index`, `ext_sub_string`, `ext_dom`, `ext_range`, `ext_size`, `ext_year`, plus record concat support.
  - Program support: `renderRustProg2Shown` renders a complete `main` from a `Prog2`, including table loaders for `loadPaths` and optional `SourceLocation` comments.

Notable patterns:

- Shape-directed multiply is specified via `ScaleM.mulDenote`, ensuring compile-time result shape `tensor t1 t2`; Rust codegen currently emits a placeholder `sdql_mul(...)`.
- For optimisation passes that pattern-match on `Term2`, avoid computed indices in inductive families:
  - `Term2.mul` carries a `has_tensor t1 t2 t3` witness (typeclass) instead of returning `Term2 ctx (tensor t1 t2)` directly.
  - `Term2.proj` carries a `has_proj l i t` witness instead of returning `Term2 ctx (l.getD i Ty.int)` directly.
- Optimisation passes are structured as local, non-recursive rewrites over core terms (`PartIiProject/Optimisations/Apply.lean`): each `Optimisation` is `Term2 ctx ty → Option (Term2 ctx ty)`, and `applyOptimisations{,Loc}` provides the recursive traversal and fuel-bounded fixpoint iteration.
- Addition and scaling are encoded as explicit evidence, guiding typing and compilation.
- Lookups and sums rely on the additive identity of the result to stay total and align with sparse semantics.
- Tests compare Rust program output against expected strings or a reference binary. Rust programs use `SDQLShow::show(&result)`.
- Performance benchmarking uses `Performance.lean` to time direct execution of `sdql-rs` reference binaries vs Lean-generated Rust binaries, writing build artifacts to `.sdql-perf-out/`.

Legacy/experiments:

- Earlier surface/named-record experiments (`SurfaceCore.lean`, `surface2.lean`) are archived under `old/` and are not part of the active core.
