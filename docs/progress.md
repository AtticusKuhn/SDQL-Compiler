# Progress

What works:

- Typed core foundations: `bool`, `int`, `real`, `date`, `string`, `record`, `dict`, plus denotations and pretty-printing for values.
- Semimodule structure: `AddM` (with zeros) and `ScaleM`; includes `AddM.realA` and `ScaleM.realS`; tensor-shaped multiply via `ScaleM.mulDenote`.
- Boolean addition now matches SDQL/reference semantics (OR), fixing set-style aggregations like TPCH Q04’s `l_h`.
- Source locations: `SourceLocation` threaded through the pipeline (`LoadTermLoc`, `UntypedTermLoc`, `STermLoc2`, `TermLoc2`) for better debugging/error reporting.
- Terms: variables, constants, records (construct/proj by index), dict (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, `semiringMul`, `closure`, `sum`, and builtins (`And`, `Or`, `Eq`, `Leq`, `Sub`, `Div`, `StrEndsWith`, `StrStartsWith`, `StrContains`, `FirstIndex`, `LastIndex`, `SubString`, `Dom`, `Range`, `Size`, `DateLit`, `Year`, `Concat`).
- Syntactic equality for core terms: `BEq` on `Term2`/`TermLoc2` checks AST equality up to alpha-equivalence (DeBruijn) and ignores `SourceLocation` and typing evidence.
- Pretty-printing for records/dicts; numerous `#eval` demos.
- SDQL DSL macros: `[SDQL| ... ]` elaborates to `LoadTermLoc`, supporting literals, records (positional and named), dict literals, lookup, `sum`, `let`, `if`, `not`, `+`, `-`, tensor `*` (scalar inferred; optional `*{bool|int|real|max_prod}`), semiring `*s`, `closure(...)`, `/`, boolean ops, and builtins (`dom`, `range`, `size`, `endsWith`, `date`, `concat`).
- New program pipeline (DeBruijn): `[SDQLProg2 { T }| ... ]` elaborates to `LoadTermLoc` then runs `LoadTermLoc → UntypedTermLoc → STermLoc2` to produce an `SProg2` with an explicit typed context (`ctx : List SurfaceTy`) and `loadPaths`.
- Rust codegen: compiles into a DeBruijn-indexed Rust AST (`Expr : Nat → Type`, vars are `Fin ctx`) and renders expressions/blocks/loops; `sum` becomes a block with a mutable accumulator and a `for (k,v) in map.clone().into_iter()` loop. Runtime calls are represented by `RuntimeFn` (no stringly-typed function names).
- Rust codegen optimization: `sum(<k,v> in range(N)) ...` emits a `forRange` loop (`for k in 0..N { let v = true; ... }`) to avoid allocating a `BTreeMap` just to iterate a contiguous integer range.
- Program-level Rust codegen: `renderRustProg2Shown` compiles a core `Prog2` to a standalone Rust program. Generated programs import `sdql_runtime.rs` (a standalone file with helpers, loaders, and printing) via `#[path = "sdql_runtime.rs"] mod sdql_runtime;`. The runtime includes:
  - Helpers: `map_insert`, `lookup_or_default`, `dict_add`, `tuple_add!`
  - Core types: `Real` (Ord-capable f64), `Date` (YYYYMMDD integer)
  - Traits: `SdqlAdd` for semimodule addition, `FromTblField` for TBL parsing, `SDQLShow` for printing
  - TBL loaders: `build_col<T>`, `load_tbl`
  - Extension functions: `ext_and`, `ext_or`, `ext_eq`, `ext_leq`, `ext_lt`, `ext_sub`, `ext_div`, `ext_str_ends_with`, `ext_dom`, `ext_range`, `ext_size`, `ext_year`
- Generic table loading: For each table parameter, `genTableLoader` generates inline Rust code that uses `load_tbl` to parse the TBL file and `build_col<T>` to extract typed columns. The `elabTyPreserveOrder` function in the DSL preserves field declaration order for load schemas, ensuring column indices match TBL file order.
- Testing: Lean test executable `sdql-tests` compiles SDQL→Rust, builds with `rustc`, runs programs, and compares outputs. Supports two modes:
  - `TestCase.program`: compares against hardcoded expected strings
  - `TestCase.programRef`: dynamically compares against a reference Rust binary (e.g., sdql-rs)
- Optimisation testing: `TestCase.optimisationEq` compiles and runs both the unoptimised program and an optimised variant (after applying a list of `Optimisation` rewrites over `Term2`), and asserts their outputs match (end-to-end via the Rust backend).
- Tests: updated to consume `SProg2` programs built via `[SDQLProg2 { T }| ... ]` and to generate Rust via `renderRustProg2Shown`. `.sdql-test-out/*.rs` and binaries are regenerated through this path.
- TPCH Q02: now tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q02_tiny`) using dynamic output comparison.
- TPCH Q01: now tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q01_tiny`) using dynamic output comparison.
- TPCH Q03: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q03_tiny`); relies on the `<` builtin (`Lt`/`ext_lt`) and `TPCH_DATASET_PATH` path rewriting for sources that use upstream `datasets/tpch/...` paths.
- TPCH Q07: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q07_tiny`); relies on `year : date → int` (`year(e)` / `ext_year`).
- TPCH Q09: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q09_tiny`); relies on `StrContains` (`StrContains(s, sub)` / `ext_str_contains`).
- TPCH Q11: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q11_tiny`).
- TPCH Q15: compiles and is tested against the sdql-rs reference implementation on the SF=0.01 dataset (`tpch_q15_sf001`), using `promote[max_prod](...)` and the `max_prod` semiring.
- TPCH Q17: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q17_tiny`); relies on real division `/ : real → real → real` (`ext_div`).
- TPCH Q21: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q21_tiny`); relies on `size : {K -> V} → int` (`size(d)` / `ext_size`).
- TPCH Q13: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q13_tiny`); relies on `FirstIndex`/`LastIndex`.
- TPCH Q14: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q14_tiny`); relies on `StrStartsWith`.
- TPCH Q16: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q16_tiny`); relies on `StrStartsWith` and `FirstIndex`.
- TPCH Q20: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q20_tiny`); relies on `StrStartsWith`.
- TPCH Q22: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q22_tiny`); relies on `StrStartsWith` and `SubString`.
- Date type: added `Ty.date` primitive with `SDQLDate` wrapper (YYYYMMDD integer), `DateLit` builtin constructor, and `Leq` comparison. Rust codegen uses a simple `Date` struct.
- Real number literals: added `constReal` for floating-point constants in the DSL.
- Subtraction: added `Sub` builtin for arithmetic subtraction on int/real types.
- CI: GitHub Actions workflow builds the project and runs the test executable on pushes/PRs.
- `nix run` support: wrapper script ensures datasets are present and runs tests with proper environment setup; reference binaries are built on-demand by the Lean test runner when missing.
- Performance comparison: `Performance.lean` executable `performanceComparison` benchmarks runtime (ms) of `sdql-rs` reference binaries vs Lean-generated Rust binaries.
- Flamegraph profiling: `Flamegraph.lean` executable `flamegraph` generates per-TPCH SVG flamegraphs for Lean-generated Rust binaries.
- Flamegraph runner normalizes `TPCH_DATASET_PATH` and TPCH tiny load paths to absolute paths so dataset loading works from the profiling cargo workspace.
- Optimisation performance comparison: `OptimisationPerformanceComparison.lean` executable `optimisationPerformanceComparison` benchmarks runtime (ms) of unoptimised vs optimised Lean-generated Rust binaries for the implemented SDQL optimisations.
- Surface/core terms are DeBruijn-indexed: surface terms in `SurfaceCore2.lean`, core terms in `Term2.lean`, with lowering in `ToCore2`.
- Optimisation-friendly `Term2` indices: `mul`/`proj` carry `has_tensor`/`has_proj` witnesses to avoid dependent-elimination failures when pattern-matching in optimisation passes.
- Optimisations over `Term2`: `PartIiProject/Optimisations/Apply.lean` provides a recursive driver for non-recursive `Optimisation` rewrites; `PartIiProject/Optimisations/VerticalLoopFusion.lean` implements key-map and value-map vertical loop fusion with `#guard_msgs` regression tests.

What's left to build:

- **TPCH benchmark completion**:
  - Q03-Q22: not yet implemented; will require additional builtins and potentially more complex aggregation patterns.
- Additional scalar semirings and broader promotion rules beyond `max_prod` (promotion infrastructure exists).
- Replace unsafe `stensor` and rewrite lemmas with total, proven definitions (or otherwise structure recursion so Lean accepts termination), and clean up any remaining `unsafe` markers.
- Surface sugar for sets, arrays, `dom`, `range`.
- Program EDSL polish: configurable load-variable assignment policy (first occurrence vs alphabetical), duplicate-path type consistency checks, and integration hooks for codegen inputs.
- Codegen/runtime completeness for multiply (`sdql_mul`) with tensor-shape behavior (outer product for dicts, fieldwise for records), and extend tuple helpers beyond arity 5 as needed.
- ~~Real file loaders for program inputs~~ (DONE: generic TBL loaders with type-directed parsing).
- ~~Optional: factor the inlined Rust runtime out into a standalone crate and build program binaries with `cargo`.~~ (DONE: runtime extracted to `sdql_runtime.rs`; further migration to a cargo crate is optional)
- ~~Optional: centralize Rust runtime into a crate and drive testing via `cargo` if needed.~~ (DONE: centralized in `sdql_runtime.rs`)
- DSL niceties: multi-entry dict literals, n-ary records beyond 3 fields, named fields at the surface level.

Known issues / caveats:

- `lookup` returns additive identity on misses; sparse representation may elide zero-valued entries.
- Codegen depends on helpers/traits included in generated files; multiplication is not yet wired end-to-end for programs (helpers exist for addition/tuples, and stubs for loaders).
- Rust runtime stubs remain for `sdql_semiring_mul` and `sdql_closure` (square-matrix semantics).
- Rust printing for tuples (records) is implemented for arities up to 5; extend as needed.
- Rust loop codegen clones maps before iterating (`.clone().into_iter()`) to avoid moving shared intermediates.
- `nix build` may fail to resolve newly-added Lean modules unless the lean4‑nix manifest mapping is updated; In this case, you need to `git add` the new Lean file.
- The DeBruijn pipeline is the only supported term/program representation (older PHOAS layers have been removed).
