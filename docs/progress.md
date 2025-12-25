# Progress

What works:

- Typed core foundations: `bool`, `int`, `real`, `date`, `string`, `record`, `dict`, plus denotations and pretty-printing for values.
- Semimodule structure: `AddM` (with zeros) and `ScaleM`; includes `AddM.realA` and `ScaleM.realS`; tensor-shaped multiply via `ScaleM.mulDenote`.
- Source locations: `SourceLocation` threaded through the pipeline (`LoadTermLoc`, `UntypedTermLoc`, `STermLoc2`, `TermLoc2`) for better debugging/error reporting.
- Terms: variables, constants, records (construct/proj by index), dict (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, `sum`, and builtins (`And`, `Or`, `Eq`, `Leq`, `Sub`, `StrEndsWith`, `Dom`, `Range`, `DateLit`, `Concat`).
- Pretty-printing for records/dicts; numerous `#eval` demos.
- SDQL DSL macros: `[SDQL| ... ]` elaborates to `LoadTermLoc`, supporting literals, records (positional and named), dict literals, lookup, `sum`, `let`, `if`, `not`, `+`, `*` (scalar inferred; optional `*{bool|int|real}`), boolean ops, and builtins (`dom`, `range`, `endsWith`, `date`, `concat`).
- New program pipeline (DeBruijn): `[SDQLProg2 { T }| ... ]` elaborates to `LoadTermLoc` then runs `LoadTermLoc → UntypedTermLoc → STermLoc2` to produce an `SProg2` with an explicit typed context (`ctx : List SurfaceTy`) and `loadPaths`.
- Rust codegen: renders expressions, let-blocks, conditionals, dict ops, lookup-with-default, and `sum` as a loop with an accumulator; open-term functions with typed parameters. Supports `real` zeros/addition and maps builtins to external helpers (`ext_and`, `ext_or`, `ext_eq`, `ext_str_ends_with`, `ext_dom`, `ext_range`).
- Program-level Rust codegen: `renderRustProg2Shown` compiles a core `Prog2` to a standalone Rust program. Generated programs import `sdql_runtime.rs` (a standalone file with helpers, loaders, and printing) via `#[path = "sdql_runtime.rs"] mod sdql_runtime;`. The runtime includes:
  - Helpers: `map_insert`, `lookup_or_default`, `dict_add`, `tuple_add0..tuple_add5`
  - Core types: `Real` (Ord-capable f64), `Date` (YYYYMMDD integer)
  - Traits: `SdqlAdd` for semimodule addition, `FromTblField` for TBL parsing, `SDQLShow` for printing
  - TBL loaders: `build_col<T>`, `load_tbl`
  - Extension functions: `ext_and`, `ext_or`, `ext_eq`, `ext_leq`, `ext_sub`, `ext_str_ends_with`, `ext_dom`, `ext_range`
- Generic table loading: For each table parameter, `genTableLoader` generates inline Rust code that uses `load_tbl` to parse the TBL file and `build_col<T>` to extract typed columns. The `elabTyPreserveOrder` function in the DSL preserves field declaration order for load schemas, ensuring column indices match TBL file order.
- Testing: Lean test executable `sdql-tests` compiles SDQL→Rust, builds with `rustc`, runs programs, and compares outputs. Supports two modes:
  - `TestCase.program`: compares against hardcoded expected strings
  - `TestCase.programRef`: dynamically compares against a reference Rust binary (e.g., sdql-rs)
- Tests: updated to consume `SProg2` programs built via `[SDQLProg2 { T }| ... ]` and to generate Rust via `renderRustProg2Shown`. `.sdql-test-out/*.rs` and binaries are regenerated through this path.
- TPCH Q02: now tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q02_tiny`) using dynamic output comparison.
- TPCH Q01: now tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q01_tiny`) using dynamic output comparison.
- TPCH Q03: compiles and is tested against the sdql-rs reference implementation (`sdql-rs/target/release/tpch_q03_tiny`); relies on the `<` builtin (`Lt`/`ext_lt`) and `TPCH_DATASET_PATH` path rewriting for sources that use upstream `datasets/tpch/...` paths.
- Date type: added `Ty.date` primitive with `SDQLDate` wrapper (YYYYMMDD integer), `DateLit` builtin constructor, and `Leq` comparison. Rust codegen uses a simple `Date` struct.
- Real number literals: added `constReal` for floating-point constants in the DSL.
- Subtraction: added `Sub` builtin for arithmetic subtraction on int/real types.
- CI: GitHub Actions workflow builds the project and runs the test executable on pushes/PRs.
- `nix run` support: wrapper script ensures datasets are present and runs tests with proper environment setup; reference binaries are built on-demand by the Lean test runner when missing.
- Surface/core terms are DeBruijn-indexed: surface terms in `SurfaceCore2.lean`, core terms in `Term2.lean`, with lowering in `ToCore2`.

What's left to build:

- **TPCH benchmark completion**:
  - Q03-Q22: not yet implemented; will require additional builtins and potentially more complex aggregation patterns.
- Boolean semiring OR (instead of XOR) to match SDQL; update examples.
- Promotion and additional scalar semirings beyond `bool`/`int`.
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
- Rust printing for tuples (records) is implemented for arities up to 5; extend as needed.
- `nix build` may fail to resolve newly-added Lean modules unless the lean4‑nix manifest mapping is updated; `lake build` remains authoritative and succeeds.
- The DeBruijn pipeline is the only supported term/program representation (older PHOAS layers have been removed).
