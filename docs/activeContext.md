# Active Context

Current focus:

- Maintain an accurate Memory Bank reflecting the Lean core, Rust codegen, the new Rust-backed test harness with CI, and the surface→core translator.
- Keep guidance aligned with the actual codebase (lookup and sum exist; a surface/named-records layer now exists in `PartIiProject/SurfaceCore.lean`).
- Lean macro-based SDQL mini‑DSL for ergonomic authoring of terms that elaborates to surface `STerm'` (then translated to core).
- Program EDSL `[SDQLProg { T }| … ]` in `PartIiProject/SyntaxSDQLProg.lean` now delegates all expression parsing to `SyntaxSDQL.lean`. It scans for `load[U]("path.tbl")`, assigns each distinct path to a free-variable index (alphabetically by path), rewrites the SDQL surface term by replacing each `load[...]` with a `fvar[i]` placeholder, and then calls the shared `[SDQL| … ]` elaborator to obtain an `STerm'`. Field projections on loaded records work via hierarchical identifier splitting in the SDQL elaborator. The resulting `SProg` packages the result type, free-variable typing function `fvar`, surface term, and `loadPaths`.

Latest changes:

- **Standalone Rust runtime file**: Extracted the embedded `sdql_runtime` module (~220 lines) from `CodegenRust.lean` into a standalone `sdql_runtime.rs` file (~418 lines, well-documented). Generated SDQL programs now import this file via `#[path = "sdql_runtime.rs"] mod sdql_runtime;`. Benefits:
  - Generated `.rs` files are much smaller and easier to read (e.g., `add_int.rs`: 11 lines vs 236 lines previously)
  - Runtime code is now properly formatted Rust with documentation
  - Single source of truth for the runtime implementation
  - Easier to test and modify the runtime independently
  - Test runner (`Tests/Main.lean`) copies `sdql_runtime.rs` to the output directory before compiling tests

- **TPCH Q01 implementation**: Added a simplified Q01 query that groups lineitem rows by (returnflag, linestatus) and sums quantities. The full Q01 requires `concat` builtin for string concatenation which is not yet implemented. Q01 is currently a compile-only test.

- **Date type and comparison**: Added `Ty.date` as a new primitive type with:
  - `SDQLDate` wrapper struct around an YYYYMMDD integer for proper ordering
  - `DateLit` builtin constructor: `date ( 19980902 )` syntax (note: spaces required due to parser ambiguity)
  - `Leq` builtin for `<=` comparison returning bool
  - Rust codegen generates a `Date` struct with `Ord` implementation

- **Real number literals**: Added `Term'.constReal` for floating-point constants, with DSL support for scientific notation literals.

- **Subtraction operator**: Added `Sub` builtin for arithmetic subtraction on int/real types, with `-` syntax in the DSL.

- **Generic TBL file loader framework**: Replaced hardcoded table-specific loaders with a generic, type-parametrized loading system inspired by sdql-rs. Key changes:
  - `rustRuntimeHeader` now includes `FromTblField` trait for type-directed parsing, `build_col<T>` for generic column extraction, and `load_tbl` for parsing TBL files.
  - `genTableLoader` in `CodegenRust.lean` generates inline loader code based on the table schema type.
  - Added `elabTyPreserveOrder` in `SyntaxSDQL.lean` that preserves field declaration order (for load schemas matching TBL column order) while keeping `elabTy` for alphabetically sorted fields (for type checking).
  - `SyntaxSDQLProg.lean` now uses `elabTyPreserveOrder` for load schemas, ensuring the type field order matches TBL column order.

- **Dynamic reference testing for TPCH Q02**: Added a new `TestCase.programRef` variant that compares Lean-generated Rust code output against a reference Rust implementation (sdql-rs). The test runner now:
  1. Runs the sdql-rs reference binary (`sdql-rs/target/release/tpch_q02_tiny`)
  2. Compiles and runs the Lean-generated Rust code
  3. Compares outputs for equality
  This replaces hardcoded expected strings with dynamic comparison against the reference implementation.

- **Fixed string output formatting**: Updated `SDQLShow` for `String` in `CodegenRust.lean` to wrap strings in quotes (`format!("\"{}\"", self)`) to match the reference implementation's output format.

- **Reordered Q02 record fields**: Adjusted field names in `Tests/TPCH/Q02.lean` to use numeric names (`_1`, `_2`, etc.) ensuring proper alphabetical sorting that matches the reference implementation's field order: `(acctbal, name, nation_name, partkey, mfgr, phone, address, comment)`.

- **Updated flake.nix for nix run**: Added `sdqlTestsWithRef` wrapper that builds the sdql-rs reference binary if needed and runs the tests. Both `lake exe sdql-tests` and `nix run` now work with dynamic reference comparison.

- **Fixed `record.field` parsing in SDQL DSLs**: Resolved parser ambiguity where Lean interpreted `record.field` either as a hierarchical identifier or as dot projection syntax. Added handling for `Lean.choiceKind` in `elabSDQL` to prefer the simpler identifier interpretation when ambiguous. Simplified `SDQLProg` load handling to bind records directly without intermediate field let-bindings. Field projections now work correctly both as hierarchical identifiers (`r.fieldname`) and after expressions (`lookup(d)._1`). This fix enables `Tests/TPCH/Q02.lean` to typecheck successfully.

- Core type system now includes `real` with `AddM.realA` (zero 0.0, +) and `ScaleM.realS` (scalar multiply).
- New builtin functions available through the surface and core: logical `And`/`Or`, equality `Eq` (for int/real/string), string `StrEndsWith`, dictionary `Dom` (key set), and integer `Range` (0..n-1 as `{ int -> bool }`). Implemented as `Term'.builtin` in core and `SBuiltin`/`STerm'.builtin` in the surface, with interpreter support.
- Term DSL `[SDQL| … ]` gains: `&&`, `||`, `==`, `dom(e)`, `range(e)`, `endsWith(x,y)`, and a placeholder `unique(e)` that currently elaborates to `e`. Typed empty dictionaries are no longer supported in the term DSL (kept in the program DSL).
- Program DSL `[SDQLProg { … }| … ]` adds type sugar and forms: `real`, `varchar(n)` (aliased to `string`), `@vec { K -> V }` (alias for `{ K -> V }`), projection `e.field`, `sum(<k,v> <- d) body` sugar, and typed empty dicts `{}_{ Tdom, Trange }`.
- Rust codegen extended to handle `real` zeros/addition and to map builtins to external helpers (`ext_and`, `ext_or`, `ext_eq`, `ext_str_ends_with`, `ext_dom`, `ext_range`).

Recent changes (captured here):

- Moved inline tests out of `Term.lean` and top-level into `Tests/`.
- Added a Lean test executable `sdql-tests` that compiles SDQL → Rust, builds with `rustc`, runs binaries, and compares printed strings from Rust against Lean’s pretty-printed results.
- Introduced `renderRustShown` and a new embedded runtime trait `SDQLShow` for value pretty-printing in Rust.
- Adjusted Rust AST printer to use `map_insert(...)` and `.into_iter()` to match runtime helper semantics; dictionary `show` uses `.iter()` for stable order.
- Added GitHub Actions workflow to build and run tests on pushes/PRs.
- Memory Bank correction: removed `Mathlib` as a stated dependency in tech docs; the active core only imports `Std` and local modules.
- Updated: `PartIiProject/SyntaxSDQL.lean` implements `[SDQL| ... ]` macros that elaborate to the surface layer (`STerm'`). It now covers literals, records (positional and named), dict singleton/lookup, `sum(<k,v> in d)`, `let`, `if`, `not`, addition, multiply with scalar tags (`*{int}`, `*{bool}`), boolean ops `&&`/`||`/`==`, and builtins `dom`, `range`, `endsWith`. It also provides the shared SDQL type grammar (`sdqlty`) and type elaborator `elabTy`, including support for `real`, `varchar(n)` (as `string`), `@vec {K -> V}`, `{K -> V}`, and record schemas `< name : Ty, … >`. Typed empty dicts `{}_{Tdom,Trange}` and `fvar[i]` placeholders are elaborated here so both the term DSL and the program EDSL use exactly the same elaboration pipeline.

- New: Program-level Rust codegen from core `Prog` via `renderRustProgShown`. Generated sources embed a small `sdql_runtime` module containing helpers (`map_insert`, `lookup_or_default`, `dict_add`, `tuple_add0..tuple_add5`), generic TBL loaders (`FromTblField` trait, `build_col<T>`, `load_tbl`), and `SDQLShow` impls for pretty-printing. This shifts codegen from term-level to program-level (inputs are loaded by filename).
- Tests updated to construct programs using `[SDQLProg { T }| ... ]` and to call `renderRustProgShown` on `ToCore.trProg` results. The test runner now regenerates `.sdql-test-out/*.rs` and `.bin` files using the program pipeline.
- Table loading: For each table parameter, codegen generates inline loader code using `load_tbl` and `build_col` with the correct column types and indices, derived from the table schema type.

- New: `PartIiProject/SurfaceCore.lean` adds an explicit surface layer with named records and field selection by name, plus a surface→core translation (`ToCore.tr`). Translation erases names to positional records, supports `constRecord`, `projByName`, `lookup`, `sum`, `add`, `mul`, `let`, `if`, and `not`. Surface-side scaling evidence covers scalars, dictionaries, and records (`SScale.recordS` with typed membership `Mem`). Multiplication uses a surface tensor `stensor` and rewrite lemmas (`ty_stensor_eq`, `tyFields_map_stensor`) to align result types with core `tensor`. Named projection uses `HasField.index_getD_ty` to coerce the projected field to the expected core type.

Next steps (proposed):

- **TPCH benchmark progress**:
  - Q02: fully working with dynamic reference comparison against sdql-rs
  - Q01: simplified version works (compile-only); full version needs `concat` builtin for string concatenation
  - Q03-Q22: not yet implemented
  - Add `concat` builtin to enable full Q01 and potentially other queries
- Boolean semiring alignment: switch `AddM.boolA` from XOR to OR; update examples and, if needed, Rust helpers.
- Expand Rust runtime and codegen to cover multiplication (`sdql_mul`) with full tensor-shape behavior and broaden tuple support.
- ~~Replace the inlined runtime with a shared Rust crate when switching to `cargo` builds; keep the small embedded module for simple `rustc` paths and tests.~~ (DONE: runtime is now in standalone `sdql_runtime.rs` file, imported via `#[path = ...]`)
- ~~Implement typed file loaders for common inputs~~ (DONE: generic TBL loaders using `FromTblField` trait).
- Extend `SDQLShow` tuple implementations beyond arity 5 as needed for larger records.
- Scalar promotion: add explicit scalar universes and a `promote` term; extend `ScaleM` to additional semirings.
- Surface sugar: sets/arrays elaboration layered on top of new `dom`/`range` builtins.
- Grow the test suite: add dict addition, nested records/dicts, `ite`, `letin`, more `sum` patterns, and negative cases.
- DSL: support multi-entry dictionary literals `{ k1 -> v1, k2 -> v2, ... }`, n-ary records, and named field syntax (later) or use the new surface translator. Align boolean semiring with the paper (OR/AND) when ready.
- Surface translator: replace `unsafe` pieces (the `stensor` definition and associated lemmas) with total definitions and proven termination; generalize proofs and tidy the translation. Consider integrating named-records at the DSL level or keep the surface→core pass as the front end.
- Program EDSL: optional dedup policy ("first occurrence" vs alphabetical), and stricter duplicate-type checking for repeated `load` of the same path.

Quick usage examples (Lean):

- Build an `SProg` for a closed arithmetic term:
  - `[SDQLProg { int }| 3 + 5 ]`
- Build an `SProg` referencing an input dictionary file:
  - `[SDQLProg { { int -> int } }| { 3 -> 7 } + load[{ int -> int }]("data.tbl") ]`
  - Use `SurfaceCore.ToCore.trProg` and `Term.show` to pretty-print the lowered core term for debugging.

Open questions:

- How strictly to follow the paper’s boolean semiring in the core vs. keep XOR for debugging convenience?
- Preferred path for named records (core vs. surface translation) given current goals; current direction is a surface→core translator.
- ~~Whether to use `cargo` and a shared Rust crate for runtime helpers vs. embedding helpers in generated sources~~ (resolved: standalone `sdql_runtime.rs` file is used, imported via `#[path = ...]`; optionally could migrate to a cargo crate later).
 - How to wire lean4‑nix manifests so `nix build` recognizes newly added modules (lake build already works).
