# Active Context

Current focus:

- Maintain an accurate Memory Bank reflecting the DeBruijn-only pipeline, Rust codegen, and the Rust-backed test harness.
- Keep parsing simple: `SyntaxSDQL.lean` elaborates SDQL to `LoadTermLoc`, then `untyped.lean` handles load extraction + type inference.
- Keep surface/core terms DeBruijn-indexed (`SurfaceCore2.lean` / `Term2.lean`) with a single lowering pass (`ToCore2`).
- Grow TPCH coverage while filling missing backend pieces (notably multiplication `sdql_mul`).

Latest changes:

- Refactored fully to DeBruijn-indexed terms/programs:
  - Removed PHOAS surface/core term layers (`STerm'`/`SProg` and `Term'`/`Prog`).
  - `Term.lean` and `SurfaceCore.lean` now define only shared types, builtins, and semimodule evidence.
  - Typed terms live in `SurfaceCore2.lean` (`STermLoc2`/`SProg2`) and `Term2.lean` (`TermLoc2`/`Prog2`), with lowering in `ToCore2`.
- Parser now targets the pipeline directly:
  - `SyntaxSDQL.lean` elaborates to `LoadTermLoc`.
  - `untyped.lean` does load extraction (`LoadTermLoc → UntypedTermLoc`) and type inference to `STermLoc2`.
- Rust backend now consumes `Prog2` and imports a shared `sdql_runtime.rs` runtime file.
- Tests use `SProg2` throughout; TPCH Q01/Q02/Q03 compare against sdql-rs reference binaries.
- Testing flow: `Tests/Main.lean` builds missing sdql-rs reference binaries on-demand (via `cargo build --release --bin ...`), and `sdql_runtime.rs` supports `TPCH_DATASET_PATH` rewriting for `datasets/tpch/...` paths.
- Fixed a Rust precedence bug in the pretty-printer that could change program meaning (missing parentheses under `*`).
- Surface DSL: multiplication no longer requires a scalar annotation (`*{real}`); the scalar is inferred from operand types, with the annotation still available to disambiguate.
- Added date builtin `year : date → int` with surface syntax `year(e)`; Rust codegen targets `ext_year`, implemented in `sdql_runtime.rs`.
- Added dictionary builtin `size(d) : int`; Rust codegen targets `ext_size`, implemented in `sdql_runtime.rs`.
- Added real division builtin `/ : real → real → real`; Rust codegen targets `ext_div`, implemented in `sdql_runtime.rs`.
- Added string builtins and surface syntax:
  - `StrStartsWith(s, pre) : bool`, `StrContains(s, sub) : bool`, `FirstIndex(s, pat) : int`, `LastIndex(s, pat) : int`, `SubString(s, start, end) : string`
  - Rust codegen targets `ext_str_starts_with`, `ext_str_contains`, `ext_first_index`, `ext_last_index`, `ext_sub_string`, implemented in `sdql_runtime.rs`.
- Enabled TPCH Q07 in `Tests/Cases.lean` (Q08 still pending).
- Enabled TPCH Q11 in `Tests/Cases.lean` (tiny + SF=0.01).
- Enabled TPCH Q15 in `Tests/Cases.lean` (tiny only; SF=0.01 still needs `promote[max_prod]` / max-semirings support).
- Enabled TPCH Q17 in `Tests/Cases.lean` (was blocked on real division).
- Enabled TPCH Q21 in `Tests/Cases.lean` (was blocked on `size`).
- Enabled TPCH Q09/Q13/Q14/Q16/Q20/Q22 in `Tests/Cases.lean` (tiny + SF=0.01), unblocking additional TPC-H coverage that depends on string functions.
- Fixed SDQL operator precedence in the DSL so `*` and `/` bind tighter than `+` and `-` (this affects expressions like `a*b - c*d` in TPCH Q09).
- Fixed TPCH Q04 on SF=0.01 by (1) making record-field sorting stable for duplicate field names like `_`, and (2) aligning boolean addition with SDQL/reference semantics (OR).
- Fixed Rust backend issues surfaced by Q11/Q15:
  - `sdql_runtime.rs`: `tuple_add*` now uses `SdqlAdd` (so tuple fields like `BTreeMap` can be added).
  - `PartIiProject/Rust.lean`: generated `for` loops iterate via `.clone().into_iter()` to avoid moving maps used more than once.
- Refactored the Rust AST to be DeBruijn-indexed (`Expr : Nat → Type`, vars are `Fin ctx`) and replaced stringly-typed runtime calls with `RuntimeFn`; updated `PartIiProject/CodegenRust.lean` accordingly.

Next steps (proposed):

- Implement `sdql_mul` in the Rust runtime/codegen to match `tensor` / `ScaleM.mulDenote`.
- Extend tuple helpers (`tuple_add*`) beyond current arities as needed by larger TPCH record shapes.
