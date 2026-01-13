# Active Context

Current focus:

- Maintain an accurate Memory Bank reflecting the DeBruijn-only pipeline, Rust codegen, and the Rust-backed test harness.
- Keep parsing simple: `SyntaxSDQL.lean` elaborates SDQL to `LoadTermLoc`, then `untyped.lean` handles load extraction + type inference.
- Keep surface/core terms DeBruijn-indexed (`SurfaceCore2.lean` / `Term2.lean`) with a single lowering pass (`ToCore2`).
- Grow TPCH coverage while filling missing backend pieces (notably multiplication `sdql_mul`).

Latest changes:

- Fixed and documented `Term2` syntactic equality (`BEq`) used by optimisation tests: `PartIiProject/Term2.lean` now implements AST equality up to alpha-equivalence (DeBruijn) while ignoring `SourceLocation` and typing evidence.
- Optimized `sum(<k,v> in range(N)) ...` codegen by adding `Rust.Stmt.forRange` and compiling this pattern to `for k in 0..N { let v = true; ... }`, avoiding an intermediate `BTreeMap` from `ext_range`.
- Added end-to-end optimisation regression tests that compare unoptimised vs optimised program outputs after compiling to Rust and running the produced binaries (`Tests.Cases.TestCase.optimisationEq` + `Tests/Main.lean` support); currently covers vertical loop fusion.
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
- Implemented scalar promotion `promote[max_prod](e)` and the `max_prod` scalar type:
  - Added `Ty.maxProduct` / `SurfaceTy.maxProduct`, `AddM.maxProductA` (addition = max), and `ScaleM.maxProductS` (multiplication).
  - Added `promote` to the parser (`SyntaxSDQL.lean`), pipeline ASTs (`LoadTerm`/`UntypedTerm`), typed surface/core terms (`STerm2`/`Term2`), and surface→core lowering (`ToCore2`).
  - Rust backend: added `MaxProduct` plus `max_product_add` and `promote_*` helpers in `sdql_runtime.rs`; codegen emits these for sums/promotions.
- Enabled TPCH Q15 on SF=0.01 in `Tests/Cases.lean` (the tiny reference binary hardcodes a max-revenue constant and produces `{}` on our tpch-tiny dataset).
- Enabled TPCH Q17 in `Tests/Cases.lean` (was blocked on real division).
- Enabled TPCH Q21 in `Tests/Cases.lean` (was blocked on `size`).
- Enabled TPCH Q09/Q13/Q14/Q16/Q20/Q22 in `Tests/Cases.lean` (tiny + SF=0.01), unblocking additional TPC-H coverage that depends on string functions.
- Fixed SDQL operator precedence in the DSL so `*` and `/` bind tighter than `+` and `-` (this affects expressions like `a*b - c*d` in TPCH Q09).
- Fixed TPCH Q04 on SF=0.01 by (1) making record-field sorting stable for duplicate field names like `_`, and (2) aligning boolean addition with SDQL/reference semantics (OR).
- Fixed Rust backend issues surfaced by Q11/Q15:
  - `sdql_runtime.rs`: `tuple_add*` now uses `SdqlAdd` (so tuple fields like `BTreeMap` can be added).
  - `PartIiProject/Rust.lean`: generated `for` loops iterate via `.clone().into_iter()` to avoid moving maps used more than once.
- Refactored the Rust AST to be DeBruijn-indexed (`Expr : Nat → Type`, vars are `Fin ctx`) and replaced stringly-typed runtime calls with `RuntimeFn`; updated `PartIiProject/CodegenRust.lean` accordingly.
- Added a performance benchmarking runner `Performance.lean` (flake app `performanceComparsion`) that compares runtime (ms) of `sdql-rs` binaries vs Lean-generated Rust binaries, including microbenchmarks and TPCH cases.
- Fixed a dependent-pattern-matching blocker in optimisation passes by refactoring `Term2.mul`/`Term2.proj` to carry typeclass witnesses (`has_tensor`/`has_proj`) instead of computed indices (`tensor` / `List.getD`) directly.
- Added a small `Term2` optimisation framework (`PartIiProject/Optimisations/Apply.lean`) where each rewrite is a non-recursive `Optimisation` and `applyOptimisations{,Loc}` performs the recursive traversal + (fuel-bounded) fixpoint iteration.
- Implemented vertical loop fusion over `Term2` as two separate rewrites in `PartIiProject/Optimisations/VerticalLoopFusion.lean` (`verticalLoopFusionKeyMap2` and `verticalLoopFusionValueMap2`).
- Added/confirmed `#guard_msgs` coverage for vertical loop fusion in `Tests/Optimisations/VerticalLoopFusion.lean` (pulled in via `Tests/GuardMsgs.lean`).

Next steps (proposed):

- Implement `sdql_mul` in the Rust runtime/codegen to match `tensor` / `ScaleM.mulDenote`.
- Extend tuple helpers (`tuple_add*`) beyond current arities as needed by larger TPCH record shapes.
