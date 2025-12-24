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

Next steps (proposed):

- Implement `sdql_mul` in the Rust runtime/codegen to match `tensor` / `ScaleM.mulDenote`.
- Extend tuple helpers (`tuple_add*`) beyond current arities as needed by larger TPCH record shapes.
- Decide whether to align boolean semiring addition with the SDQL paper (OR instead of XOR).
