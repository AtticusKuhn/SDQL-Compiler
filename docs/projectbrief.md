# Project Brief

This project implements a typed core calculus and verified foundations for the Sparse Dictionary Query Language (SDQL) in Lean 4. It provides:

- A mechanized core: types, semimodule structure, and tensor-shaped multiplication.
- A DeBruijn-indexed front-end pipeline: parse SDQL to `LoadTermLoc`, extract loads to `UntypedTermLoc`, type-infer to `STermLoc2`/`SProg2`, and lower to core `TermLoc2`/`Prog2`.
- A minimal code generation path: compile DeBruijn core terms/programs to a small Rust-like AST to explore execution and future optimization/compilation.
- A Rust-backed test harness and CI that compiles generated Rust, executes tests, and compares printed outputs against expected strings (or a reference implementation for TPCH cases).
- Room to extend toward the full SDQL spec (kinds, additional semirings, surface sugar, and verified optimizations).

Primary objectives:

- Faithfully model SDQL’s dictionary-centric semantics and tensor-shaped multiply in Lean.
- Keep terms typed by construction via `AddM`/`ScaleM` evidence for addition and scaling.
- Support practical experimentation via pretty-printing, `#eval` demos, and Rust codegen stubs.
- Provide an ergonomic SDQL surface via Lean macros (`[SDQL| ... ]`, `[SDQLProg2 { T }| ... ]`) that elaborates into the front-end pipeline for quick experiments.
- Provide robust regression testing (Lean→Rust roundtrip) so changes are safe and issues are caught early in CI.

Out of scope for now:

- Full kinding system and cross-semirings promotion proofs.
- Verified optimization passes and more sophisticated performance tooling (multi-run statistics, profiling).
