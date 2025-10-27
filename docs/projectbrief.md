# Project Brief

This project implements a typed core calculus and verified foundations for the Sparse Dictionary Query Language (SDQL) in Lean 4. It provides:

- A mechanized core: types, semimodule structure, tensor-shaped multiplication, and a PHOAS term language with a definitional evaluator.
- A minimal code generation path: compile core terms to a small Rust-like AST to explore execution and future optimization/compilation.
- A Rust-backed test harness and CI that compiles generated Rust, executes tests, and compares printed outputs against the Lean evaluator’s printed outputs.
- Room to extend toward the full SDQL spec (kinds, additional semirings, surface sugar, and verified optimizations).

Primary objectives:

- Faithfully model SDQL’s dictionary-centric semantics and tensor-shaped multiply in Lean.
- Keep terms typed by construction via `AddM`/`ScaleM` evidence for addition and scaling.
- Support practical experimentation via pretty-printing, `#eval` demos, and Rust codegen stubs.
- Provide robust regression testing (Lean→Rust roundtrip) so changes are safe and issues are caught early in CI.

Out of scope for now:

- Full kinding system and cross-semirings promotion proofs.
- Verified optimization passes and end-to-end performance tooling.
