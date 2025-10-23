# Active Context

Current focus:

- Maintain an accurate Memory Bank reflecting the Lean core, Rust codegen, and the new Rust-backed test harness with CI.
- Keep guidance aligned with the actual codebase (lookup and sum exist; surface/named-records are archived under `old/`).

Recent changes (captured here):

- Moved inline tests out of `Term.lean` and top-level into `Tests/`.
- Added a Lean test executable `sdql-tests` that compiles SDQL → Rust, builds with `rustc`, runs binaries, and compares a structural measure against Lean’s evaluator.
- Introduced `renderRustMeasured` to emit standalone Rust programs with embedded mini-runtime (map helpers and `SDQLMeasure`).
- Adjusted Rust AST printer to use `map_insert(...)` and `.into_iter()` to match runtime helper semantics.
- Added GitHub Actions workflow to build and run tests on pushes/PRs.

Next steps (proposed):

- Boolean semiring alignment: switch `AddM.boolA` from XOR to OR; update tests and Rust runtime (`tuple_add`/`dict_add` if introduced).
- Expand Rust runtime and codegen to cover multiplication (`sdql_mul`) and record operations so tests can include those.
- Scalar promotion: add explicit scalar universes and a `promote` term; extend `ScaleM` to additional semirings.
- Surface sugar: sets/arrays/range and `dom` via elaboration to the core.
- Grow the test suite: add dict addition, nested records/dicts, `ite`, `letin`, more `sum` patterns, and negative cases.

Open questions:

- How strictly to follow the paper’s boolean semiring in the core vs. keep XOR for debugging convenience?
- Preferred path for named records (core vs. surface translation) given current goals.
- Whether to use `cargo` and a shared Rust crate for runtime helpers vs. embedding helpers in generated sources.
