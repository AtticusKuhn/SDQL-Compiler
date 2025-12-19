# Product Context

Why it exists:

- SDQL is a functional, sparse-collection language used for concise, analyzable data queries. This project aims to give SDQL a small, rigorous core in Lean to reason about semantics and guide verified compilation.

What it provides today:

- Core calculus: types `bool|int|real|date|string|record|dict` with a denotation into Lean types.
- Semimodule structure: `AddM` (addition) and `ScaleM` (scalar action) for dictionaries, records, and scalars; tensor-shaped multiply.
- Terms and evaluation: PHOAS core terms with source locations (`TermLoc'`/`Term'`) plus a definitional evaluator. Builtins include `And`, `Or`, `Eq`, `Leq`, `Sub`, `StrEndsWith`, `Dom`, `Range`, `DateLit`, and `Concat`.
- Pretty-printing: custom renderers for records and dictionaries to keep `#eval` usable.
- Surface syntax macros: `[SDQL| ... ]` elaborates to located surface terms (`STermLoc'`/`STerm'`) and can be lowered to the PHOAS core via `SurfaceCore.ToCore.tr`.
- New pipeline (DeBruijn): SDQL parsing can instead produce a `LoadTermLoc`, then run `LoadTermLoc → UntypedTermLoc → SProg2 → Prog2 → Rust` (typed DeBruijn indices throughout).
- A surface layer with named records: `PartIiProject/SurfaceCore.lean` models a named-record surface and translates to the core positional representation. It supports named `constRecord`, `projByName`, and the same core constructs (`lookup`, `sum`, `add`, `let`, `if`, `not`) plus surface multiplication `mul` with surface-side scaling evidence. Record scaling is supported via `SScale.recordS` using a typed membership proof `Mem` for fields. The translation compiles multiplication by aligning a surface tensor shape `stensor` with the core `tensor` through lemmas (`ty_stensor_eq`, `tyFields_map_stensor`) and uses `HasField.index_getD_ty` to coerce named projections to the correct core type.
- Codegen (prototype): translation of core terms to a compact Rust-like AST and string rendering for quick demos and a path to real backends.
- Tests: a Lean test executable that compiles SDQL to Rust, builds with `rustc`, runs outputs, and compares printed outputs (optionally against a reference implementation for TPCH queries).

How it should work:

- Addition applies only when an `AddM` is available; multiply requires compatible `ScaleM` evidence and follows tensor-shape rules (outer products for dictionaries, fieldwise for records, left-unit on scalars).
- Dictionary `lookup` defaults to the additive identity of the value type (via its `AddM`).
- `sum(x in d) e` folds by addition from the zero of the result type.

User experience goals:

- Keep examples simple to explore (`#eval`, `Term.show`, and `renderRust`).
- Provide a compact, readable DSL that mirrors SDQL syntax closely while remaining strictly typed and total.
- Favor small, typed increments that mirror the spec and are easy to verify.
- Enable fearless refactors via an automated, Rust-backed test suite and GitHub Actions CI.
