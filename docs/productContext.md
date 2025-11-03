# Product Context

Why it exists:

- SDQL is a functional, sparse-collection language used for concise, analyzable data queries. This project aims to give SDQL a small, rigorous core in Lean to reason about semantics and guide verified compilation.

What it provides today:

- Core calculus: types `bool|int|string|record|dict` with a denotation into Lean types.
- Semimodule structure: `AddM` (addition) and `ScaleM` (scalar action) for dictionaries, records, and scalars; tensor-shaped multiply.
- Terms and evaluation: a PHOAS `Term'` with variables, constants, records (construct and positional projection), dictionaries (empty/insert/lookup), boolean ops, `if`, `let`, addition, multiply, and `sum` over dictionaries. An evaluator executes terms.
- Pretty-printing: custom renderers for records and dictionaries to keep `#eval` usable.
- Surface syntax macros: a Lean mini‑DSL `[SDQL| ... ]` for ergonomic SDQL terms that elaborates to the surface representation (`STerm'`) and is translated to the typed core via `SurfaceCore.ToCore.tr`. Supports literals, records (positional and named literals), dict singleton/lookup, typed empty dicts, `sum`, `let`, `if`, `not`, `+`, and `*{int|bool}`.
- A surface layer with named records: `PartIiProject/SurfaceCore.lean` models a named-record surface and translates to the core positional representation. It supports named `constRecord`, `projByName`, and the same core constructs (`lookup`, `sum`, `add`, `let`, `if`, `not`) plus surface multiplication `mul` with surface-side scaling evidence. Record scaling is supported via `SScale.recordS` using a typed membership proof `Mem` for fields. The translation compiles multiplication by aligning a surface tensor shape `stensor` with the core `tensor` through lemmas (`ty_stensor_eq`, `tyFields_map_stensor`) and uses `HasField.index_getD_ty` to coerce named projections to the correct core type.
- Codegen (prototype): translation of core terms to a compact Rust-like AST and string rendering for quick demos and a path to real backends.
- Tests: a Lean test executable that compiles SDQL to Rust, builds with `rustc`, runs outputs, and compares the printed string of the Rust program against the printed string from Lean’s evaluator.

How it should work:

- Addition applies only when an `AddM` is available; multiply requires compatible `ScaleM` evidence and follows tensor-shape rules (outer products for dictionaries, fieldwise for records, left-unit on scalars).
- Dictionary `lookup` defaults to the additive identity of the value type (via its `AddM`).
- `sum(x in d) e` folds by addition from the zero of the result type.

User experience goals:

- Keep examples simple to explore (`#eval`, `Term.show`, and `renderRust`).
- Provide a compact, readable DSL that mirrors SDQL syntax closely while remaining strictly typed and total.
- Favor small, typed increments that mirror the spec and are easy to verify.
- Enable fearless refactors via an automated, Rust-backed test suite and GitHub Actions CI.
