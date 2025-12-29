# Product Context

Why it exists:

- SDQL is a functional, sparse-collection language used for concise, analyzable data queries. This project aims to give SDQL a small, rigorous core in Lean to reason about semantics and guide verified compilation.

What it provides today:

- Core calculus: types `bool|int|real|date|string|record|dict` with a denotation into Lean types.
- Semimodule structure: `AddM` (addition) and `ScaleM` (scalar action) for dictionaries, records, and scalars; tensor-shaped multiply.
- Terms (DeBruijn): typed surface terms `STermLoc2`/`SProg2` and typed core terms `TermLoc2`/`Prog2`, both indexed by an explicit context `ctx : List _` and using `Mem` proofs for variables. Builtins include `And`, `Or`, `Eq`, `Leq`, `Sub`, `StrEndsWith`, `Dom`, `Range`, `Size`, `DateLit`, `Year`, and `Concat`.
- Parser pipeline: SDQL macros elaborate to `LoadTermLoc`, then run `LoadTermLoc → UntypedTermLoc → STermLoc2/SProg2 → TermLoc2/Prog2 → Rust`.
- Pretty-printing: renderers for records/dictionaries values (`showValue`) and term printers (`Term2.showTermLoc2`) keep `#eval` usable.
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
