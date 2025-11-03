# Active Context

Current focus:

- Maintain an accurate Memory Bank reflecting the Lean core, Rust codegen, the new Rust-backed test harness with CI, and the new surface→core translator.
- Keep guidance aligned with the actual codebase (lookup and sum exist; a surface/named-records layer now exists in `PartIiProject/SurfaceCore.lean`).
- Introduce a Lean macro-based SDQL mini‑DSL for ergonomic authoring of terms that elaborates to surface `STerm'` (then translated to core).

Recent changes (captured here):

- Moved inline tests out of `Term.lean` and top-level into `Tests/`.
- Added a Lean test executable `sdql-tests` that compiles SDQL → Rust, builds with `rustc`, runs binaries, and compares printed strings from Rust against Lean’s pretty-printed results.
- Introduced `renderRustShown` and a new embedded runtime trait `SDQLShow` (replacing `SDQLMeasure`) for value pretty-printing in Rust.
- Adjusted Rust AST printer to use `map_insert(...)` and `.into_iter()` to match runtime helper semantics; dictionary `show` uses `.iter()` for stable order.
- Added GitHub Actions workflow to build and run tests on pushes/PRs.
- Memory Bank correction: removed `Mathlib` as a stated dependency in tech docs; the active core only imports `Std` and local modules.
- New: `PartIiProject/SyntaxSDQL.lean` implements `[SDQL| ... ]` macros that elaborate to the surface layer (`STerm'`). They cover literals, records (positional and named literals), dict singleton/lookup, typed empty dicts `{}_{T1,T2}`, `sum(<k,v> in d)`, `let`, `if`, `not`, addition, and multiply with scalar tags (`*{int}`, `*{bool}`). Added examples with `#eval` to verify via surface→core translation.

- New: `PartIiProject/SurfaceCore.lean` adds an explicit surface layer with named records and field selection by name, plus a surface→core translation (`ToCore.tr`). Translation erases names to positional records, supports `constRecord`, `projByName`, `lookup`, `sum`, `add`, `mul`, `let`, `if`, and `not`. Surface-side scaling evidence covers scalars, dictionaries, and records (`SScale.recordS` with typed membership `Mem`). Multiplication uses a surface tensor `stensor` and rewrite lemmas (`ty_stensor_eq`, `tyFields_map_stensor`) to align result types with core `tensor`. Named projection uses `HasField.index_getD_ty` to coerce the projected field to the expected core type.

Next steps (proposed):

- Boolean semiring alignment: switch `AddM.boolA` from XOR to OR; update examples and, if needed, Rust helpers.
- Expand Rust runtime and codegen to cover multiplication (`sdql_mul`) and record operations so tests can include those.
- Extend `SDQLShow` tuple implementations beyond arity 5 as needed for larger records.
- Scalar promotion: add explicit scalar universes and a `promote` term; extend `ScaleM` to additional semirings.
- Surface sugar: sets/arrays/range and `dom` via elaboration to the core.
- Grow the test suite: add dict addition, nested records/dicts, `ite`, `letin`, more `sum` patterns, and negative cases.
 - DSL: support multi-entry dictionary literals `{ k1 -> v1, k2 -> v2, ... }`, n-ary records, and named field syntax (later) or use the new surface translator. Align boolean semiring with the paper (OR/AND) when ready.
- Surface translator: replace `unsafe` pieces (the `stensor` definition and associated lemmas) with total definitions and proven termination; generalize proofs and tidy the translation. Consider integrating named-records at the DSL level or keep the surface→core pass as the front end.

Open questions:

- How strictly to follow the paper’s boolean semiring in the core vs. keep XOR for debugging convenience?
- Preferred path for named records (core vs. surface translation) given current goals; current direction is a surface→core translator.
- Whether to use `cargo` and a shared Rust crate for runtime helpers vs. embedding helpers in generated sources.
 - How to wire lean4‑nix manifests so `nix build` recognizes newly added modules (lake build already works).
