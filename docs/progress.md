# Progress

What works:

- Typed core with interpreter: `bool`, `int`, `string`, `record`, `dict`.
- Semimodule structure: `AddM` (with zeros) and `ScaleM`; tensor-shaped multiply via `ScaleM.mulDenote`.
- Terms: variables, constants, records (construct/proj by index), dict (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, `sum`.
- Pretty-printing for records/dicts; numerous `#eval` demos.
- SDQL DSL macros: `[SDQL| ... ]` elaborating to `Term'` with support for literals, records/projection, dict singleton/lookup, typed empty dicts, `sum`, `let`, `if`, `not`, `+`, and `*{int|bool}`; examples are evaluated via `#eval`.
- Rust codegen: renders expressions, let-blocks, conditionals, dict ops, lookup-with-default, and `sum` as a loop with an accumulator; open-term functions with typed parameters.
- Testing: Lean test executable `sdql-tests` compiles SDQL→Rust, builds with `rustc`, runs programs, and compares printed strings against Lean’s interpreter (`showValue`).
- CI: GitHub Actions workflow builds the project and runs the test executable on pushes/PRs.
 - Surface layer: `PartIiProject/SurfaceCore.lean` implements a named-record surface representation and a surface→core translation. Supports named `constRecord`, `projByName`, dictionary `lookup`, `sum`, `add`, `let`, `if`, and `not`. Builds cleanly and coexists with the DSL and tests.

What’s left to build:

- Boolean semiring OR (instead of XOR) to match SDQL; update examples.
- Promotion and additional scalar semirings beyond `bool`/`int`.
- Surface multiplication and record scaling evidence on the surface (consider re‑introducing `SScale.recordS` with an `HList`-based approach) and a robust `stensor`/`tensor` alignment lemma if surface emits multiply.
- Surface sugar for sets, arrays, `dom`, `range`.
- Codegen/runtime completeness for multiply (`sdql_mul`) and record/dict addition helpers (or inline expansions) so they can be exercised in tests.
- Optional: centralize Rust runtime into a crate and drive testing via `cargo` if needed.
 - DSL niceties: multi-entry dict literals, n-ary records beyond 3 fields, named fields at the surface level.

Known issues / caveats:

- `lookup` returns additive identity on misses; sparse representation may elide zero-valued entries.
- Codegen depends on helpers/traits included in generated files; multiplication and tuple addition remain placeholders not yet tested end-to-end.
- Rust printing for tuples (records) is implemented for arities up to 5; extend as needed.
 - `nix build` may fail to resolve newly-added Lean modules unless the lean4‑nix manifest mapping is updated; `lake build` remains authoritative and succeeds.
