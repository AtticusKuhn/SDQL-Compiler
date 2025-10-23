# Progress

What works:

- Typed core with interpreter: `bool`, `int`, `string`, `record`, `dict`.
- Semimodule structure: `AddM` (with zeros) and `ScaleM`; tensor-shaped multiply via `ScaleM.mulDenote`.
- Terms: variables, constants, records (construct/proj by index), dict (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, `sum`.
- Pretty-printing for records/dicts; numerous `#eval` demos.
- Rust codegen: renders expressions, let-blocks, conditionals, dict ops, lookup-with-default, and `sum` as a loop with an accumulator; open-term functions with typed parameters.
- Testing: Lean test executable `sdql-tests` compiles SDQL→Rust, builds with `rustc`, runs programs, and compares structural measures against Lean’s interpreter.
- CI: GitHub Actions workflow builds the project and runs the test executable on pushes/PRs.

What’s left to build:

- Boolean semiring OR (instead of XOR) to match SDQL; update examples.
- Promotion and additional scalar semirings beyond `bool`/`int`.
- Named records and field access by name (or a surface translator).
- Surface sugar for sets, arrays, `dom`, `range`.
- Codegen/runtime completeness for multiply (`sdql_mul`) and record/dict addition helpers (or inline expansions) so they can be exercised in tests.
- Optional: centralize Rust runtime into a crate and drive testing via `cargo` if needed.

Known issues / caveats:

- `lookup` returns additive identity on misses; sparse representation may elide zero-valued entries.
- Codegen depends on helpers/traits included in generated files; multiplication and tuple addition remain placeholders not yet tested end-to-end.
- The measure-based comparison abstracts away shapes; it is robust for current use but may miss shape-only differences with equal measures unless expanded (e.g., multi-metric assertions).
