# Progress

What works:

- Typed core with interpreter: `bool`, `int`, `real`, `string`, `record`, `dict`.
- Semimodule structure: `AddM` (with zeros) and `ScaleM`; includes `AddM.realA` and `ScaleM.realS`; tensor-shaped multiply via `ScaleM.mulDenote`.
- Terms: variables, constants, records (construct/proj by index), dict (empty/insert/lookup), `not`, `if`, `let`, `add`, `mul`, `sum`, and builtins (`And`, `Or`, `Eq`, `StrEndsWith`, `Dom`, `Range`).
- Pretty-printing for records/dicts; numerous `#eval` demos.
- SDQL DSL macros: `[SDQL| ... ]` elaborating to surface `STerm'` with support for literals, records (positional and named), dict singleton/lookup, `sum`, `let`, `if`, `not`, `+`, `*{int|bool}`, boolean ops `&&`/`||`/`==`, and builtins `dom`, `range`, `endsWith`. Typed empty dict has moved to the program DSL.
- Program EDSL: `[SDQLProg { T }| ... ]` produces an `SProg` by scanning `load[U]("file")` occurrences, mapping each distinct path to a free-variable index (alphabetically by path), rewriting the SDQL program body by replacing each `load[...]` with a `fvar[i]` placeholder (and expanding record-typed loads into field-level `let` bindings via positional projections), and then delegating expression elaboration to the shared `[SDQL| … ]` machinery in `SyntaxSDQL.lean`. This EDSL adds type sugar `real`, `varchar(n)` (as `string`), `@vec {K->V}` (alias of `{K->V}`) and forms `sum(<k,v> <- d) …`, `e.field`, and typed empty dicts `{}_{ Tdom, Trange }`. See examples in `PartIiProject/SyntaxSDQLProg.lean`. Use `SurfaceCore.ToCore.trProg` and `Term.show` to inspect the lowered core term.
- Rust codegen: renders expressions, let-blocks, conditionals, dict ops, lookup-with-default, and `sum` as a loop with an accumulator; open-term functions with typed parameters. Supports `real` zeros/addition and maps builtins to external helpers (`ext_and`, `ext_or`, `ext_eq`, `ext_str_ends_with`, `ext_dom`, `ext_range`).
- Program-level Rust codegen: `renderRustProgShown` compiles a core `Prog` to a standalone Rust program. It embeds a tiny `sdql_runtime` module with helpers (`map_insert`, `lookup_or_default`, `dict_add`, `tuple_add0..tuple_add5`), a stub `load<T: Default>` for inputs, and `SDQLShow` printing for scalars, maps, and tuples.
- Testing: Lean test executable `sdql-tests` compiles SDQL→Rust, builds with `rustc`, runs programs, and compares printed strings against Lean’s interpreter (`showValue`).
- Tests: updated to consume `SProg` programs built via `[SDQLProg { T }| ... ]` and to generate Rust via `renderRustProgShown`. `.sdql-test-out/*.rs` and binaries are regenerated through this path.
- CI: GitHub Actions workflow builds the project and runs the test executable on pushes/PRs.
- Surface layer: `PartIiProject/SurfaceCore.lean` implements a named-record surface representation and a surface→core translation. Supports named `constRecord`, `projByName`, dictionary `lookup`, `sum`, `add`, `mul`, `let`, `if`, and `not`. Surface scaling includes scalars, dictionaries, and records (`SScale.recordS`). The translation uses membership proofs `Mem` for record scaling, `HasField.index_getD_ty` for named projection, and `stensor` shape lemmas (`ty_stensor_eq`, `tyFields_map_stensor`) to emit core `mul`.

What’s left to build:

- Boolean semiring OR (instead of XOR) to match SDQL; update examples.
- Promotion and additional scalar semirings beyond `bool`/`int`.
- Replace unsafe `stensor` and rewrite lemmas with total, proven definitions (or otherwise structure recursion so Lean accepts termination), and clean up any remaining `unsafe` markers.
- Surface sugar for sets, arrays, `dom`, `range`.
- Program EDSL polish: configurable load-variable assignment policy (first occurrence vs alphabetical), duplicate-path type consistency checks, and integration hooks for codegen inputs.
- Codegen/runtime completeness for multiply (`sdql_mul`) with tensor-shape behavior (outer product for dicts, fieldwise for records), and extend tuple helpers beyond arity 5 as needed.
- Real file loaders for program inputs (`load[...]`), likely CSV/delimited formats, with type-directed parsing based on `SProg.fvar`.
- Optional: factor the inlined Rust runtime out into a standalone crate and build program binaries with `cargo`.
- Optional: centralize Rust runtime into a crate and drive testing via `cargo` if needed.
 - DSL niceties: multi-entry dict literals, n-ary records beyond 3 fields, named fields at the surface level.

Known issues / caveats:

- `lookup` returns additive identity on misses; sparse representation may elide zero-valued entries.
- Codegen depends on helpers/traits included in generated files; multiplication is not yet wired end-to-end for programs (helpers exist for addition/tuples, and stubs for loaders).
- Rust printing for tuples (records) is implemented for arities up to 5; extend as needed.
- `nix build` may fail to resolve newly-added Lean modules unless the lean4‑nix manifest mapping is updated; `lake build` remains authoritative and succeeds.
- The program EDSL is not yet imported by default; examples in `SyntaxSDQLProg.lean` compile when that module is built. Unrelated TPCH test scaffolding currently fails in `nix build` and is orthogonal to the program EDSL. Build and run tests with `lake build sdql-tests && ./.lake/build/bin/sdql-tests`.
