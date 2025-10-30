# Tech Context

Stack:

- Lean 4 (`lean-toolchain` pinned to `v4.24.0`).
- Lake build (`lake build`) and `#eval` for in-file demos.
- Dependencies: `Std` (TreeMap); no direct `Mathlib` imports in the active core.
- Rust toolchain (`rustc` and `cargo`) available in dev/CI environments.

Dev environment:

- Enter with `nix develop`. The shell uses `elan` to install and expose the
  Lean/Lake toolchain specified in `lean-toolchain` (currently `leanprover/lean4:v4.24.0`).
  We avoid pinning Lean via a Nix overlay beyond what `lean4-nix` derives from `lean-toolchain`; the
  shell prepends the matching `elan` toolchain `bin` directory to `PATH`.

Key modules:

- `PartIiProject/Term.lean`: core types, semimodule evidence, tensor, PHOAS terms, interpreter, printers, examples.
- `PartIiProject/SyntaxSDQL.lean`: Lean macros providing an SDQL mini‑DSL via `[SDQL| ... ]` elaborating to `Term'`. Includes lightweight typeclasses `HasAddM`/`HasScaleM` and helper combinators to infer addition/scaling evidence.
- `PartIiProject/Dict.lean`: purely functional dictionary wrapper on `Std.TreeMap` with an embedded comparator.
- `PartIiProject/HList.lean`: minimal heterogeneous list utilities.
- `PartIiProject/Rust.lean`: simplified Rust AST and pretty-printer.
- `PartIiProject/CodegenRust.lean`: core→Rust AST compiler; `renderRust`/`renderRustFn` and `renderRustShown` helpers; embeds `SDQLShow` runtime for printing.
- `PartIiProject/SurfaceCore.lean`: an explicit surface layer with named records and a surface→core translation (`ToCore.tr`) that erases names to positional records. Translation covers `constRecord`, `projByName`, `lookup`, `sum`, `add`, `mul`, and control flow. Surface scaling covers scalars, dictionaries, and records via `SScale.recordS` (typed membership `Mem`). Multiplication on the surface uses a tensor‑shape `stensor` with rewrite lemmas to align with core `tensor` during translation.
- `PartIiProject.lean`: examples invoking `renderRust` for quick demos.
- Tests:
  - `Tests/Cases.lean`: SDQL test cases and expected printed strings.
  - `Tests/Main.lean`: test runner that compiles and executes Rust programs; compares `stdout` string to expected.

Nix/flake integration:

- `flake.nix` wires `lean4-nix` to the `lean-toolchain`, exposes a dev shell, and provides a package/app to run the `sdql-tests` executable directly via `nix run`.

How to run:

- Build library: `lake build`.
- Build tests: `lake build sdql-tests`.
- Run tests: `lake exe sdql-tests`.
- Explore: open the `.lean` files and evaluate examples with `#eval`.
- Try the DSL: define `def t : Term f0 _ := [SDQL| 3 + 5 ]` or more complex SDQL snippets; evaluate via `#eval` using `Term'.denote`.

Notes/constraints:

- Boolean addition is currently XOR by design; aligning with SDQL would switch to OR. Boolean scaling remains AND.
- Codegen uses placeholder helpers (`sdql_mul`, `dict_add`, `tuple_add`). Execution path for tests relies on embedded runtime shims (`map_insert`, `lookup_or_default`, `SDQLShow`) in the generated program.
- Rust iteration uses `.into_iter()` in the printed `for` loops to match ownership in helpers.
- Kinds and scalar promotion are not modeled yet; only `bool` and `int` scalars are implemented.
- The surface layer now emits multiplication and record scaling. It relies on an unsafe `stensor` (termination not proven) and rewrite lemmas (`ty_stensor_eq`, `tyFields_map_stensor`) to align shapes during translation; consider replacing unsafe definitions once proofs are available.
- Nix caveat: adding new modules (like `PartIiProject/SyntaxSDQL.lean`) can require the flake’s lean4‑nix manifest mapping to include them. Lake builds work; if `nix build` reports a missing module attribute, update manifests/lock or bump to the matching lean manifest (v4.24).
CI:

- GitHub Actions workflow at `.github/workflows/ci.yml` installs Lean and Rust, builds `sdql-tests`, and runs the test executable on pushes/PRs.
