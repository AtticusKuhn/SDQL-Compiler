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
- `PartIiProject/Dict.lean`: purely functional dictionary wrapper on `Std.TreeMap` with an embedded comparator.
- `PartIiProject/HList.lean`: minimal heterogeneous list utilities.
- `PartIiProject/Rust.lean`: simplified Rust AST and pretty-printer.
- `PartIiProject/CodegenRust.lean`: core→Rust AST compiler; `renderRust`/`renderRustFn` and `renderRustShown` helpers; embeds `SDQLShow` runtime for printing.
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

Notes/constraints:

- Boolean addition is currently XOR by design; aligning with SDQL would switch to OR. Boolean scaling remains AND.
- Codegen uses placeholder helpers (`sdql_mul`, `dict_add`, `tuple_add`). Execution path for tests relies on embedded runtime shims (`map_insert`, `lookup_or_default`, `SDQLShow`) in the generated program.
- Rust iteration uses `.into_iter()` in the printed `for` loops to match ownership in helpers.
- Kinds and scalar promotion are not modeled yet; only `bool` and `int` scalars are implemented.
CI:

- GitHub Actions workflow at `.github/workflows/ci.yml` installs Lean and Rust, builds `sdql-tests`, and runs the test executable on pushes/PRs.
