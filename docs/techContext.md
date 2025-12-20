# Tech Context

Stack:

- Lean 4 (`lean-toolchain` pinned to `v4.24.0`).
- Lake build (`lake build`) and `#eval` for in-file demos.
- Dependencies: `Std` (TreeMap); no direct `Mathlib` imports in the active core.
- Rust toolchain (`rustc` and `cargo`) available in dev/CI environments. The
  dev shell uses nightly via `oxalica/rust-overlay` to support crates that
  require `#![feature]` (e.g., running `cargo bench`).

Dev environment:

- Enter with `nix develop`.
  - Lean/Lake: provided via `lean4-nix` reading `lean-toolchain` (currently
    `leanprover/lean4:v4.24.0`) using `elan` under the hood.
  - Rust: provided by `rust-overlay` nightly
    (`rust-bin.selectLatestNightlyWith (toolchain: toolchain.default)`), so
    `rustc`/`cargo` in PATH are nightly builds.

Key modules:

- `PartIiProject/Term.lean`: core types (`Ty`), semimodule evidence (`AddM`/`ScaleM`), `tensor`, builtins, and `SourceLocation`.
- `PartIiProject/SurfaceCore.lean`: surface types (`SurfaceTy`), field proofs (`HasField`), surface semimodule evidence (`SAdd`/`SScale`), and surface tensor `stensor`.
- `PartIiProject/SurfaceCore2.lean`: typed DeBruijn surface terms (`STerm2`/`STermLoc2`) and `SProg2`.
- `PartIiProject/Term2.lean`: typed DeBruijn core terms (`Term2`/`TermLoc2`), `Prog2`, and lowering `ToCore2.trProg2`.
- `PartIiProject/untyped.lean`: new pipeline pieces:
  - `LoadTermLoc` (parser output, includes `load`)
  - `UntypedTermLoc` (DeBruijn, untyped)
  - type inference `typeinferOpen2` and pipeline entrypoint `loadTermToSProg2`
- `PartIiProject/SyntaxSDQL.lean`: SDQL mini‑DSL:
  - `[SDQL| ... ]` elaborates to `LoadTermLoc` (parser output for the pipeline)
  - `elabSDQLToLoad` elaborates SDQL syntax to `LoadTermLoc`
- `PartIiProject/SyntaxSDQLProg.lean`: program EDSL:
  - `[SDQLProg2 { T }| ... ]` builds an `SProg2` via `LoadTermLoc → UntypedTermLoc → STermLoc2`
- `PartIiProject/Dict.lean`: purely functional dictionary wrapper on `Std.TreeMap` with an embedded comparator.
- `PartIiProject/HList.lean`: minimal heterogeneous list utilities.
- `PartIiProject/Rust.lean`: simplified Rust AST and pretty-printer.
- `PartIiProject/CodegenRust.lean`: core→Rust compiler; supports `Prog2` via `renderRustProg2Shown` and imports the shared runtime from `sdql_runtime.rs`.
- `PartIiProject.lean`: examples invoking `renderRust` for quick demos.
- Tests:
  - `Tests/Cases.lean`: SDQL test cases and expected printed strings.
  - `Tests/Main.lean`: test runner that compiles and executes Rust programs; compares `stdout` string to expected.

Nix/flake integration:

- `flake.nix` wires `lean4-nix` to the `lean-toolchain`, exposes a dev shell, and provides a package/app to run the `sdql-tests` executable directly via `nix run`.
- Repository dependencies used by the test suite are tracked as git submodules (`sdql-rs`, `tpch-dbgen`, `sdql_reference/sdql`, `lean4nix/lean4-nix`).

How to run:

- Build library: `lake build`.
- Build tests: `lake build sdql-tests`.
- Run tests: `lake exe sdql-tests`.
- Preferred: `nix run` (runs the full test suite, including building the sdql-rs reference binary if needed).
- Explore: open the `.lean` files and evaluate examples with `#eval`.
- Try the DSL: use `[SDQLProg2 { int }| 3 + 5 ]` (runs the full pipeline) or start from `[SDQL| 3 + 5 ]` and call `loadTermToSProg2` explicitly.

Notes/constraints:

- Boolean addition is currently XOR by design; aligning with SDQL would switch to OR. Boolean scaling remains AND.
- Codegen uses placeholder helpers (`sdql_mul`, `dict_add`, `tuple_add`). Execution path for tests relies on embedded runtime shims (`map_insert`, `lookup_or_default`, `SDQLShow`) in the generated program.
- Rust iteration uses `.into_iter()` in the printed `for` loops to match ownership in helpers.
- Kinds and scalar promotion are not modeled yet; scalars implemented include `bool`, `int`, and now `real` in the core.
- Surface multiplication uses `stensor` and casts via `ty_stensor_eq2`/`tyFields_map_stensor2` during surface→core lowering; these are currently `unsafe` (termination not proven).
- Nix caveat: adding new modules (like `PartIiProject/SyntaxSDQL.lean`) can require the flake’s lean4‑nix manifest mapping to include them. Lake builds work; if `nix build` reports a missing module attribute, update manifests/lock or bump to the matching lean manifest (v4.24).
CI:

- GitHub Actions workflow at `.github/workflows/ci.yml` installs Lean and Rust, builds `sdql-tests`, and runs the test executable on pushes/PRs.
