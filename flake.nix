{
  description = "Part II Project (Lean 4) with lean4-nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    # Use local git repo (requires committing changes)
    lean4-nix.url = "git+file:///home/atticusk/coding/part_ii_project/lean4nix/lean4-nix";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    ...
  }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "aarch64-darwin"
        "aarch64-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];

      perSystem = { system, ... }:
        let
          pkgs = import nixpkgs {
            inherit system;
            overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
          };
          lake = (lean4-nix.lake { inherit pkgs; });
          # Build the test executable via lake-manifest integration
          sdqlTests = (lake.mkPackage {
            src = ./.;
            # Explicit roots to avoid auto-capitalization from manifest name
            roots = [
              # Build the library part too so tests can import it
              { mod = "PartIiProject"; glob = "andSubmodules"; }
              "Tests.Main"
            ];
          }).executable;
          # Tiny helper to run sbt tests for the Scala sdql reference
          sdqlRefTestRunner = pkgs.writeShellApplication {
            name = "sdql-reference-tests";
            runtimeInputs = with pkgs; [
              # JVM + Scala toolchain
              jdk17
              sbt
              scala_2_13
              # C/C++ toolchain for optional codegen/compilation paths
              clang
              clang-tools
              gcc
              gnumake
              # misc utils mentioned in README
              gnused
              git
            ];
            text = ''
              set -euo pipefail
              cd sdql_reference/sdql
              # The flag -Dsbt.log.noformat=false enables color output
              if [ "$#" -gt 0 ]; then
                exec sbt -Dsbt.log.noformat=false "$@"
              else
                exec sbt -Dsbt.log.noformat=false test
              fi
            '';
          };
        in
        {
          packages = {
            default = sdqlTests;
            sdql-tests = sdqlTests;
            sdql-reference-tests = sdqlRefTestRunner;
          };

          # The executable name defaults to the lowercased manifest name
          # (see lean4-nix buildLeanPackage), which for this repo is
          # "part_ii_project".
          apps = let exePath = "${sdqlTests}/bin/part_ii_project"; in {
            default = {
              type = "app";
              program = exePath;
            };
            sdql-tests = {
              type = "app";
              program = exePath;
            };
            sdql-ref-tests = {
              type = "app";
              program = "${sdqlRefTestRunner}/bin/sdql-reference-tests";
            };
          };

          devShells.default = pkgs.mkShell {
            # Provide Lean + Lake matching ./lean-toolchain, plus essential tools.
            # Keep this minimal to avoid attr or non-derivation issues on some channels.
            packages =
              [ pkgs.lean.lean pkgs.lean.lake]
              ++ (with pkgs; [
                git unzip rustc cargo codex uv
                # sdql reference prerequisites
                jdk17 sbt scala_2_13
                clang clang-tools gcc gnumake gnused
              ]);
          };
        };
    };
}
