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
        in
        {
          packages = {
            default = sdqlTests;
            sdql-tests = sdqlTests;
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
          };

          devShells.default = pkgs.mkShell {
            # Provide Lean + Lake matching ./lean-toolchain, plus essential tools.
            # Keep this minimal to avoid attr or non-derivation issues on some channels.
            packages =
              [ pkgs.lean.lean pkgs.lean.lake]
              ++ (with pkgs; [ git unzip rustc cargo codex uv ]);
          };
        };
    };
}
