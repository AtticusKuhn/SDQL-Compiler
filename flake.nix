{
  description = "Part II Project (Lean 4) with lean4-nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    # Keep lean4-nix as an input in case we restore Nix builds later,
    # but do not depend on its toolchain overlay for dev shells.
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    # lean4-nix is intentionally unused in devShell to avoid pinning Lean
    # in Nix. We rely on `elan` + `lean-toolchain` instead.
    # It remains available in `inputs` for future use.
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
          # Use plain nixpkgs for the dev shell; do not pin Lean here.
          # Lean/Lake will come from `elan` according to `lean-toolchain`.
          pkgs = import nixpkgs { inherit system; };
        in
        {
          devShells.default = pkgs.mkShell {
            # Keep the shell minimal and reproducible. We rely on `elan`
            # to supply Lean/Lake that match `./lean-toolchain`.
            packages = with pkgs; [ git unzip rustc cargo codex uv elan ];

            # Ensure the desired toolchain is available and preferred.
            # This avoids depending on a Lean version packaged in nixpkgs
            # or an overlay that may lag behind the toolchain file.
            shellHook = ''
              if command -v elan >/dev/null 2>&1; then
                TOOLCHAIN=$(cat lean-toolchain)
                echo "Using Lean toolchain $TOOLCHAIN via elan"
                # Try to install silently if missing (ignore failures offline)
                elan toolchain install "$TOOLCHAIN" >/dev/null 2>&1 || true
                # Derive the toolchain path used by elan without shell parameter expansion
                ELAN_TC=$(printf "%s" "$TOOLCHAIN" | sed -e 's#/#--#g' -e 's#:#---#g')
                ELAN_BIN="$HOME/.elan/toolchains/$ELAN_TC/bin"
                if [ -d "$ELAN_BIN" ]; then
                  export PATH="$ELAN_BIN:$PATH"
                fi
              else
                echo "Warning: elan not found; system Lean/Lake (if any) will be used."
              fi
            '';
          };
        };
    };
}
