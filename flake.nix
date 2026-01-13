{
  description = "Part II Project (Lean 4) with lean4-nix";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
    lean4-nix.inputs.nixpkgs.follows = "nixpkgs";
    # Rust nightly via oxalica/rust-overlay
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = inputs @ {
    nixpkgs,
    flake-parts,
    lean4-nix,
    rust-overlay,
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
            config.allowUnfree = true;
            overlays = [
              (lean4-nix.readToolchainFile ./lean-toolchain)
              (import rust-overlay)
            ];
          };
          lake = pkgs.callPackage lean4-nix.lake { };

          # Rust toolchain for sdql-rs
          rustToolchain = pkgs.rust-bin.selectLatestNightlyWith (toolchain: toolchain.default);

          # Build the test executable via lake-manifest integration
          sdqlTests = lake.mkPackage {
            name = "sdql-tests";
            src = ./.;
          };

          sdqlPerf = lake.mkPackage {
            name = "performanceComparsion";
            src = ./.;
          };

          # Wrapper script that sets up datasets for tests and runs the Lean test runner.
          # TPCH reference binaries are built on-demand by `Tests/Main.lean`.
          sdqlTestsWithRef = pkgs.writeShellApplication {
            name = "sdql-tests-with-ref";
            runtimeInputs = [ rustToolchain ];
            text = ''
              set -euo pipefail

              # Ensure we're in the project root or can find sdql-rs
              if [ ! -d "sdql-rs" ]; then
                echo "Error: must be run from the project root directory (sdql-rs/ not found)" >&2
                exit 1
              fi

              # Ensure datasets exist
              if [ ! -d "datasets/tpch-tiny" ]; then
                echo "Error: datasets/tpch-tiny not found" >&2
                exit 1
              fi

              # Run tests from the current directory
              exec ${sdqlTests}/bin/sdql-tests "$@"
            '';
          };

          performanceComparsion = pkgs.writeShellApplication {
            name = "performanceComparsion";
            runtimeInputs = [ rustToolchain ];
            text = ''
              set -euo pipefail

              if [ ! -d "sdql-rs" ]; then
                echo "Error: must be run from the project root directory (sdql-rs/ not found)" >&2
                exit 1
              fi

              if [ ! -f "sdql_runtime.rs" ]; then
                echo "Error: must be run from the project root directory (sdql_runtime.rs not found)" >&2
                exit 1
              fi

              if [ ! -d "datasets/tpch-tiny" ]; then
                echo "Error: datasets/tpch-tiny not found" >&2
                exit 1
              fi

              exec ${sdqlPerf}/bin/performanceComparsion "$@"
            '';
          };
          # Runtime tools shared by sdql reference test runners
          sdqlRefRuntimeInputs = with pkgs; [
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

          # Tiny helper to run sbt tests for the Scala sdql reference
          sdqlRefTestRunner = pkgs.writeShellApplication {
            name = "sdql-reference-tests";
            runtimeInputs = sdqlRefRuntimeInputs;
            text = ''
              set -euo pipefail
              cd sdql_reference/sdql
              # build.sbt excludes optional TPCH tests globally via -l tags.
              # Override testOptions in-session so we can run specific suites.
              # Default: run the TPCH codegen suite (fast, dataset‑independent),
              # so we always exercise TPCH coverage and report a non-zero count.
              sbt \
                "set Test / testOptions := Seq(Tests.Argument(TestFrameworks.ScalaTest, \"-P32\"))" \
                "testOnly sdql.backend.CppCodegenTestTPCH"
            '';
          };

          # Optional: end-to-end TPCH tests @ SF=0.01 (interpreter)
          sdqlRefTPCH001 = pkgs.writeShellApplication {
            name = "sdql-reference-tpch-0_01";
            runtimeInputs = sdqlRefRuntimeInputs;
            text = ''
              set -euo pipefail
              cd sdql_reference/sdql
              # Heuristic guard: SF=0.01 lineitem is typically < 20MB.
              if [ ! -f datasets/tpch/lineitem.tbl ]; then
                echo "Missing datasets/tpch/lineitem.tbl. See README.md (TPCH datasets)." >&2
                exit 1
              fi
              sz=$(stat -c %s datasets/tpch/lineitem.tbl || stat -f %z datasets/tpch/lineitem.tbl || echo 0)
              if [ "$sz" -gt 50000000 ]; then
                echo "Detected large TPCH tables (likely SF=1). For fast tests, generate SF=0.01." >&2
                echo "Run: (cd tpch-dbgen && ./dbgen -s 0.01 -vf && mv *.tbl ../datasets/tpch && sed -i 's/|$//' ../datasets/tpch/*.tbl)" >&2
                exit 1
              fi
              # Increase heap a bit for safety on some machines
              set +u
              export SBT_OPTS="$SBT_OPTS -Xmx2g -Xms512m -Xss4m -XX:+UseG1GC"
              set -u
              sbt \
                "set Test / testOptions := Seq(Tests.Argument(TestFrameworks.ScalaTest, \"-P32\"))" \
                "testOnly sdql.backend.InterpreterTest -- -n TestTPCH0_01"
            '';
          };

          # Optional: end-to-end TPCH tests @ SF=1 (compiled C++), requires results symlink
          sdqlRefTPCH1 = pkgs.writeShellApplication {
            name = "sdql-reference-tpch-1";
            runtimeInputs = sdqlRefRuntimeInputs;
            text = ''
              set -euo pipefail
              cd sdql_reference/sdql
              if [ ! -d results ]; then
                echo "Missing ./results symlink. Clone sdql-benchmark and symlink ./results -> sdql-benchmark/results" >&2
                echo "  git clone https://github.com/edin-dal/sdql-benchmark" >&2
                echo "  ln -s sdql-benchmark/results results" >&2
                exit 1
              fi
              if [ ! -f datasets/tpch/lineitem.tbl ]; then
                echo "Missing datasets/tpch/*.tbl. See README.md (TPCH datasets)." >&2
                exit 1
              fi
              # These tests are heavy; don’t change global excludes, just include explicit tag
              set +u
              export SBT_OPTS="$SBT_OPTS -Xmx4g -Xms1g -Xss4m -XX:+UseG1GC"
              set -u
              sbt \
                "set Test / testOptions := Seq(Tests.Argument(TestFrameworks.ScalaTest, \"-P32\"))" \
                "testOnly * -- -n TestTPCH1"
            '';
          };
        in
        {
          packages = {
            default = sdqlTestsWithRef;
            sdql-tests = sdqlTestsWithRef;
            sdql-tests-bare = sdqlTests;
            performanceComparsion = performanceComparsion;
            sdql-reference-tests = sdqlRefTestRunner;
            sdql-reference-tpch-0_01 = sdqlRefTPCH001;
            sdql-reference-tpch-1 = sdqlRefTPCH1;
          };

          # `lake.mkPackage` copies `.lake/build/bin` into `$out/bin`.
          apps = {
            default = {
              type = "app";
              program = "${sdqlTestsWithRef}/bin/sdql-tests-with-ref";
            };
            sdql-tests = {
              type = "app";
              program = "${sdqlTestsWithRef}/bin/sdql-tests-with-ref";
            };
            sdql-tests-bare = {
              type = "app";
              program = "${sdqlTests}/bin/sdql-tests";
            };
            sdql-ref-tests = {
              type = "app";
              program = "${sdqlRefTestRunner}/bin/sdql-reference-tests";
            };
            sdql-ref-tpch-0_01 = {
              type = "app";
              program = "${sdqlRefTPCH001}/bin/sdql-reference-tpch-0_01";
            };
            sdql-ref-tpch-1 = {
              type = "app";
              program = "${sdqlRefTPCH1}/bin/sdql-reference-tpch-1";
            };
            performanceComparsion = {
              type = "app";
              program = "${performanceComparsion}/bin/performanceComparsion";
            };
          };

          devShells.default = pkgs.mkShell {
            # Provide Lean + Lake matching ./lean-toolchain, plus essential tools.
            # Keep this minimal to avoid attr or non-derivation issues on some channels.
            # Use oxalica/rust-overlay nightly toolchain so `cargo bench`
            # works for crates requiring unstable features.
            packages =
              [
                pkgs.lean.lean
                pkgs.lean.lake
                (pkgs.rust-bin.selectLatestNightlyWith (toolchain: toolchain.default))
              ]
              ++ (with pkgs; [
                git unzip codex uv
                gemini-cli
                claude-code
                sshpass
                # sdql reference prerequisites
                # commenting out scala for now
                # jdk17 sbt scala_2_13
                # clang clang-tools gcc gnumake gnused
                # bench/report helpers
                jq gnuplot
              ]);
          };
        };
    };
}
