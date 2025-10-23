# part_ii_project

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

## Development

- Enter the dev shell with `nix develop`. The shell uses `elan` to provide the
  Lean toolchain specified in `lean-toolchain` (currently `leanprover/lean4:v4.24.0`).
  The flake does not pin a Lean version via nix overlays to avoid version skew.

- First time in the shell, `elan` will install the requested toolchain. Then:
  - Check the compiler: `lean --version` should report `4.24.0`.
  - Build the project: `lake build`.

If you prefer not to use the dev shell, you can install `elan` separately and run
`elan toolchain install $(cat lean-toolchain)` to provision Lean + Lake, then `lake build`.
