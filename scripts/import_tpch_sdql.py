#!/usr/bin/env python3
"""
Import TPCH SDQL programs from `sdql-rs/progs/tpch/*.sdql` and scaffold Lean
modules under `Tests/TPCH/QXX.lean`.

Each generated module contains:
- A commented copy of the original SDQL program for reference,
- A stub `SProg` that compiles and keeps the module loadable, and
- A commented "attempted port" using the `[SDQLProg { .. }| .. ]` macro where
  the original program is wrapped in the ergonomic DSL. This is intentionally
  commented out because many constructs are not yet supported in the Lean DSL.

Run this script after updating SDQL sources to refresh the scaffolding.
"""
from __future__ import annotations

import os
import glob
import textwrap

SRC_DIR = os.path.join('sdql-rs', 'progs', 'tpch')
OUT_DIR = os.path.join('Tests', 'TPCH')


def to_modname(n: int | str) -> str:
    return f"Q{int(n):02d}"


def main() -> None:
    os.makedirs(OUT_DIR, exist_ok=True)
    sdql_files = sorted(
        glob.glob(os.path.join(SRC_DIR, '*.sdql')),
        key=lambda p: int(os.path.basename(p).split('.')[0]),
    )
    for path in sdql_files:
        base = os.path.basename(path)
        qnum = os.path.splitext(base)[0]
        mod = to_modname(qnum)
        with open(path, 'r') as f:
            sdql = f.read().rstrip('\n')

        commented = '\n'.join('-- ' + line for line in sdql.splitlines())

        lean = f'''import PartIiProject.SyntaxSDQLProg
import PartIiProject.SurfaceCore

namespace Tests.TPCH

open PartIiProject

/-
Source: {path}
-/

-- Raw SDQL (for reference)
-- BEGIN SDQL
{commented}
-- END SDQL

-- Stub SProg to keep module usable
unsafe def {mod}_stub : SProg := [SDQLProg {{ int }}| 0 ]

-- Attempted port (placeholder; unsupported syntax likely)
/-
unsafe def {mod} : SProg :=
  [SDQLProg {{ int }}|
{textwrap.indent(sdql, '    ')}
  ]
-/

end Tests.TPCH
'''
        out_path = os.path.join(OUT_DIR, f"{mod}.lean")
        with open(out_path, 'w') as wf:
            wf.write(lean)
    print(f"Generated {len(sdql_files)} Lean files in {OUT_DIR}")


if __name__ == '__main__':
    main()

