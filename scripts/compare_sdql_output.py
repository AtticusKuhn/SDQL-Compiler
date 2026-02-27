#!/usr/bin/env python3
"""Compare two SDQL dictionary output strings numerically.

Handles floating-point formatting differences between Rust and Python
(e.g. last-digit rounding: Rust may output 0.000000029802322387695313
while Python outputs 0.000000029802322387695312 for the same f64 value).

Usage:
    python3 compare_sdql_output.py <file1> <file2>

Exit code 0 if outputs are numerically equivalent, 1 otherwise.
"""
import re
import sys


def normalize_sdql(s: str) -> str:
    """Round all floating-point literals to 12 significant digits in decimal notation."""
    from decimal import Decimal

    def normalize_float(match: re.Match) -> str:
        val = float(match.group())
        if val == int(val) and abs(val) < 1e15:
            return str(int(val))
        # Round to 12 significant digits to eliminate last-digit tie-breaking
        rounded_str = f"{val:.12g}"
        d = Decimal(rounded_str)
        result = format(d, "f")
        if "." in result:
            result = result.rstrip("0").rstrip(".")
        return result

    return re.sub(r"-?\d+\.\d+(?:[eE][+-]?\d+)?", normalize_float, s)


def main() -> None:
    if len(sys.argv) != 3:
        print("Usage: compare_sdql_output.py <file1> <file2>", file=sys.stderr)
        sys.exit(2)

    with open(sys.argv[1]) as f:
        s1 = f.read().strip()
    with open(sys.argv[2]) as f:
        s2 = f.read().strip()

    n1 = normalize_sdql(s1)
    n2 = normalize_sdql(s2)

    if n1 == n2:
        print("MATCH")
        sys.exit(0)
    else:
        # Find first difference for debugging
        for i, (a, b) in enumerate(zip(n1, n2)):
            if a != b:
                ctx = 40
                print(f"MISMATCH at position {i}:", file=sys.stderr)
                print(f"  normalized1: ...{n1[max(0,i-ctx):i+ctx]}...", file=sys.stderr)
                print(f"  normalized2: ...{n2[max(0,i-ctx):i+ctx]}...", file=sys.stderr)
                break
        else:
            print(f"MISMATCH: length differs ({len(n1)} vs {len(n2)})", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
