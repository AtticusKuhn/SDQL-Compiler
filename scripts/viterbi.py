#!/usr/bin/env python3
"""Kleene closure of a max-product (Viterbi) adjacency matrix via log-domain Floyd-Warshall.

Semiring: (max, ×) over [0,1] probabilities.
Log-domain trick: log turns (max, ×) into (max, +), giving standard Floyd-Warshall.

Input  (JSON): {"1": {"2": 0.8, "3": 0.5}, "2": {"3": 0.9}}
Output (SDQL): {1 -> {1 -> 1, 2 -> 0.8, 3 -> 0.72, }, ...}
"""
import json, sys
import numpy as np


def viterbi_closure(adj: dict[int, dict[int, float]]) -> dict[int, dict[int, float]]:
    """Kleene closure for (max, ×) via Floyd-Warshall in log-domain."""
    nodes = sorted({n for s, ds in adj.items() for n in (s, *ds)})
    idx = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)

    w = np.full((n, n), -np.inf)
    for s, ds in adj.items():
        for d, p in ds.items():
            w[idx[s], idx[d]] = np.log2(p)

    for k in range(n):
        w[k, k] = 0.0  # star(a) = 1 ⟹ log₂(1) = 0
        w = np.maximum(w, w[:, k:k+1] + w[k:k+1, :])

    prob = np.exp2(w)
    return {
        nodes[i]: {nodes[j]: float(prob[i, j]) for j in range(n) if prob[i, j] > 0}
        for i in range(n) if np.any(prob[i] > 0)
    }


def format_value(v: float) -> str:
    """Format a float: use integer representation if exact.

    Uses decimal notation (no scientific notation) to match
    Rust's f64::to_string() output used by the SDQL runtime.
    """
    if v == int(v):
        return str(int(v))
    s = repr(v)
    if 'e' in s or 'E' in s:
        from decimal import Decimal
        s = format(Decimal(s), 'f')
    return s


def format_sdql(m: dict[int, dict[int, float]]) -> str:
    """Format as SDQL dictionary string."""
    def row(src):
        inner = ", ".join(f"{d} -> {format_value(m[src][d])}" for d in sorted(m[src]))
        return f"{src} -> {{{inner}, }}"
    return "{" + ", ".join(row(s) for s in sorted(m)) + ", }"


def main() -> None:
    if len(sys.argv) > 1:
        with open(sys.argv[1]) as f:
            data = json.load(f)
    else:
        data = json.load(sys.stdin)
    adj = {int(k): {int(d): float(w) for d, w in v.items()} for k, v in data.items()}
    print(format_sdql(viterbi_closure(adj)))


if __name__ == "__main__":
    main()
