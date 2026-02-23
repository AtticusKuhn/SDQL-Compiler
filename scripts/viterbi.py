#!/usr/bin/env python3
"""Compute the Kleene closure of a max-product (Viterbi) adjacency matrix.

This solves the all-pairs most-probable-path problem.

Semiring: (max, ×) over non-negative reals.
  - "addition" = max
  - "multiplication" = × (standard real multiplication)
  - star(a) = 1.0 for a ≤ 1 (probability weights)

Input (stdin, JSON):
  { "1": {"2": 0.8, "3": 0.5}, "2": {"3": 0.9} }
  Keys are node IDs (ints as strings), values are dicts mapping successor to weight.

Output (stdout):
  SDQL dictionary format with values rounded to integers where exact, e.g.:
  {1 -> {1 -> 1, 2 -> 0.8, 3 -> 0.72, }, ...}
"""
import json
import sys


def viterbi_closure(adj: dict[int, dict[int, float]]) -> dict[int, dict[int, float]]:
    """Kleene's algorithm for the (max, ×) semiring."""
    # Collect all nodes
    nodes: set[int] = set()
    for src, dsts in adj.items():
        nodes.add(src)
        nodes.update(dsts.keys())

    node_list = sorted(nodes)
    n = len(node_list)

    # Initialise W from adjacency matrix (zero = 0.0)
    w: dict[int, dict[int, float]] = {}
    for i in node_list:
        w[i] = {}
        for j in node_list:
            w[i][j] = 0.0
    for src, dsts in adj.items():
        for dst, weight in dsts.items():
            w[src][dst] = weight

    # Kleene's algorithm with (max, ×) semiring
    for k in node_list:
        wkk_star = 1.0  # star(a) = 1.0 for probabilities ≤ 1
        w_new: dict[int, dict[int, float]] = {i: {} for i in node_list}
        for i in node_list:
            for j in node_list:
                if i == k and j == k:
                    val = wkk_star
                elif i == k:
                    val = wkk_star * w[k][j]
                elif j == k:
                    val = w[i][k] * wkk_star
                else:
                    val = max(w[i][j], w[i][k] * wkk_star * w[k][j])
                w_new[i][j] = val
        w = w_new

    # Remove zero entries (sparse representation)
    result: dict[int, dict[int, float]] = {}
    for i in node_list:
        row = {}
        for j in node_list:
            if w[i][j] != 0.0:
                row[j] = w[i][j]
        if row:
            result[i] = row

    return result


def format_value(v: float) -> str:
    """Format a float: use integer representation if exact."""
    if v == int(v):
        return str(int(v))
    return str(v)


def format_sdql(matrix: dict[int, dict[int, float]]) -> str:
    """Format as SDQL dictionary string."""
    parts = []
    for src in sorted(matrix):
        inner_parts = []
        for dst in sorted(matrix[src]):
            inner_parts.append(f"{dst} -> {format_value(matrix[src][dst])}")
        inner = ", ".join(inner_parts)
        parts.append(f"{src} -> {{{inner}, }}")
    return "{" + ", ".join(parts) + ", }"


def main() -> None:
    data = json.load(sys.stdin)
    adj: dict[int, dict[int, float]] = {}
    for k, v in data.items():
        adj[int(k)] = {int(dst): float(w) for dst, w in v.items()}
    result = viterbi_closure(adj)
    print(format_sdql(result))


if __name__ == "__main__":
    main()
