#!/usr/bin/env python3
"""Compute the reflexive-transitive closure of a boolean adjacency matrix.

Input (stdin, JSON):
  { "1": [2], "2": [3] }
  Keys are node IDs (ints as strings), values are lists of successor node IDs.

Output (stdout):
  SDQL dictionary format, e.g.:
  {1 -> {1 -> true, 2 -> true, 3 -> true, }, 2 -> {2 -> true, 3 -> true, }, 3 -> {3 -> true, }, }
"""
import json
import sys


def transitive_closure(adj: dict[int, list[int]]) -> dict[int, set[int]]:
    """Floyd-Warshall style reflexive-transitive closure."""
    # Collect all nodes
    nodes: set[int] = set()
    for src, dsts in adj.items():
        nodes.add(src)
        nodes.update(dsts)

    # Initialise reachability: edge + reflexive
    reach: dict[int, set[int]] = {n: {n} for n in nodes}
    for src, dsts in adj.items():
        reach[src].update(dsts)

    # Floyd-Warshall
    node_list = sorted(nodes)
    for k in node_list:
        for i in node_list:
            if k in reach[i]:
                for j in reach[k]:
                    reach[i].add(j)

    return reach


def format_sdql(reach: dict[int, set[int]]) -> str:
    """Format as SDQL dictionary string."""
    parts = []
    for src in sorted(reach):
        inner_parts = []
        for dst in sorted(reach[src]):
            inner_parts.append(f"{dst} -> true")
        inner = ", ".join(inner_parts)
        parts.append(f"{src} -> {{{inner}, }}")
    return "{" + ", ".join(parts) + ", }"


def main() -> None:
    data = json.load(sys.stdin)
    adj = {int(k): v for k, v in data.items()}
    reach = transitive_closure(adj)
    print(format_sdql(reach))


if __name__ == "__main__":
    main()
