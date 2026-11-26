"""Count necessary OR gates along zero certificates for maximal independent sets.

Run `python or_certificates.py` next to seed_tables.json and star_upper.json.
The proof applies to every binary monotone circuit on these samples. The code
checks its conclusions independently at each maximal negative input in the
known nineteen-gate constructions.

Let M be a maximal independent set, C its vertex complement. The output is
zero on M and one on every edge. Choose the earliest wire h with that property.
For these graphs no input meets every edge, and the constant zero misses
every edge. If h were AND, both parents would be one on all edges and at least
one would be zero on M. That contradicts the choice of h, so h is OR.

Certify h=0 on M by following both parents of each zero OR and one zero
parent of each zero AND. Each v in C must occur as a primary leaf: otherwise
changing v to one preserves this zero certificate, while M union {v} contains
an edge and monotonicity forces h=1. After contracting the one-child choices,
the connected certificate with |C| distinct primary leaves has at least
|C|-1 binary OR gates, even with reused intermediate wires. At most one of
these gates, h, is one on every edge. Thus at least |C|-2 distinct OR gates
are zero on M and on some positive edge. Each of the four graphs has a
three-vertex maximal independent set and ten vertices, giving at least five
such intermediate OR gates for any circuit for each graph.
"""

import json
from collections import Counter
from pathlib import Path


def verify(row, gates):
    positives = (1 << 14) - 1
    vertices = {i for i, mask in enumerate(row) if mask}
    edges = [{v for v in vertices if row[v] >> bit & 1} for bit in range(14)]
    if len(vertices) != 10 or any(len(edge) != 2 for edge in edges):
        raise ValueError("Unexpected projected graph")
    if any(all(v in edge for edge in edges) for v in vertices):
        raise ValueError("A primary meets every edge")

    values = list(row)
    for op, left, right, expected in gates:
        assert op in ("AND", "OR") and 0 <= left < len(values) and 0 <= right < len(values)
        result = values[left] & values[right] if op == "AND" else values[left] | values[right]
        assert result == expected
        values.append(result)
    assert values[-1] == positives

    sizes = Counter()
    for column in range(14, 32):
        high = {v for v in vertices if row[v] >> column & 1}
        if not high:
            continue
        low = vertices - high
        assert not any(edge <= high for edge in edges)
        assert all(any(edge <= high | {v} for edge in edges) for v in low)
        bit = 1 << column
        root = next(i for i, val in enumerate(values) if not val & bit and val & positives == positives)
        assert root >= len(row) and gates[root - len(row)][0] == "OR"
        visited = set()
        ors = set()
        pending = [root]
        while pending:
            wire = pending.pop()
            if wire in visited:
                continue
            assert not values[wire] & bit
            visited.add(wire)
            if wire < len(row):
                continue
            op, a, b, _ = gates[wire - len(row)]
            if op == "OR":
                ors.add(wire)
                pending.extend((a, b))
            else:
                pending.append(a if not values[a] & bit else b)
        assert low <= visited and len(ors) >= len(low) - 1
        assert all(values[i] & positives != positives for i in ors - {root})
        sizes[len(high)] += 1
    return sizes


if __name__ == "__main__":
    base = Path(__file__).resolve().parent
    rows = json.loads((base / "seed_tables.json").read_text())
    networks = json.loads((base / "star_upper.json").read_text())
    for i, (row, network) in enumerate(zip(rows, networks, strict=True)):
        sizes = verify(row, network)
        assert sizes[3] and sum(sizes.values()) in range(15, 19)
        print(f"case {i}: verified {sizes[3]} maximal triples and {sizes[4]} maximal four-sets")
