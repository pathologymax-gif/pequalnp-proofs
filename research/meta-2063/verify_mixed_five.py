"""Recheck the integer ordinary-leaf certificates for five-gate shared helpers.

Requires the standard-library modules verify_plane_formula and verify_raw_shared_gate.
Run mixed_five_orbits.py to check independently the list of residual formulas.
"""

import json
from collections import Counter
from itertools import combinations
from pathlib import Path
from verify_plane_formula import FLAGS, quadrangle_data
from verify_raw_shared_gate import verify_weighted


HERE = Path(__file__).resolve().parent
CERTIFICATES = HERE / "mixed_five_certificates.json"
COLUMNS = [assignment for assignment, _ in quadrangle_data()]


def check_mandatory_inputs():
    neighbors = [set() for _ in range(26)]
    for v, w in FLAGS:
        neighbors[v].add(w)
        neighbors[w].add(v)
    for m in COLUMNS:
        assert len(m) == 7
        assert all(neighbors[v].isdisjoint(m) if v in m else neighbors[v] & m
                   for v in range(26))
    assert all(any(w in m and v not in m for m in COLUMNS)
               for e in FLAGS for v, w in (e, e[::-1]))
    maxima = []
    for k in range(8):
        counts = Counter(s for m in COLUMNS for s in combinations(sorted(m), k))
        maxima.append(max(counts.values()))
    assert maxima == [234, 72, 24, 9, 4, 2, 1, 1]
    print("Mandatory-input counts for 0 through 7 prescribed vertices:", maxima)


def check(case):
    support = case["support"]
    assert len(support) == len(set(support)) == 6
    terms = [frozenset(v for j, v in enumerate(support) if m & (1 << j))
             for m in case["minterms"]]
    assert all(terms) and all(0 < m < (1 << len(support)) for m in case["minterms"])
    h_edge = {e: any(t.issubset(e) for t in terms) for e in FLAGS}
    h_negative = {m: any(t.issubset(m) for t in terms) for m in COLUMNS}
    def optional(edge, negative):
        return h_edge[edge] and not h_negative[negative]
    numerator, denominator, _ = verify_weighted(
        support, COLUMNS, case["base"], case["point_count"], case["line_count"],
        case["point_private"], case["line_private"], case["row_weights"],
        helper_optional=optional)
    assert denominator > 0 and numerator > 57 * denominator
    return numerator, denominator


def main():
    if not __debug__:
        raise SystemExit("Run without -O to enable all checks.")
    check_mandatory_inputs()
    cases = json.loads(CERTIFICATES.read_text())
    assert len(cases) == 64
    keys = {(tuple(c["support"]), tuple(c["minterms"])) for c in cases}
    assert len(keys) == len(cases)
    records = json.loads((HERE / "mixed_five_orbits.json").read_text())
    assert len(records) == len(keys)
    assert keys == {(tuple(s), tuple(m)) for s, g, m, _ in records if g == 5}
    from fractions import Fraction
    bounds = []
    for i, case in enumerate(cases):
        n, d = check(case)
        assert n == case["numerator"] and d == 4 * case["base"]
        bounds.append(Fraction(n, d))
        print(f"{i+1:2}/64  {n}/{d}  ordinary leaves >= {-(-n//d)}", flush=True)
    print(f"All 64 bounds exceed 57, with minimum {min(bounds)}.")


if __name__ == "__main__":
    main()
