"""Compute how single-reader primary variables can enter an intermediate with a false positive."""
import json
from itertools import combinations
from pathlib import Path


ROOT = Path(__file__).resolve().parent


def analyze(row, max_count=10, all_sets=False):
    vs = tuple(i for i, x in enumerate(row) if x)
    vs_mask = sum(1 << v for v in vs)
    samples = [sum(1 << v for v in vs if row[v] >> j & 1) for j in range(32)]
    edges = samples[:14]
    neg = set(samples[14:]) - {0}
    hood = {v: sum(e ^ (1 << v) for e in edges if e >> v & 1) for v in vs}
    assert all(hood[v].bit_count() >= 2 for v in vs)
    assert all((hood[x] & hood[y]).bit_count() <= 1 for x, y in combinations(vs, 2))
    assert all(any(m >> x & 1 and not m >> y & 1 for m in neg) for x in vs for y in vs if x != y)
    def close(initial):
        active = initial
        while True:
            after = active
            has_edge = any(e & active == e for e in edges)
            for z in vs:
                if active >> z & 1:
                    continue
                # z AND h: h sees all singleton neighbors and must also fire on
                # a sample containing z and no neighbor of z. h uses active primaries.
                dirty_and = hood[z] & ~active == 0 and bool(active & ~hood[z])
                # z OR h: h must improve a positive not incident to z. It cannot
                # accept a single active vertex, as its negative support is contained
                # in z's. A negative where h fires must force z among the maximal
                # independent sets extending its active input pattern.
                dirty_or = has_edge and any(all((m & active) & ~other for other in neg if not other >> z & 1)
                                            for m in neg if m >> z & 1)
                if dirty_and or dirty_or:
                    after |= 1 << z
            if after == active:
                return active
            active = after
    out = []
    for k in range(min(max_count, len(vs)) + 1):
        coverings = []
        noncovering = []
        for repeat in combinations(vs, k):
            start = sum(1 << v for v in repeat)
            reached = close(start)
            (coverings if all(e & reached for e in edges) else noncovering).append(start)
        out.append((k, len(coverings), len(noncovering), coverings if all_sets else coverings[:3]))
    return out


if __name__ == '__main__':
    for i, row in enumerate(json.loads((ROOT / 'seed_tables.json').read_text())):
        print(i, analyze(row))
