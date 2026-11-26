"""Verify the two independent OR-tree exclusions. Requires Python 3.10+."""
from collections import Counter
from functools import cache
from itertools import combinations
import gzip
import json
from pathlib import Path

from verify_kw_first_shared import check_tree

HERE = Path(__file__).resolve().parent
TARGET = (1 << 14) - 1
NEGATIVE = ((1 << 32) - 1) ^ TARGET


def hull_lower_bound(inputs):
    edges = [tuple(i for i, w in enumerate(inputs) if w & (1 << j)) for j in range(14)]
    assert all(len(e) == 2 for e in edges) and len(set(edges)) == 14

    @cache
    def cover(mask):
        if not mask:
            return 0
        a,b = edges[(mask & -mask).bit_length() - 1]
        return 1 + min(cover(mask & ~inputs[a]), cover(mask & ~inputs[b]))

    def lower(negative, helpers=()):
        rows, cols = [0] * len(inputs), [0] * len(inputs)
        for j,(a,b) in enumerate(edges):
            unavailable = negative
            for h in helpers:
                if h & (1 << j):
                    unavailable &= h
            for v,other in ((a,b),(b,a)):
                forced = inputs[other] & unavailable
                if forced:
                    rows[v] |= 1 << j
                    cols[v] |= forced
        conflicts = sum(1 << j for j,(a,b) in enumerate(edges)
                        if rows[a] & rows[b] and cols[a] & cols[b])
        return sum(bool(r) for r in rows) + cover(conflicts)
    return lower


def verify(row, seed, evidence):
    inputs = [w for w in seed if w]
    assert len(inputs) == 10 and len(seed) == 11 and seed.index(0) == row
    lower = hull_lower_bound(inputs)
    ordinary = cache(lower)
    joined = [0] * (1 << len(inputs))
    for s in range(1,len(joined)):
        low = s & -s
        joined[s] = joined[s ^ low] | inputs[low.bit_length()-1]
    sets = [s for s in range(len(joined)) if s.bit_count() >= 2]
    counts = Counter()
    needed, single_used = {}, set()
    for a,b in combinations(sets,2):
        # q is a lower bound on the combined cost of disjoint inner OR trees.
        q = a.bit_count() + b.bit_count() - 2
        if q == 2:
            continue
        h1,h2 = joined[a],joined[b]
        neg = h1 & h2 & NEGATIVE
        if ordinary(neg) > 15-q:
            counts['double hull'] += 1
            continue
        key = str(neg)
        if key in evidence['double']:
            needed[key] = max(needed.get(key,-100),15-q)
            counts['double dual'] += 1
            continue
        if lower(NEGATIVE,(h1,h2)) + 4 > 19-q:
            counts['full hull'] += 1
            continue
        pair = str(a)+','+str(b)
        method,tree = evidence['single'][pair]
        assert method in ('left','right')
        fixed,other = (h1,h2) if method == 'left' else (h2,h1)
        table = [w & (TARGET | fixed) for w in inputs+[other]]
        counts['dual leaves'] += check_tree(table,tree,17-q)
        counts['single dual'] += 1
        single_used.add(pair)
    assert set(evidence) == {'double','single'}
    assert set(needed) == set(evidence['double']) and single_used == set(evidence['single'])
    for key,threshold in needed.items():
        table = [w & (TARGET | int(key)) for w in inputs]
        counts['dual leaves'] += check_tree(table,evidence['double'][key],threshold)
    total = sum(counts[k] for k in ('double hull','double dual','full hull','single dual'))
    assert total == 511588
    print(row, total, dict(counts), flush=True)


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Enable Python assertions.')
    rows = json.loads((HERE/'seed_tables.json').read_text())
    certificates = json.loads(gzip.decompress((HERE/'two_or_trees.json.gz').read_bytes()))
    assert len(rows) == len(certificates) == 4
    for row,(seed,evidence) in enumerate(zip(rows,certificates)):
        verify(row,seed,evidence)
