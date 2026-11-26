"""Elementary unrestricted 9-AND and 21-OR lower bounds for the plane samples."""

from collections import Counter
from itertools import combinations

from quadrangle_faces import LINES, POINTS, facets


def polarity_counts():
    negatives = list(facets())
    positives = [1 << p | 1 << (13+j) for j, line in enumerate(LINES)
                 for p in POINTS if line >> p & 1]
    vertices = range(26)
    high = [sum(1 << i for i, q in enumerate(negatives) if q >> v & 1)
            for v in vertices]
    assert len(negatives) == 234 and len(positives) == 52
    # Every row is independent and maximal. Each outside vertex has a neighbor
    # inside it, so the zero-certificate argument forces nineteen raw leaves.
    for row in negatives:
        assert row.bit_count() == 7
        assert not any(e & row == e for e in positives)
        for v in vertices:
            if not (row >> v & 1):
                assert any(e & (row | (1 << v)) == e for e in positives)
    # A crossing edge in the union separates any two distinct negative rows.
    assert all(any(e & (q | r) == e for e in positives)
               for q, r in combinations(negatives, 2))
    assert all(sum(bool(e >> v & 1) for e in positives) == 4 for v in vertices)
    sizes = Counter(w.bit_count() for w in high)
    common = Counter((x & y).bit_count() for x, y in combinations(high, 2))
    assert sizes == {54: 13, 72: 13} and max(common) == 24
    assert min((a | b | c).bit_count() for a, b, c in combinations(high, 3)) > 128

    # An 8-bit code admits only 128 suffixes after the first bit. Each operand
    # must hit at least 234-128 negative rows and at most 128. Enumerate all
    # subsets that meet those limits, pruning only monotone upper violations.
    low, high_limit = len(negatives) - 128, 128
    unions = []
    def subsets(start, occupied):
        weight = occupied.bit_count()
        if weight > high_limit:
            return
        if weight >= low:
            unions.append(occupied)
        for v in range(start, 26):
            subsets(v+1, occupied | high[v])
    subsets(0, 0)
    best = max(min((x & ~y).bit_count(), (y & ~x).bit_count())
               for x in unions for y in unions)
    assert len(unions) == 130 and {w.bit_count() for w in unions} == {126}
    assert min((x & y).bit_count() for x, y in combinations(unions, 2)) == 36
    assert best == 90 < low

    # At most 20 ORs gives at most 21 distinct raw-conjunction leaves. Each
    # singleton raw variable covers four positive edges and all other leaves
    # cover at most one. There must be at least eleven distinct singletons.
    d = (52 - (20+1) + 2) // 3
    lower = min(sizes) * d - max(common) * (d // 2)
    upper = len(negatives) * (20-18)
    assert (d, lower, upper) == (11, 474, 468)
    print('234 maximal negative rows, 52 edges, 26 raw vertices.')
    print(f'Raw union candidates {len(unions)}, best two-side count {best}, required {low}.')
    print(f'Singleton terminal lower {d}, required negative incidences {lower}, available {upper}.')
    print('Unrestricted AND >= 9, OR >= 21, total >= 30.')


if __name__ == '__main__':
    polarity_counts()
