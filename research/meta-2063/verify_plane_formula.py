"""Integer checker for the rectangle-partition lower bound in QuadrangleFormula.md.

Run with Python 3.10 or later. Uses only the standard library.
"""

from collections import Counter
from itertools import combinations


DIFFERENCE_SET = (0, 1, 3, 9)
LINES = [frozenset((l + d) % 13 for d in DIFFERENCE_SET) for l in range(13)]
FLAGS = [(p, l + 13) for l in range(13) for p in sorted(LINES[l])]
STARS = [[edge for edge in FLAGS if v in edge] for v in range(26)]
SINGLETONS = (1, 2, 4, 8)
BASE_COST = 216
# Every finite cost at a vertex and column is at most twenty.
INF = 1_000_000
EXPECTED = (
    (None, 1782, 1728, 1728),
    (1755, 1809, 1755, 1755),
    (1710, 1764, 1710, 1773),
    (1728, 1782, 1728, 1890),
)


def quadrangle_data():
    assert len(FLAGS) == 52 and all(len(s) == 4 for s in STARS)
    assert all(len(a & b) == 1 for a, b in combinations(LINES, 2))
    columns = []
    histogram = Counter()
    for points in combinations(range(13), 4):
        q = frozenset(points)
        degrees = [len(line & q) for line in LINES]
        if max(degrees) > 2:
            continue
        exterior = {13 + l for l, degree in enumerate(degrees) if degree == 0}
        assert len(exterior) == 3
        column = q | exterior
        charges = {}
        for p, line in FLAGS:
            w = 0
            if p not in q and degrees[line - 13] == 2:
                count = sum(degrees[k - 13] == 2 for _, k in STARS[p])
                assert count in (1, 2)
                w = {1: 1, 2: 5}[count]
            assert p not in column or line not in column
            charges[p, line] = w
            histogram[w] += 1
        columns.append((column, charges))
    assert len(columns) == 234
    assert histogram == {0: 9360, 1: 1404, 5: 1404}
    assert all(any(v in m for m, _ in columns) for v in range(26))
    assert all(any(a + 13 not in m and b + 13 in m for m, _ in columns)
               for a in range(13) for b in range(13) if a != b)
    return columns


def row_families():
    for size in range(1, 5):
        choices = [SINGLETONS] if size == 4 else combinations(range(1, 16), size)
        for family in choices:
            unions = {0}
            for rows in family:
                unions.update([u | rows for u in unions if not (u & rows)])
            if all(any(u & singleton for u in unions) for singleton in SINGLETONS):
                yield family, unions


def local_pattern(v, column, charges):
    neighbors = [edge[1] if v < 13 else edge[0] for edge in STARS[v]]
    forced = sum(1 << k for k, w in enumerate(neighbors) if w in column)
    return v in column, forced, tuple(charges[e] for e in STARS[v])


def local_options(v, edge, patterns, multiplicities):
    shared = 1 << STARS[v].index(edge)
    # Tabulate choices on distinct local patterns before expanding to joint ones.
    unique = dict.fromkeys(patterns)
    for excluded, forced, weights in unique:
        cost = {}
        for u in range(16):
            if (excluded and u != 0) or (not excluded and u & forced != forced):
                continue
            cost[u] = sum(w for k, w in enumerate(weights) if u & (1 << k))
        unique[excluded, forced, weights] = cost
    rows = []
    for family, unions in row_families():
        choices = {}
        for key, cost in unique.items():
            off, on = INF, INF
            for u in unions.intersection(cost):
                if u & shared:
                    on = min(on, cost[u])
                else:
                    off = min(off, cost[u])
            if min(off, on) == INF:
                break
            choices[key] = off, on
        else:
            options = tuple(choices[pat] for pat in patterns)
            score = BASE_COST * len(family) + sum(n * min(pair)
                                                  for pair, n in zip(options, multiplicities))
            if v < 13:
                assert score >= 828
                if len(family) == 3:
                    assert family[0] | family[1] | family[2] == 15
                    is_partition = sum(x.bit_count() for x in family) == 4
                    assert is_partition or score >= 891
            else:
                assert score >= 864
            rows.append((len(family), options))
    return rows


def verify_flag(point, line, columns):
    edge = point, line
    groups = Counter((local_pattern(point, m, charges), local_pattern(line, m, charges))
                     for m, charges in columns)
    pm, lm = zip(*groups)
    multiplicities = tuple(groups.values())
    left = local_options(point, edge, pm, multiplicities)
    right = local_options(line, edge, lm, multiplicities)
    best = [[INF] * 4 for _ in range(4)]
    for t, pchoice in left:
        for s, lchoice in right:
            bound = best[t - 1][s - 1]
            score = BASE_COST * (t + s)
            for (poff, pon), (loff, lon), n in zip(pchoice, lchoice, multiplicities):
                score += n * min(poff + lon, pon + loff)
                if score >= bound:
                    break
            else:
                best[t - 1][s - 1] = score
    table = tuple(tuple(None if x == INF else x for x in row) for row in best)
    assert table == EXPECTED, (edge, table)
    return table


def main():
    columns = quadrangle_data()
    for point in DIFFERENCE_SET:
        table = verify_flag(point, 13, columns)
        print(f"Flag ({point}, line 0) verified.")
    for row in table:
        print(row)
    charge = sum(sum(charges.values()) for _, charges in columns)
    assert charge == 8424
    assert 4 * (BASE_COST * 63 + charge) < 52 * 1710
    assert 4 * (BASE_COST * 64 + charge) - 52 * 1710 == 72
    # After the flag exclusions, at most one point cost is 1 or 4;
    # the remaining twelve points have cost 3, and line costs are 1 or 3.
    line_counts = [(exception, k) for exception in (1, 3, 4) for k in range(14)
                   if 12 * 3 + exception + k + 3 * (13 - k) == 64]
    assert line_counts == [(1, 6), (3, 7)]
    print("Total charge 8424; budget 64 gives flag slack 72; cost-one lines 6 or 7.")
    print("Rectangle partition and monotone formula optimum: 65 leaves, 64 binary gates.")


if __name__ == "__main__":
    main()
