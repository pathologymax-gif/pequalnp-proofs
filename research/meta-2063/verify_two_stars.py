"""Exhaust the possible small replacements for two stars in PG(2,3).

Python 3.10+, standard library only. A row is encoded by a bit mask.
"""
from collections import defaultdict
from itertools import combinations


def build_instance(other_center):
    lines = [{(i + d) % 13 for d in (0, 1, 3, 9)} for i in range(13)]
    centers = (0, other_center)
    neighbors = [{13 + i for i, line in enumerate(lines) if p in line} for p in centers]
    common, = neighbors[0] & neighbors[1]
    left, right = (sorted(row - {common}) for row in neighbors)
    sources = [(p,) for p in centers] + [(common,)] + [(v,) for v in left + right]
    sources += [(a, b) for a in left for b in right]
    assert len(sources) == 18
    for a, b in sources[9:]:
        owner, = lines[a - 13] & lines[b - 13]
        assert owner not in centers
    def project(vertices):
        return sum(any(v in vertices for v in s) << k for k, s in enumerate(sources))
    positives = sorted(project({p, w}) for p, row in zip(centers, neighbors) for w in row)
    negative_samples = []
    for q in combinations(range(13), 4):
        points = set(q)
        if any(len(line & points) >= 3 for line in lines):
            continue
        misses = {13 + i for i, line in enumerate(lines) if not line & points}
        negative_samples.append(project(points | misses))
    assert len(negative_samples) == 234
    negatives = set(negative_samples)
    maximal = sorted(n for n in negatives if not any(n != m and n & m == n for m in negatives))
    assert len(positives) == 8 and len(maximal) == 34
    return sources, positives, maximal


def check_number_of_sources(sources, positives, negatives):
    all_bits = (1 << len(sources)) - 1
    def fails(selected):
        return any(p & selected & ~n == 0 for p in positives for n in negatives)
    for mandatory in (0, 1, 2):
        assert fails(all_bits ^ (1 << mandatory))
    count = 0
    for other in combinations(range(3, 18), 5):
        selected = 7 | sum(1 << j for j in other)
        assert fails(selected)
        count += 1
    assert count == 3003
    print("At least nine reachable source signals required; 3003 maximal eight-source choices excluded.")


def check_formulas(sources, positives, negatives):
    rows = positives + negatives
    target = (1 << len(positives)) - 1
    words = [sum(1 << row for row, x in enumerate(rows) if x >> i & 1)
             for i in range(len(sources))]
    levels = [list(set(words))]
    # For a fixed positive trace, fewer false positives can only help under AND/OR.
    frontier = defaultdict(list)
    for word in words:
        frontier[word & target].append(word & ~target)
    seen = set(words)
    assert target not in seen
    for budget in range(1, 9):
        candidates = defaultdict(set)
        for a in range((budget - 1) // 2 + 1):
            b = budget - 1 - a
            for i, x in enumerate(levels[a]):
                for y in (levels[b][i:] if a == b else levels[b]):
                    for z in (x | y, x & y):
                        assert z != target, "A smaller formula exists"
                        p = z & target
                        if p and z not in seen and budget < 8:
                            candidates[p].add(z & ~target)
        level = []
        for p, masks in candidates.items():
            for mask in sorted(masks, key=int.bit_count):
                if any(old & mask == old for old in frontier[p]):
                    continue
                frontier[p].append(mask)
                level.append(p | mask)
        seen.update(level)
        levels.append(level)
    print("No formula with at most eight binary gates on the eighteen freely reusable source signals.")


if __name__ == "__main__":
    for difference in range(1, 13):
        print("Centers:", 0, difference)
        atoms, pos, neg = build_instance(difference)
        check_number_of_sources(atoms, pos, neg)
        check_formulas(atoms, pos, neg)
    print("Minimum additional gates for two point-stars with every outside-star OR available: 9.")
