"""Check the sharp fourteen-gate lower bound for three noncollinear stars."""
from functools import lru_cache
from itertools import combinations, product
from quadrangle_faces import facets, LINES
from verify_three_stars import minimal_clauses, source_constraints, read_once


def projected_tests(positive, negative, sources):
    def project(row):
        return sum(bool(row & mask) << i for i, mask in enumerate(sources))
    positives = sorted({project(row) for row in positive})
    negatives = {project(row) for row in negative}
    maximal = sorted(n for n in negatives if not any(n != m and n & m == n for m in negatives))
    return positives, maximal


def truth_words(rows, count):
    return [sum((row >> k & 1) << i for i, row in enumerate(rows)) for k in range(count)]


def enumerate_hitting(clauses, remaining, selected=0):
    clauses = minimal_clauses(clauses)
    if not clauses:
        yield selected
        return
    if not clauses[0] or remaining <= 0:
        return
    occupied = 0
    packing = 0
    for clause in clauses:
        if not occupied & clause:
            occupied |= clause
            packing += 1
    if packing > remaining:
        return
    pivot = clauses[0]
    earlier = 0
    while pivot:
        bit = pivot & -pivot
        pivot -= bit
        rest = (c & ~earlier for c in clauses if not c & bit)
        yield from enumerate_hitting(rest, remaining - 1, selected | bit)
        earlier |= bit


def verify_orbit():
    generators = [tuple((p+1) % 13 for p in range(13)), (0,1,2,3,10,11,7,6,12,9,4,5,8)]
    for perm in generators:
        assert sorted(perm) == list(range(13))
        for row in LINES:
            assert sum(1 << perm[p] for p in range(13) if row >> p & 1) in LINES
    orbit = {(0, 1, 2)}
    pending = list(orbit)
    while pending:
        triple = pending.pop()
        for perm in generators:
            image = tuple(sorted(perm[p] for p in triple))
            if image not in orbit:
                orbit.add(image)
                pending.append(image)
    expected = {s for s in combinations(range(13), 3)
                if not any(all(row >> p & 1 for p in s) for row in LINES)}
    assert orbit == expected and len(orbit) == 234


def verify_twin_free(positive, negatives):
    neighbors = [set() for _ in range(9)]
    singleton = [1 << k for k in range(9)]
    for v in singleton:
        assert any(not v & ~n for n in negatives)
    for i, j in combinations(range(9), 2):
        pair = singleton[i] | singleton[j]
        if pair in positive:
            neighbors[i].add(j)
            neighbors[j].add(i)
        else:
            assert any(not pair & ~n for n in negatives)
    assert len(set(map(frozenset, neighbors))) == 9
    reached = {0}
    for _ in range(9):
        reached |= set().union(*(neighbors[i] for i in reached))
    assert len(reached) == 9


def check(centers):
    signals, raw, clauses = source_constraints(centers)
    assert len(signals) == 34 and len(raw) == 12
    raw_mask = sum(1 << k for k, s in enumerate(signals) if s.bit_count() == 1)
    helpers = [k for k, s in enumerate(signals) if s.bit_count() > 1]
    menus = {raw_mask | 1 << a | 1 << b for a, b in combinations(helpers, 2)}
    for v in raw:
        banned = 1 << signals.index(1 << v)
        alternatives = set(enumerate_hitting((c & ~banned for c in clauses), 14))
        assert all(s.bit_count() == 14 for s in alternatives)
        menus.update(alternatives)
    assert len(menus) == 243

    neighbors = [[13+i for i, line in enumerate(LINES) if line >> p & 1] for p in centers]
    private = [[v for v in group if sum(v in row for row in neighbors) == 1] for group in neighbors]
    shared = sorted({v for group in neighbors for v in group if sum(v in row for row in neighbors)>1})
    fixed = [1 << v for v in [*centers, *shared]]
    positive = [1 << p | 1 << v for p, group in zip(centers, neighbors) for v in group]
    negative = list(facets())
    broad = fixed + [sum(1 << v for v in group) for group in private]
    core_pos, core_neg = projected_tests(positive, negative, broad)
    assert len(core_pos) == 9 and len(core_neg) == 21
    verify_twin_free(core_pos, core_neg)
    representatives = []
    for choice in product(*private):
        groups = fixed + [1 << v for v in choice]
        retain = sum(groups)
        kept = [row for row in positive if row & retain == row]
        if projected_tests(kept, negative, groups) == (core_pos, core_neg):
            representatives.append(retain)
    assert len(representatives) == 4
    for helper in helpers:
        assert any((signals[helper] & r).bit_count() <= 1 for r in representatives)
    core_rows = core_pos + core_neg
    goal = (1 << len(core_pos)) - 1
    assert not two_extra(truth_words(core_rows, 9), goal, len(core_rows))

    exceptions = 0
    for menu in sorted(menus):
        used = [s for i, s in enumerate(signals) if menu >> i & 1]
        choices = [(sum((r & s).bit_count() > 1 for s in used),
                    -sum(not r & s for s in used), r) for r in representatives]
        retained_helpers, negative_discard, retain = min(choices)
        assert negative_discard <= -3
        if not retained_helpers:
            continue
        # Only an exact fourteen-source menu can be exceptional. The original
        # circuit is then a tree. Additional leaves may vanish under restriction.
        assert retained_helpers == 1 and len(used) == 14
        survive = [s & retain for s in used if s & retain]
        kept = [row for row in positive if row & retain == row]
        pos, neg = projected_tests(kept, negative, survive)
        rows = pos + neg
        assert not optional_read_once(truth_words(rows, len(survive)), (1 << len(pos))-1, len(rows))
        exceptions += 1
    assert exceptions == 33
    print("234 noncollinear triples; 243 maximal source menus and 33 residual read-once checks.")
    print("Minimum replacement cost for three noncollinear stars: 14 gates.")


def optional_read_once(seeds, target, width):
    """Find a formula that can use each of the supplied leaf occurrences once."""
    all_inputs = (1 << len(seeds)) - 1
    negatives = ((1 << width) - 1) ^ target
    npos = target.bit_count()
    difference = {(p, n): sum(1 << k for k, s in enumerate(seeds)
                              if s >> p & 1 and not s >> n & 1)
                  for p in range(npos) for n in range(npos, width)}

    @lru_cache(None)
    def smaller(mask):
        values = [s for k, s in enumerate(seeds) if mask >> k & 1]
        return read_once(values, target)

    @lru_cache(None)
    def solve(mask, ones, zeros):
        if not ones or not zeros:
            return True
        for (p, n), permitted in difference.items():
            if ones >> p & 1 and zeros >> n & 1 and not permitted & mask:
                return False
        remaining = [k for k in range(len(seeds)) if mask >> k & 1]
        if any(seeds[k] & ones == ones and not seeds[k] & zeros for k in remaining):
            return True
        # At a binary root the smaller child uses at most half the available leaves.
        for size in range(1, len(remaining) // 2 + 1):
            for group in combinations(remaining, size):
                side = sum(1 << k for k in group)
                rest = mask ^ side
                for v in smaller(side):
                    if not v & zeros and v & ones and solve(rest, ones & ~v, zeros):
                        return True
                    if v & ones == ones and v & zeros != zeros and solve(rest, ones, zeros & v):
                        return True
        return False
    return solve(all_inputs, target, negatives)


def two_extra(seeds, target, width):
    """The connected twin-free pair graph reduces two extra wire uses to these cases."""
    indices = list(range(len(seeds)))
    npos = target.bit_count()

    @lru_cache(None)
    def test(signals):
        return optional_read_once(signals, target, width)

    for i in indices:
        for j in range(i, len(seeds)):
            if test(tuple(sorted(seeds + [seeds[i], seeds[j]]))):
                return True

    candidates = 0
    for repeated in indices:
        others = [j for j in indices if j != repeated]
        for size in range(1, len(others)+1):
            for group in combinations(others, size):
                inside = [seeds[repeated]] + [seeds[j] for j in group]
                outside = [seeds[repeated]] + [seeds[j] for j in others if j not in group]
                profiles = [sum((s >> j & 1) << k for k, s in enumerate(outside)) for j in range(width)]
                required_true = 0
                required_false = 0
                for p in range(npos):
                    for n in range(npos, width):
                        if not profiles[p] & ~profiles[n]:
                            required_true |= 1 << p
                            required_false |= 1 << n
                # Any pair not separated by an outside signal must be separated by the shared gate.
                possible = all(any(s >> p & 1 and not s >> n & 1 for s in inside)
                               for p in range(npos) if required_true >> p & 1
                               for n in range(npos, width) if required_false >> n & 1)
                if not possible:
                    continue
                for shared in read_once(inside, target):
                    if shared & required_true != required_true or shared & required_false:
                        continue
                    candidates += 1
                    if test(tuple(sorted(outside + [shared, shared]))):
                        return True
    print("No circuit with two extra wire uses passed the nine-input core;", candidates,
          "shared traces survived the local monotonicity check.")
    return False


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to execute all certificate assertions.")
    verify_orbit()
    check((0, 1, 2))
