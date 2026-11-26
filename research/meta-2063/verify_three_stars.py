"""Certify that three collinear point-stars need fourteen gates with all outside-star ORs free."""
from functools import lru_cache
from itertools import combinations, product
from quadrangle_faces import facets, LINES

def minimal_clauses(clauses):
    result = []
    for c in sorted(set(clauses), key=lambda x: (x.bit_count(), x)):
        if not any((old & c == old for old in result)):
            result.append(c)
    return tuple(result)

def has_hitting_set(clauses, limit):

    @lru_cache(None)
    def search(unhit, remaining):
        if not unhit:
            return True
        if not unhit[0] or remaining <= 0:
            return False
        occupied = 0
        packing_size = 0
        for clause in unhit:
            if not clause & occupied:
                packing_size += 1
                occupied |= clause
        if packing_size > remaining:
            return False
        # Branch on the first selected bit in this smallest unhit clause.
        pivot = unhit[0]
        excluded = 0
        while pivot:
            bit = pivot & -pivot
            pivot -= bit
            todo = [c & ~excluded for c in unhit if not c & bit]
            if search(minimal_clauses(todo), remaining - 1):
                return True
            excluded |= bit
        return False
    return search(minimal_clauses(clauses), limit)

def source_constraints(centers):
    adj = [[13 + i for i, l in enumerate(LINES) if l >> p & 1] for p in range(13)]
    line_set = set().union(*(adj[p] for p in centers))
    raw = set(centers) | line_set
    signals = {1 << k for k in raw}
    for p in set(range(13)) - set(centers):
        local = set(adj[p]) & line_set
        for k in range(2, len(local) + 1):
            for s in combinations(local, k):
                signals.add(sum((1 << z for z in s)))
    signals = sorted(signals)

    def project(r):
        return sum((bool(r & a) << k for k, a in enumerate(signals)))
    positive = [project(1 << p | 1 << l) for p in centers for l in adj[p]]
    negative = [project(q) for q in facets()]
    constraints = minimal_clauses((p & ~n for p in positive for n in negative))
    return (signals, raw, constraints)

def read_once(values, target, wanted=None):
    n = len(values)

    @lru_cache(None)
    def formula_words(mask):
        if mask & mask - 1 == 0:
            return (values[mask.bit_length() - 1],)
        result = set()
        first = mask & -mask
        s = mask - 1 & mask
        while s:
            if s & first:
                for a in formula_words(s):
                    for b in formula_words(mask ^ s):
                        for w in (a & b, a | b):
                            if wanted is not None and mask == (1 << n) - 1 and (w == wanted):
                                return (w,)
                            if w & target:
                                result.add(w)
            s = s - 1 & mask
        # The same positive trace and fewer negatives always improve a formula.
        frontier = {}
        for w in sorted(result, key=int.bit_count):
            p = w & target
            if any((z & w == z for z in frontier.get(p, ()))):
                continue
            frontier.setdefault(p, []).append(w)
        return tuple((w for fs in frontier.values() for w in fs))
    return formula_words((1 << n) - 1)

def can_use_one_extra_wire(seeds, target):
    indices = list(range(len(seeds)))
    if target in read_once(seeds, target, target):
        return True
    for size in range(1, len(seeds) + 1):
        for group in combinations(indices, size):
            inside = [seeds[i] for i in group]
            outside = [seeds[i] for i in indices if i not in group]
            for shared in read_once(inside, target):
                if target in read_once(outside + [shared, shared], target, target):
                    return True
    return False

def reduced_geometry(centers, negatives):
    neighbors = [{13 + i for i, l in enumerate(LINES) if l >> p & 1} for p in centers]
    common, = set.intersection(*neighbors)
    private_groups = [sorted(a - {common}) for a in neighbors]
    positives = [sum((1 << p, 1 << q)) for p, ns in zip(centers, neighbors) for q in ns]

    def project(bits, groups):
        return sum((bool(bits & g) << i for i, g in enumerate(groups)))
    raw = [1 << v for v in [*centers, common]]
    grouped = raw + [sum((1 << v for v in group)) for group in private_groups]

    def maximal(groups):
        image = {project(n, groups) for n in negatives}
        return tuple(sorted((q for q in image if not any((q != w and q & w == q for w in image)))))
    required_negative = maximal(grouped)
    target = tuple(sorted({project(p, grouped) for p in positives}))
    assert len(target) == 6 and len(required_negative) == 10
    choices = []
    for representatives in product(*private_groups):
        signals = raw + [1 << v for v in representatives]
        if maximal(signals) == required_negative:
            choices.append(sum((1 << v for v in representatives)))
    return (target, required_negative, choices)

def main():
    if not __debug__:
        raise SystemExit("Run without -O so the certificate assertions are checked.")
    negatives = list(facets())
    template = None
    count = 0
    for line in LINES:
        for centers in combinations([p for p in range(13) if line >> p & 1], 3):
            signals, raw, clauses = source_constraints(centers)
            assert len(signals) == 49 and len(raw) == 13
            for v in raw:
                forbidden = 1 << signals.index(1 << v)
                assert not has_hitting_set([c & ~forbidden for c in clauses], 14)
            positive, negative, choices = reduced_geometry(centers, negatives)
            assert choices
            for shared in signals:
                if shared.bit_count() > 1:
                    assert any(((shared & r).bit_count() <= 1 for r in choices))
            if template is None:
                template = (positive, negative)
                rows = [*positive, *negative]
                seeds = [sum(((x >> k & 1) << r for r, x in enumerate(rows))) for k in range(7)]
                assert not can_use_one_extra_wire(seeds, (1 << len(positive)) - 1)
            assert template == (positive, negative)
            count += 1
    assert count == 52
    print('All 52 collinear triples need all 13 raw signals within any 14-source budget.')
    print('The specified 7-source restriction has no <=7-gate circuit, including one shared wire.')
    print('Minimum cost for three collinear point-stars, with every outside-star OR free: 14 gates.')
if __name__ == '__main__':
    main()
