"""Check the nineteen-gate lower bound for four collinear projective-plane stars."""
import argparse
from itertools import combinations, product
from pathlib import Path

from quadrangle_faces import LINES, facets
from verify_three_stars import source_constraints
from verify_triangle_stars import projected_tests, truth_words, two_extra, verify_twin_free


def line_pair_orbit():
    generators = [tuple((p + 1) % 13 for p in range(13)),
                  (0, 1, 2, 3, 10, 11, 7, 6, 12, 9, 4, 5, 8)]
    line_maps = []
    for mapping in generators:
        assert sorted(mapping) == list(range(13))
        line_maps.append([LINES.index(sum(1 << mapping[p] for p in range(13) if line >> p & 1))
                          for line in LINES])
    reached = {(0, 1)}
    queue = list(reached)
    while queue:
        a, b = queue.pop()
        for mapping in line_maps:
            image = (mapping[a], mapping[b])
            if image not in reached:
                reached.add(image)
                queue.append(image)
    assert len(reached) == 13 * 12


def at_most(literals, limit, clauses):
    """Balanced unary counter. The j-th output is forced if at least j inputs are true."""
    next_id = len(literals) + 1
    def join(group):
        nonlocal next_id
        if len(group) == 1:
            return group
        middle = len(group) // 2
        left, right = join(group[:middle]), join(group[middle:])
        length = min(limit + 1, len(left) + len(right))
        result = list(range(next_id, next_id + length))
        next_id += length
        for a in range(len(left) + 1):
            for b in range(len(right) + 1):
                if not 1 <= a + b <= length:
                    continue
                clause = ([-left[a-1]] if a else []) + ([-right[b-1]] if b else [])
                clauses.append(clause + [result[a+b-1]])
        return result
    clauses.append([-join(literals)[limit]])
    return next_id - 1


def source_menus():
    centers = [p for p in range(13) if LINES[0] >> p & 1]
    signals, raw, constraints = source_constraints(centers)
    assert len(signals) == 116 and len(raw) == 17 and len(constraints) == 869
    raw_signals = {1 << i for i in raw}
    omitted = 1 << 14
    optional = [s for s in signals if s.bit_count() == 2 and s & omitted]
    numbers = {s: i+1 for i, s in enumerate(signals)}
    unit_sources = {signals[c.bit_length()-1] for c in constraints if c.bit_count() == 1}
    assert unit_sources == {1 << v for v in [*centers, 13]}
    def used_mask(menu):
        return sum(1 << (numbers[s]-1) for s in menu)
    def separates(menu):
        mask = used_mask(menu)
        return all(mask & c for c in constraints)

    menus = []
    for group in combinations(optional, 3):
        menu = (raw_signals - {omitted}) | set(group)
        if separates(menu):
            menus.append(menu)
    assert len(menus) == 12
    for p in range(13):
        if p in centers or not LINES[1] >> p & 1:
            continue
        pencil = {1 << (13+i) for i, line in enumerate(LINES) if line >> p & 1}
        menu = (raw_signals - pencil) | {x | y for x, y in combinations(pencil, 2)}
        assert separates(menu)
        menus.append(menu)
    assert len(menus) == 15 and all(len(menu) == 19 for menu in menus)

    private = [[13+i for i, line in enumerate(LINES) if i and line >> p & 1] for p in centers]
    fixed = sum(1 << v for v in [*centers, 13])
    representatives = [fixed | sum(1 << v for v in choice) for choice in product(*private)]
    leaf_bounds = [min(sum((s & r).bit_count() for s in menu) for r in representatives)
                   for menu in menus]
    assert max(leaf_bounds) == 10
    # The other possibility is all seventeen raw sources and at most two helpers.
    for s in signals:
        if s not in raw_signals:
            assert all(sum(bool(s & (1 << v)) for v in group) <= 1 for group in private)
            assert not s & fixed

    positives = [(1 << p) | (1 << (13+i)) for p in centers
                 for i, line in enumerate(LINES) if line >> p & 1]
    negatives = list(facets())
    core_pos = None
    for choice, retain in zip(product(*private), representatives):
        sources = [1 << v for v in [*centers, 13, *choice]]
        restricted = [p for p in positives if not p & ~retain]
        pos, neg = projected_tests(restricted, negatives, sources)
        verify_twin_free(pos, neg)
        if core_pos is None:
            core_pos = pos
        assert pos == core_pos and len(pos) == 8
    nonedges = [(1 << i) | (1 << j) for i, j in combinations(range(9), 2)
                if ((1 << i) | (1 << j)) not in core_pos]
    assert len(nonedges) == 28
    rows = core_pos + nonedges
    assert not two_extra(truth_words(rows, 9), (1 << len(core_pos))-1, len(rows))

    clauses = [[i+1 for i in range(len(signals)) if c >> i & 1] for c in constraints]
    clauses.append([-numbers[omitted]])
    for menu in menus:
        clauses.append(sorted(-numbers[s] for s in menu))
    nvar = at_most(list(range(1, len(signals)+1)), 19, clauses)
    return clauses, nvar


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cnf', type=Path, help='write deterministic DIMACS input')
    parser.add_argument('--proof', type=Path, help='generate DRAT using python-sat for independent verification')
    args = parser.parse_args()
    if not __debug__:
        raise SystemExit('Run without -O so all assertions execute.')
    line_pair_orbit()
    clauses, nvar = source_menus()
    with args.cnf.open('w', encoding='ascii', newline='\n') as out:
        print(f'p cnf {nvar} {len(clauses)}', file=out)
        for clause in clauses:
            print(*clause, 0, file=out)
    print('13 collinear quadruples, 156 ordered line pairs, 81 restrictions, 15 candidate menus.')
    print(f'The remaining source-menu test is {nvar} variables and {len(clauses)} clauses.')
    if args.proof:
        from pysat.solvers import Solver
        with Solver(name='glucose42', bootstrap_with=clauses, with_proof=True) as solver:
            if solver.solve():
                raise ValueError('Another source menu exists.')
            proof = solver.get_proof()
        if not proof or '0' not in proof:
            raise ValueError('Solver returned no refutation.')
        with args.proof.open('w', encoding='ascii', newline='\n') as out:
            for line in proof:
                print(line, file=out)
        print('Solver refutation generated. Verify it independently against the emitted DIMACS input.')


if __name__ == '__main__':
    main()
