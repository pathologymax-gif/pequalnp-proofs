"""Compare the free-OR SAT grammar against exhaustive truth-vector closure."""

from itertools import combinations_with_replacement
from random import Random
from unittest import TestCase, main

from pysat.solvers import Solver

from exact_synthesis import samples_for
from free_operation import encode


def closure(ws):
    result = {0}
    for w in ws:
        result.update([v | w for v in result])
    return frozenset(result)


def reachable(ws, bound):
    state = {closure(ws)}
    for _ in range(bound):
        state = {closure((*pool, a & b)) for pool in state
                 for a, b in combinations_with_replacement(pool, 2)}
    return set().union(*state)


class FreeBudgetTests(TestCase):
    def test_truth_vectors(self):
        rng = Random(314159)
        checks = 0
        for _ in range(12):
            seeds = [rng.randrange(16) for _ in range(4)]
            for budget in (0, 1, 2):
                expected = reachable(seeds, budget)
                for target in range(16):
                    try:
                        samples_for(seeds, target, 4)
                    except ValueError:
                        self.assertNotIn(target, expected)
                        continue
                    for strengthen, aligned in ((False, False), (True, False), (True, True)):
                        f = encode(seeds, target, 4, budget, strengthen, aligned).formula
                        with Solver(name='cadical195', bootstrap_with=f.clauses) as solver:
                            self.assertEqual(solver.solve(), target in expected,
                                             (seeds, budget, target, strengthen, aligned))
                    checks += 1
        self.assertGreater(checks, 300)


if __name__ == '__main__':
    main()
