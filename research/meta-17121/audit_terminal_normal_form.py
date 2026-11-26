"""Compare unrestricted optimum with independent enumeration of terminal products."""

from collections import Counter
from itertools import combinations
from random import Random


def next_words(pool):
    for x, y in combinations(pool, 2):
        yield x & y
        yield x | y


def ordinary(seeds, budget):
    optimum = {w:0 for w in seeds}
    pools = {frozenset(seeds)}
    for size in range(1, budget+1):
        pools = {pool | {v} for pool in pools for v in next_words(pool) if v and v not in pool}
        for pool in pools:
            for v in pool:
                optimum.setdefault(v, size)
    return optimum


def normalized(seeds, target, budget):
    pools = {frozenset(seeds)}
    best = budget+1
    best_terms = None
    for d in range(budget):
        if d+1 > best:
            break
        for pool in pools:
            products = {x & y for x,y in combinations(pool,2) if x & y and (x & y) & ~target == 0}
            counts = {0:0}
            for word in products:
                if counts.get(target, budget+1) == 1:
                    break
                for old, cost in list(counts.items()):
                    w = old | word
                    counts[w] = min(cost+1, counts.get(w, budget+1))
            t = counts.get(target, budget+1)
            if d+2*t-1 < best:
                best, best_terms = d+2*t-1, t
        pools = {pool | {v} for pool in pools for v in next_words(pool)
                 if v not in pool and v & ~target and v & target}
    return best, best_terms


def check(seeds, budget, cases):
    reachable = ordinary(seeds, budget)
    for target, size in reachable.items():
        if size == 0 or not target or any(x & ~target == 0 for x in seeds):
            continue
        norm, terms = normalized(seeds, target, size)
        assert norm == size, (seeds, target, size, norm)
        cases[size, terms] += 1


if __name__ == '__main__':
    counts = Counter()
    for seeds in combinations(range(1,16), 3):
        check(seeds, 4, counts)
    rng = Random(17121)
    for _ in range(100):
        check(rng.sample(range(1,128), 4), 5, counts)
    print('Matched unrestricted and terminal minima:', sum(counts.values()))
    print('By (minimum gates, terminal terms):', sorted(counts.items()))
