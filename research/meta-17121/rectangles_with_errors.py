"""Exact raw rectangle covers, with a combined negative-incidence allowance."""

from functools import cache
import json
from pathlib import Path


def minimum_rectangles(words, target, width, errors):
    joins = {0}
    for w in words:
        joins |= {v | w for v in joins}
    negative_mask = ((1 << width) - 1) ^ target
    candidates = set()
    for i, a in enumerate(values := sorted(joins)):
        for b in values[:i+1]:
            product = a & b
            cost = (product & negative_mask).bit_count()
            if product & target and cost <= errors:
                candidates.add((product & target, cost))
    # A superset of covered edges at no greater cost can replace a candidate.
    maximal = [(m, c) for m, c in candidates if not any(
        (m, c) != (n, d) and m & ~n == 0 and c >= d for n, d in candidates)]
    rem = target
    for w in words:
        if w & negative_mask == 0:
            rem &= ~w

    @cache
    def cover(remaining, allowance):
        if not remaining:
            return 0
        p = remaining & -remaining
        return 1 + min((cover(remaining & ~m, allowance - c)
                        for m, c in maximal if m & p and c <= allowance),
                       default=float('inf'))
    return cover(rem, errors)


if __name__ == '__main__':
    tables = json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    for i, seeds in enumerate(tables):
        zero, one = [minimum_rectangles(seeds, 16383, 32, limit) for limit in (0, 1)]
        assert zero == 6 and one == [5, 6, 6, 6][i]
        print(f'Case {i}: clean minimum {zero}, one-incidence minimum {one}.')
