"""Overapproximate usable intermediate signals by their order on finite test inputs."""
from itertools import combinations
import json
from pathlib import Path


def bits(mask):
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask ^= b


class Problem:
    def __init__(self, row):
        self.vs = tuple(i for i, w in enumerate(row) if w)
        original = [sum(1 << v for v in self.vs if row[v] >> j & 1) for j in range(32)]
        self.edges = original[:14]
        self.neg = sorted(set(original[14:]) - {0})
        self.tests = self.edges + self.neg + [1 << v for v in self.vs] + [0]
        self.zero = len(self.tests) - 1
        self.all = (1 << len(self.tests)) - 1
        self.neg_bits = sum(1 << j for j in range(14, 14 + len(self.neg)))
        self.required = []
        self.primary = {v: sum(1 << j for j, s in enumerate(self.tests) if s >> v & 1) for v in self.vs}
        self.neighbor_singles = {v: [14 + len(self.neg) + self.vs.index((e ^ (1 << v)).bit_length() - 1)
            for e in self.edges if e >> v & 1] for v in self.vs}
        # Every raw variable has a private negative against each other raw
        # variable. Also no two variables can be each other's only AND reader.
        assert all(len(ns) >= 2 for ns in self.neighbor_singles.values())
        assert all(self.primary[a] & ~self.primary[b] & self.neg_bits for a in self.vs for b in self.vs if a != b)

    def initial(self, repeat):
        r = sum(1 << v for v in repeat)
        return [sum(1 << j for j, b in enumerate(self.tests) if a & r & ~b == 0) for a in self.tests]

    def alternatives(self, v, order):
        z = self.primary[v]
        contain, omit = self.neg_bits & z, self.neg_bits & ~z
        near = self.neighbor_singles[v]
        base = 0
        for i in near:
            base |= order[i]
        # An AND reader is positive on every singleton neighbor on its h side.
        # It must fire on, and improve z on, two different negative samples.
        for one in bits(contain):
            force_one = base | order[one]
            for zero in bits(contain & ~force_one):
                yield True, force_one, (1 << zero) | (1 << self.zero)
        # An OR reader's dirty h is zero on every maximal negative omitting z.
        # To improve upon raw z it must also be true on some nonincident edge.
        force_zero = omit | (1 << self.zero)
        for one in bits(contain):
            for edge in bits(16383 & ~z):
                yield False, order[one] | order[edge], force_zero

    def relax(self, repeat):
        order = self.initial(repeat)
        while True:
            after = order[:]
            for v in self.vs:
                if v in repeat:
                    continue
                z = self.primary[v]
                forbidden_cache = {}
                for is_and, up, force_zero in self.alternatives(v, order):
                    if up & force_zero:
                        continue
                    if force_zero not in forbidden_cache:
                        forbidden_cache[force_zero] = sum(1 << j for j, d in enumerate(order) if d & force_zero)
                    down = forbidden_cache[force_zero]
                    if is_and:
                        # For a<=b a new comparison can break only at z(a)=1,
                        # z(b)=0 and when some feasible h has h(a)=1.
                        for j in bits(z & ~down):
                            after[j] &= z
                    else:
                        # At z(a)=1,z(b)=0 it suffices to set h(b)=0, unless
                        # b is above one of the forced positive inputs.
                        for j in bits(z):
                            after[j] &= z | up
            if after == order:
                break
            order = after
        # If an edge is below a negative even under this optimistic basis,
        # its terminal AND needs a raw, once-read operand on that edge.
        possible_stars = {}
        for v in self.vs:
            contain = self.neg_bits & self.primary[v]
            possible_stars[v] = not any(order[j] & contain for j in self.neighbor_singles[v])
        missed = [e for j, e in enumerate(self.edges) if order[j] & self.neg_bits
                  and not any(v not in repeat and possible_stars[v] for v in bits(e))]
        return missed


if __name__ == '__main__':
    seed = json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    for k, row in enumerate(seed):
        p = Problem(row)
        for n in range(2, 6):
            possible = [s for s in combinations(p.vs, n) if not p.relax(s)]
            print(k, n, len(possible), possible[:10], flush=True)
