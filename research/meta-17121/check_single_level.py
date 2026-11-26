"""Constructively lift ANDs that never fire on negative rows, then check four graph counts."""
from functools import reduce
from itertools import combinations
import json
from pathlib import Path


class Network:
    """A binary circuit over tabulated inputs. Signal -1 is the constant zero."""

    def __init__(self, inputs):
        self.inputs = inputs
        self.gates = {}
        self.values = dict(enumerate(inputs))
        self.values[-1] = 0
        self.known = {}

    def add(self, op, a, b):
        if a == b:
            return a
        if -1 in (a, b):
            return -1 if op == 'AND' else max(a, b)
        key = (op, *sorted((a, b)))
        if key not in self.known:
            out = len(self.inputs) + len(self.gates)
            self.gates[out] = key
            self.known[key] = out
            x, y = self.values[a], self.values[b]
            self.values[out] = x & y if op == 'AND' else x | y
        return self.known[key]

    def cone(self, outputs):
        pending = list(outputs)
        gates = set()
        while pending:
            i = pending.pop()
            if i in self.gates and i not in gates:
                gates.add(i)
                pending.extend(self.gates[i][1:])
        return sorted(gates)

    def lift(self, root):
        target = self.values[root]
        initial = self.cone([root])
        if any(x and not (x & ~target) for x in self.inputs):
            raise ValueError('A nonzero primary input is safe on all negative rows')
        if any(self.gates[i][0] == 'AND' and self.values[i] & ~target for i in initial):
            raise ValueError('An AND fires on a negative row')
        terms = []
        residual = root
        while True:
            live = self.cone([residual])
            h = next((i for i in live if self.gates[i][0] == 'AND'), None)
            if h is None:
                assert self.values[residual] == 0
                break
            terms.append(h)
            if h == residual:
                break
            sub = {h: -1}
            for i in live:
                if i != h:
                    op, a, b = self.gates[i]
                    sub[i] = self.add(op, sub.get(a, a), sub.get(b, b))
            residual = sub[residual]

        out = reduce(lambda a, b: self.add('OR', a, b), terms, -1)
        final = self.cone([out])
        depth = {}
        for i in final:
            op, a, b = self.gates[i]
            depth[i] = max(depth.get(a, 0), depth.get(b, 0)) + (op == 'AND')
        assert depth.get(out, 0) <= 1
        assert self.values[out] == target and len(final) <= len(initial)
        return len(initial), len(final)


def graph_counts(row):
    vertices = [v for v, word in enumerate(row) if word]
    columns = [frozenset(v for v in vertices if row[v] >> j & 1) for j in range(32)]
    edges = set(columns[:14])
    assert len(vertices) == 10 and len(edges) == 14 and all(len(e) == 2 for e in edges)
    independent = [frozenset(s) for k in range(len(vertices) + 1) for s in combinations(vertices, k)
                   if all(not e.issubset(s) for e in edges)]
    maximal = {s for s in independent if not any(s < u for u in independent)}
    assert maximal == set(columns[14:]) - {frozenset()}
    neighbors = {v: set().union(*(e - {v} for e in edges if v in e)) for v in vertices}
    assert max(len(neighbors[a] & neighbors[b]) for a, b in combinations(vertices, 2)) <= 1
    cover = len(vertices) - max(map(len, independent))
    return len(edges), cover, len(maximal)


def check():
    here = Path(__file__).resolve().parent
    rows = json.loads((here / 'seed_tables.json').read_text())
    stars = json.loads((here / 'star_upper.json').read_text())
    assert len(rows) == len(stars) == 4
    for case, (row, gates) in enumerate(zip(rows, stars)):
        edges, cover, negatives = graph_counts(row)
        circuit = Network(row)
        wires = [i if word else -1 for i, word in enumerate(row)]
        for op, a, b, word in gates:
            out = circuit.add(op, wires[a], wires[b])
            assert circuit.values[out] == word
            wires.append(out)
        assert circuit.values[out] == 16383
        assert circuit.lift(out) == (19, 19)
        assert edges + cover - 1 == 19
        print(f'case {case}: {edges} edges, cover {cover}, {negatives} maximal independent sets, size 19')

    # This circuit uses an AND twice inside mixed OR wires that feed other ANDs.
    # The complete four-variable truth table lets the transformation check every input.
    table = [sum(1 << j for j in range(16) if j >> i & 1) for i in range(4)]
    c = Network(table)
    h = c.add('AND', 0, 1)
    left = c.add('AND', c.add('OR', h, 0), 2)
    right = c.add('AND', c.add('OR', h, 1), 3)
    output = c.add('OR', h, c.add('OR', left, right))
    assert c.lift(output) == (7, 5)
    print('Shared nested AND example reduces from 7 to 5 gates.')


if __name__ == '__main__':
    check()
