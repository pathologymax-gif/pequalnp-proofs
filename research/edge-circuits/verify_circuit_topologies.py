"""Independently count graph edge functions realized with at most n Boolean gates.

Inputs are the n nonisolated vertices of a labeled simple graph. AND and OR
have fan-in two. NOT has fan-in one. The gate budget is n. With n reachable
essential inputs, even allowing constants, an extremal cone is either a tree or
a tree with one shared wire. A single NOT in a tree makes at least one essential
variable decreasing, so it cannot compute a monotone edge function.

We enumerate all binary gate topologies with arbitrary AND/OR labels at these
two budgets. In a tree with n gates, one leaf can be wired to an earlier input
or to a completed gate, yielding n distinct inputs. Plane orientations suffice:
at the branching point between uses, visit the defining occurrence first.

Run with Python 3.10 or later. The default checks n = 2 through 6.
Pass --max-n 8 to extend the exhaustive enumeration through eight vertices.
"""

from argparse import ArgumentParser
from functools import cache, lru_cache
from itertools import combinations, permutations


@cache
def plane_trees(gates):
    if gates == 0:
        return (None,)
    return tuple((left, right)
                 for size in range(gates)
                 for left in plane_trees(size)
                 for right in plane_trees(gates - 1 - size))


def indexed_gates(tree):
    """Negative wire indices encode leaves; nonnegative indices encode gates."""
    gates = []
    nleaves = 0

    def visit(subtree):
        nonlocal nleaves
        if subtree is None:
            nleaves += 1
            return -nleaves
        left, right = map(visit, subtree)
        gates.append((left, right, nleaves - 1))
        return len(gates) - 1

    visit(tree)
    return gates


def binary_topologies(n, gate_count):
    for tree in plane_trees(gate_count):
        gates = indexed_gates(tree)
        if gate_count == n - 1:
            rewires = [(-1, -1)]
        else:
            rewires = []
            for leaf in range(1, gate_count + 1):
                rewires.extend((leaf, earlier) for earlier in range(leaf))
                rewires.extend((leaf, n + gate)
                               for gate, (_, _, last) in enumerate(gates)
                               if last < leaf)

        for replaced, source in rewires:
            def wire(index):
                if index >= 0:
                    return n + index
                leaf = -1 - index
                if leaf == replaced:
                    return source
                return leaf - int(0 <= replaced < leaf)

            yield [(wire(left), wire(right)) for left, right, _ in gates]


def graph_recognizer(n, variables, edges):
    """A graph is forced by the truth table values on two-element sets."""
    samples = [1 << ((1 << u) | (1 << v)) for u, v in edges]
    terms = [variables[u] & variables[v] for u, v in edges]
    endpoints = [(1 << u) | (1 << v) for u, v in edges]
    singleton_or_empty = 1 + sum(1 << (1 << i) for i in range(n))

    @lru_cache(maxsize=12000)
    def recognize(function):
        if function & singleton_or_empty:
            return None
        graph = covered = reconstructed = 0
        for k, sample in enumerate(samples):
            if function & sample:
                graph |= 1 << k
                covered |= endpoints[k]
                reconstructed |= terms[k]
        if reconstructed == function and covered == (1 << n) - 1:
            return graph
        return None

    return recognize


def count(n):
    variables = [sum(1 << assignment for assignment in range(1 << n)
                     if assignment & (1 << v)) for v in range(n)]
    edges = list(combinations(range(n), 2))
    recognize = graph_recognizer(n, variables, edges)
    edge_bits = {edge: 1 << index for index, edge in enumerate(edges)}
    relabelings = [[edge_bits[tuple(sorted((p[u], p[v])))] for u, v in edges]
                   for p in permutations(range(n))]
    labeled = set()
    classes = 0
    totals = []

    for gate_count in (n - 1, n):
        for topology in binary_topologies(n, gate_count):
            for ops in range(1 << gate_count):
                values = variables.copy()
                for k, (u, v) in enumerate(topology):
                    a, b = values[u], values[v]
                    values.append((a & b) if ops & (1 << k) else (a | b))
                graph = recognize(values[-1])
                if graph is None or graph in labeled:
                    continue
                classes += 1
                active = [i for i in range(len(edges)) if graph & (1 << i)]
                for relabel in relabelings:
                    labeled.add(sum(relabel[i] for i in active))
        totals.append((len(labeled), classes))
    return totals


EXPECTED = {
    2: [(1, 1), (1, 1)],
    3: [(3, 1), (3, 1)],
    4: [(10, 3), (22, 4)],
    5: [(45, 3), (225, 6)],
    6: [(241, 7), (2101, 17)],
    7: [(1428, 8), (19068, 31)],
    8: [(9325, 16), (178417, 69)],
}


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, choices=range(2, 9), default=6)
    args = parser.parse_args()
    print("n  labeled<=n-1  labeled<=n  labeled=n  unlabeled<=n-1  unlabeled<=n")
    for n in range(2, args.max_n + 1):
        result = count(n)
        if n in EXPECTED and result != EXPECTED[n]:
            raise ValueError(f"unexpected count for {n}: {result}")
        (tight, iso_tight), (extra, iso_extra) = result
        print(n, tight, extra, extra - tight, iso_tight, iso_extra, sep="  ")
