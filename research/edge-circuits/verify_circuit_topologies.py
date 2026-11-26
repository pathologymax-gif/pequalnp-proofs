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
"""

from argparse import ArgumentParser
from functools import cache
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


def truth_table_index(n, variables, edges):
    """Bit j of a truth table is its value on the assignment encoded by j."""
    functions = [0] * (1 << len(edges))
    used = [0] * len(functions)
    index = {}
    for graph in range(1, len(functions)):
        bit = graph & -graph
        other = graph ^ bit
        u, v = edges[bit.bit_length() - 1]
        functions[graph] = functions[other] | (variables[u] & variables[v])
        used[graph] = used[other] | (1 << u) | (1 << v)
        if used[graph] == (1 << n) - 1:
            index[functions[graph]] = graph
    return index


def count(n):
    variables = [sum(1 << assignment for assignment in range(1 << n)
                     if assignment & (1 << v)) for v in range(n)]
    edges = list(combinations(range(n), 2))
    matching = truth_table_index(n, variables, edges)
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
                graph = matching.get(values[-1])
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
}


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, choices=range(2, 7), default=6)
    args = parser.parse_args()
    print("n  labeled<=n-1  labeled<=n  labeled=n  unlabeled<=n-1  unlabeled<=n")
    for n in range(2, args.max_n + 1):
        result = count(n)
        if result != EXPECTED[n]:
            raise ValueError(f"unexpected count for {n}: {result}")
        (tight, iso_tight), (extra, iso_extra) = result
        print(n, tight, extra, extra - tight, iso_tight, iso_extra, sep="  ")
