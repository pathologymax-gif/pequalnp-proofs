"""Exact graph edge-function synthesis up to n+1 unit-cost AND/OR/NOT gates.

Use Python 3.10+ with no third-party packages. Run this file for n=2,...,6;
pass --max-n to choose a smaller size, or --classes for orbit representatives.
Inputs are the nonisolated vertices of a labeled loopless undirected graph.
A vertex assignment accepts iff both endpoints of at least one edge are true.

Completeness: drop dead gates and simplify constants. Write b and u for binary
and unary gates. In the connected output cone, 2b+u >= n+b+u-1, so b >= n-1.
Depth-first search from the output expands every node once. Every repeated
visit is to a previously completed node, since the circuit is acyclic. Mark
each such visit by a leaf pointing back to that node. The expanded plane
expression has b binary and u unary nodes, b+1 leaves, and b+1-n backreferences.
Conversely any such expression with valid references describes a rooted DAG.
We enumerate all plane expressions, choose exactly that many backreferences,
assign each one any previously completed gate or fresh input seen earlier,
and try all binary labels. Inputs receive names in order of first encounter.
Restoring all permutations of those names covers every labeled graph.
"""

from argparse import ArgumentParser
from functools import cache
from itertools import combinations, permutations
from struct import Struct
from time import perf_counter


@cache
def shapes(binary, unary):
    if binary == unary == 0:
        return (None,)
    result = []
    if unary:
        result.extend((child,) for child in shapes(binary, unary - 1))
    if binary:
        for left_b in range(binary):
            for left_u in range(unary + 1):
                for left in shapes(left_b, left_u):
                    for right in shapes(binary - left_b - 1, unary - left_u):
                        result.append((left, right))
    return tuple(result)


def encoding(tree, leaf_count):
    """Negative positions denote original leaves, nonnegative ones denote gates."""
    schedule = []
    last_leaf = []
    leaves = 0

    def visit(node):
        nonlocal leaves
        if node is None:
            leaves += 1
            return -leaves
        children = tuple(visit(child) for child in node)
        index = len(schedule)
        schedule.append(children)
        last_leaf.append(leaves - 1)
        return index

    visit(tree)
    completed_before = [
        tuple(i for i, last in enumerate(last_leaf) if last < leaf)
        for leaf in range(leaf_count)
    ]
    return schedule, completed_before


def leaf_bindings(n, leaf_count, completed_before):
    refs = leaf_count - n
    for holes in combinations(range(1, leaf_count), refs):
        hole_set = set(holes)
        bindings = [0] * leaf_count
        choices = []
        fresh = 0
        for leaf in range(leaf_count):
            if leaf in hole_set:
                choices.append(tuple(range(fresh)) +
                               tuple(n + gate for gate in completed_before[leaf]))
            else:
                bindings[leaf] = fresh
                fresh += 1
        if not holes:
            yield bindings
        elif len(holes) == 1:
            for source in choices[0]:
                bindings[holes[0]] = source
                yield bindings
        else:
            first, second = holes
            for src_first in choices[0]:
                bindings[first] = src_first
                for src_second in choices[1]:
                    bindings[second] = src_second
                    yield bindings


class GraphTables:
    def __init__(self, n):
        self.n = n
        self.edges = list(combinations(range(n), 2))
        self.variables = [sum(1 << a for a in range(1 << n) if a & (1 << v))
                          for v in range(n)]
        terms = [self.variables[u] & self.variables[v] for u, v in self.edges]
        endpoints = [(1 << u) | (1 << v) for u, v in self.edges]
        size = 1 << len(self.edges)
        tables = [0] * size
        support = [0] * size
        self.by_table = {}
        for mask in range(1, size):
            bit = mask & -mask
            i = bit.bit_length() - 1
            tables[mask] = tables[mask ^ bit] | terms[i]
            support[mask] = support[mask ^ bit] | endpoints[i]
            if support[mask] == (1 << n) - 1:
                self.by_table[tables[mask]] = mask
        self.eligible = set(self.by_table)
        bit_by_edge = {edge: 1 << i for i, edge in enumerate(self.edges)}
        self.relabelings = [
            [bit_by_edge[tuple(sorted((p[u], p[v])))] for u, v in self.edges]
            for p in permutations(range(n))
        ]
        self.orbits = {}
        self.reps = {}

    def orbit_reps(self, tables):
        reps = set()
        for table in tables:
            graph = self.by_table[table]
            if graph not in self.reps:
                used = [i for i in range(len(self.edges)) if graph & (1 << i)]
                orbit = frozenset(sum(mapping[i] for i in used)
                                  for mapping in self.relabelings)
                rep = min(orbit)
                self.orbits[rep] = orbit
                self.reps.update((g, rep) for g in orbit)
            reps.add(self.reps[graph])
        return reps

    def labeled_count(self, reps):
        return sum(len(self.orbits[rep]) for rep in reps)


def solve_budget(graphs, binary, unary):
    """Each 64-bit lane is a truth table for one labeling of the binary gates."""
    n = graphs.n
    lanes = 1 << binary
    broadcast = ((1 << (64 * lanes)) - 1) // ((1 << 64) - 1)
    packed_variables = [value * broadcast for value in graphs.variables]
    full = ((1 << (1 << n)) - 1) * broadcast
    selectors = []
    for gate in range(binary):
        selectors.append(sum(((1 << 64) - 1) << (64 * op)
                             for op in range(lanes) if op & (1 << gate)))
    reader = Struct(f"<{lanes}Q")
    hits = set()
    examined = 0
    leaf_count = binary + 1
    for tree in shapes(binary, unary):
        schedule, completed = encoding(tree, leaf_count)
        # Use [0,n) for inputs and [n,n+b+u) for gates. Negative placeholders
        # identify leaves until their input or backreference choice is known.
        fixed = [n + k if k >= 0 else k for children in schedule for k in children]
        remap = [(i, -v - 1) for i, v in enumerate(fixed) if v < 0]
        gates = []
        pos = op = 0
        for children in schedule:
            binary_gate = len(children) == 2
            gates.append((pos, selectors[op] if binary_gate else None))
            pos += len(children)
            op += int(binary_gate)
        for bindings in leaf_bindings(n, leaf_count, completed):
            for i, leaf in remap:
                fixed[i] = bindings[leaf]
            values = packed_variables.copy()
            for pos, selector in gates:
                left = values[fixed[pos]]
                if selector is None:
                    values.append(full ^ left)
                else:
                    right = values[fixed[pos + 1]]
                    values.append((left & right) | ((left ^ right) & selector))
            results = reader.unpack(values[-1].to_bytes(reader.size, "little"))
            hits.update(graphs.eligible.intersection(results))
            examined += 1
    return graphs.orbit_reps(hits), examined


KNOWN_FIRST_STRATA = {2: (1, 0), 3: (3, 0), 4: (10, 12), 5: (45, 180), 6: (241, 1860)}


def direct_gate_layers(graphs, allow_not):
    """Independently enumerate straight-line circuits without topology restrictions."""
    frontier = {frozenset(graphs.variables)}
    full = (1 << (1 << graphs.n)) - 1
    cumulative = set()
    hits = {}
    for depth in range(1, graphs.n + 2):
        following = set()
        for available in frontier:
            choices = {full ^ x for x in available} if allow_not else set()
            for x, y in combinations(available, 2):
                choices.update((x & y, x | y))
            # A previously available value can be used directly, so a duplicate
            # gate never reduces the minimum cost in the unrestricted DAG model.
            choices.difference_update(available)
            cumulative.update(graphs.eligible.intersection(choices))
            if depth < graphs.n + 1:
                following.update(available | {value} for value in choices)
        if depth >= graphs.n - 1:
            hits[depth] = graphs.orbit_reps(cumulative)
        frontier = following
    return hits


def run(n, show_classes):
    start = perf_counter()
    graphs = GraphTables(n)
    all_reps = set()
    monotone = set()
    exact = []
    topologies = 0
    benefited = set()
    if n <= 4:
        direct_all = direct_gate_layers(graphs, True)
        direct_monotone = direct_gate_layers(graphs, False)
    for budget in range(n - 1, n + 2):
        before = all_reps.copy()
        for binary in range(n - 1, budget + 1):
            unary = budget - binary
            reps, tested = solve_budget(graphs, binary, unary)
            all_reps.update(reps)
            topologies += tested
            if not unary:
                monotone.update(reps)
        exact.append(all_reps - before)
        benefited.update(all_reps - monotone)
        if n <= 4 and (all_reps != direct_all[budget] or monotone != direct_monotone[budget]):
            raise RuntimeError(f"Independent straight-line search differs at n={n}, size={budget}")
    counts = [graphs.labeled_count(reps) for reps in exact]
    if tuple(counts[:2]) != KNOWN_FIRST_STRATA[n]:
        raise RuntimeError(f"Earlier gate budgets disagree at n={n}: {counts}")
    print(f"{n:>1}  {len(graphs.by_table):>7,}  {counts[0]:>7,}  {counts[1]:>7,}  "
          f"{counts[2]:>8,}  {len(exact[2]):>6}  {graphs.labeled_count(benefited):>10,}  "
          f"{topologies:>11,}  {perf_counter() - start:.2f}", flush=True)
    if show_classes:
        for rep in sorted(exact[2]):
            edges = " ".join(f"{u}-{v}" for i, (u, v) in enumerate(graphs.edges)
                             if rep & (1 << i))
            print(f"  {rep:>5}  {len(graphs.orbits[rep]):>4} labelings  {edges}")
        for rep in sorted(benefited):
            print(f"  strictly helped by NOT at a tested budget: representative {rep}")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--max-n", default=6, type=int, choices=range(2, 7))
    parser.add_argument("--classes", action="store_true")
    args = parser.parse_args()
    print("n  eligible      n-1        n       n+1   types  NOT helped   topologies  seconds")
    for size in range(2, args.max_n + 1):
        run(size, args.classes)
