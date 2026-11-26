"""Enumerate minimal forbidden induced subgraphs for the one-extra-gate class.

A minimal connected obstruction has no false twins. Pick a vertex whose deletion
preserves connectedness. The smaller allowed graph is an independent blow-up of
K2, P4, or P5. Each of its false-twin classes is either a singleton (adjacent or
nonadjacent to the deleted vertex), or a pair split by that vertex. These three
possibilities per template vertex exhaust the connected candidates. The sole
minimal disconnected obstruction is the disjoint union of two P4s.
"""

from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, permutations, product
from math import comb
from random import Random


def subsets(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def components(graph, vertices):
    unseen = vertices
    while unseen:
        todo = unseen & -unseen
        seen = 0
        while todo:
            seen |= todo
            adjacent = 0
            for vertex in subsets(todo):
                adjacent |= graph[vertex]
            todo = (adjacent & vertices) & ~seen
        unseen ^= seen
        yield seen


def allowed(graph, vertices):
    exceptional = 0
    for component in components(graph, vertices):
        if component.bit_count() < 2:
            continue
        representatives = {}
        for vertex in subsets(component):
            representatives[graph[vertex] & component] = vertex
        if len(representatives) == 2:
            continue
        if len(representatives) not in (4, 5):
            return False
        core = sum(1 << v for v in representatives.values())
        degrees = sorted((graph[v] & core).bit_count() for v in subsets(core))
        if degrees != [1, 1] + [2] * (len(degrees) - 2):
            return False
        exceptional += 1
        if exceptional > 1:
            return False
    return True


def extension(options):
    groups = []
    n = 1
    neighbors = []
    for code in options:
        group = [n]
        if code == 2:
            group.append(n + 1)
        if code:
            neighbors.append(n)
        groups.append(group)
        n += len(group)
    graph = [0] * n
    def edge(x, y):
        graph[x] |= 1 << y
        graph[y] |= 1 << x
    for v in neighbors:
        edge(0, v)
    for left, right in zip(groups, groups[1:]):
        for x, y in product(left, right):
            edge(x, y)
    return graph


def canonical(graph):
    """Minimize edge bits over all degree-preserving relabelings."""
    groups = {}
    for v, mask in enumerate(graph):
        groups.setdefault(mask.bit_count(), []).append(v)
    ordered = [groups[k] for k in sorted(groups)]
    pairs = list(combinations(range(len(graph)), 2))
    result = None
    for blocks in product(*(permutations(group) for group in ordered)):
        order = sum(blocks, ())
        mask = sum(1 << i for i, (u, v) in enumerate(pairs)
                   if graph[order[u]] & (1 << order[v]))
        if result is None or mask < result:
            result = mask
    return len(graph), result


def minimal(graph):
    vertices = (1 << len(graph)) - 1
    return (not allowed(graph, vertices)
            and all(allowed(graph, vertices ^ (1 << v)) for v in range(len(graph))))


NAMED = {
    "triangle": (3, "01 02 12"),
    "five-cycle": (5, "01 12 23 34 40"),
    "six-cycle": (6, "01 12 23 34 45 50"),
    "six-vertex path": (6, "01 12 23 34 45"),
    "domino": (6, "01 12 23 30 34 45 52"),
    "square with adjacent pendant leaves": (6, "01 12 23 30 04 15"),
    "three arms of lengths 1, 2, 2": (6, "01 02 23 04 45"),
    "two disjoint four-vertex paths": (8, "01 12 23 45 56 67"),
}


def graph_from_edges(n, edge_list):
    graph = [0] * n
    for edge in edge_list.split():
        u, v = map(int, edge)
        graph[u] |= 1 << v
        graph[v] |= 1 << u
    return graph


def check(condition, message):
    if not condition:
        raise AssertionError(message)


def named_patterns():
    return {name: graph_from_edges(*spec) for name, spec in NAMED.items()}


def pattern_masks(patterns):
    """All labeled versions of the eight forbidden graphs; no isomorphism tests."""
    masks = {}
    for graph in patterns.values():
        n = len(graph)
        pairs = list(combinations(range(n), 2))
        labeled = masks.setdefault(n, set())
        for order in permutations(range(n)):
            labeled.add(sum(1 << k for k, (u, v) in enumerate(pairs)
                            if graph[order[u]] & (1 << order[v])))
    return masks


def has_obstruction(graph, masks):
    for size, forbidden in masks.items():
        for subgraph in combinations(range(len(graph)), size):
            edges = combinations(subgraph, 2)
            mask = sum(1 << k for k, (u, v) in enumerate(edges)
                       if graph[u] & (1 << v))
            if mask in forbidden:
                return True
    return False


def graph_from_mask(n, edges, mask):
    graph = [0] * n
    for k in subsets(mask):
        u, v = edges[k]
        graph[u] |= 1 << v
        graph[v] |= 1 << u
    return graph


def compare_induced_test(masks, n, samples=None):
    edges = list(combinations(range(n), 2))
    count = 1 << len(edges)
    if samples is None:
        cases = range(count)
    else:
        cases = Random(20261126 + n).sample(range(count), samples)
    for mask in cases:
        graph = graph_from_mask(n, edges, mask)
        agrees = allowed(graph, (1 << n) - 1) != has_obstruction(graph, masks)
        check(agrees, f"quotient and obstruction tests disagree: n={n}, mask={mask}")
    return len(cases)


def labeled_counts(max_n):
    """Count labeled graphs having no isolated vertices by component decomposition."""
    stirling = [[0] * (max_n + 1) for _ in range(max_n + 1)]
    stirling[0][0] = 1
    biclique_unions = [1] + [0] * max_n
    exceptional = [0] * (max_n + 1)
    one_extra = [0] * (max_n + 1)
    for n in range(1, max_n + 1):
        for k in range(1, n + 1):
            stirling[n][k] = k * stirling[n - 1][k] + stirling[n - 1][k - 1]
        # Choose the component of one distinguished vertex, then its bipartition.
        for size in range(2, n + 1):
            biclique_unions[n] += (comb(n - 1, size - 1)
                                   * ((1 << (size - 1)) - 1)
                                   * biclique_unions[n - size])
        # An unordered partition into k groups admits k!/2 linear arrangements.
        exceptional[n] = 12 * stirling[n][4] + 60 * stirling[n][5]
        one_extra[n] = sum(comb(n, k) * exceptional[k] * biclique_unions[n - k]
                           for k in range(1, n + 1))
    return list(zip(biclique_unions, one_extra))


def run():
    connected = set()
    attempts = 0
    for size in (2, 4, 5):
        for options in product(range(3), repeat=size):
            graph = extension(options)
            vertices = (1 << len(graph)) - 1
            attempts += 1
            if len(set(graph)) != len(graph):
                continue
            if next(components(graph, vertices)) != vertices:
                continue
            if minimal(graph):
                connected.add(canonical(graph))
    patterns = named_patterns()
    disjoint = patterns["two disjoint four-vertex paths"]
    check(all(minimal(g) for g in patterns.values()), "a named obstruction is not minimal")
    obstructions = connected | {canonical(disjoint)}
    check(obstructions == {canonical(g) for g in patterns.values()},
          "computed obstructions differ from named graphs")
    check(len(obstructions) == 8 and attempts == 333, "unexpected enumeration size")
    print(f"Connected template extensions considered: {attempts}")
    print(f"Minimal obstructions by order: {dict(sorted(Counter(n for n, _ in obstructions).items()))}")
    for name, graph in patterns.items():
        n, mask = canonical(graph)
        print(f"  {name}: n={n}, canonical mask={mask}")
    return patterns


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true",
                        help="omit exhaustive small graph and random larger graph tests")
    args = parser.parse_args()
    patterns = run()
    # Independent gate-topology enumeration in verify_circuit_topologies.py.
    direct = {7: (1428, 17640), 8: (9325, 169092)}
    counts = labeled_counts(8)
    for n, expected in direct.items():
        check(counts[n] == expected, f"mismatch with direct circuit count for {n}")
        print(f"n={n}: minimum n-1: {counts[n][0]}; minimum n: {counts[n][1]}")
    if not args.quick:
        masks = pattern_masks(patterns)
        exhaustive = sum(compare_induced_test(masks, n) for n in range(7))
        print(f"Cross-checked all {exhaustive:,} labeled graphs of orders 0 through 6.")
        for n in (7, 8):
            samples = compare_induced_test(masks, n, 2048)
            print(f"n={n}: {samples:,} reproducible sampled graphs passed.")
