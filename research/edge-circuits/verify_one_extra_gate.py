"""Classify edge functions implementable with at most n gates, for 2 <= n <= 6.

Python 3.9+; no third-party dependencies. Run directly for counts. Pass
--classes for a representative edge list of every class requiring exactly n.

Scope: simple labeled graphs with no isolates. Each AND/OR has two inputs;
NOT has one. All gates cost one. Input variables and constants are free.
The edge function is true precisely when the selected vertices span an edge.

Counting the wires in the output cone gives b >= n-1 for the number of
binary gates. Indeed it has n input nodes, b binary and u unary gates, and
2b+u wires, and is connected. Constant inputs can be simplified away.
If b=n-1, the cone is a tree. A single NOT would make the function decreasing
in an essential leaf below that NOT, impossible for an edge function.
When b=n, no room remains for a unary gate. Every node except the output
must feed at least one wire. There is then exactly one surplus wire:
one node feeds two wires and every other non-output node feeds one.
The subcircuit at this shared node is a read-once formula B (possibly a
single input). Contract it to an input q and unfold the two uses of q.
The remaining AND/OR tree then uses every outside input once and q twice.
This describes all possibilities, and every such composite costs n gates.
"""

from argparse import ArgumentParser
from itertools import combinations, permutations
from time import perf_counter


def formula_tables(leaves):
    """Truth tables of all binary AND/OR trees on these leaf occurrences."""
    sets = {1 << i: {table} for i, table in enumerate(leaves)}
    full = (1 << len(leaves)) - 1
    for subset in range(1, full + 1):
        if subset in sets:
            continue
        result = set()
        left = (subset - 1) & subset
        while left:
            right = subset ^ left
            if left < right:
                for f in sets[left]:
                    for g in sets[right]:
                        result.add(f & g)
                        result.add(f | g)
            left = (left - 1) & subset
        sets[subset] = result
    return sets[full]


def graph_tables(n, pairs, inputs):
    tables = {}
    table_by_mask = [0] * (1 << len(pairs))
    used_by_mask = [0] * len(table_by_mask)
    for graph in range(1, len(table_by_mask)):
        low = graph & -graph
        u, v = pairs[low.bit_length() - 1]
        rest = graph ^ low
        table_by_mask[graph] = table_by_mask[rest] | (inputs[u] & inputs[v])
        used_by_mask[graph] = used_by_mask[rest] | (1 << u) | (1 << v)
        if used_by_mask[graph] == (1 << n) - 1:
            tables[table_by_mask[graph]] = graph
    return tables


def one_shared_block(inputs, graph_by_table):
    """Find graph witnesses with shared block on the first b input labels."""
    n = len(inputs)
    q = inputs[0]
    even = q >> 1
    witnesses = set()
    for b in range(1, n):  # Sharing a block on every variable only repeats it.
        blocks = formula_tables(inputs[:b])
        contexts = formula_tables([q, q, *inputs[b:]])
        for context in contexts:
            # q is the least significant assignment bit. Outside variables
            # have indices >= b. Broadcast both q-cofactors to all positions.
            off = context & even
            off |= off << 1
            on = context & q
            on |= on >> 1
            for block in blocks:
                composed = off | (block & on)  # off implies on by monotonicity.
                if composed in graph_by_table:
                    witnesses.add(graph_by_table[composed])
    return witnesses


def orbits(n, pairs, graphs):
    """Return representatives and orbit sizes, closing the given set under relabeling."""
    index = {edge: i for i, edge in enumerate(pairs)}
    mappings = [
        [1 << index[tuple(sorted((p[u], p[v])))] for u, v in pairs]
        for p in permutations(range(n))
    ]
    pending = set(graphs)
    classes = {}
    while pending:
        graph = min(pending)
        indices = [i for i in range(len(pairs)) if graph & (1 << i)]
        orbit = {sum(mapping[i] for i in indices) for mapping in mappings}
        classes[min(orbit)] = orbit
        pending.difference_update(orbit)
    return classes


def unrestricted_search(n, inputs, graph_by_table):
    """Independent gate-by-gate search, including NOT and arbitrary fanout."""
    universe = (1 << (1 << n)) - 1
    frontier = {frozenset(inputs)}
    hit = set()
    for depth in range(1, n + 1):
        following = set()
        for available in frontier:
            candidates = {universe ^ a for a in available}
            for a, b in combinations(available, 2):
                candidates.update((a & b, a | b))
            for new in candidates - available:
                if new in graph_by_table:
                    hit.add(graph_by_table[new])
                if depth < n:
                    following.add(available | {new})
        frontier = following
    return hit


def structural_cost(n, pairs, graph):
    """Return n-1, n, or None according to the proposed graph characterization.

    Vertices with identical open neighborhoods are independent false twins.
    Collapsing them turns each complete bipartite component into K2 and each
    blown-up path into its underlying path (for four and five vertices).
    """
    neighbors = [0] * n
    for i, (u, v) in enumerate(pairs):
        if graph & (1 << i):
            neighbors[u] |= 1 << v
            neighbors[v] |= 1 << u
    representatives = [neighbors.index(row) for row in set(neighbors)]
    quotient = {
        u: {v for v in representatives if neighbors[u] & (1 << v)}
        for u in representatives
    }
    unseen = set(quotient)
    exceptional = 0
    while unseen:
        stack = [unseen.pop()]
        degrees = []
        while stack:
            u = stack.pop()
            degrees.append(len(quotient[u]))
            new = unseen & quotient[u]
            unseen.difference_update(new)
            stack.extend(new)
        if sorted(degrees) == [1, 1]:
            continue
        if sorted(degrees) not in ([1, 1, 2, 2], [1, 1, 2, 2, 2]):
            return None
        exceptional += 1
    return n - 1 + exceptional if exceptional <= 1 else None


def check(n, show_classes):
    timer = perf_counter()
    pairs = list(combinations(range(n), 2))
    inputs = [
        sum(1 << a for a in range(1 << n) if a & (1 << v))
        for v in range(n)
    ]
    graph_by_table = graph_tables(n, pairs, inputs)
    minimum = {graph_by_table[t] for t in formula_tables(inputs) if t in graph_by_table}
    witnesses = one_shared_block(inputs, graph_by_table) - minimum
    classes = orbits(n, pairs, witnesses)
    extra = set().union(*classes.values())
    all_hits = minimum | extra
    for graph in graph_by_table.values():
        cost = n - 1 if graph in minimum else n if graph in extra else None
        if structural_cost(n, pairs, graph) != cost:
            raise AssertionError(f"Graph characterization differs: n={n}, mask={graph}.")
    if n <= 4:
        independent = unrestricted_search(n, inputs, graph_by_table)
        if independent != all_hits:
            raise AssertionError(f"Unrestricted search differs at n={n}.")
    print(f"{n:2} {len(graph_by_table):9,} {len(minimum):9,} {len(extra):10,}"
          f" {len(all_hits):10,} {len(classes):13,} {perf_counter() - timer:8.3f}")
    if show_classes:
        for rep, orbit in sorted(classes.items()):
            edges = " ".join(f"{u}-{v}" for i, (u, v) in enumerate(pairs) if rep & (1 << i))
            print(f"   {len(orbit):4} labelings   {edges}")
    return len(minimum), len(extra)


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--classes", action="store_true", help="print exact-n representatives")
    args = parser.parse_args()
    print(" n  eligible  size n-1     size n   size <=n  size-n types  seconds")
    for size in range(2, 7):
        check(size, args.classes)
    print("Every graph agrees with the biclique / one P4-or-P5 blow-up characterization.")
    print("Direct gate-by-gate enumeration independently agrees for n <= 4.")
