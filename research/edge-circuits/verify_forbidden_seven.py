"""Independently check the proposed obstructions for graph edge-function circuits.

Run with Python 3.9 or later: python verify_forbidden_seven.py
The standard library is sufficient. The program classifies every labeled simple
graph on at most seven vertices, including isolates. It also checks every
one-vertex deletion of the proposed eight-vertex obstruction, two disjoint P4s.

The allowed class is generated from empty graphs, P4, and P5 by adding an
isolate, duplicating a vertex without joining the two copies, or attaching a new
vertex to an isolate to make a separate K2. These operations generate exactly
the disjoint unions of bicliques and isolates with at most one component that
is a nonempty independent-set blowup of P4 or P5. This verifier uses neither
the false-twin quotient recognition algorithm nor the 333 extension cases.
It tests the structural class; it does not enumerate Boolean circuits.
"""

from collections import Counter
from itertools import permutations
from time import perf_counter


def edge(u, v):
    """Bit for an edge, indexing first by its larger endpoint."""
    hi, lo = max(u, v), min(u, v)
    return 1 << (hi * (hi - 1) // 2 + lo)


def labeled(edges, labels):
    return sum(edge(labels[u], labels[v]) for u, v in edges)


def path(order):
    return [(i, i + 1) for i in range(order - 1)]


def cycle(order):
    return path(order) + [(0, order - 1)]


OBSTRUCTIONS = {
    3: {"triangle": cycle(3)},
    5: {"C5": cycle(5)},
    6: {
        "C6": cycle(6),
        "P6": path(6),
        "domino": cycle(4) + [(1, 4), (4, 5), (5, 2)],
        "square with leaves at adjacent vertices": cycle(4) + [(1, 4), (2, 5)],
        "S(1,2,2)": [(0, 1), (0, 2), (2, 3), (0, 4), (4, 5)],
    },
}
TWO_P4 = path(4) + [(u + 4, v + 4) for u, v in path(4)]


def map_edges_tables(labels):
    """Lookup tables for permuting or deleting vertices, seven bits at a time."""
    n = len(labels)
    target_bits = []
    for hi in range(n):
        for lo in range(hi):
            u, v = labels[hi], labels[lo]
            target_bits.append(0 if u is None or v is None else edge(u, v))
    target_bits.extend([0] * (28 - len(target_bits)))
    tables = []
    for start in range(0, 28, 7):
        table = [0] * 128
        for mask in range(1, 128):
            bit = mask & -mask
            table[mask] = table[mask ^ bit] | target_bits[start + bit.bit_length() - 1]
        tables.append(table)
    return tables


def remap(mask, tables):
    a, b, c, d = tables
    return a[mask & 127] | b[(mask >> 7) & 127] | c[(mask >> 14) & 127] | d[(mask >> 21) & 127]


def deletion_tables(order):
    return [
        map_edges_tables([None if i == d else i - int(i > d) for i in range(order)])
        for d in range(order)
    ]


def generate_allowed(max_order):
    allowed = [{0}]
    for n in range(1, max_order + 1):
        latest = n - 1
        fixed_latest = set()
        for mask in allowed[n - 1]:
            fixed_latest.add(mask)  # add an isolated vertex
            for old in range(latest):
                neighbors = sum(
                    edge(latest, other)
                    for other in range(latest)
                    if old != other and mask & edge(old, other)
                )
                fixed_latest.add(mask | neighbors)  # add a false twin
                if neighbors == 0:
                    fixed_latest.add(mask | edge(latest, old))  # new K2 component

        # All labelings of the old vertices already occur. Place the new vertex
        # at every label by swapping it with the last vertex.
        pool = set(fixed_latest)
        for old in range(latest):
            labels = list(range(n))
            labels[old], labels[latest] = labels[latest], labels[old]
            tables = map_edges_tables(labels)
            pool.update(remap(mask, tables) for mask in fixed_latest)
        if n in (4, 5):
            pool.update(labeled(path(n), labels) for labels in permutations(range(n)))
        allowed.append(pool)
    return allowed


def check_order(n, allowed):
    expected = {}
    for name, edges in OBSTRUCTIONS.get(n, {}).items():
        for labels in permutations(range(n)):
            mask = labeled(edges, labels)
            if expected.setdefault(mask, name) != name:
                raise AssertionError("Two proposed obstruction types are isomorphic.")

    prior = allowed[n - 1]
    tables = deletion_tables(n)
    prefix = (1 << ((n - 1) * (n - 2) // 2)) - 1
    count = 1 << (n * (n - 1) // 2)
    found = Counter()
    for mask in range(count):
        # Deleting the largest label just drops its incident high-order bits.
        minimal = mask not in allowed[n] and (mask & prefix) in prior and all(
            remap(mask, tab) in prior for tab in tables[:-1]
        )
        if minimal != (mask in expected):
            raise AssertionError(f"Unexpected classification: order={n}, edge mask={mask}.")
        if minimal:
            found[expected[mask]] += 1
    print(f"n={n}: {count:,} graphs, {len(allowed[n]):,} allowed, {sum(found.values()):,} minimal exclusions")
    for name in sorted(found):
        print(f"  {name}: {found[name]}")


def main():
    start = perf_counter()
    allowed = generate_allowed(7)
    for n in range(1, 8):
        check_order(n, allowed)
    # Two disjoint P4s have two exceptional components, so the graph itself
    # is excluded by definition. Check each of its eight proper vertex deletions.
    mask = labeled(TWO_P4, range(8))
    if not all(remap(mask, tab) in allowed[7] for tab in deletion_tables(8)):
        raise AssertionError("A one-vertex deletion of two disjoint P4s is excluded.")
    print("All eight one-vertex deletions of two disjoint P4s are allowed.")
    print(f"All checks passed in {perf_counter() - start:.2f} seconds.")


if __name__ == "__main__":
    main()
