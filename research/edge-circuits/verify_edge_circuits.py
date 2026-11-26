"""Check minimum-size edge circuits on all labeled graphs with 2 to 6 vertices.

Run with Python 3.9 or later. The script uses only the standard library.

The edge function is true if the selected vertices contain both ends of an
edge. Every nonisolated vertex is an essential variable. Consider the cone of
a circuit output with n essential inputs, b binary gates and u unary gates.
Its underlying graph is connected, so its wire count 2b + u is at least
n + b + u - 1. Thus b >= n - 1. Equality at n - 1 total gates forces a tree
and rules out unary gates, extra constants, and shared subexpressions. Hence
it suffices to enumerate AND/OR formulas in which each input occurs once.
"""

from itertools import combinations


def read_once_tables(input_tables, full_set):
    """Enumerate the truth tables on each subset by all possible root splits."""
    tables = {1 << v: {table} for v, table in enumerate(input_tables)}
    for subset in range(1, full_set + 1):
        if subset in tables:
            continue
        results = set()
        left = (subset - 1) & subset
        while left:
            right = subset ^ left
            if left < right:  # One orientation of every unordered split.
                for f in tables[left]:
                    for g in tables[right]:
                        results.add(f & g)
                        results.add(f | g)
            left = (left - 1) & subset
        tables[subset] = results
    return tables[full_set]


def is_union_of_bicliques(neighbors):
    """Test whether every component has two nonempty, fully joined parts."""
    unseen = set(range(len(neighbors)))
    while unseen:
        root = min(unseen)
        right = neighbors[root]
        if not right:
            return False
        left = neighbors[min(right)]
        if left & right:
            return False
        if any(neighbors[v] != right for v in left):
            return False
        if any(neighbors[v] != left for v in right):
            return False
        unseen.difference_update(left, right)
    return True


def check_size(n):
    # Bit a of each truth table is its output on assignment a.
    assignments = range(1 << n)
    inputs = [
        sum(1 << a for a in assignments if a & (1 << v)) for v in range(n)
    ]
    minimum_tables = read_once_tables(inputs, (1 << n) - 1)
    pairs = list(combinations(range(n), 2))
    edge_tables = [inputs[u] & inputs[v] for u, v in pairs]
    eligible = minimum = 0

    for graph in range(1 << len(pairs)):
        neighbors = [set() for _ in range(n)]
        table = 0
        for i, (u, v) in enumerate(pairs):
            if graph & (1 << i):
                neighbors[u].add(v)
                neighbors[v].add(u)
                table |= edge_tables[i]
        if not all(neighbors):
            continue
        eligible += 1
        uses_minimum = table in minimum_tables
        if uses_minimum != is_union_of_bicliques(neighbors):
            raise AssertionError(f"Classification mismatch: n={n}, graph mask={graph}")
        minimum += uses_minimum

    return eligible, minimum


if __name__ == "__main__":
    print("vertices  graphs without isolates  edge functions with n-1 gates")
    for size in range(2, 7):
        graphs, functions = check_size(size)
        print(f"{size:8}  {graphs:22,}  {functions:29,}")
    print("Every minimum-gate result agreed with the graph classification.")
