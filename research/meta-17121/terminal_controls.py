"""Pin each known 19-gate star circuit in the terminal-product encoding."""
import json
from terminal_synthesis import build, decode, ROOT
from test_synthesis import canonicalize
from exact_synthesis import check_witness
from pysat.solvers import Solver


def check(case, row, original):
    dirty = [g for g in original if g[0] == 'OR'][:8]
    products = [g for g in original if g[0] == 'AND']
    assert original[:8] == dirty and original[8:14] == products
    arranged = canonicalize(row, dirty)
    f, meta = build(row, 8, 6)
    ids, gates, _, _ = meta
    # All dirty outputs of this fixture have distinct truth words.
    indices = {row[k]: j for j, k in enumerate(ids)}
    old = row + [g[3] for g in dirty]
    ordered = row[:]
    assumed = []
    for i, (op, a, b, val) in enumerate(arranged):
        x, y = sorted((indices[ordered[a]], indices[ordered[b]]))
        l, r, oper, _, _ = gates[i]
        assumed += [l[x], r[y], -oper]
        indices[val] = len(ids) + i
        ordered.append(val)
    for i, (_, a, b, v) in enumerate(sorted(products, key=lambda g: (g[3] & -g[3]).bit_length())):
        x, y = sorted((indices[old[a]], indices[old[b]]))
        l, r, _, _, _ = gates[8 + i]
        assumed += [l[x], r[y]]
    with Solver(name='cadical195', bootstrap_with=f.clauses) as s:
        assert s.solve(assumptions=assumed)
        trace = decode(row, meta, {x for x in s.get_model() if x > 0})
        check_witness(row, 16383, trace, 19)
    print('Verified case', case, 'at 19 gates with six terminal products')


if __name__ == '__main__':
    rows = json.loads((ROOT/'seed_tables.json').read_text())
    circuits = json.loads((ROOT/'star_upper.json').read_text())
    for i,(row,program) in enumerate(zip(rows,circuits)):
        check(i,row,program)
