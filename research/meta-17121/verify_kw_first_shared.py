"""Check the base and 236 augmented rectangle bounds using Python integers."""
from base64 import b64decode
import gzip
import itertools
import json
from pathlib import Path
import zlib

HERE = Path(__file__).resolve().parent
TARGET = 16383
SCALE = 100000


def model(words):
    """Generate incidence in numeric vertex, subset, then negative-column order."""
    tests = [tuple(i for i,word in enumerate(words) if word & (1 << k)) for k in range(32)]
    positive = tests[:14]
    negative = sorted(set(tests[14:]) - {()})
    width = len(negative)
    uses = []
    number = 0
    for vertex in range(len(words)):
        possible_rows = [r for r,e in enumerate(positive) if vertex in e]
        for mask in range(1, 1 << len(possible_rows)):
            rows = [r for j,r in enumerate(possible_rows) if mask & (1 << j)]
            for c,test in enumerate(negative):
                if vertex not in test:
                    uses.append((number, tuple(r*width+c for r in rows)))
            number += 1
    return number, uses, len(positive)*width


def check_tree(words, root, threshold, base=False):
    ny, uses, cells = model(words)
    nz = len(uses)
    fixed = {}

    def visit(node):
        internal = isinstance(node,dict) if base else isinstance(node,list)
        if internal:
            if base:
                assert set(node) == {'split','children'} and len(node['children']) == 2
                j, branches = node['split'], node['children']
            else:
                assert len(node) == 3
                j, *branches = node
            assert type(j) is int and 0 <= j < ny+nz and j not in fixed
            leaves = 0
            for bit,branch in enumerate(branches):
                fixed[j] = bit
                leaves += visit(branch)
            del fixed[j]
            return leaves
        if base:
            multipliers = node
        else:
            assert isinstance(node,str)
            multipliers = json.loads(zlib.decompress(b64decode(node,validate=True)))
        assert isinstance(multipliers,list) and len(multipliers) == cells+nz
        assert all(type(x) is int for x in multipliers)
        p, q = multipliers[:cells], multipliers[cells:]
        assert all(lam <= 0 for lam in q)
        # Independently compute the Lagrangian reduced coefficient of each
        # selector y, column-use z, and cell slack, in that order.
        reduced_y = [SCALE] * ny
        reduced_z = []
        for (y, covered), lam in zip(uses,q):
            reduced_y[y] += lam
            reduced_z.append(-lam - sum(p[cell] for cell in covered))
        reduced_slack = [32*SCALE-weight for weight in p]
        bound = sum(p)
        for j,coef in enumerate(itertools.chain(reduced_y,reduced_z,reduced_slack)):
            bound += coef*fixed[j] if j in fixed else min(0,coef)
        assert bound > threshold*SCALE, (bound,threshold)
        return 1

    return visit(root)


def first_gates(row):
    assert len(row) == 11 and row.count(0) == 1
    assert all(type(w) is int and 0 <= w < 2**32 for w in row)
    slot = row.index(0)
    variables = [j for j in range(11) if j != slot]
    pairs = list(itertools.combinations(variables,2))
    assert all(sum((word>>bit)&1 for word in row)==2 for bit in range(14))
    assert len({tuple(j for j in variables if (row[j]>>bit)&1) for bit in range(14)}) == 14
    cases = {}
    counts = {'and':0,'or':0}
    for i,j in pairs:
        for op,w in [('and',row[i]&row[j]),('or',row[i]|row[j])]:
            error = w ^ TARGET
            admissible = all(((s^TARGET)&error)!=(s^TARGET) for s in row)
            if not admissible:
                assert op == 'and' and (w & TARGET) == 0
                continue
            augmented = row.copy()
            augmented[slot] = w
            cases[f'{op}-{i}-{j}'] = augmented
            counts[op] += 1
    assert counts == {'and':14,'or':45}
    return cases


def main():
    if not __debug__:
        raise RuntimeError('Use regular Python so all certificate assertions run.')
    rows = json.loads((HERE/'seed_tables.json').read_text())
    base = json.loads(gzip.decompress((HERE/'kw_formula_certificates.json.gz').read_bytes()))
    assert len(rows) == len(base) == 4
    total = 0
    for i,(row,base_tree) in enumerate(zip(rows,base)):
        assert row.index(0) == i
        base_leaves = check_tree(row,base_tree,19,base=True)
        cases = first_gates(row)
        stored = json.loads(gzip.decompress((HERE/f'kw_first_shared_{i}.json.gz').read_bytes()))
        assert set(stored) == set(cases)
        augmented_leaves = 0
        for label,words in cases.items():
            assert set(stored[label]) == {'tree'}
            augmented_leaves += check_tree(words,stored[label]['tree'],18)
        total += len(cases)
        print(f'row {i}: {base_leaves} base leaves, {len(cases)} gate cases, '
              f'{augmented_leaves} augmented leaves',flush=True)
    assert total == 236
    print('Verified all four base bounds and all 236 first-gate bounds.')


if __name__ == '__main__':
    main()
