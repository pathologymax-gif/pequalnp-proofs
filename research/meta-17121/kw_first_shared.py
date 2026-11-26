"""Prove or refute the 18-leaf rectangle relaxation after one raw binary gate.

Usage: python kw_first_shared.py ROW  (emits one gzip certificate per row).
Replay: python kw_first_shared.py ROW --replay (Python standard library only).
The first shared gate is paid once. All following gate outputs have fanout one.
Unfolding those gates gives a formula with at most 18 leaves, over the original
ten variables and the shared gate as an eleventh possible leaf.
"""
import argparse
from base64 import b64decode, b64encode
from collections import Counter
import gzip
from itertools import combinations
import json
from pathlib import Path
from time import monotonic
import zlib

HERE = Path(__file__).resolve().parent
TARGET = (1 << 14) - 1
LIMIT = 18
SCALE = 100000


def augment(seed, or_size):
    free = seed.index(0)
    if or_size:
        for indices in combinations([i for i,w in enumerate(seed) if w],or_size):
            word=0
            for i in indices:
                word |= seed[i]
            new=seed.copy()
            new[free]=word
            yield 'or-'+'-'.join(map(str,indices)),new
        return
    for i, j in combinations([i for i, word in enumerate(seed) if word], 2):
        for operation, word in [('and', seed[i] & seed[j]), ('or', seed[i] | seed[j])]:
            if not (word & TARGET):
                continue
            new = seed.copy()
            new[free] = word
            yield f'{operation}-{i}-{j}', new


def restrict_columns(seed, free):
    # On negative tests where h is one, a KW leaf labeled h cannot work.
    # Discard the columns on which h is zero, and then omit the useless h.
    ordinary=seed.copy()
    keep=TARGET | seed[free]
    ordinary[free]=0
    return [word & keep for word in ordinary]


def incidence(seed):
    """Define the binary rectangle model independently of the SciPy builder."""
    tests = [tuple(i for i,w in enumerate(seed) if (w>>bit)&1) for bit in range(32)]
    rows = tests[:14]
    columns = sorted(set(tests[14:]) - {()})
    cells = len(rows) * len(columns)
    candidates = []
    for i in range(len(seed)):
        hits = [r for r, test in enumerate(rows) if i in test]
        for mask in range(1, 1 << len(hits)):
            candidates.append((i, [r for j,r in enumerate(hits) if (mask>>j)&1]))
    uses = [(y, [r*len(columns)+j for r in selected])
            for y, (label, selected) in enumerate(candidates)
            for j, c in enumerate(columns) if label not in c]
    return len(candidates), uses, cells


def packed(values):
    return b64encode(zlib.compress(json.dumps(values, separators=(',', ':')).encode(), 6)).decode()


def unpack(text):
    return json.loads(zlib.decompress(b64decode(text)))


def generate(seed, deadline, limit):
    import numpy as np
    from scipy.optimize._highspy._core import _Highs
    from scipy.sparse import eye, hstack
    from kw_integral_partition import model

    matrix, lhs, rhs, ny, neq = model(seed)
    nv = matrix.shape[1]
    matrix = hstack((matrix, eye(matrix.shape[0], neq)), format='csr', dtype=np.int64)
    cost = np.r_[np.ones(ny), np.zeros(nv-ny), np.full(neq, 32)].astype(np.int64)
    low = np.zeros(len(cost), dtype=np.int64)
    high = np.ones(len(cost), dtype=np.int64)
    lp = _Highs()
    lp.setOptionValue('output_flag', False)
    lp.setOptionValue('threads', 1)
    lp.setOptionValue('presolve', 'off')
    lp.addCols(len(cost), cost, low, high, 0, [], [], [])
    lp.addRows(len(lhs), lhs, rhs, matrix.nnz, matrix.indptr, matrix.indices, matrix.data.astype(float))

    class Witness(Exception):
        pass

    def visit():
        if monotonic() > deadline:
            raise TimeoutError
        lp.run()
        solution = lp.getSolution()
        if lp.getObjectiveValue() > limit + 1e-6:
            dual = np.rint(np.array(solution.row_dual)*SCALE).astype(np.int64)
            dual[neq:] = np.minimum(dual[neq:], 0)
            reduced = cost*SCALE - matrix.T @ dual
            value = sum(dual[:neq]) + np.maximum(reduced,0) @ low + np.minimum(reduced,0) @ high
            if value > limit*SCALE:
                return packed(dual.tolist())
        actual = np.array(solution.col_value[:nv])
        fraction = np.minimum(actual, 1-actual)
        fraction[low[:nv]==high[:nv]] = 0
        fraction[ny:] *= .1
        j = int(np.argmax(fraction))
        if fraction[j] < 1e-8:
            if lp.getObjectiveValue() <= limit + 1e-6:
                raise Witness(np.flatnonzero(actual > .5).tolist())
            raise RuntimeError('Ambiguous leaf bound')
        branches = []
        for bit in (0,1):
            low[j] = high[j] = bit
            lp.changeColBounds(j, bit, bit)
            branches.append(visit())
        low[j], high[j] = 0, 1
        lp.changeColBounds(j, 0, 1)
        return [j, *branches]

    try:
        return {'tree': visit()}
    except Witness as witness:
        return {'partition':witness.args[0]}
    except TimeoutError:
        return {'timeout':True}


def replay(seed, outcome, limit):
    ny, uses, neq = incidence(seed)
    nz = len(uses)
    if 'partition' in outcome:
        ones = set(outcome['partition'])
        assert all(type(j) is int and 0<=j<ny+nz for j in ones)
        assert sum(j<ny for j in ones)<=limit
        counts = [0]*neq
        for z, (y, cells) in enumerate(uses,ny):
            if z in ones:
                assert y in ones
                for cell in cells:
                    counts[cell] += 1
        assert all(k==1 for k in counts)
        return 'partition', sum(j<ny for j in ones)
    if 'timeout' in outcome:
        return 'timeout', 0
    low, high = [0]*(ny+nz+neq), [1]*(ny+nz+neq)
    def visit(tree):
        if isinstance(tree, list):
            j, *children = tree
            assert len(children)==2 and type(j) is int and 0<=j<ny+nz and (low[j],high[j])==(0,1)
            leaves = 0
            for b, child in enumerate(children):
                low[j] = high[j] = b
                leaves += visit(child)
            low[j], high[j] = 0, 1
            return leaves
        dual = unpack(tree)
        assert isinstance(dual,list) and len(dual)==neq+nz and all(type(x) is int for x in dual)
        assert all(x<=0 for x in dual[neq:])
        reduced = [SCALE]*ny + [0]*nz + [32*SCALE-dual[i] for i in range(neq)]
        for k,(y,cells) in enumerate(uses):
            q = dual[neq+k]
            reduced[y] += q
            reduced[ny+k] -= q + sum(dual[i] for i in cells)
        assert sum(dual[:neq])+sum(min(r*a,r*b) for r,a,b in zip(reduced,low,high)) > limit*SCALE
        return 1
    return 'excluded', visit(outcome['tree'])


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('row',type=int,choices=range(4))
    parser.add_argument('--seconds-per-case',type=float,default=120.)
    parser.add_argument('--replay',action='store_true')
    parser.add_argument('--or-size',type=int,choices=range(3,11),default=0)
    args=parser.parse_args()
    seed=json.loads((HERE/'seed_tables.json').read_text())[args.row]
    suffix=f'_or{args.or_size}' if args.or_size else ''
    path=HERE/f'kw_first_shared_{args.row}{suffix}.json.gz'
    limit=20-args.or_size if args.or_size else LIMIT
    evidence = json.loads(gzip.decompress(path.read_bytes())) if path.exists() else {}
    summary=Counter()
    for label,augmented in augment(seed,args.or_size):
        restricted=restrict_columns(augmented,seed.index(0)) if args.or_size else None
        if not args.replay and (label not in evidence or 'timeout' in evidence[label]):
            if restricted is not None:
                result=generate(restricted, monotonic()+min(5,args.seconds_per_case),limit)
            else:
                result={}
            if 'tree' in result:
                result['restricted']=True
            else:
                result=generate(augmented,monotonic()+args.seconds_per_case,limit)
            evidence[label]=result
            path.write_bytes(gzip.compress(json.dumps(evidence,separators=(',',':')).encode(),mtime=0))
        status,count=replay(restricted if evidence[label].get('restricted') else augmented,
                            evidence[label],limit)
        summary[status]+=1
        print(args.row,label,status,count,flush=True)
    print('TOTAL',args.row,dict(summary),flush=True)


if __name__ == '__main__':
    main()
