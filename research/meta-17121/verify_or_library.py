"""Replay every dependent pure-OR library with three to five shared gates."""
from collections import Counter
from functools import reduce
from itertools import combinations
from math import comb, prod
import gzip
import json
import operator
from pathlib import Path
import re
import subprocess
import tempfile

from verify_kw_first_shared import check_tree
from verify_many_or_trees import compiler, graph_check

HERE = Path(__file__).resolve().parent
TARGET = (1 << 14) - 1
SHAPE = re.compile(r'r=(\d+) families=(\d+) common=(\d+) incomparable=(\d+) '
                   r'dependent=(\d+) eliminated=(\d+) remaining=(\d+)')


def union(values):
    return reduce(operator.or_,values,0)


def formal_counts(r):
    """Count structures once on each abstract raw alphabet, independently of C#."""
    counts = Counter()
    for k in range(2,10-r):
        all_vars = (1 << k)-1
        weight = comb(10,k)
        available = [s for s in range(1,all_vars+1) if s.bit_count() >= 2]
        for family in combinations(available,r):
            if union(family) != all_vars:
                continue
            counts['all'] += weight
            if reduce(operator.and_,family).bit_count() >= 2:
                counts['common'] += weight
                continue
            # For each node, count the admissible choices of its direct
            # parents. Proper subset relations alone enforce acyclicity.
            options = []
            for child in family:
                earlier = [s for s in family if s != child and s & ~child == 0]
                n = 1
                for size in range(1,len(earlier)+1):
                    for parents in combinations(earlier,size):
                        raw = child & ~union(parents)
                        if size + raw.bit_count() < 2:
                            continue
                        if all(u & ~union(v for v in parents if u != v) for u in parents):
                            n += 1
                options.append(n)
            structures = prod(options)-1
            if structures:
                counts['dependent'] += weight*structures
            else:
                counts['incomparable'] += weight
    return tuple(counts[k] for k in ('all','common','incomparable','dependent'))


def verify_residual(seed, descriptor, proof):
    inputs = [w for w in seed if w]
    a,b = descriptor.split(';')
    support = tuple(map(int,a.split(',')))
    parents = tuple(map(int,b.split(',')))
    r = len(support)
    assert len(parents) == r and len(set(support)) == r
    assert all(0 < s < 1024 and s.bit_count() >= 2 for s in support)
    inside = 0
    uses = [0]*r
    for i,tag in enumerate(parents):
        assert 0 <= tag < (1 << i)
        direct = [j for j in range(i) if tag & (1 << j)]
        inherited = union(support[j] for j in direct)
        assert inherited & ~support[i] == 0
        raw = support[i] ^ inherited
        n = len(direct)+raw.bit_count()
        assert n >= 2
        inside += n-1
        for j in direct:
            assert support[j] & ~union(support[l] for l in direct if l != j)
            uses[j] += 1
    outside_occ = [max(0,2-n) for n in uses]
    order,fixed,tree = proof
    assert sorted(order) == list(range(r))
    assert len(fixed) == len(set(fixed)) and all(type(i) is int and 0 <= i < r for i in fixed)
    hs = [union(w for j,w in enumerate(inputs) if support[i] & (1 << j)) for i in order]
    keep = reduce(operator.and_,(TARGET|hs[i] for i in fixed),(1<<32)-1)
    table = [w & keep for w in inputs+[h for i,h in enumerate(hs) if i not in fixed]]
    threshold = 19-inside-sum(outside_occ[order[i]] for i in fixed)
    return check_tree(table,tree,threshold)


def run():
    seeds = json.loads((HERE/'seed_tables.json').read_text())
    proofs = json.loads(gzip.decompress((HERE/'or_library.json.gz').read_bytes()))
    assert len(seeds) == 4
    counts = {r:formal_counts(r) for r in (3,4,5)}
    used = set()
    configs = leaves = 0
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)
        tool = compiler(tmp,'AllOrLibrary')
        for row,seed in enumerate(seeds):
            graph_check([w for w in seed if w])
            for r in (3,4,5):
                targets = tmp/f'cases-{row}-{r}.txt'
                result = subprocess.check_output([*tool,','.join(map(str,seed)),str(r),targets],text=True)
                match = SHAPE.fullmatch(result.strip())
                assert match, result
                k,families,common,incomparable,dependent,eliminated,uncertain = map(int,match.groups())
                assert k == r and (families,common,incomparable,dependent) == counts[r]
                assert dependent == eliminated + uncertain
                records = targets.read_text().splitlines()
                assert len(records) == len(set(records)) == uncertain
                for desc in records:
                    key = f'{row}:{desc}'
                    leaves += verify_residual(seed,desc,proofs[key])
                    used.add(key)
                configs += dependent
                print(f'row {row}, {r} helpers: {dependent} dependent configurations, '
                      f'{uncertain} integer-dual certificates',flush=True)
    assert set(proofs) == used
    print(f'{configs} configurations, {len(used)} certificates, {leaves} integer-dual leaves.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Enable assertions for certificate verification.')
    run()
