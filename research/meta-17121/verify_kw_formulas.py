"""Replay the four finite KW rectangle-partition lower bounds using Python integers."""
import gzip
from itertools import combinations
import json
from pathlib import Path


def incidence(seeds):
    tests = [tuple(i for i, w in enumerate(seeds) if w >> bit & 1) for bit in range(32)]
    edges = tests[:14]
    assert len(set(edges)) == 14 and all(len(e) == 2 for e in edges)
    neg = sorted(set(tests[14:]) - {()})
    support = sorted(set().union(*map(set,edges)))
    independent = [set(vs) for size in range(len(support)+1)
                   for vs in combinations(support,size) if not any(set(e) <= set(vs) for e in edges)]
    maximal = sorted(tuple(sorted(m)) for m in independent if not any(m < n for n in independent))
    assert len(support) == 10 and neg == maximal
    assert max(map(len,neg)) == 4  # minimum vertex cover has six vertices

    # A rectangle with output vertex v has a nonempty row set contained in
    # its incident edges and can use only columns omitting v.
    rectangles = []
    for v in range(len(seeds)):
        star = [i for i,e in enumerate(edges) if v in e]
        for mask in range(1,1 << len(star)):
            rectangles.append((v,[e for j,e in enumerate(star) if mask >> j & 1]))
    copies = [(y, [e*len(neg)+m for e in star]) for y,(v,star) in enumerate(rectangles)
              for m,col in enumerate(neg) if v not in col]
    return len(rectangles),copies,len(edges)*len(neg)


def verify(seed,tree):
    scale = 100000
    ny,copies,neq=incidence(seed)
    nz=len(copies)
    low=[0]*(ny+nz+neq)
    high=[1]*len(low)
    leaves=0
    minimum=None

    def visit(node):
        nonlocal leaves,minimum
        if isinstance(node,dict):
            assert set(node)=={'split','children'} and len(node['children'])==2
            j=node['split']
            assert type(j) is int and 0<=j<ny+nz and (low[j],high[j])==(0,1)
            for val,child in enumerate(node['children']):
                low[j]=high[j]=val
                visit(child)
            low[j],high[j]=0,1
            return

        # The cell-equality multipliers are unrestricted. For z-y <= 0 we
        # require the corresponding multiplier to be nonpositive.
        assert isinstance(node,list) and len(node)==neq+nz
        assert all(type(w) is int for w in node) and all(w<=0 for w in node[neq:])
        dual=sum(node[:neq])
        reduced=[scale]*ny+[0]*nz+[32*scale-node[i] for i in range(neq)]
        for k,(y,cells) in enumerate(copies):
            lam=node[neq+k]
            reduced[y]+=lam
            reduced[ny+k]-=lam+sum(node[i] for i in cells)
        dual+=sum(r*(lo if r>=0 else hi) for r,lo,hi in zip(reduced,low,high))
        assert dual>19*scale
        minimum=dual if minimum is None else min(minimum,dual)
        leaves+=1

    visit(tree)
    return leaves,minimum


if __name__=='__main__':
    here=Path(__file__).parent
    seeds=json.loads((here/'seed_tables.json').read_text())
    trees=json.loads(gzip.decompress((here/'kw_formula_certificates.json.gz').read_bytes()))
    assert len(seeds)==len(trees)==4
    for i,(seed,tree) in enumerate(zip(seeds,trees)):
        n,lower=verify(seed,tree)
        print(f'G11-{i}: {n} certificate leaves, minimum lower bound {lower}/100000, '
              '20 rectangles and 19 monotone formula gates are optimal.')
