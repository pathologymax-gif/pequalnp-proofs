"""Independent vectorized audit of every two-incomparable-helper case."""
from collections import Counter
from itertools import combinations
import json
from pathlib import Path
import subprocess
import tempfile
import numpy as np
from verify_independent_mixed import compile_source, graph_check

HERE = Path(__file__).resolve().parent
T = np.uint32(16383)
N = np.uint32(~T)


def run(row,seed,folder,frontier,audit):
    graph_check(seed)
    folder.mkdir()
    seed_words=','.join(map(str,seed))
    subprocess.run([*frontier,seed_words,folder],check=True)
    subprocess.run([*audit,seed_words,folder,str(row)],check=True)
    raw = [w for w in seed if w]
    ends = [tuple(i for i,w in enumerate(raw) if w >> j & 1) for j in range(14)]
    size = np.array([m.bit_count() for m in range(16384)],dtype=np.uint8)
    # Superset minimum transform of vertex-cover sizes on all edge sets;
    # independent of the endpoint deletion recurrence in the C# checker.
    cover = np.full(16384,11,dtype=np.uint8)
    for vertices in range(1024):
        hit = 0
        for j,w in enumerate(raw):
            if vertices & (1<<j):
                hit |= w & int(T)
        cover[hit] = min(cover[hit],vertices.bit_count())
    for e in range(14):
        block = cover.reshape((-1,2,1<<e))
        np.minimum(block[:,0,:],block[:,1,:],out=block[:,0,:])
    correction = size+cover
    ors = {}
    for d in range(10):
        ors[d] = np.array([np.bitwise_or.reduce(np.array(x,dtype=np.uint32))
                           for x in combinations(raw,d+1)],dtype=np.uint32)
    residual = {}
    for g in range(1,11):
        vector = np.loadtxt(folder/f'{g}.txt',dtype=np.uint32,ndmin=1)
        pos = vector & T
        mask = ((pos != 0) & (pos != T) & ((vector & N) != 0) & (correction[pos] > g+2))
        for d in range(min(9,g)+1):
            for w in ors[d]:
                mask &= ((w & N & ~vector)!=0) | (correction[pos & ~w] > g-d)
        residual[g] = vector[mask]

    def hull(neg, hs):
        shape = neg.shape
        r = np.zeros((10,*shape),dtype=np.uint16)
        c = np.zeros((10,*shape),dtype=np.uint32)
        for e,(a,b) in enumerate(ends):
            avail=neg.copy()
            for h in hs:
                avail &= np.where(h & np.uint32(1<<e),h,N)
            for v,w in ((a,b),(b,a)):
                col=avail & np.uint32(raw[w])
                c[v] |= col
                r[v] |= (col!=0).astype(np.uint16)<<e
        conflict = np.zeros(shape,dtype=np.uint16)
        for e,(a,b) in enumerate(ends):
            meet=((r[a]&r[b])!=0) & ((c[a]&c[b])!=0)
            conflict |= meet.astype(np.uint16)<<e
        return np.count_nonzero(r,axis=0)+cover[conflict]

    keys = np.arange(1<<18,dtype=np.uint32)<<14
    cofactor = hull(keys,())
    total = Counter()
    def pairs(left,right,g,d,triangle=False):
        cap=15-g-d
        if not len(left) or not len(right):return
        right_ix=np.arange(len(right))
        batch=max(1,200000//len(right))
        for idx in range(0,len(left),batch):
            lhs=left[idx:idx+batch]
            actual=np.arange(idx,idx+len(lhs))[:,None] > right_ix[None,:] if triangle else None
            n=int(actual.sum()) if triangle else len(lhs)*len(right)
            total['total']+=n
            a,b=(lhs^T)[:,None],(right^T)[None,:]
            incomparable=((a & ~b)!=0)&((b & ~a)!=0)
            if triangle:incomparable &= actual
            count=int(np.count_nonzero(incomparable))
            total['comparable']+=n-count
            untested=incomparable & (cofactor[(lhs[:,None]&right[None,:])>>14]<=cap)
            l,r=np.nonzero(untested)
            total['cofactor']+=count-len(l)
            if len(l):
                lb=hull(np.full(len(l),N,dtype=np.uint32),(lhs[l],right[r]))
                assert np.all(lb>cap), (row,g,d,lhs[l][lb<=cap],right[r][lb<=cap])
            total['full']+=len(l)
    for g in range(1,11):
        for d in range(1,min(9,13-g)+1):
            pairs(residual[g],ors[d],g,d)
        for d in range(1,min(g,13-g)+1):
            pairs(residual[g],residual[d],g,d,triangle=g==d)
    print(row, [len(residual[g]) for g in range(1,11)],dict(total),flush=True)
    return total['total']


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Enable assertions for the independent arithmetic replay.')
    seeds=json.loads((HERE/'seed_tables.json').read_text())
    with tempfile.TemporaryDirectory() as temp:
        root=Path(temp)
        frontier=compile_source(root,'SharedGateFrontier')
        audit=compile_source(root,'AuditSharedFrontier')
        assert sum(run(row,seed,root/f'row{row}',frontier,audit) for row,seed in enumerate(seeds))==291703443
