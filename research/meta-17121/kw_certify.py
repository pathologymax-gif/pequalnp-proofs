"""Exact-integer dual verification of a branch and bound for 19 rectangles."""
from collections import Counter
from pathlib import Path
import gzip
import json
import sys
import time
import numpy as np
from scipy.optimize._highspy._core import _Highs
from scipy.sparse import eye, hstack
from kw_integral_partition import model

def solve(seed,limit):
    a, l, u, ny, neq = model(seed)
    nv = a.shape[1]
    # Paying for missing cells makes every LP feasible, even at impossible leaves.
    a = hstack([a, eye(a.shape[0], neq, format='csr')],format='csr',dtype=np.int64)
    c = np.r_[np.ones(ny), np.zeros(nv-ny), np.full(neq,32)].astype(np.int64)
    lo = np.zeros(len(c),dtype=np.int64)
    hi = np.ones(len(c),dtype=np.int64)
    lp = _Highs()
    lp.setOptionValue('output_flag',False)
    lp.setOptionValue('threads',1)
    lp.setOptionValue('presolve','off')
    lp.addCols(len(c),c,lo,hi,0,[],[],[])
    lp.addRows(len(l),l,u,a.nnz,a.indptr,a.indices,a.data.astype(float))
    t = time.monotonic()
    stats = Counter()
    def visit():
        stats['nodes']+=1
        if stats['nodes']%1000==0: print('nodes',stats,'sec',round(time.monotonic()-t,1),flush=True)
        if time.monotonic()-t>limit: raise TimeoutError
        lp.run()
        sol = lp.getSolution()
        if lp.getObjectiveValue()>19.000001:
            scale=100000
            d=np.rint(np.asarray(sol.row_dual)*scale).astype(np.int64)
            d[neq:]=np.minimum(d[neq:],0)
            reduced=c*scale-a.T @ d
            val=d[:neq].sum() + np.maximum(reduced,0) @ lo + np.minimum(reduced,0) @ hi
            if val>scale*19:
                stats['certified']+=1
                return [int(x) for x in d]
        v=np.array(sol.col_value[:nv])
        frac = np.minimum(v,1-v)
        frac[lo[:nv]==hi[:nv]]=0
        frac[ny:]*=0.1
        j=int(np.argmax(frac))
        if frac[j] < 1e-8: raise ValueError(('Unexpected integral witness or ambiguous bound',lp.getObjectiveValue(),v))
        children=[]
        for bit in [0,1]:
            lo[j],hi[j]=bit,bit
            lp.changeColBounds(j,bit,bit)
            children.append(visit())
        lo[j],hi[j]=0,1
        lp.changeColBounds(j,0,1)
        return {'split':j,'children':children}
    tree=visit()
    return stats,time.monotonic()-t,tree

if __name__=='__main__':
    seeds=json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    if len(sys.argv)>1:
        stats,elapsed,_=solve(seeds[int(sys.argv[1])],int(sys.argv[2]))
        print(stats,elapsed,flush=True)
    else:
        trees=[]
        for i,seed in enumerate(seeds):
            stats,elapsed,tree=solve(seed,120)
            print(i,stats,elapsed,flush=True)
            trees.append(tree)
        out=Path(__file__).with_name('kw_formula_certificates.json.gz')
        out.write_bytes(gzip.compress(json.dumps(trees,separators=(',',':')).encode(),mtime=0))
