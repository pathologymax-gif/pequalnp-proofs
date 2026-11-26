"""Rule out three or four distinct shared raw ORs. For five or more see ManyRawHelpers.md."""
import argparse
import base64
from collections import Counter
from functools import cache
import gzip
from itertools import combinations
import json
from pathlib import Path
import zlib

from verify_kw_first_shared import check_tree,model

HERE=Path(__file__).resolve().parent
TARGET=(1<<14)-1
SCALE=100000


class Projection:
    def __init__(self,seed):
        self.raw=[w for w in seed if w]
        assert len(self.raw)==10
        self.edges=[tuple(v for v,w in enumerate(self.raw) if (w>>e)&1) for e in range(14)]
        assert len(set(self.edges))==14 and all(len(e)==2 for e in self.edges)
        neighbors=[set() for _ in self.raw]
        for a,b in self.edges:
            neighbors[a].add(b)
            neighbors[b].add(a)
        assert min(map(len,neighbors))>=2
        assert all(len(neighbors[a]&neighbors[b])<=1 for a,b in combinations(range(10),2))
        self.pairs=[a|b for a,b in combinations(self.raw,2)]
        tests=[tuple(v for v,w in enumerate(self.raw) if (w>>j)&1) for j in range(14,32)]
        positions={test:i+14 for i,test in enumerate(tests) if test}
        self.negative_positions=[positions[test] for test in sorted(positions)]
        actual_mis=set()
        for mask in range(1<<10):
            verts={i for i in range(10) if mask & (1<<i)}
            if any(a in verts and b in verts for a,b in self.edges):
                continue
            if all(v in verts or neighbors[v]&verts for v in range(10)):
                actual_mis.add(tuple(sorted(verts)))
        assert set(positions)==actual_mis
        self.ny,self.uses,self.neq=model(self.raw)

    @cache
    def cover(self,mask):
        if not mask:
            return 0
        edge=(mask & -mask).bit_length()-1
        return 1+min(self.cover(mask & ~self.raw[v]) for v in self.edges[edge])

    def forced_bound(self,helpers):
        rows=[0]*10
        columns=[0]*10
        for e,(a,b) in enumerate(self.edges):
            unavailable=0xffffffff ^ TARGET
            for h in helpers:
                if (h>>e)&1:
                    unavailable &= h
            for vertex,other in ((a,b),(b,a)):
                mandatory=unavailable & self.raw[other]
                if mandatory:
                    rows[vertex] |= 1<<e
                    columns[vertex] |= mandatory
        conflict=sum(1<<e for e,(a,b) in enumerate(self.edges)
                     if rows[a]&rows[b] and columns[a]&columns[b])
        return 2*len(helpers)+sum(bool(r) for r in rows)+self.cover(conflict)

    def penalties(self,helpers):
        # A slack covers a cell left uncovered by all ordinary rectangles.
        # At a cell without an eligible helper its coefficient is 32.
        return [0 if any((h>>e)&1 and not (h>>m)&1 for h in helpers) else 32
                for e in range(14) for m in self.negative_positions]

    def replay(self,helpers,tree,limit):
        penalties=self.penalties(helpers)
        fixed={}
        ny,uses,neq=self.ny,self.uses,self.neq
        nz=len(uses)
        def visit(node):
            if isinstance(node,list):
                assert len(node)==3
                index,left,right=node
                assert type(index) is int and 0<=index<ny+nz and index not in fixed
                fixed[index]=0
                n=visit(left)
                fixed[index]=1
                n+=visit(right)
                del fixed[index]
                return n
            assert isinstance(node,str)
            weights=json.loads(zlib.decompress(base64.b64decode(node,validate=True)))
            assert len(weights)==neq+nz and all(type(w) is int for w in weights)
            p,q=weights[:neq],weights[neq:]
            assert all(x<=0 for x in q)
            reduced=[SCALE]*ny+[0]*nz+[cost*SCALE-weight for cost,weight in zip(penalties,p)]
            for k,(y,cells) in enumerate(uses):
                reduced[y]+=q[k]
                reduced[ny+k]-=q[k]+sum(p[j] for j in cells)
            bound=sum(p)+sum(c*fixed[j] if j in fixed else min(0,c) for j,c in enumerate(reduced))
            assert bound>limit*SCALE
            return 1
        return visit(tree)

    def generate(self,helpers,limit):
        import numpy as np
        from scipy.optimize import linprog
        from scipy.sparse import eye,hstack
        from kw_integral_partition import model as sparse_model
        a,_,b,ny,neq=sparse_model(self.raw)
        nv=a.shape[1]
        matrix=hstack((a,eye(a.shape[0],neq)),format='csr',dtype=np.int64)
        c=np.r_[np.ones(ny),np.zeros(nv-ny),self.penalties(helpers)].astype(np.int64)
        bounds=np.zeros((len(c),2),dtype=np.int64)
        bounds[:,1]=1
        def visit():
            sol=linprog(c,A_eq=matrix[:neq],b_eq=b[:neq],A_ub=matrix[neq:],b_ub=b[neq:],
                        bounds=bounds,method='highs-ds')
            assert sol.success
            if sol.fun>limit+1e-6:
                real=np.r_[sol.eqlin.marginals,sol.ineqlin.marginals]
                dual=np.rint(real*SCALE).astype(np.int64)
                dual[neq:]=np.minimum(dual[neq:],0)
                red=c*SCALE-matrix.T@dual
                bound=sum(dual[:neq])+np.minimum(red*bounds[:,0],red*bounds[:,1]).sum()
                if bound>limit*SCALE:
                    raw=json.dumps(dual.tolist(),separators=(',',':')).encode()
                    return base64.b64encode(zlib.compress(raw)).decode()
            x=sol.x[:nv]
            frac=np.minimum(x,1-x)
            frac[bounds[:nv,0]==bounds[:nv,1]]=0
            frac[ny:]*=.1
            j=int(np.argmax(frac))
            if frac[j]<1e-8:
                raise ValueError(f'Integral relaxed partition of cost {sol.fun:.4f}')
            children=[]
            for bit in (0,1):
                bounds[j]=(bit,bit)
                children.append(visit())
            bounds[j]=(0,1)
            return [j,*children]
        return visit()

    def cofactor(self,helpers,fixed):
        # Fix the listed helpers to one and retain every positive row.
        keep=0xffffffff
        for i in fixed:
            keep &= helpers[i] | TARGET
        live=self.raw+[w for i,w in enumerate(helpers) if i not in fixed]
        return [w&keep for w in live]

    def certify_family(self,helpers):
        try:
            return {'ordinary':self.generate(helpers,19-3*len(helpers))}
        except ValueError:
            from kw_first_shared import generate
            from scipy.optimize._highspy._core import _Highs
            from time import monotonic
            # linprog selects its default parallelism, whereas the augmented
            # generator requests one thread. Release the old HiGHS scheduler.
            _Highs.resetGlobalScheduler(True)
            for count in reversed(range(len(helpers)+1)):
                for fixed in combinations(range(len(helpers)),count):
                    words=self.cofactor(helpers,fixed)
                    if not any(w & ~TARGET for w in words):
                        continue
                    threshold=19-len(helpers)-2*count
                    result=generate(words,monotonic()+20,threshold)
                    if set(result)=={'tree'}:
                        return {'fixed':list(fixed),'tree':result['tree']}
            raise ValueError('No certificate for this family')

    def verify_family(self,helpers,proof):
        if set(proof)=={'ordinary'}:
            return self.replay(helpers,proof['ordinary'],19-3*len(helpers))
        assert set(proof)=={'fixed','tree'}
        fixed=proof['fixed']
        assert isinstance(fixed,list) and all(type(i) is int and 0<=i<len(helpers) for i in fixed)
        assert len(fixed)==len(set(fixed))
        words=self.cofactor(helpers,fixed)
        assert any(w & ~TARGET for w in words)
        return check_tree(words,proof['tree'],19-len(helpers)-2*len(fixed))


def main():
    if not __debug__:
        raise RuntimeError('Run Python with assertions enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate',action='store_true')
    args=parser.parse_args()
    rows=json.loads((HERE/'seed_tables.json').read_text())
    path=HERE/'many_raw_helpers.json.gz'
    cases=[{} for _ in rows] if args.generate else json.loads(gzip.decompress(path.read_bytes()))
    assert len(rows)==len(cases)==4
    for row,seed in enumerate(rows):
        projection=Projection(seed)
        keys=set()
        statistics=Counter()
        for r in (3,4):
            for indices in combinations(range(45),r):
                statistics[r]+=1
                hs=[projection.pairs[i] for i in indices]
                if projection.forced_bound(hs)>19-r:
                    continue
                key='_'.join(map(str,indices))
                keys.add(key)
                if args.generate:
                    cases[row][key]=projection.certify_family(hs)
                proof=cases[row][key]
                statistics['ordinary' if 'ordinary' in proof else 'cofactor']+=1
                statistics['leaves']+=projection.verify_family(hs,proof)
        assert keys==set(cases[row])
        print(row,dict(statistics),'certificate families',len(keys),flush=True)
    if args.generate:
        path.write_bytes(gzip.compress(json.dumps(cases,separators=(',',':')).encode(),mtime=0))


if __name__=='__main__':
    main()
