"""Minimum KW rectangle partition, contracting rectangles with equal rows and label."""
import json
from pathlib import Path
import sys
import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

def model(seed):
    assignments = [tuple(i for i,w in enumerate(seed) if w >> b & 1) for b in range(32)]
    edges = assignments[:14]
    neg = sorted(set(assignments[14:]) - {()})
    N=len(neg)
    yidx, zidx, rows, cols, vals = {}, {}, [], [], []
    def row(r, terms):
        for i,v in terms: rows.append(r); cols.append(i); vals.append(v)
    for v in range(11):
        inc=[i for i,e in enumerate(edges) if v in e]
        for mask in range(1,1 << len(inc)):
            star=tuple(i for ii,i in enumerate(inc) if mask>>ii&1)
            yidx[v, star]=len(yidx)
    for v,star in yidx:
        for m,M in enumerate(neg):
            if v not in M:
                z=len(yidx)+len(zidx)
                zidx[v,star,m]=z
                for e in star:
                    row(e*N+m, [(z,1)])
                row(14*N+len(zidx)-1, [(z,1),(yidx[v,star],-1)])
    n=len(yidx)+len(zidx)
    A=coo_matrix((vals,(rows,cols)),shape=(14*N+len(zidx),n)).tocsr()
    L=np.r_[np.ones(14*N),np.full(len(zidx),-np.inf)]
    U=np.r_[np.ones(14*N),np.zeros(len(zidx))]
    return A,L,U,len(yidx),14*N

def solve(seed):
    A,L,U,ny,neq=model(seed)
    n=A.shape[1]
    sol=milp(np.r_[np.ones(ny),np.zeros(n-ny)],integrality=np.ones(n),
             bounds=Bounds(0,1),constraints=LinearConstraint(A,L,U),
             options={'time_limit':180,'mip_rel_gap':0.0,'disp':False})
    return sol.message,sol.fun,sol.mip_dual_bound

if __name__=='__main__':
    seeds=json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    for i in map(int,sys.argv[1:] or range(4)): print(i,solve(seeds[i]),flush=True)
