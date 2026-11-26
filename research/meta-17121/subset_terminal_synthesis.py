"""Choose all pure lower terminal products as an unordered set of operand pairs."""

import argparse
from itertools import combinations
import json
from pathlib import Path
from time import monotonic

from exact_synthesis import Formula, bits, neg, samples_for
from refined_synthesis import at_least, conjunction, disjunction
from symmetric_synthesis import choose, possible_repeats


def build(row,size,terms,reader_patterns,private=False):
    dirty = size-2*terms+1
    if terms<2 or dirty<0:
        raise ValueError('Invalid lower-terminal shape')
    ids = [i for i,w in enumerate(row) if w]
    samples = samples_for(row,16383,32)
    labels = bits(16383,samples)
    ps = [j for j,x in enumerate(labels) if x]
    qs = [j for j,x in enumerate(labels) if not x]
    pool = [bits(row[i],samples) for i in ids]
    original = pool.copy()
    f = Formula()
    reads = [[] for _ in range(len(ids)+dirty)]
    gates = []
    for g in range(dirty):
        l,x = choose(f,pool,len(samples))
        r,y = choose(f,pool,len(samples))
        op = f.var()
        selected = [disjunction(f,[u,v]) for u,v in zip(l,r)]
        for i,s in enumerate(selected):
            reads[i].append(s)
            for v in r[:i+1]:
                f.clause(-l[i],-v)
            if i>=len(ids):
                for k,child in enumerate(gates[i-len(ids)][3]):
                    f.clause(neg(s),neg(selected[k]),neg(child))
        if g:
            pl,pr,_,_,_ = gates[-1]
            tie = disjunction(f,[conjunction(f,[a,b]) for a,b in zip(pr,r)])
            for i,v in enumerate(pr):
                for b in r[:i]:
                    f.clause(-v,-b)
            for i,v in enumerate(pl):
                for b in l[:i]:
                    f.clause(neg(tie),-v,-b)
        z = [f.var() for _ in samples]
        for a,b,w in zip(x,y,z):
            f.clause(-a,-b,w); f.clause(a,b,-w)
            f.clause(-op,-w,a); f.clause(-op,-w,b)
            f.clause(op,w,-a); f.clause(op,w,-b)
        for side in (ps,qs):
            f.clause(*[z[j] for j in side])
            f.clause(*[-z[j] for j in side])
        for v in pool:
            f.clause(*[conjunction(f,[z[p],neg(v[p])]) for p in ps],
                     *[conjunction(f,[-z[q],v[q]]) for q in qs])
        gates.append((l,r,op,selected,z))
        pool.append(z)

    products = []
    cover = {p:[] for p in ps}
    for i,j in combinations(range(len(pool)),2):
        a,b = pool[i],pool[j]
        active = f.var()
        products.append((i,j,active))
        reads[i].append(active)
        reads[j].append(active)
        for q in qs:
            f.clause(-active,neg(a[q]),neg(b[q]))
        for p in ps:
            cover[p].append(conjunction(f,[active,a[p],b[p]]))
        if j>=len(ids):
            f.clause(-active,neg(gates[j-len(ids)][3][i]))
    for ws in cover.values():
        f.clause(*ws)
    if private:
        unique = {p:neg(at_least(f,ws,2)) for p,ws in cover.items()}
        for i,(_,_,chosen) in enumerate(products):
            f.clause(-chosen, *[conjunction(f,[unique[p], ws[i]]) for p,ws in cover.items()])
    selectors = [v for _,_,v in products]
    f.clause(at_least(f,selectors,terms))
    f.clause(neg(at_least(f,selectors,terms+1)))
    copies = []
    for rr in reads:
        f.clause(*rr)
        copies.append(at_least(f,rr,2))
    for i,raw in enumerate(original):
        multiple = copies[i]
        for _,_,op,selected,z in gates:
            for p in ps:
                if raw[p]: f.clause(neg(selected[i]),multiple,-op,z[p])
            for q in qs:
                if not raw[q] and any(w[q] for w in original):
                    f.clause(neg(selected[i]),multiple,op,-z[q])
        for a,b,v in products:
            if i not in (a,b):
                continue
            h = pool[b if a==i else a]
            for p in ps:
                if raw[p]: f.clause(-v,multiple,h[p])
    if size<=18:
        f.clause(at_least(f,copies[len(ids):],2))
        f.clause(*(g[2] for g in gates))
        if reader_patterns:
            choices=[]
            for repeat in possible_repeats(tuple(row),size):
                flag=f.var()
                choices.append(flag)
                for i,v in enumerate(ids):
                    f.clause(-flag,copies[i] if v in repeat else neg(copies[i]))
            f.clause(*choices)
    f.clause(at_least(f,[g[2] for g in gates]+[True]*terms,6))
    f.clause(at_least(f,[-g[2] for g in gates]+[True]*(terms-1),7))
    return f,(ids,gates,products)


def main():
    from pysat.solvers import Solver
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('case',type=int,choices=range(4))
    p.add_argument('size',type=int)
    p.add_argument('terms',type=int)
    p.add_argument('--conflicts',type=int,default=300000)
    p.add_argument('--reader-patterns',action='store_true')
    p.add_argument('--private',action='store_true')
    p.add_argument('--solver',default='cadical195')
    args=p.parse_args()
    row=json.loads(Path(__file__).with_name('seed_tables.json').read_text())[args.case]
    f,(ids,gates,products)=build(row,args.size,args.terms,args.reader_patterns,args.private)
    t=monotonic()
    with Solver(name=args.solver,bootstrap_with=f.clauses) as solver:
        solver.conf_budget(args.conflicts)
        result=solver.solve_limited()
        print(args.case,args.size,args.terms,{True:'SAT',False:'UNSAT',None:'UNKNOWN'}[result],
              round(monotonic()-t,2),solver.accum_stats()['conflicts'],flush=True)
        if result:
            model={x for x in solver.get_model() if x>0}
            ws=[row[i] for i in ids]
            for l,r,op,_,_ in gates:
                a,=[ws[j] for j,k in enumerate(l) if k in model]
                b,=[ws[j] for j,k in enumerate(r) if k in model]
                ws.append(a&b if op in model else a|b)
            target=0
            chosen=[(i,j) for i,j,f in products if f in model]
            for i,j in chosen:
                target|=ws[i]&ws[j]
            assert target==16383 and len(gates)+2*len(chosen)-1==args.size


if __name__=='__main__':
    main()
