"""Independent truth-vector minimization and SAT replay for two-sided extraction."""

from collections import Counter
from itertools import combinations
from random import Random

from audit_terminal_normal_form import ordinary, next_words
from symmetric_synthesis import build, replay
from extract_guards import extract


def cover(universe, family):
    opt = {0:0}
    for w in family:
        b = w & universe
        if b:
            for old,c in list(opt.items()):
                v = old | b
                opt[v] = min(opt.get(v,100),c+1)
    return opt.get(universe,100)


def symmetric(words, target, width, bound):
    mask = (1<<width)-1
    neg = target ^ mask
    pools = {frozenset(words)}
    layouts = set()
    for d in range(bound):
        for pool in pools:
            products = set()
            clauses = set()
            for x,y in combinations(pool,2):
                if not ((x&y) & neg):
                    products.add(x&y)
                if not (target & ~(x|y)):
                    clauses.add(mask ^ (x|y))
            a = cover(target,products)
            b = cover(neg,clauses)
            if d+2*a-1 <= bound:
                layouts.add((d,a,0))
            if d+2*b-1 <= bound:
                layouts.add((d,0,b))
            if d+4 <= bound:
                for r in pool:
                    a = cover(target & ~r,products)
                    b = cover(neg & r,clauses)
                    if d+2*(a+b) <= bound:
                        layouts.add((d,a,b))
        pools = {pool|{w} for pool in pools for w in next_words(pool)
                 if w not in pool and w&neg and target&~w}
    return layouts


def check(words, width, budget, counts, examples):
    optimum = ordinary(words,budget)
    for target,n in optimum.items():
        if not n or any(not (x&~target) or not(target&~x) for x in words):
            continue
        layouts = symmetric(words,target,width,n)
        assert layouts, (words,target,n)
        assert all(d+2*(a+b)-int(not (a and b))==n for d,a,b in layouts)
        types = tuple(sorted({('mixed' if a and b else 'lower' if a else 'upper') for _,a,b in layouts}))
        counts[n, types] += 1
        for layout in layouts:
            examples.setdefault((n,layout),(list(words),width,target))


if __name__ == '__main__':
    from pysat.solvers import Solver
    counts, examples = Counter(), {}
    for seeds in combinations(range(1,16),3):
        check(seeds,4,4,counts,examples)
    for variables, budget in ((3,6),(4,5)):
        width = 1 << variables
        seeds = [sum(1 << j for j in range(width) if j >> i & 1) for i in range(variables)]
        check(seeds,width,budget,counts,examples)
    rand = Random(17121)
    for _ in range(180):
        check(rand.sample(range(1,128),4),7,5,counts,examples)
    print('Exact optimum matches:',sum(counts.values()))
    print('Optimal layout categories:',sorted(counts.items()))
    for (n,(d,a,b)),(seeds,width,target) in examples.items():
        e = build(seeds,target,width,d,a,b,minimum=True)
        with Solver(name='cadical195',bootstrap_with=e.cnf.clauses) as s:
            assert s.solve(),(seeds,target,(d,a,b))
            witness = replay(seeds,target,e,{v for v in s.get_model() if v>0})
        # Preserve each witness while adding redundant shared gates via
        # absorption. This tests dynamic trimming and exact output restoration.
        for _ in range(30):
            decorated = []
            mapping = list(range(len(seeds)))
            for op, x, y, _ in witness:
                decorated.append((op.lower(), mapping[x], mapping[y]))
                last = len(seeds)+len(decorated)-1
                if rand.randrange(3):
                    tag = rand.randrange(len(seeds))
                    aux, back = rand.choice((('or','and'),('and','or')))
                    decorated.append((aux,last,tag))
                    decorated.append((back,last,last+1))
                    last += 2
                mapping.append(last)
            _,_,_,_,program,out = extract(seeds,width,decorated,mapping[-1])
            vals = seeds.copy()
            for op,x,y in program:
                vals.append(vals[x]&vals[y] if op=='and' else vals[x]|vals[y])
            assert vals[out]==target and len(program)<=len(decorated)
    print('Independently realized SAT/replay (size,prefix,lower,upper) layouts:',len(examples))
