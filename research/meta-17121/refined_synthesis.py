"""Minimum-circuit clauses for the four G11 projections. See RefinedSynthesis.md."""
import argparse
from itertools import combinations
import json
from pathlib import Path
from time import monotonic
from exact_synthesis import decode, encode, neg

ROOT=Path(__file__).resolve().parent
TARGET=(1<<14)-1


def disjunction(f,literals):
    if any(x is True for x in literals): return True
    items=list(dict.fromkeys(x for x in literals if x is not False))
    if not items: return False
    if len(items)==1: return items[0]
    out=f.var()
    for x in items: f.clause(neg(x),out)
    f.clause(-out,*items)
    return out


def conjunction(f,items):
    return neg(disjunction(f,[neg(x) for x in items]))


def at_least(f,entries,threshold):
    """A truncated prefix counter; works with signed or constant literals."""
    counts=[True]+[False]*threshold
    for lit in entries:
        counts=[True]+[disjunction(f,[counts[k],conjunction(f,[counts[k-1],lit])])
                       for k in range(1,threshold+1)]
    return counts[threshold]


def separation_clauses(f,m,and_gate,or_gate,positive,negative):
    """A leaf unable to solve a three-test subproblem forces a separating gate."""
    seed_indices=m['seed_indices']
    seeds=m['seed_words']
    tests=[{i for i in seed_indices if seeds[i]>>sample&1} for sample in m['samples']]
    z=m['gate_values']
    operand_states=[]
    for x,y in m['operand_values']:
        ten=[conjunction(f,[a,-b]) for a,b in zip(x,y)]
        one=[conjunction(f,[-a,b]) for a,b in zip(x,y)]
        operand_states.append((ten,one))
    for kind,entries,other,ops in [('and',negative,positive,and_gate),
                                   ('or',positive,negative,or_gate)]:
        for i,j in combinations(entries,2):
            if kind=='and':
                needed=[k for k in other if tests[k]<=tests[i]|tests[j]]
            else:
                needed=[k for k in other if tests[i]&tests[j]<=tests[k]]
            if not needed: continue
            splits=[]
            for g,(ten,one) in enumerate(operand_states):
                cross=disjunction(f,[conjunction(f,[ten[i],one[j]]),
                                     conjunction(f,[ten[j],one[i]])])
                splits.append(conjunction(f,[ops[g],cross]))
            for k in needed:
                witnesses=[conjunction(f,[split,z[g][k] if kind=='and' else -z[g][k]])
                           for g,split in enumerate(splits)]
                f.clause(*witnesses)


def encode_refined(case,bound,separations=False):
    seeds=json.loads((ROOT/'seed_tables.json').read_text())[case]
    f,m=encode(seeds,TARGET,32,bound,expose_values=True)
    ls,rs,op,z,live=(m[k] for k in ('left','right','op','gate_values','live'))
    n=len(m['seed_indices'])
    samples=m['samples']
    positive=[k for k,j in enumerate(samples) if TARGET>>j&1]
    negative=[k for k,j in enumerate(samples) if not TARGET>>j&1]
    use=[[disjunction(f,(a,b)) for a,b in zip(left,right)] for left,right in zip(ls,rs)]
    fp=[disjunction(f,[w[k] for k in negative]) for w in z]
    fn=[disjunction(f,[-w[k] for k in positive]) for w in z]
    and_gate=[conjunction(f,[live[g],op[g]]) for g in range(bound)]
    or_gate=[conjunction(f,[live[g],-op[g]]) for g in range(bound)]

    # Equal largest operands are tied first by smaller operand, then AND before OR.
    for g in range(1,bound):
        tie=disjunction(f,[conjunction(f,[a,b]) for a,b in zip(rs[g-1],rs[g])])
        for i,prev in enumerate(ls[g-1]):
            for cur in ls[g][:i]:
                f.clause(neg(tie),-prev,-cur)
            f.clause(neg(tie),-prev,-ls[g][i],op[g-1],-op[g])

    # If a current gate reads both an earlier gate and one of its operands,
    # either idempotence or absorption removes it regardless of the operators.
    shares=[]
    for g in range(bound):
        later_uses=[use[j][n+g] for j in range(g+1,bound)]
        shared=at_least(f,later_uses,2)
        shares.append(shared)
        f.clause(neg(shared),fp[g])
        f.clause(neg(shared),fn[g])
        for j in range(g+1,bound):
            selected=use[j][n+g]
            for i,operand in enumerate(use[g]):
                f.clause(neg(selected),neg(operand),neg(use[j][i]))
            f.clause(neg(selected),-op[j],fp[g])
            f.clause(neg(selected),op[j],fn[g])

    # Every nonzero primary is essential. A unique reader must preserve each
    # boundary test on which toggling the primary changes the output.
    for i,original in enumerate(m['seed_indices']):
        reads=[gate[i] for gate in use]
        f.clause(*reads)
        multiple=at_least(f,reads,2)
        word=seeds[original]
        for g,reader in enumerate(reads):
            for k in positive:
                if word>>samples[k]&1:
                    f.clause(neg(reader),multiple,-op[g],z[g][k])
            for k in negative:
                column=samples[k]
                nonempty=any(w>>column&1 for w in seeds)
                if nonempty and not word>>column&1:
                    f.clause(neg(reader),multiple,op[g],-z[g][k])

    f.clause(at_least(f,and_gate,(5,4,5,4)[case]))
    full_or=[conjunction(f,[or_gate[g],neg(fn[g])]) for g in range(bound)]
    f.clause(*full_or)
    # At every maximal independent M, at least |V-M|-1 ORs are zero
    # on M. At least |V-M|-2 of these also miss a positive test.
    for k in negative:
        size=sum((w>>samples[k])&1 for w in seeds)
        if size==0: continue
        zero_or=[conjunction(f,[or_gate[g],-z[g][k]]) for g in range(bound)]
        f.clause(at_least(f,zero_or,n-size-1))
        bad=[conjunction(f,[zero_or[g],fn[g]]) for g in range(bound)]
        f.clause(at_least(f,bad,n-size-2))
    if bound<=18:
        f.clause(at_least(f,shares,2))
        dirty_ands=[conjunction(f,[and_gate[g],fp[g]]) for g in range(bound)]
        f.clause(*dirty_ands)
    if separations:
        separation_clauses(f,m,and_gate,or_gate,positive,negative)
    return f,m


def fixed_star(case,m):
    from test_synthesis import canonicalize
    seeds=json.loads((ROOT/'seed_tables.json').read_text())[case]
    witness=json.loads((ROOT/'star_upper.json').read_text())[case]
    pos={j:i for i,j in enumerate(m['seed_indices'])}
    assumed=[]
    for g,(symbol,a,b,_) in enumerate(canonicalize(seeds,witness)):
        x,y=sorted((pos[a],pos[b]))
        assumed.extend([m['left'][g][x],m['right'][g][y],
                        m['op'][g] if symbol=='AND' else -m['op'][g]])
        pos[len(seeds)+g]=len(m['seed_indices'])+g
    return assumed


def run(case,bound,conflicts,star,solver_name,separations):
    from pysat.solvers import Solver
    f,m=encode_refined(case,bound,separations)
    start=monotonic()
    with Solver(name=solver_name,bootstrap_with=f.clauses) as solver:
        assumed=fixed_star(case,m) if star else []
        solver.conf_budget(conflicts)
        status=solver.solve_limited(assumptions=assumed)
        result={'case':case,'gates':bound,'solver':solver_name,'conflict_budget':conflicts,
                'status':'SAT' if status else ('UNSAT' if status is False else 'UNKNOWN'),
                'clauses':len(f.clauses),'variables':f.nvars,
                'seconds':round(monotonic()-start,3),'stats':solver.accum_stats(),'fixed_star':star,
                'separations':separations}
        if status:
            result['witness']=decode(m,{x for x in solver.get_model() if x>0})
        if star and status is not True:
            raise RuntimeError(f'Known star fixture failed in case {case}: {result}')
        return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--case',type=int,choices=range(4),required=True)
    p.add_argument('--gates',type=int,default=18)
    p.add_argument('--conflicts',type=int,default=25000)
    p.add_argument('--fixed-star',action='store_true')
    p.add_argument('--separations',action='store_true',
                   help='Require an AND/OR witness for every incompatible three-test cell.')
    p.add_argument('--solver',default='cadical195')
    p.add_argument('--out',type=Path)
    args=p.parse_args()
    if args.fixed_star and args.gates!=19:p.error('The fixed star fixture has 19 gates.')
    if args.conflicts<=0 or args.gates<=0:p.error('Positive budgets are required.')
    result=run(args.case,args.gates,args.conflicts,args.fixed_star,args.solver,args.separations)
    summary=json.dumps(result,indent=2)
    if args.out:args.out.write_text(summary)
    print(summary)
