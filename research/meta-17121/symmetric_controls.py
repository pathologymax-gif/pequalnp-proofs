"""Pin and replay the known 19-gate circuits in the guard normal form."""

import json
from pathlib import Path

from pysat.solvers import Solver
from symmetric_synthesis import build, replay
from test_synthesis import canonicalize


def check(case, seeds, trace):
    e = build(seeds,16383,32,8,6,0,graph=True)
    ordinary = canonicalize(seeds,trace[:8])
    pool = {seeds[i]:j for j,i in enumerate(e.ids)}
    words = list(seeds)
    assumptions = []
    for i, (op,a,b,value) in enumerate(ordinary):
        assert op == 'OR'
        l,r,g,_ = e.gates[i]
        x,y = sorted((pool[words[a]],pool[words[b]]))
        assumptions.extend((l[x],r[y],-g))
        pool[value] = len(e.ids)+i
        words.append(value)
    old = seeds + [g[3] for g in trace[:8]]
    for j,(op,a,b,value) in enumerate(sorted(trace[8:14],key=lambda g:(g[3]&-g[3]).bit_length())):
        assert op == 'AND'
        x,y = sorted((pool[old[a]],pool[old[b]]))
        l,r,_,_ = e.gates[8+j]
        assumptions.extend((l[x],r[y]))
    with Solver(name='cadical195', bootstrap_with=e.cnf.clauses) as solver:
        assert solver.solve(assumptions=assumptions)
        witness = replay(seeds,16383,e,{w for w in solver.get_model() if w>0})
        assert len(witness)==19
    print(f'Case {case}: fixed 19-gate construction is SAT and replays on every bit.')


if __name__ == '__main__':
    root = Path(__file__).resolve().parent
    rows = json.loads((root/'seed_tables.json').read_text())
    known = json.loads((root/'star_upper.json').read_text())
    for i,(row,trace) in enumerate(zip(rows,known)):
        check(i,row,trace)
