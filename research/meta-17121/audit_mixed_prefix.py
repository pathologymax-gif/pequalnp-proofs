"""Check all mixed-residual layouts of sizes 17/18 up to a prefix-size limit."""

import argparse
import hashlib
import json
from pathlib import Path

from pysat.solvers import Solver
from check_rup import check
from symmetric_synthesis import build, replay


def run(case, conflicts, max_prefix):
    row = json.loads(Path(__file__).with_name('seed_tables.json').read_text())[case]
    reports = []
    for size in (17,18):
        for total in range(2,size//2+1):
            dirty = size-2*total
            if dirty > max_prefix:
                continue
            for lower in range(1,total):
                upper = total-lower
                e = build(row,16383,32,dirty,lower,upper,graph=True)
                with Solver(name='cadical195',bootstrap_with=e.cnf.clauses,with_proof=True) as solver:
                    solver.conf_budget(conflicts)
                    result = solver.solve_limited()
                    item = dict(case=case,size=size,dirty=dirty,lower=lower,upper=upper,
                                verdict={True:'SAT',False:'UNSAT',None:'UNKNOWN'}[result])
                    if result is False:
                        proof = solver.get_proof() or []
                        # Some immediately inconsistent inputs have only
                        # deletion records. The checker must derive the
                        # explicit empty clause independently in every case.
                        if '0' not in proof:
                            proof.append('0')
                        item['rup_additions'] = check(e.cnf.clauses,proof)
                        item['proof_sha256'] = hashlib.sha256(('\n'.join(proof)+'\n').encode()).hexdigest()
                    elif result:
                        item['witness'] = replay(row,16383,e,{w for w in solver.get_model() if w>0})
                    reports.append(item)
    return reports


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('case',type=int,choices=range(4))
    p.add_argument('--conflicts',type=int,default=400000)
    p.add_argument('--max-prefix',type=int,default=6)
    p.add_argument('--out',type=Path)
    args = p.parse_args()
    reports = run(args.case,args.conflicts,args.max_prefix)
    if args.out:
        args.out.write_text(json.dumps(reports,indent=2)+'\n')
    print({key:sum(r['verdict']==key for r in reports) for key in ('SAT','UNSAT','UNKNOWN')})
