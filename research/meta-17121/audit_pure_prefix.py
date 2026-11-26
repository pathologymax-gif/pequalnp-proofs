"""Certify pure terminal layouts up to specified mixed-prefix limits."""

import argparse
import hashlib
import json
from pathlib import Path

from pysat.solvers import Solver
from check_rup import check
from subset_terminal_synthesis import build as lower_pairs
from symmetric_synthesis import build as by_position


def run(case, size, max_lower_prefix, max_upper_prefix, use_reader_patterns, conflicts):
    rows=json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    record=[]
    for lower in (True,False):
        for terms in range(2,(size+1)//2+1):
            d=size+1-2*terms
            if d>(max_lower_prefix if lower else max_upper_prefix):
                continue
            row=rows[case]
            if lower:
                f,_=lower_pairs(row,size,terms,use_reader_patterns)
            else:
                f=by_position(row,16383,32,d,0,terms,graph=True).cnf
            with Solver(name='cadical195',bootstrap_with=f.clauses,with_proof=True) as solver:
                solver.conf_budget(conflicts)
                result=solver.solve_limited()
                item={'case':case,'size':size,'dirty':d,'lower':terms if lower else 0,
                      'upper':0 if lower else terms,'reader_patterns':lower and use_reader_patterns,
                      'verdict':{True:'SAT',False:'UNSAT',None:'UNKNOWN'}[result]}
                if result is False:
                    proof=solver.get_proof() or []
                    if '0' not in proof:
                        proof.append('0')
                    item['rup_additions']=check(f.clauses,proof)
                    item['proof_sha256']=hashlib.sha256(('\n'.join(proof)+'\n').encode()).hexdigest()
                record.append(item)
    return record


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('case',type=int,choices=range(4))
    p.add_argument('--size',type=int,choices=(17,18),default=18)
    p.add_argument('--max-lower-prefix',type=int,default=6)
    p.add_argument('--max-upper-prefix',type=int,default=6)
    p.add_argument('--conflicts',type=int,default=600000)
    p.add_argument('--reader-patterns',action='store_true')
    p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    result=run(args.case,args.size,args.max_lower_prefix,args.max_upper_prefix,
               args.reader_patterns,args.conflicts)
    args.out.write_text(json.dumps(result,indent=2)+'\n')
    print([(r['lower'],r['upper'],r['verdict']) for r in result])
