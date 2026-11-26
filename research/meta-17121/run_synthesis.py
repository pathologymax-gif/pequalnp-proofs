"""Run bounded SAT search; record SAT, UNSAT, and a timeout distinctly."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
from time import monotonic

from exact_synthesis import encode, decode


def solve(case, gates, out):
    from pysat.solvers import Solver
    tables=json.loads(Path(__file__).with_name("seed_tables.json").read_text())
    formula,metadata=encode(tables[case],16383,32,gates)
    start=monotonic()
    with Solver(name="cadical195",bootstrap_with=formula.clauses) as solver:
        for conflicts in (1000,10000,100000,300000,1000000,3000000,10000000):
            solver.conf_budget(conflicts)
            status=solver.solve_limited()
            stats=solver.accum_stats()
            print(f"case={case} gates={gates} seconds={monotonic()-start:.1f} "
                  f"status={status!r} stats={stats}",flush=True)
            if status is not None:
                result={"case":case,"gate_bound":gates,"solver":"cadical195",
                        "verdict":"SAT" if status else "UNSAT","stats":stats}
                if status:
                    result["witness"]=decode(metadata,{v for v in solver.get_model() if v>0})
                out.write_text(json.dumps(result,indent=2),encoding="utf8")
                return
    out.write_text(json.dumps({"case":case,"gate_bound":gates,"verdict":"UNKNOWN",
                              "reason":"conflict budget","stats":stats}),encoding="utf8")


def launch(args):
    args.out.mkdir(parents=True,exist_ok=True)
    processes=[]
    for i in range(4):
        target=args.out/f"case{i}.json"
        cmd=[sys.executable,"-u",str(Path(__file__).resolve()),"--case",str(i),
             "--gates",str(args.gates),"--out",str(target)]
        processes.append((subprocess.Popen(cmd),i,target))
    deadline=monotonic()+args.seconds
    failures=[]
    try:
        for proc,i,out in processes:
            try:
                rc=proc.wait(timeout=max(0,deadline-monotonic()))
            except subprocess.TimeoutExpired:
                if proc.poll() is None:
                    proc.kill()
                rc=proc.wait()
                if not out.exists():
                    out.write_text(json.dumps({"case":i,"gate_bound":args.gates,
                                               "verdict":"UNKNOWN","reason":"wall-clock budget"}))
                    continue
            if rc != 0:
                failures.append((i,rc))
        if failures:
            raise RuntimeError(f"Solver processes failed: {failures}")
    finally:
        for proc,_,_ in processes:
            if proc.poll() is None:
                proc.kill()
            proc.wait()
    for _,_,out in processes:
        print(out.read_text(encoding="utf8"),flush=True)


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case",type=int,choices=range(4))
    parser.add_argument("--gates",type=int,default=18)
    parser.add_argument("--seconds",type=int,default=1500)
    parser.add_argument("--out",type=Path,required=True)
    args=parser.parse_args()
    if args.case is None:
        launch(args)
    else:
        solve(args.case,args.gates,args.out)
