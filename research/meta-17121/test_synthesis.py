"""Cross-check the SAT encoding against tiny exhaustive networks and known circuits."""
from itertools import combinations
import json
from pathlib import Path
import unittest

from exact_synthesis import encode, decode, check_witness


def reachable(seeds,bound):
    seen=set(seeds)
    states={frozenset(seeds)}
    for _ in range(bound):
        new_states=set()
        for wires in states:
            for a,b in combinations(wires,2):
                for out in (a&b,a|b):
                    if out not in wires:
                        seen.add(out)
                        new_states.add(wires|{out})
        states=new_states
    return seen


def canonicalize(seeds,gates):
    ready={i:i for i in range(len(seeds))}
    pending=set(range(len(gates)))
    order=[]
    while pending:
        choices=[i for i in pending if gates[i][1] in ready and gates[i][2] in ready]
        i=min(choices,key=lambda i: (max(ready[gates[i][1]],ready[gates[i][2]]),
                                     min(ready[gates[i][1]],ready[gates[i][2]]),i))
        op,a,b,value=gates[i]
        order.append((op,ready[a],ready[b],value))
        ready[len(seeds)+i]=len(ready)
        pending.remove(i)
    return order


class Encoding(unittest.TestCase):
    def test_tiny_truth_tables(self):
        from pysat.solvers import Solver
        seeds=[0,170,204,240]
        for n in (1,2):
            possible=reachable(seeds,n)
            for target in range(2,256,5):
                if target in seeds:
                    continue
                f,m=encode(seeds,target,8,n)
                with Solver(name="cadical195",bootstrap_with=f.clauses) as s:
                    sat=s.solve()
                    self.assertEqual(sat,target in possible,(target,n))
                    if sat:
                        decode(m,{v for v in s.get_model() if v>0})

    def test_known_19_gate_witnesses(self):
        from pysat.solvers import Solver
        root=Path(__file__).resolve().parent
        seeds=json.loads((root/"seed_tables.json").read_text())
        solutions=json.loads((root/"star_upper.json").read_text())
        for table,solution in zip(seeds,solutions):
            self.assertEqual(len(solution),19)
            witness=[dict(a=a,b=b,op=op.lower(),value=value) for op,a,b,value in solution]
            check_witness(table,16383,witness,19)
            reordered=canonicalize(table,solution)
            f,m=encode(table,16383,32,19)
            pos={j:i for i,j in enumerate(m["seed_indices"])}
            assumptions=[]
            for g,(op,a,b,_) in enumerate(reordered):
                av,bv=sorted((pos[a],pos[b]))
                assumptions.extend((m["left"][g][av],m["right"][g][bv],
                                    m["op"][g] if op=="AND" else -m["op"][g]))
                pos[len(table)+g]=len(m["seed_indices"])+g
            # A minimum witness would survive any topological sort. A known
            # 19-gate witness may have a dominator after renumbering if 18 is
            # achievable. Check the unrestricted ordered encoding as well.
            with Solver(name="cadical195",bootstrap_with=f.clauses) as s:
                sat=s.solve(assumptions=assumptions)
                if sat:
                    decode(m,{v for v in s.get_model() if v>0})
            if not sat:
                f,m=encode(table,16383,32,19,dominance=False)
                assumptions=[]
                for g,(op,a,b,_) in enumerate(reordered):
                    av,bv=sorted((pos[a],pos[b]))
                    assumptions.extend((m["left"][g][av],m["right"][g][bv],
                                        m["op"][g] if op=="AND" else -m["op"][g]))
                with Solver(name="cadical195",bootstrap_with=f.clauses) as s:
                    self.assertTrue(s.solve(assumptions=assumptions))
                    shorter=decode(m,{v for v in s.get_model() if v>0})
                    self.assertLess(len(shorter),19)
                    print("Shorter checked circuit",shorter,flush=True)


if __name__ == "__main__":
    unittest.main()
