"""Check three-test separation on every three-variable two-gate topology."""
from itertools import combinations, product
import unittest

from exact_synthesis import Formula
from refined_synthesis import at_least


class Refinements(unittest.TestCase):
    def test_prefix_cardinality_all_assignments(self):
        from pysat.solvers import Solver
        for threshold in range(1,6):
            f=Formula()
            raw=[f.var() for _ in range(4)]
            lit=at_least(f,[raw[0],-raw[1],raw[2],-raw[3]],threshold)
            f.clause(lit)
            with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
                for values in product([0,1],repeat=4):
                    expected=values[0]+(1-values[1])+values[2]+(1-values[3])>=threshold
                    fixed=[x if value else -x for x,value in zip(raw,values)]
                    self.assertEqual(solver.solve(assumptions=fixed),expected)

    def test_incompatible_triples(self):
        base=[170,204,240]
        def bit(w,i):
            return (w>>i)&1
        def check(steps):
            output=steps[-1][-1]
            for target_bit in (0,1):
                p=[k for k in range(8) if bit(output,k)==target_bit]
                n=[k for k in range(8) if bit(output,k)!=target_bit]
                for i,j in combinations(p,2):
                    for k in n:
                        if any(bit(w,i)==bit(w,j)==target_bit and bit(w,k)!=target_bit for w in base):
                            continue
                        found=any(op==('and' if target_bit==0 else 'or')
                                  and (bit(a,i),bit(b,i)) in ((0,1),(1,0))
                                  and (bit(a,j),bit(b,j))==(bit(b,i),bit(a,i))
                                  and bit(z,k)!=target_bit for op,a,b,z in steps)
                        self.assertTrue(found,(steps,i,j,k))
        def enumerate_steps(wires,steps):
            if len(steps)==2: return
            for a,b in combinations(wires,2):
                for op,z in [('and',a&b),('or',a|b)]:
                    new=steps+[(op,a,b,z)]
                    check(new)
                    enumerate_steps(wires+[z],new)
        enumerate_steps(base,[])


if __name__=='__main__':
    unittest.main()
