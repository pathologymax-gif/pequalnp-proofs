"""Independently validate every added DRAT clause by reverse unit propagation."""

import argparse
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Solver


def check(clauses, proof):
    """Ignore deletions and accept only the RUP fragment of DRAT."""
    count = 0
    with Solver(name='glucose42', bootstrap_with=clauses) as checker:
        for line_number, line in enumerate(proof, 1):
            tokens = line.split()
            if not tokens or tokens[0] in ('c', 'd'):
                continue
            if tokens[-1] != '0':
                raise ValueError(f'Missing clause terminator on line {line_number}')
            clause = [int(x) for x in tokens[:-1]]
            if 0 in clause:
                raise ValueError(f'Unexpected zero on line {line_number}')
            consistent, _ = checker.propagate(assumptions=[-x for x in clause])
            if consistent:
                raise ValueError(f'Addition on line {line_number} failed RUP')
            count += 1
            if not clause:
                return count
            checker.add_clause(clause)
    raise ValueError('Missing derived empty clause')


if __name__ == '__main__':
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('cnf', type=Path)
    args.add_argument('proof', type=Path)
    paths = args.parse_args()
    with paths.proof.open(encoding='ascii') as proof:
        additions = check(CNF(from_file=str(paths.cnf)).clauses, proof)
    print(f'RUP VERIFIED: {additions} additions through the derived empty clause')
