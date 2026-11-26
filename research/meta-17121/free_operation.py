"""Exact budget for one gate type with arbitrary fan-in for the other type."""

from dataclasses import dataclass
from pathlib import Path
import argparse
import json
from time import monotonic

from exact_synthesis import Formula, bits, neg, samples_for


@dataclass
class Encoding:
    formula: Formula
    gates: list
    output: list


def conjunction(form, a, b):
    if a is False or b is False:
        return False
    if a is True or b is True:
        return b if a is True else a
    v = form.var()
    form.clause(-v, a)
    form.clause(-v, b)
    form.clause(v, -a, -b)
    return v


def join_operand(form, selectors, sources):
    values = []
    for col in zip(*sources):
        value = form.var()
        terms = [conjunction(form, s, x) for s, x in zip(selectors, col)]
        for term in terms:
            form.clause(neg(term), value)
        form.clause(-value, *terms)
        values.append(value)
    return values


def encode(words, target, width, budget, strengthen=True, aligned=False):
    """Use at most budget binary ANDs. OR and the empty OR are free."""
    form = Formula()
    samples = samples_for(words, target, width)
    values = [bits(w, samples) for w in words]
    labels = bits(target, samples)
    positive = [p for p,v in enumerate(labels) if v]
    negative = [q for q,v in enumerate(labels) if not v]
    seeds = values.copy()
    separated = {(q, r): [p for p in positive
                          if not any(row[p] and not row[q] and not row[r] for row in seeds)]
                 for j, q in enumerate(negative) for r in negative[:j]}
    signatures = {pair: [] for pair, witnesses in separated.items() if witnesses}
    triples = {(p,q,r): [] for (q,r), witnesses in separated.items() for p in witnesses} if aligned else {}
    raw_coverage = {p: [] for p in positive if not any(row[p] and all(not row[q] for q in negative)
                                                       for row in seeds)}
    gates = []
    for _ in range(budget):
        left, right = ([form.var() for _ in values] for _ in range(2))
        # Pull common operands through by distributivity; choose the orientation
        # whose first selected wire is on the left. Empty dummy gates permit
        # padding every shorter solution to the requested bound.
        for i, (l, r) in enumerate(zip(left, right)):
            form.clause(-l, -r)
            form.clause(-r, *left[:i])
        x = join_operand(form, left, values)
        y = join_operand(form, right, values)
        z = [conjunction(form, a, b) for a, b in zip(x, y)]
        if strengthen:
            plus = {q: conjunction(form, x[q], -y[q]) for q in negative}
            minus = {q: conjunction(form, -x[q], y[q]) for q in negative}
            for (q, r), terms in signatures.items():
                xy = conjunction(form, plus[q], minus[r])
                yx = conjunction(form, minus[q], plus[r])
                terms.extend((xy, yx))
                if aligned:
                    for p in separated[q,r]:
                        triples[p,q,r].extend((conjunction(form, z[p], xy), conjunction(form, z[p], yx)))
            raw_left = join_operand(form, left[:len(seeds)], seeds)
            raw_right = join_operand(form, right[:len(seeds)], seeds)
            for p, terms in raw_coverage.items():
                terms.append(conjunction(form, raw_left[p], raw_right[p]))
            # A minimum active gate improves one positive bit over the free join
            # of every old wire whose negative truth set is contained in its own.
            live = form.var()
            for s in left + right:
                form.clause(-s, live)
            necessary_at = {p: form.var() for p in positive}
            form.clause(-live, *necessary_at.values())
            for p, witness in necessary_at.items():
                form.clause(-witness, z[p])
            for row in values:
                outside = [conjunction(form, row[q], neg(z[q])) for q in negative]
                for p, witness in necessary_at.items():
                    form.clause(-witness, neg(row[p]), *outside)
        values.append(z)
        gates.append((left, right))
    output = [form.var() for _ in values]
    for v, expected in zip(join_operand(form, output, values), labels):
        form.clause(v if expected else -v)
    if strengthen:
        for terms in list(signatures.values()) + list(raw_coverage.values()) + list(triples.values()):
            form.clause(*terms)
    return Encoding(form, gates, output)


def replay(words, target, width, gates, output):
    values = list(words)
    for left, right in gates:
        def joined(select):
            value = 0
            for j in select:
                assert 0 <= j < len(values)
                value |= values[j]
            return value
        values.append(joined(left) & joined(right))
    result = 0
    for j in output:
        assert 0 <= j < len(values)
        result |= values[j]
    assert 0 <= result < 1 << width and result == target


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('case', type=int, choices=range(4))
    p.add_argument('kind', choices=['and', 'or'])
    p.add_argument('budget', type=int)
    p.add_argument('--conflicts', type=int, default=50000)
    p.add_argument('--output', type=Path)
    p.add_argument('--plain', action='store_true')
    p.add_argument('--aligned', action='store_true', help='add the three-coordinate necessary conditions')
    p.add_argument('--solver', default='cadical195')
    p.add_argument('--proof', type=Path, help='write a textual DRAT certificate on UNSAT')
    args = p.parse_args()
    from pysat.solvers import Solver
    tables = json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    words, target = tables[args.case], 16383
    if args.kind == 'or':
        words = [w ^ 0xffffffff for w in words]
        target ^= 0xffffffff
    enc = encode(words, target, 32, args.budget, not args.plain, args.aligned)
    start = monotonic()
    with Solver(name=args.solver, bootstrap_with=enc.formula.clauses, with_proof=bool(args.proof)) as solver:
        solver.conf_budget(args.conflicts)
        result = solver.solve_limited()
        report = dict(case=args.case, counted=args.kind, budget=args.budget,
                      variables=enc.formula.nvars, clauses=len(enc.formula.clauses),
                      verdict={True:'SAT', False:'UNSAT', None:'UNKNOWN'}[result],
                      solver=args.solver, conflicts=solver.accum_stats()['conflicts'])
        if result is False and args.proof:
            proof = solver.get_proof()
            if not proof:
                raise ValueError('solver did not produce a proof')
            with args.proof.open('w', encoding='ascii', newline='\n') as f:
                for line in proof:
                    f.write(line+'\n')
            enc.formula.write(args.proof.with_suffix('.cnf'))
        if result:
            model = {x for x in solver.get_model() if x > 0}
            def selected(vs):
                return [i for i, v in enumerate(vs) if v in model]
            gates = [[selected(l), selected(r)] for l, r in enc.gates]
            output = selected(enc.output)
            replay(words, target, 32, gates, output)
            report.update(gates=gates, output=output)
    report['seconds'] = round(monotonic()-start, 3)
    print(json.dumps(report), flush=True)
    if args.output:
        args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
