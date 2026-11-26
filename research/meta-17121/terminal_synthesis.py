"""Search minimum circuits as an arbitrary erroneous core followed by clean products and one OR tree."""
import argparse
from itertools import combinations
import json
from pathlib import Path
from time import monotonic

from exact_synthesis import Formula, bits, correct, neg, samples_for
from refined_synthesis import at_least, conjunction, disjunction


ROOT = Path(__file__).resolve().parent
TARGET = 16383


def build(row, dirty, terms, repeat=None, minimum=True, repeat_sets=None):
    f = Formula()
    ids = [i for i, w in enumerate(row) if w]
    samples = samples_for(row, TARGET, 32)
    labels = bits(TARGET, samples)
    positive = [j for j, b in enumerate(labels) if b]
    negative = [j for j, b in enumerate(labels) if not b]
    n = len(ids)
    values = [bits(row[i], samples) for i in ids]
    gates = []
    reads = [[] for _ in range(n + dirty)]
    terms_values = []
    size = dirty + 2 * terms - 1

    for g in range(dirty + terms):
        final = g >= dirty
        sel_l = [f.var() for _ in values]
        sel_r = [f.var() for _ in values]
        for options in (sel_l, sel_r):
            f.clause(*options)
            for a, b in combinations(options, 2):
                f.clause(-a, -b)
        for i, left in enumerate(sel_l):
            for right in sel_r[:i + 1]:
                f.clause(-left, -right)
        if 0 < g < dirty:
            old_l, old_r, _, _, _ = gates[-1]
            for i, rv in enumerate(old_r):
                for curr in sel_r[:i]:
                    f.clause(-rv, -curr)
            tie = disjunction(f, [conjunction(f, [a, b]) for a, b in zip(old_r, sel_r)])
            for i, lv in enumerate(old_l):
                for curr in sel_l[:i]:
                    f.clause(neg(tie), -lv, -curr)
        op = True if final else f.var()
        lo = [f.var() for _ in samples]
        hi = [f.var() for _ in samples]
        z = [f.var() for _ in samples]
        chosen = [disjunction(f, [a, b]) for a, b in zip(sel_l, sel_r)]
        for i, data in enumerate(values):
            reads[i].append(chosen[i])
            for j, source in enumerate(data):
                for sel, val in ((sel_l[i], lo[j]), (sel_r[i], hi[j])):
                    f.clause(-sel, -val, source)
                    f.clause(-sel, val, neg(source))
            if i >= n:
                # Absorption makes any reader using a gate plus its own
                # input redundant in a minimum circuit, for either operation.
                for k, earlier in enumerate(gates[i - n][4]):
                    if minimum:
                        f.clause(neg(chosen[i]), neg(earlier), neg(chosen[k]))
        for j, (a, b, w) in enumerate(zip(lo, hi, z)):
            f.clause(-a, -b, w)
            f.clause(a, b, -w)
            f.clause(neg(op), -w, a)
            f.clause(neg(op), -w, b)
            f.clause(op, w, -a)
            f.clause(op, w, -b)
        f.clause(*(z[j] for j in positive))
        if final:
            for j in negative:
                f.clause(-z[j])
            terms_values.append(z)
        else:
            f.clause(*(z[j] for j in negative))
            if minimum:
                for old in values:
                    improves = [conjunction(f, [correct(z[j], labels[j]),
                                                neg(correct(old[j], labels[j]))]) for j in range(len(samples))]
                    f.clause(*improves)
            values.append(z)
        gates.append((sel_l, sel_r, op, z, chosen))

    for j in positive:
        f.clause(*(z[j] for z in terms_values))
    # Assign each product a private edge, strictly increasing by index.
    # Every term of a minimum circuit has one; freely permute final products.
    if minimum:
        witnesses = []
        for t, word in enumerate(terms_values):
            own = [f.var() for _ in positive]
            f.clause(*own)
            for idx, j in enumerate(positive):
                for u, other in enumerate(terms_values):
                    f.clause(-own[idx], other[j] if u == t else -other[j])
                if t:
                    for prev in witnesses[-1][idx:]:
                        f.clause(-own[idx], -prev)
            witnesses.append(own)

    shared = []
    repeat_primary = []
    pattern_choices = [f.var() for _ in repeat_sets] if repeat_sets is not None else []
    if repeat_sets is not None:
        f.clause(*pattern_choices)
    for i, users in enumerate(reads):
        f.clause(*users)
        multiple = at_least(f, users, 2)
        if i >= n:
            shared.append(multiple)
            if minimum:
                f.clause(neg(multiple), *[-values[i][j] for j in positive])
        elif minimum:
            repeat_primary.append(multiple)
            if repeat is not None:
                f.clause(multiple if ids[i] in repeat else neg(multiple))
            if repeat_sets is not None:
                for choice, pattern in zip(pattern_choices, repeat_sets):
                    f.clause(-choice, multiple if ids[i] in pattern else neg(multiple))
            for g, (_, _, op, word, chosen) in enumerate(gates):
                read = chosen[i]
                for j in positive:
                    if values[i][j]:
                        f.clause(neg(read), multiple, neg(op), word[j])
                for j in negative:
                    if not values[i][j] and any(row[k] >> samples[j] & 1 for k in ids):
                        f.clause(neg(read), multiple, op, -word[j])
    if minimum:
        # No two distinct raw inputs can be the only-reader pair of either
        # variable. An AND would miss another incident edge, and an OR would
        # add a maximal negative containing the other input. A raw AND has
        # either no positive edge or no false positive, so it is never dirty.
        for g, (left, right, op, _, _) in enumerate(gates):
            for i, j in combinations(range(n), 2):
                f.clause(-left[i],-right[j],repeat_primary[i])
                f.clause(-left[i],-right[j],repeat_primary[j])
                if g < dirty:
                    f.clause(-left[i],-right[j],neg(op))
    if minimum and size <= 18:
        f.clause(at_least(f, shared, 2))
        f.clause(*(gates[g][2] for g in range(dirty)))
    if minimum:
        # Six ANDs are necessary even with arbitrary ORs; seven ORs are
        # necessary even with arbitrary ANDs, by the frozen free-op proofs.
        f.clause(at_least(f, [g[2] for g in gates], 6))
        f.clause(at_least(f, [neg(gates[i][2]) for i in range(dirty)] + [True] * (terms - 1), 7))
    return f, (ids, gates, dirty, terms)


def decode(row, meta, model):
    ids, gates, dirty, terms = meta
    wires = row[:]
    mapped = ids[:]
    results, terminal = [], []

    def emit(op, a, b):
        val = wires[a] & wires[b] if op == 'and' else wires[a] | wires[b]
        results.append({'op': op, 'a': a, 'b': b, 'value': val})
        wires.append(val)
        return len(wires) - 1

    for i, (l, r, op, _, _) in enumerate(gates):
        a, = [mapped[k] for k, selector in enumerate(l) if selector in model]
        b, = [mapped[k] for k, selector in enumerate(r) if selector in model]
        k = emit('and' if op is True or op in model else 'or', a, b)
        if i < dirty:
            mapped.append(k)
        else:
            terminal.append(k)
    k = terminal[0]
    for nxt in terminal[1:]:
        k = emit('or', k, nxt)
    if wires[k] != TARGET or len(results) != dirty + 2 * terms - 1:
        raise ValueError('Model failed original 32-bit circuit replay')
    return results


def solve(case, size, terms, repeats, budget, out, verify=False, restrict_sets=False, first=None):
    from pysat.solvers import Solver
    from check_rup import check
    import gzip
    dirty = size - 2 * terms + 1
    rows = json.loads((ROOT / 'seed_tables.json').read_text())
    patterns = None
    if restrict_sets:
        from read_once_closure import analyze
        patterns = [tuple(i for i in range(len(rows[case])) if mask >> i & 1)
                    for _, _, _, choices in analyze(rows[case],size-11,True) for mask in choices]
    f, meta = build(rows[case], dirty, terms, repeats, repeat_sets=patterns)
    if first is not None:
        ids, gates, _, _ = meta
        i,j=sorted(ids.index(k) for k in first)
        f.clause(gates[0][0][i])
        f.clause(gates[0][1][j])
    begin = monotonic()
    with Solver(name='cadical195', bootstrap_with=f.clauses, with_proof=verify) as s:
        s.conf_budget(budget)
        state = s.solve_limited()
        result = dict(case=case, size=size, terms=terms, dirty=dirty, repeats=repeats,
                      verdict={True:'SAT', False:'UNSAT', None:'UNKNOWN'}[state], stats=s.accum_stats(),
                      variables=f.nvars, clauses=len(f.clauses), eligible_reader_patterns=patterns, first=first,
                      seconds=round(monotonic()-begin, 2))
        if state is True:
            result['gates'] = decode(rows[case], meta, {x for x in s.get_model() if x > 0})
        if verify and state is False:
            proof = s.get_proof()
            result['rup'] = check(f.clauses, proof)
            with gzip.open(out.with_suffix('.drat.gz'),'wt',encoding='ascii') as fp:
                fp.write('\n'.join(proof) + '\n')
    out.write_text(json.dumps(result, indent=2))
    print(result['case'], result['size'], result['terms'], result['repeats'], result['verdict'],
          result['seconds'], result.get('rup'))
    return result


if __name__ == '__main__':
    p=argparse.ArgumentParser()
    p.add_argument('case', type=int)
    p.add_argument('size', type=int)
    p.add_argument('terms', type=int)
    p.add_argument('--repeat', type=int, nargs='+')
    p.add_argument('--budget', type=int, default=60000)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--verify', action='store_true')
    p.add_argument('--restrict-sets', action='store_true')
    p.add_argument('--first', nargs=2,type=int)
    a=p.parse_args()
    solve(a.case,a.size,a.terms,a.repeat,a.budget,a.out,a.verify,a.restrict_sets,a.first)
