"""Minimum monotone circuits with a mixed prefix and exposed lower/upper terms."""

from dataclasses import dataclass
from functools import cache
from itertools import combinations
from pathlib import Path
import argparse
import json
from time import monotonic

from exact_synthesis import Formula, bits, neg, samples_for
from refined_synthesis import conjunction, disjunction, at_least


@dataclass
class CircuitEncoding:
    cnf: Formula
    ids: list
    gates: list
    residual: list
    dirty: int
    lower: int
    upper: int
    size: int


@cache
def possible_repeats(words, size):
    from reader_preorder import Problem
    p = Problem(words)
    return [set(s) for k in range(min(len(p.vs), size-11)+1)
            for s in combinations(p.vs,k) if not p.relax(s)]


def choose(form, available, columns):
    selection = [form.var() for _ in available]
    form.clause(*selection)
    for a, b in combinations(selection, 2):
        form.clause(-a, -b)
    value = [form.var() for _ in range(columns)]
    for s, source in zip(selection, available):
        for w, v in zip(value, source):
            form.clause(-s, -w, v)
            form.clause(-s, w, neg(v))
    return selection, value


def private_positions(form, terms, indices, residual, lower):
    prior = []
    for i, term in enumerate(terms):
        witnesses = []
        for rank, j in enumerate(indices):
            w = form.var()
            witnesses.append(w)
            for k, other in enumerate(terms):
                lit = other[j] if (i == k) == lower else -other[j]
                form.clause(-w, lit)
            if residual:
                form.clause(-w, neg(residual[j]) if lower else residual[j])
            for prev in prior[rank:]:
                form.clause(-w, -prev)
        form.clause(*witnesses)
        prior = witnesses


def build(words, target, width, dirty, lower, upper, *, minimum=True, graph=False,
          residual_private=False, reader_patterns=False):
    if min(dirty, lower, upper) < 0 or lower+upper == 0:
        raise ValueError('The prefix and terminal counts must specify a nonempty construction')
    both = bool(lower and upper)
    mask = (1 << width) - 1
    ids = [i for i, w in enumerate(words) if w not in (0, mask)]
    if not all(words[i] & ~target and target & ~words[i] for i in ids):
        raise ValueError('All nonconstant raw signals must be mixed')
    samples = samples_for(words, target, width)
    labels = bits(target, samples)
    positive = [i for i,t in enumerate(labels) if t]
    negative = [i for i,t in enumerate(labels) if not t]
    values = [bits(words[i], samples) for i in ids]
    size = dirty + 2*(lower+upper) - int(not both)
    f = Formula()
    gates, terms_l, terms_u = [], [], []
    generated_words = []
    readers = [[] for _ in range(len(ids)+dirty)]
    for g in range(dirty+lower+upper):
        core = g < dirty
        product = g < dirty+lower
        op = f.var() if core else product
        left, x = choose(f, values, len(samples))
        right, y = choose(f, values, len(samples))
        for i, l in enumerate(left):
            for r in right[:i+1]:
                f.clause(-l, -r)
        if 0 < g < dirty:
            old_left, old_right, _, _ = gates[-1]
            tie = disjunction(f, [conjunction(f, [a,b]) for a,b in zip(old_right,right)])
            for i, r in enumerate(old_right):
                for earlier in right[:i]:
                    f.clause(-r, -earlier)
            for i, l in enumerate(old_left):
                for earlier in left[:i]:
                    f.clause(neg(tie), -l, -earlier)
        selected = [disjunction(f, [a,b]) for a,b in zip(left,right)]
        for i, read in enumerate(selected):
            readers[i].append(read)
            if minimum and i >= len(ids):
                for k, old in enumerate(gates[i-len(ids)][3]):
                    f.clause(neg(read), neg(old), neg(selected[k]))
        z = [f.var() for _ in samples]
        for a,b,w in zip(x,y,z):
            f.clause(-a,-b,w)
            f.clause(a,b,-w)
            f.clause(neg(op),-w,a)
            f.clause(neg(op),-w,b)
            f.clause(op,w,-a)
            f.clause(op,w,-b)
        if core:
            f.clause(*[-z[j] for j in positive])
            f.clause(*[z[j] for j in negative])
            if minimum:
                # Otherwise constant zero or one can globally replace this gate.
                f.clause(*[z[j] for j in positive])
                f.clause(*[-z[j] for j in negative])
                for old in values:
                    wins = [conjunction(f,[w, neg(v)]) if label else conjunction(f,[-w,v])
                            for w,v,label in zip(z,old,labels)]
                    f.clause(*wins)
            values.append(z)
        elif product:
            for j in negative:
                f.clause(-z[j])
            terms_l.append(z)
        else:
            for j in positive:
                f.clause(z[j])
            terms_u.append(z)
        gates.append((left, right, op, selected))
        generated_words.append(z)
    residual, rvalue = choose(f, values, len(samples)) if both else ([], [])
    for i, read in enumerate(residual):
        readers[i].append(read)
    if terms_l:
        for j in positive:
            f.clause(*([rvalue[j]] if both else []), *[t[j] for t in terms_l])
    if terms_u:
        for j in negative:
            f.clause(*([-rvalue[j]] if both else []), *[-t[j] for t in terms_u])
    if minimum:
        private_positions(f, terms_l, positive, rvalue, True)
        private_positions(f, terms_u, negative, rvalue, False)
        if both and residual_private:
            f.clause(*(conjunction(f,[rvalue[j]]+[-t[j] for t in terms_l]) for j in positive))
            f.clause(*(conjunction(f,[-rvalue[j]]+[t[j] for t in terms_u]) for j in negative))
        for i, reads in enumerate(readers):
            if graph or i >= len(ids):
                f.clause(*reads)
    if graph:
        if len(ids) != 10 or target != 16383 or width != 32:
            raise ValueError('The extra gate-type and sharing bounds are G11-specific')
        ands = [g[2] for g in gates[:dirty]] + [True]*(lower+upper-int(not both and not lower))
        ors = [neg(g[2]) for g in gates[:dirty]] + [True]*(lower+upper-int(not both and not upper))
        f.clause(at_least(f, ands, 6))
        f.clause(at_least(f, ors, 7))
        # A once-read graph variable entering an AND must transmit every
        # incident positive, and entering an OR must stay zero on every
        # nonempty maximal negative omitting that variable. A residual read,
        # when present, is already included in the fanout count.
        copies = []
        for i, raw in enumerate(values[:len(ids)]):
            shared = at_least(f,readers[i],2)
            copies.append(shared)
            for g,(_,_,op,selected) in enumerate(gates):
                for j in positive:
                    if raw[j]:
                        f.clause(neg(selected[i]),shared,neg(op),generated_words[g][j])
                for j in negative:
                    if not raw[j] and any(values[t][j] for t in range(len(ids))):
                        f.clause(neg(selected[i]),shared,op,-generated_words[g][j])
        # Any full-positive upper terminal rejecting a maximal negative q
        # requires |V\\q|-1 zero ORs. Only its own OR is outside the mixed
        # prefix, even when other terminal outputs use the same prefix.
        for j in negative:
            support = sum((words[i] >> samples[j]) & 1 for i in ids)
            if not support or not terms_u:
                continue
            core_zero_or = [conjunction(f,[neg(gates[i][2]),neg(values[len(ids)+i][j])])
                            for i in range(dirty)]
            bound = at_least(f,core_zero_or,len(ids)-support-2)
            for term in terms_u:
                f.clause(term[j],bound)
        if terms_l:
            from symmetric_bounds import positive_obstructions
            for needed,masks in positive_obstructions(tuple(words)).items():
                enough = at_least(f,[g[2] for g in gates[:dirty]],needed)
                for term in terms_l:
                    for mask in masks:
                        f.clause(enough,*[-term[j] for j in positive if mask >> samples[j] & 1])
        if size <= 18:
            f.clause(at_least(f,[at_least(f, users, 2) for users in readers[len(ids):]],2))
            if not upper:
                f.clause(*(g[2] for g in gates[:dirty]))
            if reader_patterns:
                choices = []
                for repeat in possible_repeats(tuple(words),size):
                    choice = f.var()
                    choices.append(choice)
                    for i, v in enumerate(ids):
                        f.clause(-choice,copies[i] if v in repeat else neg(copies[i]))
                f.clause(*choices)
    return CircuitEncoding(f,ids,gates,residual,dirty,lower,upper,size)


def replay(row, target, enc, model):
    pool = enc.ids.copy()
    values = list(row)
    steps = []
    def emit(is_and, a, b):
        w = values[a] & values[b] if is_and else values[a] | values[b]
        steps.append(['AND' if is_and else 'OR',a,b,w])
        values.append(w)
        return len(values)-1
    def selected(options):
        i, = [i for i, x in enumerate(options) if x in model]
        return pool[i]
    low, high = [], []
    for i,(l,r,op,_) in enumerate(enc.gates):
        both = op if isinstance(op,bool) else op in model
        j = emit(both,selected(l),selected(r))
        if i < enc.dirty:
            pool.append(j)
        elif both:
            low.append(j)
        else:
            high.append(j)
    if enc.residual:
        last = selected(enc.residual)
    else:
        group = low if low else high
        last = group.pop()
    for g in low:
        last = emit(False,last,g)
    for g in high:
        last = emit(True,last,g)
    assert values[last] == target and len(steps) == enc.size
    return steps


def main():
    from pysat.solvers import Solver
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('case', type=int, choices=range(4))
    p.add_argument('size', type=int)
    p.add_argument('lower', type=int)
    p.add_argument('upper', type=int)
    p.add_argument('--conflicts', type=int, default=60000)
    p.add_argument('--residual-private', action='store_true')
    p.add_argument('--reader-patterns', action='store_true')
    args = p.parse_args()
    rows = json.loads(Path(__file__).with_name('seed_tables.json').read_text())
    row = rows[args.case]
    dirty = args.size-2*(args.lower+args.upper) + int(not (args.lower and args.upper))
    encoding = build(row,16383,32,dirty,args.lower,args.upper,graph=True,
                     residual_private=args.residual_private,reader_patterns=args.reader_patterns)
    start = monotonic()
    with Solver(name='cadical195',bootstrap_with=encoding.cnf.clauses) as solver:
        solver.conf_budget(args.conflicts)
        verdict = solver.solve_limited()
        result = {'case':args.case,'size':args.size,'lower':args.lower,'upper':args.upper,
                  'dirty':dirty,'verdict':{True:'SAT',False:'UNSAT',None:'UNKNOWN'}[verdict]}
        if verdict:
            result['gates'] = replay(row,16383,encoding,{v for v in solver.get_model() if v>0})
        result['seconds'] = round(monotonic()-start,3)
        print(json.dumps(result))


if __name__ == '__main__':
    main()
