"""Exhaust all eligible repeated-input sets, splitting the first gate where needed."""
import argparse
import gzip
import hashlib
from itertools import combinations
import json
from pathlib import Path
from terminal_synthesis import ROOT, solve
from read_once_closure import analyze


def checkpoint(path, obj):
    temp = path.with_suffix('.tmp')
    temp.write_text(json.dumps(obj, indent=1))
    temp.replace(path)


def run(args):
    row = json.loads((ROOT / 'seed_tables.json').read_text())[args.case]
    directory = ROOT / 'terminal-results'
    directory.mkdir(exist_ok=True)
    name = f'size{args.size}-case{args.case}-terms{args.terms}'
    report = directory / (name + '.json')
    cases = json.loads(report.read_text()) if report.exists() else {}
    paths = (ROOT/'terminal_synthesis.py',ROOT/'terminal_cubes.py',ROOT/'read_once_closure.py',
             ROOT/'exact_synthesis.py',ROOT/'refined_synthesis.py',ROOT/'check_rup.py')
    digest = hashlib.sha256(b''.join(p.read_bytes() for p in paths)).hexdigest()
    if cases.get('source_sha256', digest) != digest:
        raise ValueError('Existing results used different source files')
    cases.update(source_sha256=digest, size=args.size, case=args.case, terms=args.terms)
    done = cases.setdefault('cubes', {})
    has_witness = False

    def attempt(repeat, first):
        repeat_key = ','.join(map(str,repeat))
        first_key = 'all' if first is None else ','.join(map(str,first))
        key = repeat_key + '/' + first_key
        if key in done and done[key]['verdict'] != 'UNKNOWN':
            return done[key]['verdict']
        local = directory / f'{name}-R{repeat_key}-F{first_key}.json'
        result = solve(args.case, args.size, args.terms, repeat, args.budget, local, True, False, first)
        if result['verdict'] == 'UNSAT':
            proof = local.with_suffix('.drat.gz')
            # Every RUP addition was checked in solve(). Keep a portable hash
            # of the text, and optionally retain the actual compressed proof.
            with gzip.open(proof, 'rb') as fp:
                result['proof_sha256'] = hashlib.file_digest(fp, 'sha256').hexdigest()
            if not args.keep_proofs:
                proof.unlink()
        done[key] = result
        checkpoint(report,cases)
        return result['verdict']

    unresolved = []
    for _, _, _, masks in analyze(row,args.size-11,True):
        for mask in masks:
            repeat = [i for i in range(len(row)) if mask >> i & 1]
            if args.terms == 1 or args.split_first:
                firsts = list(combinations(repeat,2))
            else:
                firsts = [None]
            for first in firsts:
                status = attempt(repeat, first)
                if status == 'SAT':
                    has_witness = True
                    break
                if status == 'UNKNOWN' and first is None:
                    remaining = []
                    for pair in combinations(repeat, 2):
                        sub = attempt(repeat, pair)
                        if sub == 'SAT':
                            has_witness = True
                            break
                        if sub == 'UNKNOWN':
                            remaining.append(pair)
                    if remaining:
                        unresolved.append([repeat, remaining])
                    if has_witness:
                        break
                elif status == 'UNKNOWN':
                    unresolved.append([repeat, first])
            if has_witness:
                break
        if has_witness:
            break
    cases['outcome'] = 'WITNESS' if has_witness else 'UNKNOWN' if unresolved else 'RUP_VERIFIED_UNSAT'
    cases['unresolved'] = unresolved
    checkpoint(report,cases)
    print(name, cases['outcome'], len(done), len(unresolved), flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('case', type=int, choices=range(4))
    p.add_argument('size', type=int)
    p.add_argument('terms', type=int)
    p.add_argument('--budget', type=int, default=90000)
    p.add_argument('--split-first', action='store_true')
    p.add_argument('--keep-proofs', action='store_true')
    run(p.parse_args())
