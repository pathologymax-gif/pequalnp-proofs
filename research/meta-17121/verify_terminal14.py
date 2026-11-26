"""Check exact coverage of the size-14 case split and optionally replay every RUP proof."""
import argparse
from concurrent.futures import ThreadPoolExecutor
import gzip
from itertools import combinations
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from read_once_closure import analyze

ROOT = Path(__file__).resolve().parent


def coverage():
    rows = json.loads((ROOT / 'seed_tables.json').read_text())
    stored = json.loads(gzip.decompress((ROOT / 'terminal14_reports.json.gz').read_bytes()))
    by_case = {(d['case'],d['terms']): d for d in stored}
    assert len(by_case) == len(stored) == 18
    work, total = [], 0
    for case, row in enumerate(rows):
        levels = analyze(row,3,True)
        assert all(not allowed for n,_,_,allowed in levels if n < 3)
        candidates = levels[3][3]
        assert len(candidates) == (1,2,0,12)[case]
        if case == 2:
            continue
        for terms in range(1,7):
            d = by_case[case,terms]
            assert d['outcome'] == 'RUP_VERIFIED_UNSAT' and d['size'] == 14 and not d['unresolved']
            cases = d['cubes']
            for mask in candidates:
                repeat = tuple(i for i in range(11) if mask >> i & 1)
                prefix = ','.join(str(i) for i in repeat) + '/'
                if cases.get(prefix+'all',{}).get('verdict') == 'UNSAT':
                    expected = [('all',None)]
                else:
                    expected = [(f'{a},{b}',(a,b)) for a,b in combinations(repeat,2)]
                for suffix, pair in expected:
                    result = cases[prefix+suffix]
                    assert tuple(result['repeats']) == repeat and result['first'] == (list(pair) if pair else None)
                    assert result['case'] == case and result['size'] == 14 and result['terms'] == terms
                    assert result['verdict'] == 'UNSAT' and result['rup'] > 0
                    assert len(result['proof_sha256']) == 64
                    total += result['rup']
                    work.append((case,terms,repeat,pair))
    assert total == 6819075
    print(f'{len(work)} verified subproblems in manifest, {total:,} RUP additions; graph 2 is excluded analytically.',flush=True)
    return work


def run_case(job):
    case,terms,repeat,first = job
    with tempfile.TemporaryDirectory() as temp:
        path = Path(temp) / 'result.json'
        cmd = [sys.executable,str(ROOT/'terminal_synthesis.py'),str(case),'14',str(terms),
               '--repeat',*(str(i) for i in repeat),'--budget','450000','--out',str(path),'--verify']
        if first:
            cmd.extend(['--first', *(str(i) for i in first)])
        # A Windows PySAT native teardown can fail after completing a proof.
        # Only accept the source result if the solver and independent RUP
        # checker reached the success record and the proof itself exists.
        res=subprocess.run(cmd,capture_output=True,text=True)
        if not path.exists():
            raise RuntimeError(f'No proof result for {job}, exit {res.returncode}: {res.stderr[-500:]}')
        report=json.loads(path.read_text())
        if report['verdict']!='UNSAT' or not report.get('rup') or not path.with_suffix('.drat.gz').is_file():
            raise RuntimeError(f'Unverified subproblem {job}: {report}')
        return report['rup']


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--manifest-only',action='store_true')
    p.add_argument('--workers',type=int,default=3)
    args=p.parse_args()
    work=coverage()
    if not args.manifest_only:
        with ThreadPoolExecutor(max_workers=args.workers) as ex:
            counts=list(ex.map(run_case,work))
        print(f'All {len(work)} exact proofs regenerated and checked; {sum(counts):,} RUP additions.',flush=True)
