"""Replay three or more independent shared OR-tree exclusions, using Python and C#."""
from collections import Counter
from functools import reduce
import gzip
from itertools import combinations
import json
import operator
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from verify_kw_first_shared import check_tree

HERE = Path(__file__).resolve().parent
TARGET = (1 << 14) - 1
SUMMARY = re.compile(r'r=(\d+) t=(\d+) families=(\d+) degree=(\d+) all-one hull=(\d+) '
                     r'full hull=(\d+) remaining=(\d+)')


def compiler(tmp, name='ManyOrTrees'):
    source = HERE/f'{name}.cs'
    desktop = Path(os.environ.get('WINDIR','C:/Windows'))/'Microsoft.NET/Framework64/v4.0.30319/csc.exe'
    program = tmp/f'{name}.exe'
    if desktop.exists():
        subprocess.run([desktop,'/nologo','/optimize+',f'/out:{program}',source],check=True)
        return [program]
    if shutil.which('mcs') and shutil.which('mono'):
        subprocess.run(['mcs','-optimize+',f'-out:{program}',source],check=True)
        return ['mono',program]
    major = int(subprocess.check_output(['dotnet','--version'],text=True).split('.')[0])
    shutil.copyfile(source,tmp/'Program.cs')
    (tmp/f'{name}.csproj').write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
        f'<OutputType>Exe</OutputType><TargetFramework>net{major}.0</TargetFramework>'
        '</PropertyGroup></Project>')
    (tmp/'NuGet.Config').write_text('<configuration><packageSources><clear/></packageSources></configuration>')
    subprocess.run(['dotnet','build','-c','Release','-o','build'],cwd=tmp,check=True)
    return ['dotnet',tmp/f'build/{name}.dll']


def graph_check(words):
    tests = [frozenset(v for v,w in enumerate(words) if w & (1 << j)) for j in range(32)]
    edges = set(tests[:14])
    assert len(words) == 10 and len(edges) == 14 and all(len(e) == 2 for e in edges)
    neighbors = [{u for u in range(10) if frozenset((u,v)) in edges} for v in range(10)]
    assert all(len(n) >= 2 for n in neighbors)
    assert all(len(x & y) <= 1 for x,y in combinations(neighbors,2))
    maximal = set()
    for mask in range(1 << 10):
        s = frozenset(v for v in range(10) if mask & (1 << v))
        if not any(e <= s for e in edges) and all(v in s or neighbors[v] & s for v in range(10)):
            maximal.add(s)
    assert maximal == set(tests[14:]) - {frozenset()}


def counts_by_cost(r, max_t):
    # Coefficients of the support-set generating function; independent of
    # the low-cost-family recursion in the C# program.
    dp = Counter({(0,0):1})
    for mask in range(1,1 << 10):
        extra = mask.bit_count() - 2
        if extra < 0 or extra > max_t:
            continue
        for (i,t),n in list(dp.items()):
            if i < r and t+extra <= max_t:
                dp[i+1,t+extra] += n
    return {t:dp[r,t] for t in range(1,max_t+1)}


def check(tmp,command,rows,proofs):
    needed = set()
    total = leaves = 0
    for row,seed in enumerate(rows):
        inputs = [w for w in seed if w]
        graph_check(inputs)
        for r,max_t in ((3,6),(4,2)):
            outfile = tmp/f'pending-{row}-{r}.txt'
            output = subprocess.check_output([*command,','.join(map(str,seed)),str(r),outfile],text=True)
            expected = counts_by_cost(r,max_t)
            pending = 0
            for line in output.splitlines():
                match = SUMMARY.fullmatch(line)
                assert match, line
                k,t,number,degree,cofactor,hull,remain = map(int,match.groups())
                assert k == r and number == expected.pop(t) == degree+cofactor+hull+remain
                total += number
                pending += remain
            assert not expected
            cases = outfile.read_text().splitlines()
            assert len(cases) == pending == len(set(cases))
            for line in cases:
                key = f'{row}:{line}'
                supports = list(map(int,line.split(',')))
                assert len(supports) == r == len(set(supports))
                q = sum(s.bit_count()-1 for s in supports)
                helper = [reduce(operator.or_,(w for v,w in enumerate(inputs) if s & (1 << v)))
                          for s in supports]
                fixed,tree = proofs[key]
                assert len(fixed) == len(set(fixed)) and all(type(i) is int and 0<=i<r for i in fixed)
                keep = reduce(operator.and_,(TARGET | helper[i] for i in fixed),(1 << 32)-1)
                table = [w & keep for w in inputs+[h for i,h in enumerate(helper) if i not in fixed]]
                leaves += check_tree(table,tree,19-q-2*len(fixed))
                needed.add(key)
            print(f'row {row}, {r} helpers: {len(cases)} residual families, all certificates verified',flush=True)
    assert set(proofs) == needed and total == 158630660
    print(f'{total} support families, {len(needed)} residuals, {leaves} integer-dual leaves.')


if __name__ == '__main__':
    if not __debug__:
        raise RuntimeError('Enable Python assertions.')
    rows = json.loads((HERE/'seed_tables.json').read_text())
    proofs = json.loads(gzip.decompress((HERE/'many_or_trees.json.gz').read_bytes()))
    assert len(rows) == 4
    with tempfile.TemporaryDirectory() as directory:
        tmp = Path(directory)
        check(tmp,compiler(tmp),rows,proofs)
