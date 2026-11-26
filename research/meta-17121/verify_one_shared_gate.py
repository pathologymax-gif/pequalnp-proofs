"""Replay the one-shared-gate exclusions with integer arithmetic and a C# compiler."""
import argparse
import base64
from collections import Counter
from functools import cache
import gzip
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
from zipfile import ZipFile
import zlib
from verify_kw_formulas import verify as verify_base_formula

HERE = Path(__file__).resolve().parent
TARGET = (1 << 14) - 1
SCALE = 100000


def build_frontier_tool(directory):
    """Use the local .NET Framework, Mono, or .NET SDK without external packages."""
    source = HERE / 'SharedGateFrontier.cs'
    win = Path(os.environ.get('WINDIR', 'C:/Windows')) / 'Microsoft.NET/Framework64/v4.0.30319/csc.exe'
    exe = directory / 'Frontier.exe'
    if win.is_file():
        subprocess.run([win, '/nologo', '/optimize+', f'/out:{exe}', source], check=True)
        return [exe]
    if shutil.which('mcs') and shutil.which('mono'):
        subprocess.run(['mcs', '-optimize+',f'-out:{exe}',source],check=True)
        return ['mono',exe]
    if shutil.which('dotnet'):
        version = subprocess.check_output(['dotnet','--version'],text=True).strip().split('.')[0]
        shutil.copyfile(source,directory/'Program.cs')
        (directory/'Frontier.csproj').write_text(
            '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType>'
            f'<TargetFramework>net{int(version)}.0</TargetFramework></PropertyGroup></Project>')
        (directory/'NuGet.Config').write_text('<configuration><packageSources><clear/>'
                                             '</packageSources></configuration>')
        subprocess.run(['dotnet','build','-c','Release','-o','build'],cwd=directory,check=True)
        return ['dotnet',directory/'build/Frontier.dll']
    raise RuntimeError('The exhaustive formula recurrence requires a C# compiler. Use .NET SDK or Mono.')


def cell_masks(words):
    return [tuple(i for i,w in enumerate(words) if w >> j & 1) for j in range(32)]


def exterior_screen(seed):
    edges = cell_masks(seed)[:14]
    incident = [[] for _ in seed]
    for e,(v,w) in enumerate(edges):
        incident[v].append((e, seed[w] & ~TARGET))
        incident[w].append((e, seed[v] & ~TARGET))

    @cache
    def cover_number(edge_mask):
        if edge_mask == 0:
            return 0
        first = (edge_mask & -edge_mask).bit_length()-1
        u,v = edges[first]
        return 1+min(cover_number(edge_mask & ~seed[u]),cover_number(edge_mask & ~seed[v]))

    def leaf_bound(helper):
        if helper & TARGET == 0 or helper & ~TARGET == 0 or TARGET & ~helper == 0:
            return 100  # Eliminated semantically by the constant and cut arguments.
        forced_rows,forced_columns = [],[]
        for star in incident:
            rows = columns = 0
            for e,negative_tests in star:
                witnesses = negative_tests & helper if helper >> e & 1 else negative_tests
                if witnesses:
                    rows |= 1 << e
                    columns |= witnesses
            forced_rows.append(rows)
            forced_columns.append(columns)
        conflicts = sum(1 << e for e,(v,w) in enumerate(edges)
                        if forced_rows[v] & forced_rows[w] and forced_columns[v] & forced_columns[w])
        return 2 + sum(bool(x) for x in forced_rows) + cover_number(conflicts)

    return leaf_bound


def replay_duals(words,tree,limit):
    """Regenerate the rectangle incidence and check each leaf by integer weak duality."""
    tests = cell_masks(words)
    rows,columns=tests[:14],sorted(set(tests[14:]) - {()})
    n_cells=len(rows)*len(columns)
    rectangles=[]
    for label in range(len(words)):
        hits=[i for i,row in enumerate(rows) if label in row]
        for mask in range(1,1<<len(hits)):
            rectangles.append((label,[r for j,r in enumerate(hits) if mask >> j & 1]))
    uses=[(y,[r*len(columns)+j for r in rowset]) for y,(label,rowset) in enumerate(rectangles)
          for j,column in enumerate(columns) if label not in column]
    ny,nz=len(rectangles),len(uses)
    low=[0]*(ny+nz+n_cells)
    high=[1]*len(low)

    def check(node):
        if isinstance(node,list):
            assert len(node)==3
            j,left,right=node
            assert type(j) is int and 0<=j<ny+nz and (low[j],high[j])==(0,1)
            for bit,child in enumerate((left,right)):
                low[j]=high[j]=bit
                check(child)
            low[j],high[j]=0,1
            return
        assert isinstance(node,str)
        dual=json.loads(zlib.decompress(base64.b64decode(node,validate=True)))
        assert len(dual)==n_cells+nz and all(type(x) is int for x in dual)
        assert all(x<=0 for x in dual[n_cells:])
        reduced=[SCALE]*ny+[0]*nz+[32*SCALE-dual[j] for j in range(n_cells)]
        for k,(y,hit) in enumerate(uses):
            lam=dual[n_cells+k]
            reduced[y]+=lam
            reduced[ny+k]-=lam+sum(dual[cell] for cell in hit)
        lower=sum(dual[:n_cells])+sum(min(cost*a,cost*b) for cost,a,b in zip(reduced,low,high))
        assert lower>limit*SCALE
    check(tree)


def run(row,seed,archive,folder,tool):
    work=folder/f'row{row}'
    work.mkdir()
    subprocess.run([*tool,','.join(map(str,seed)),work],check=True)
    test=exterior_screen(seed)
    free=seed.index(0)
    counts=Counter()
    for cost in range(1,12):
        masks=list(map(int,(work/f'{cost}.txt').read_text().splitlines()))
        assert len(masks)==len(set(masks))
        counts['masks']+=len(masks)
        selected={str(w) for w in masks if test(w)<=19-cost}
        saved=json.loads(gzip.decompress(archive.read(f'kw_helpers_r{row}_g{cost}.json.gz')))
        assert set(saved)==selected
        for word,(method,result) in saved.items():
            h=int(word)
            assert set(result)=={'tree'}
            if method=='full':
                words=seed.copy()
                words[free]=h
                limit=19-cost
            else:
                assert method=='cofactor1'
                words=[v & (TARGET | h) for v in seed]
                limit=17-cost
            replay_duals(words,result['tree'],limit)
            counts[method]+=1
    print(f'row {row}: {counts["masks"]} helper masks, {counts["full"]} full and '
          f'{counts["cofactor1"]} cofactor exclusions',flush=True)


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Run Python with assertions enabled.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--row',type=int,choices=range(4))
    args=parser.parse_args()
    seeds=json.loads((HERE/'seed_tables.json').read_text())
    base=json.loads(gzip.decompress((HERE/'kw_formula_certificates.json.gz').read_bytes()))
    assert len(seeds)==len(base)==4
    with tempfile.TemporaryDirectory() as tmp, ZipFile(HERE/'one_shared_gate_certificates.zip') as archive:
        temp=Path(tmp)
        command=build_frontier_tool(temp)
        for i in ([args.row] if args.row is not None else range(4)):
            verify_base_formula(seeds[i],base[i])
            run(i,seeds[i],archive,temp,command)
