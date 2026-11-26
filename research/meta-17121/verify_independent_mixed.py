"""Rebuild the two private-formula frontiers and screen every residual pair."""
import argparse
from itertools import combinations
import json
from math import comb
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE=Path(__file__).resolve().parent
LEVEL=re.compile(r'cost (\d+) words (\d+) residual (\d+)')
SUMMARY=re.compile(r'through (\d+) total (\d+) comparable (\d+) cofactor (\d+) full (\d+) pending (\d+)')


def compile_source(temp,stem):
    folder=temp/stem
    folder.mkdir()
    source=HERE/(stem+'.cs')
    exe=folder/(stem+'.exe')
    classic=Path(os.environ.get('WINDIR','C:/Windows'))/'Microsoft.NET/Framework64/v4.0.30319/csc.exe'
    if classic.is_file():
        subprocess.run([classic,'/nologo','/optimize+',f'/out:{exe}',source],check=True)
        return [exe]
    if shutil.which('mcs') and shutil.which('mono'):
        subprocess.run(['mcs','-optimize+',f'-out:{exe}',source],check=True)
        return ['mono',exe]
    if not shutil.which('dotnet'):
        raise RuntimeError('Use a .NET SDK, Mono, or Windows .NET Framework compiler.')
    major=int(subprocess.check_output(['dotnet','--version'],text=True).split('.')[0])
    shutil.copyfile(source,folder/'Program.cs')
    (folder/(stem+'.csproj')).write_text('<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup>'
        f'<OutputType>Exe</OutputType><TargetFramework>net{major}.0</TargetFramework>'
        '</PropertyGroup></Project>')
    (folder/'NuGet.Config').write_text('<configuration><packageSources><clear/>'
                                      '</packageSources></configuration>')
    subprocess.run(['dotnet','build','-c','Release','-o','build'],cwd=folder,check=True)
    return ['dotnet',folder/'build'/(stem+'.dll')]


def graph_check(seed):
    assert len(seed)==11 and seed.count(0)==1 and all(type(w) is int and 0<=w<2**32 for w in seed)
    raw=[w for w in seed if w]
    probes=[frozenset(v for v,w in enumerate(raw) if w&(1<<j)) for j in range(32)]
    edges=set(probes[:14])
    assert len(edges)==14 and all(len(e)==2 for e in edges)
    maximal=set()
    for mask in range(1<<10):
        s=frozenset(v for v in range(10) if mask&(1<<v))
        if not any(e<=s for e in edges) and all(v in s or any(v in e and e&s for e in edges)
                                               for v in range(10)):
            maximal.add(s)
    assert maximal==set(probes[14:])-{frozenset()}
    assert max(map(len,maximal))==4


def run(row,seed,temp,frontier,screen):
    graph_check(seed)
    folder=temp/f'row-{row}'
    folder.mkdir()
    words=','.join(map(str,seed))
    subprocess.run([*frontier,words,folder],check=True)
    leftovers=folder/'leftovers.csv'
    report=subprocess.check_output([*screen,words,str(folder/'{0}.txt'),leftovers],text=True)
    residue={}
    summaries={}
    for line in report.splitlines():
        m=LEVEL.fullmatch(line)
        if m:
            cost,count,new=map(int,m.groups())
            assert cost not in residue and 0<=new<=count
            values=list(map(int,(folder/f'{cost}.txt').read_text().splitlines()))
            assert count==len(set(values))==len(values)
            residue[cost]=new
            continue
        m=SUMMARY.fullmatch(line)
        assert m,line
        cost,total,comparable,cofactor,full,pending=map(int,m.groups())
        assert cost not in summaries and pending==0 and total==comparable+cofactor+full
        summaries[cost]=(total,comparable,cofactor,full)
    assert set(residue)==set(summaries)==set(range(1,11))
    assert leftovers.read_bytes()==b''
    expected=0
    for g,n in sorted(residue.items()):
        # All nontrivial disjunctions with d gates use d+1 distinct vertices.
        expected+=n*sum(comb(10,d+1) for d in range(1,10) if g+d<=13)
        expected+=n*sum(residue[d] for d in range(1,g) if g+d<=13)
        if 2*g<=13:
            expected+=comb(n,2)
        assert summaries[g][0]==expected
    print(f'row {row}: {expected:,} pairs; {summaries[10][1]:,} dominance, '
          f'{summaries[10][2]:,} cofactor, {summaries[10][3]:,} full table.',flush=True)
    return expected


def main():
    if not __debug__:
        raise RuntimeError('Enable Python assertions.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--row',type=int,choices=range(4))
    args=parser.parse_args()
    seeds=json.loads((HERE/'seed_tables.json').read_text())
    assert len(seeds)==4
    with tempfile.TemporaryDirectory() as directory:
        tmp=Path(directory)
        front=compile_source(tmp,'SharedGateFrontier')
        screen=compile_source(tmp,'MixedHelperPairs')
        rows=[args.row] if args.row is not None else range(4)
        total=sum(run(i,seeds[i],tmp,front,screen) for i in rows)
    if args.row is None:
        assert total==291703443
        print(f'All {total:,} pairs excluded.')


if __name__=='__main__':
    main()
