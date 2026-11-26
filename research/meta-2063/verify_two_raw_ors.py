"""Replay integer lower bounds for two shared raw disjunctions in PG(2,3).

Run `python verify_two_raw_ors.py` next to two_raw_ors_certificates.json.gz
and verify_plane_formula.py. Python 3.10+ standard library only. Optional
integer arguments restrict the orbit indices for parallel replays.
"""
from collections import Counter, deque
from functools import cache
from itertools import combinations
from pathlib import Path
import gzip
import json
import sys

from verify_plane_formula import FLAGS, LINES, STARS, quadrangle_data


def orbit_data():
    generators=[]
    for points in [tuple((p+1)%13 for p in range(13)),(0,1,2,3,10,11,7,6,12,9,4,5,8)]:
        assert set(points)==set(range(13))
        lines=tuple(13+LINES.index({points[p] for p in line}) for line in LINES)
        generators.append(points+lines)
    pending=set(combinations(combinations(range(26),2),2)); out=[]
    while pending:
        root=min(pending); orbit={root}; queue=deque([root]); pending.remove(root)
        while queue:
            pairs=queue.popleft()
            for perm in generators:
                img=tuple(sorted(tuple(sorted(perm[t] for t in pair)) for pair in pairs))
                if img in orbit:continue
                pending.remove(img);orbit.add(img);queue.append(img)
        out.append((root,len(orbit)))
    assert len(out)==59 and sum(n for f,n in out)==52650
    return out


@cache
def union_families():
    # List possible row unions by enumerating every subfamily explicitly.
    best={}
    for size in range(5):
        choices=[(1,2,4,8)] if size==4 else combinations(range(1,16),size)
        for sets in choices:
            masks={0}
            for subsize in range(1,size+1):
                for sub in combinations(sets,subsize):
                    mask=0
                    for m in sub:
                        if m&mask:break
                        mask|=m
                    else:masks.add(mask)
            key=frozenset(masks)
            best[key]=min(size,best.get(key,5))
    return sorted((n,tuple(sorted(s))) for s,n in best.items()
                  if not any(s<t and m<=n for t,m in best.items()))


def check_local_state(proof,columns,free,cutoff=58):
    """Verify the lower bound on the supplied flag/column table with free(e,m)."""
    assert proof['mode']=='uniform'
    base,weight=proof['base'],proof['weight']
    assert type(base) is int and base>0 and type(weight) is int and weight>=0
    mandatory=sum(not free(e,m) for e in FLAGS for m in columns)
    states=[]; code=[]; pair_menu=[]; impossible=100
    for v,star in enumerate(STARS):
        patterns=[]
        for m in columns:
            forbidden=(15 if v in m else 0); needed=optional=0
            for i,e in enumerate(star):
                if free(e,m):optional|=1<<i
                elif any(x!=v and x in m for x in e):needed|=1<<i
            patterns.append((forbidden,needed,optional))
        types=sorted(set(patterns));ids={s:i for i,s in enumerate(types)}
        code.append(tuple(ids[s] for s in patterns))
        vs=[];menus=[]
        for n,unions in union_families():
            allowed=[[u for u in unions if not (u&forbidden or needed&~u)]
                     for forbidden,needed,optional in types]
            if any(not x for x in allowed):continue
            vs.append(n); by_flag=[]
            for i in range(4):
                by_pattern=[]
                for us,(_,_,optional) in zip(allowed,types):
                    vals=[impossible,impossible]
                    for u in us:
                        k=(u>>i)&1
                        vals[k]=min(vals[k],(u&~optional).bit_count())
                    by_pattern.append(tuple(vals))
                by_flag.append(by_pattern)
            menus.append(by_flag)
        states.append(vs);pair_menu.append(menus)
    vertex_score=[[base*n for n in ns] for ns in states]
    trans=proof['potentials'];assert len(trans)==len(FLAGS)
    edge_total=0
    for e,(point_t,line_t) in zip(FLAGS,trans):
        p,l=e;bp=STARS[p].index(e);bl=STARS[l].index(e)
        groups=Counter((code[p][s],code[l][s],free(e,m)) for s,m in enumerate(columns))
        for v,t in ((p,point_t),(l,line_t)):
            assert len(t)==len(states[v]) and all(type(x) is int for x in t)
            for i,potential in enumerate(t):vertex_score[v][i]+=potential
        best=None
        for ip,p_menus in enumerate(pair_menu[p]):
            left=p_menus[bp]
            for il,l_menus in enumerate(pair_menu[l]):
                value=-point_t[ip]-line_t[il]
                if best is not None and value>=best:continue
                right=l_menus[bl]
                for (i,j,is_optional),mult in groups.items():
                    p0,p1=left[i]; l0,l1=right[j]; local=min(p0+l1,p1+l0)
                    if is_optional:local=min(local,p0+l0)
                    if local>=impossible:break
                    value+=weight*mult*local
                    if best is not None and value>=best:break
                else:best=value
        assert best is not None
        edge_total+=best
    num=sum(min(s) for s in vertex_score)+edge_total-4*weight*mandatory
    assert num==proof['numerator'] and num>cutoff*base,(num,base,cutoff)
    return num,base


def check(family,proof,columns):
    assert proof['family']==[list(x) for x in family]
    def free(e,m):
        return any((v in e or w in e) and v not in m and w not in m for v,w in family)
    return check_local_state(proof,columns,free,cutoff=59)


def main():
    corpus=Path(__file__).with_name('two_raw_ors_certificates.json.gz')
    proofs=json.loads(gzip.decompress(corpus.read_bytes()))
    orbits=orbit_data();assert len(proofs)==len(orbits)
    columns=[m for m,w in quadrangle_data()]
    indices=list(map(int,sys.argv[1:])) or list(range(len(orbits)))
    for i in indices:
        family,count=orbits[i]
        num,den=check(family,proofs[i],columns)
        print(f'{i}: {family}, {count} labeled pairs, {num}/{den}',flush=True)
    print(f'Checked {len(indices)} orbits, {sum(orbits[i][1] for i in indices)} labeled pairs.')


if __name__=='__main__':main()
