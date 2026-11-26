"""Verify all mixed private formula orbits through four gates and the deleted-path certificate."""
import argparse
from collections import Counter,deque
from functools import cache,reduce
from itertools import combinations
import json
from math import comb
from operator import and_,or_
from pathlib import Path
from verify_plane_formula import FLAGS,LINES,quadrangle_data

HERE=Path(__file__).resolve().parent
TARGET=(1<<52)-1
COLS=[s for s,_ in quadrangle_data()]
SEEDS=[sum(1<<j for j,e in enumerate(list(FLAGS)+COLS) if v in e) for v in range(26)]
NEGATIVE=sum(1<<j for j in range(52,52+len(COLS)))
RAW_INCIDENCE=[w&TARGET for w in SEEDS]


def symmetries():
    gens=[]
    for pp in (tuple((i+1)%13 for i in range(13)),(0,1,2,3,10,11,7,6,12,9,4,5,8)):
        lines=tuple(13+LINES.index(frozenset(pp[i] for i in l)) for l in LINES)
        gens.append(pp+lines)
    for p in gens:
        assert sorted(p)==list(range(26))
        assert {(p[a],p[b]) for a,b in FLAGS}==set(FLAGS)
        assert {frozenset(p[v] for v in c) for c in COLS}==set(COLS)
    identity=tuple(range(26))
    group={identity}
    todo=deque([identity])
    while todo:
        perm=todo.popleft()
        for gen in gens:
            q=tuple(gen[v] for v in perm)
            if q not in group:
                group.add(q)
                todo.append(q)
    assert len(group)==5616
    return gens,list(group)


def support_orbits(k,gens):
    seen=set()
    for s in combinations(range(26),k):
        if s in seen:
            continue
        seen.add(s)
        queue=[s]
        while queue:
            t=queue.pop()
            for gen in gens:
                u=tuple(sorted(gen[v] for v in t))
                if u not in seen:
                    seen.add(u)
                    queue.append(u)
        yield s


@cache
def functions(k):
    atoms=[sum(1<<m for m in range(1<<k) if m&(1<<j)) for j in range(k)]
    levels=[set(atoms)]
    known=set(atoms)
    results=[]
    for g in range(1,5):
        new=set()
        for a in range((g-1)//2+1):
            b=g-1-a
            for x in levels[a]:
                for y in levels[b]:
                    new.update((x&y,x|y))
        new-=known
        levels.append(new)
        known|=new
        for f in sorted(new):
            mins=tuple(m for m in range(1,1<<k) if (f>>m)&1 and all(
                not (f>>(m^(1<<j)))&1 for j in range(k) if m&(1<<j)))
            if reduce(or_,mins,0)!=(1<<k)-1:
                continue
            results.append((g,mins))
    return results


@cache
def cover(m):
    if not m:
        return 0
    e=(m&-m).bit_length()-1
    return 1+min(cover(m&~RAW_INCIDENCE[v]) for v in FLAGS[e])


def permutations(s,group):
    where={v:j for j,v in enumerate(s)}
    stabilizer={tuple(where[p[v]] for v in s) for p in group if all(p[v] in where for v in s)}
    return [[sum(1<<perm[j] for j in range(len(s)) if m&(1<<j)) for m in range(1<<len(s))]
            for perm in stabilizer]


def normalize(word,cost):
    positive=word&TARGET
    if not positive or positive==TARGET or not word&NEGATIVE:
        return 'one-sided'
    if positive.bit_count()+cover(positive)-2<=cost:
        return 'zero'
    allowed=[w for w in SEEDS if not (w&NEGATIVE&~word)]
    for size in range(1,min(len(allowed),cost+1)+1):
        for subset in combinations(allowed,size):
            lost=positive&~reduce(or_,subset)
            if size-1+lost.bit_count()+cover(lost)<=cost:
                return f'OR{size}'
    return None


def certify_p4(group,survivors):
    from verify_raw_shared_gate import verify_weighted
    support={1,2,13,14}
    path=frozenset(e for e in FLAGS if set(e)<=support)
    assert len(path)==3
    orbits={frozenset((p[a],p[b]) for a,b in path) for p in group}
    assert len(orbits)==52*3*3
    for s,cost,mins,word in survivors:
        assert cost==4
        singleton,=[s[m.bit_length()-1] for m in mins if m.bit_count()==1]
        w=int(word)
        assert not SEEDS[singleton]&NEGATIVE&~w
        lost=(w&~SEEDS[singleton])&TARGET
        assert frozenset(e for j,e in enumerate(FLAGS) if (lost>>j)&1) in orbits
    c=json.loads((HERE/'mixed_four_p4_certificate.json').read_text())
    num,den,area=verify_weighted(support,COLS,c['base'],c['point_count'],c['line_count'],
        c['point_private'],c['line_private'],c['area_weights'],helper_optional=lambda e,m:e in path)
    assert (num,den,area)==(c['numerator'],c['denominator'],c['area'])
    assert num>60*den
    print(f'{len(orbits)} deleted paths, exact leaf bound {num}/{den}.',flush=True)


def main():
    if not __debug__:
        raise RuntimeError('Enable Python assertions.')
    args=argparse.ArgumentParser(description=__doc__)
    args.add_argument('--dump-residuals',type=Path)
    opts=args.parse_args()
    gens,group=symmetries()
    stats=Counter()
    survivors=[]
    for k in range(2,6):
        seen=Counter()
        for s in support_orbits(k,gens):
            orbit_size=len({tuple(sorted(p[v] for v in s)) for p in group})
            atoms=[SEEDS[v] for v in s]
            and_words=[reduce(and_,(w for j,w in enumerate(atoms) if m&(1<<j)),TARGET|NEGATIVE)
                       for m in range(1<<k)]
            action=permutations(s,group)
            for cost,mins in functions(k):
                images={tuple(sorted(a[m] for m in mins)) for a in action}
                if mins!=min(images):
                    continue
                seen[cost]+=orbit_size*len(images)
                pure=all(m.bit_count()==1 for m in mins)
                if pure:
                    stats[cost,'pure OR']+=1
                    continue
                word=reduce(or_,(and_words[m] for m in mins),0)
                witness=normalize(word,cost)
                stats[cost,witness or 'residual']+=1
                if witness is None:
                    survivors.append([s,cost,mins,str(word)])
        expected=Counter(g for g,_ in functions(k))
        assert seen==Counter({g:comb(26,k)*n for g,n in expected.items()})
    print('group',len(group))
    for key,n in sorted(stats.items(),key=lambda x:str(x[0])):
        print(key,n)
    print('residuals',len(survivors),flush=True)
    assert len(survivors)==6
    assert all(n==0 or tag in {'pure OR','one-sided','zero','OR1','OR2','OR3','residual'}
               for (_,tag),n in stats.items())
    certify_p4(group,survivors)
    if opts.dump_residuals:
        opts.dump_residuals.write_text(json.dumps(survivors,separators=(',',':')))


if __name__=='__main__':
    main()
