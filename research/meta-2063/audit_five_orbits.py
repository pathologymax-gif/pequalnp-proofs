"""Independently audit the orbit enumeration and 64 five-gate helper records."""
from collections import Counter
from functools import cache
from itertools import combinations
import json
from math import comb
from pathlib import Path

from mixed_five_orbits import functions, support_orbits, symmetries
from verify_plane_formula import FLAGS,quadrangle_data

HERE=Path(__file__).resolve().parent
POS=(1<<len(FLAGS))-1
PROBES=[frozenset(e) for e in FLAGS]+[m for m,_ in quadrangle_data()]
NEG=((1<<len(PROBES))-1)^POS
RAW=[sum(1<<i for i,s in enumerate(PROBES) if v in s) for v in range(26)]
REVERSE=[int(f'{i:08b}'[::-1],2) for i in range(256)]


def exact_five_functions(k):
    """Compute AND closures by leaf count and derive ORs by Boolean duality."""
    width=1<<k
    size=(width+7)//8
    all_bits=(1<<width)-1
    @cache
    def dual(word):
        reversed_value=0
        for byte in word.to_bytes(size,'little'):
            reversed_value=(reversed_value<<8)|REVERSE[byte]
        return all_bits^(reversed_value>>(8*size-width))
    atoms={sum(1<<x for x in range(width) if x&(1<<j)) for j in range(k)}
    by_leaves=[set(),atoms]
    for leaves in range(2,7):
        at_most=set(by_leaves[-1])
        for left in range(1,leaves//2+1):
            for a in by_leaves[left]:
                for b in by_leaves[leaves-left]:
                    ab=a&b
                    at_most.add(ab)
                    at_most.add(dual(ab))
        by_leaves.append(at_most)
    result={}
    for word in by_leaves[6]-by_leaves[5]:
        mins=tuple(x for x in range(1,width) if word&(1<<x) and all(
            not (word&(1<<(x^bit))) for bit in (1<<j for j in range(k)) if bit&x))
        if set(j for m in mins for j in range(k) if m&(1<<j))==set(range(k)):
            result[mins]=word
    assert set(result)=={m for g,m in functions(k) if g==5}
    return result


@cache
def maximum_matching(positive):
    # A maximum matching equals the minimum vertex cover of a bipartite graph.
    adjacency=[[] for _ in range(13)]
    for i,(a,b) in enumerate(FLAGS):
        if positive&(1<<i):
            adjacency[a].append(b-13)
    endpoint=[-1]*13
    def augment(point,used):
        for line in adjacency[point]:
            if line in used:
                continue
            used.add(line)
            if endpoint[line]<0 or augment(endpoint[line],used):
                endpoint[line]=point
                return True
        return False
    return sum(augment(p,set()) for p in range(13))


def reduction(word):
    p=word&POS
    if not p or p==POS or not word&NEG:
        return 'one-sided'
    if p.bit_count()+maximum_matching(p)<=7:
        return 'zero'
    eligible=[w for w in RAW if not w&NEG&~word]
    for n in range(1,min(6,len(eligible))+1):
        for selected in combinations(eligible,n):
            lost=p
            for x in selected:
                lost &= ~x
            if n-1+lost.bit_count()+maximum_matching(lost)<=5:
                return f'OR{n}'
    return 'residual'


def audit():
    gens,group=symmetries()
    flags=set(PROBES[:52])
    negatives=set(PROBES[52:])
    for gen in gens:
        assert {frozenset(gen[v] for v in e) for e in flags}==flags
        assert {frozenset(gen[v] for v in s) for s in negatives}==negatives
    records=json.loads((HERE/'mixed_five_orbits.json').read_text())
    expected={(tuple(s),tuple(mins),int(w)) for s,g,mins,w in records if g==5}
    assert len(records)==len(expected)==64
    found=set()
    stats=Counter()
    labeled=0
    for k in range(2,7):
        funcs=exact_five_functions(k)
        supports_seen=set()
        weighted=0
        for s in support_orbits(k,gens):
            support_set=set(s)
            orbit={tuple(sorted(p[v] for v in s)) for p in group}
            assert supports_seen.isdisjoint(orbit)
            supports_seen.update(orbit)
            stabilizer={tuple(s.index(p[v]) for v in s) for p in group if all(p[v] in support_set for v in s)}
            actions=[[sum(1<<pi[i] for i in range(k) if m&(1<<i)) for m in range(1<<k)]
                     for pi in stabilizer]
            projections=[0]*(1<<k)
            for j,probe in enumerate(PROBES):
                projections[sum(1<<i for i,v in enumerate(s) if v in probe)] |= 1<<j
            functions_seen=set()
            for mins in funcs:
                if mins in functions_seen:
                    continue
                images={tuple(sorted(a[m] for m in mins)) for a in actions}
                assert images<=funcs.keys() and functions_seen.isdisjoint(images)
                functions_seen.update(images)
                weighted+=len(orbit)*len(images)
                rep=min(images)
                if all(m.bit_count()==1 for m in rep):
                    stats['pure OR']+=1
                    continue
                truth=funcs[rep]
                projected=0
                while truth:
                    bit=truth&-truth
                    projected |= projections[bit.bit_length()-1]
                    truth ^= bit
                tag=reduction(projected)
                stats[tag]+=1
                if tag=='residual':
                    found.add((s,rep,projected))
            assert functions_seen==funcs.keys()
        assert len(supports_seen)==comb(26,k)
        assert weighted==comb(26,k)*len(funcs)
        labeled+=weighted
        print(f'support {k}: {len(funcs)} functions on a fixed support, {weighted:,} labeled.',flush=True)
    assert found==expected
    print(f'{labeled:,} labeled functions, orbit counts {dict(stats)}, all 64 residual records verified.')
    return stats


if __name__=='__main__':
    if not __debug__:
        raise RuntimeError('Enable Python assertions.')
    audit()
