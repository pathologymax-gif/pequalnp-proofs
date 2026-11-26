"""Exact certificates for a sole shared raw OR on the quadrangle promise.

Run beside verify_plane_formula.py with Python 3.10+. No optimizer is used.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations

from verify_plane_formula import FLAGS, INF, LINES, SINGLETONS, STARS, quadrangle_data


# For each orbit representative: B, point count, line count, point private,
# line private transfer coefficients, and the expected lower-bound numerator.
CERTIFICATES = {
    (0, 1): (243, (0,69,967,972,952), (0,-8,-11,-11,-11),
             (-24,-6,111,102,111), (65,60,112,108,99), 59578),
    (13, 14): (223, (0,5,14,0,0), (0,64,890,892,883),
               (0,39,61,77,61), (-24,10,72,67,72), 54622),
    (0, 13): (326, (0,2,13,0,9,0), (0,6,2,0,0,16),
              (-82,137,97,166,155,155), (-91,131,128,192,169,117), 82989),
    (0, 15): (285, (0,1140,1128,1121,4,0), (0,-1140,-28,-1140,-16,-1128),
              (-28,-36,135,123,119,117), (0,174,156,146,118,95), 69744),
}


def verify_symmetries():
    generators = []
    for points in (tuple((p+1) % 13 for p in range(13)),
                   (0,1,2,3,10,11,7,6,12,9,4,5,8)):
        assert sorted(points) == list(range(13))
        lines = tuple(13 + LINES.index({points[p] for p in line}) for line in LINES)
        assert sorted(lines) == list(range(13,26))
        generators.append(points + lines)
    seen = set()
    for pair, expected in zip(CERTIFICATES, (78,78,52,117)):
        orbit, todo = {pair}, [pair]
        while todo:
            u,v = todo.pop()
            for perm in generators:
                image = tuple(sorted((perm[u],perm[v])))
                if image not in orbit:
                    orbit.add(image)
                    todo.append(image)
        assert len(orbit) == expected and seen.isdisjoint(orbit)
        seen.update(orbit)
    assert seen == set(combinations(range(26),2))


def distance(v,w):
    if v == w:
        return 0
    if (v < 13) == (w < 13):
        return 2
    p, line = sorted((v,w))
    return 1 if p in LINES[line-13] else 3


@lru_cache(None)
def families(required_rows):
    result = []
    for size in range(5):
        choices = [SINGLETONS] if size == 4 else combinations(range(1,16),size)
        for family in choices:
            covered, unions = 0,{0}
            for mask in family:
                covered |= mask
                unions.update([u|mask for u in unions if not u&mask])
            if required_rows & ~covered:
                continue
            private = sum(1<<i for i in range(4)
                          if all(i==j or any(m&(1<<j) and not m&(1<<i) for m in family)
                                 for j in range(4)))
            result.append((size,unions,private))
    return result


def pattern(v,m,support):
    available = support.isdisjoint(m)
    needed, optional = 0,0
    for k,edge in enumerate(STARS[v]):
        neighbor = edge[1] if v < 13 else edge[0]
        if available and not support.isdisjoint(edge):
            optional |= 1<<k
        elif neighbor in m:
            needed |= 1<<k
    return v in m, needed, optional


def menu(v,edge,patterns,tags,base,count_transfer,private_transfer):
    bit = 1<<STARS[v].index(edge)
    local = {}
    required = 0
    for excluded,needed,optional in set(patterns):
        required |= needed
        cost = {}
        for u in range(16):
            if (excluded and u) or (not excluded and needed&~u):
                continue
            cost[u] = (u&~optional).bit_count()
        local[excluded,needed,optional] = cost
    result = []
    for size,unions,private in families(required):
        minima = {}
        for pat,cost in local.items():
            off = on = INF
            for u in unions.intersection(cost):
                if u & bit:
                    on = min(on,cost[u])
                else:
                    off = min(off,cost[u])
            if min(off,on) == INF:
                break
            minima[pat] = off,on
        else:
            change = 0
            for j,f in enumerate(STARS[v]):
                delta = 4*int(edge==f)-1
                change += delta*(count_transfer[tags[f]]*size
                                 + private_transfer[tags[f]]*((private>>j)&1))
            result.append((base*size+change,tuple(minima[pat] for pat in patterns)))
    return result


def verify_support(pair,columns):
    support = set(pair)
    base,point_count,line_count,point_private,line_private,expected = CERTIFICATES[pair]
    def tag(e):
        return tuple(sorted((distance(e[0],s),distance(e[1],s)) for s in support))
    tag_types = sorted(set(map(tag,FLAGS)))
    tags = {e:tag_types.index(tag(e)) for e in FLAGS}
    assert all(len(x)==len(tag_types) for x in (point_count,line_count,point_private,line_private))
    required_area = sum(not(support.isdisjoint(m) and not support.isdisjoint(e))
                        for m in columns for e in FLAGS)
    patterns = [[pattern(v,m,support) for m in columns] for v in range(26)]
    total = 0
    for edge in FLAGS:
        p,l = edge
        groups = Counter(zip(patterns[p],patterns[l]))
        pm,lm = zip(*groups)
        bit = 1<<STARS[p].index(edge)
        weights = tuple((n,bool(pat[2]&bit)) for (pat,_),n in groups.items())
        left = menu(p,edge,pm,tags,base,point_count,point_private)
        right = menu(l,edge,lm,tags,base,line_count,line_private)
        best = None
        for lp,ps in left:
            for rl,ls in right:
                score = lp+rl
                for (p0,p1),(l0,l1),(n,optional) in zip(ps,ls,weights):
                    a = min(p0+l1,p1+l0)
                    if optional:
                        a = min(a,p0+l0)
                    if a >= INF:
                        break
                    score += n*a
                    if best is not None and score >= best:
                        break
                else:
                    best = score
        assert best is not None
        total += best
    numerator = total-4*required_area
    assert numerator == expected and numerator > 61*4*base
    return numerator,4*base,required_area


def main():
    if not __debug__:
        raise SystemExit("Run without -O so that the certificate assertions are checked.")
    verify_symmetries()
    columns = [m for m,_ in quadrangle_data()]
    for pair in CERTIFICATES:
        n,d,area = verify_support(pair,columns)
        print(f"{pair}: area {area}, ordinary leaves at least {n}/{d}, rounded up to {-(-n//d)}")
    print("All 325 raw OR pairs verified, with arbitrary fanout of the sole shared gate.")


if __name__ == "__main__":
    main()
