"""Replay all sole shared pure-disjunction cases on the quadrangle promise."""

import json
from itertools import combinations
from pathlib import Path

from verify_plane_formula import LINES, quadrangle_data
from verify_raw_shared_gate import CERTIFICATES, verify_support, verify_symmetries, verify_weighted


def permutations():
    for points in (tuple((v+1)%13 for v in range(13)),
                   (0,1,2,3,10,11,7,6,12,9,4,5,8)):
        assert set(points)==set(range(13))
        mapped = tuple(13+LINES.index({points[v] for v in line}) for line in LINES)
        assert set(mapped)==set(range(13,26))
        yield points+mapped


def orbit(support,gens):
    complete,todo = {support},[support]
    while todo:
        subset = todo.pop()
        for perm in gens:
            image = tuple(sorted(perm[v] for v in subset))
            if image not in complete:
                complete.add(image)
                todo.append(image)
    return complete


def main():
    if not __debug__:
        raise SystemExit("Run without -O so the certificate assertions are checked.")
    columns = [m for m,_ in quadrangle_data()]
    verify_symmetries()
    for pair in CERTIFICATES:
        n,d,_ = verify_support(pair,columns)
        assert n>61*d
    data = json.loads(Path(__file__).with_name("shared_disjunction_certificates.json").read_text())
    gens = tuple(permutations())
    full,cofactors = {},{}
    for cert in data:
        support = tuple(cert["support"])
        assert support == tuple(sorted(set(support)))
        assert len(support) in (3,4) and all(0<=v<26 for v in support)
        assert cert["mode"] in ("full","cofactor")
        cofactor = cert["mode"]=="cofactor"
        keys = ("base","point_count","line_count","point_private","line_private","row_weights")
        params = [cert[k] for k in keys]
        assert type(params[0]) is int and params[0]>0
        assert all(type(x) is int for row in params[1:] for x in row)
        n,d,_ = verify_weighted(support,columns,*params,cofactor=cofactor)
        assert n==cert["numerator"]
        bound = -(-n//d)
        table = cofactors if cofactor else full
        images = orbit(support,gens)
        for s in images:
            table[s] = max(table.get(s,0),bound)
        print(f"{cert['mode']} {support}: {len(images)} images, ordinary leaves >= {bound}",flush=True)
    for k in (3,4,5):
        count = 0
        for support in combinations(range(26),k):
            # A cofactor may be applied to every larger support, a full test only to itself.
            best = full.get(support,0) if k==3 else 0
            for j in range(3,min(4,k)+1):
                best = max(best,max(cofactors.get(s,0) for s in combinations(support,j)))
            assert best+k>=64, (support,best)
            count += 1
        print(f"All {count} subsets of size {k} verified.",flush=True)
    print("Every support of size >=5 contains a certified size-five subset.")
    print("All 67,108,837 supports of size >=2 require at least 64 gates.")


if __name__=="__main__":
    main()
