"""Check the ordinary-formula lower bounds for multiple shared gates."""

import json
from itertools import combinations
from pathlib import Path

from verify_plane_formula import LINES, quadrangle_data
from verify_raw_shared_gate import verify_weighted
from verify_shared_disjunctions import permutations, orbit


def main():
    if not __debug__:
        raise SystemExit("Run without -O so the certificate assertions are checked.")
    columns = [m for m,_ in quadrangle_data()]
    gens = tuple(permutations())
    tables = {}
    # The six earlier singleton-triple cofactor cases already contain coefficients.
    for filename in ("common_singleton_certificates.json","shared_disjunction_certificates.json"):
        records = json.loads(Path(__file__).with_name(filename).read_text())
        for cert in records:
            s = tuple(cert["support"])
            if cert["mode"] != "cofactor" or len(s)>3:
                continue
            keys = ("base","point_count","line_count","point_private","line_private","row_weights")
            params = [cert[k] for k in keys]
            assert type(params[0]) is int and params[0]>0
            assert all(type(x) is int for row in params[1:] for x in row)
            n,d,_ = verify_weighted(s,columns,*params,cofactor=True)
            assert n==cert["numerator"]
            bound = -(-n//d)
            for image in orbit(s,gens):
                tables[image] = max(tables.get(image,0),bound)
            print(f"{s}: {n}/{d}, at least {bound} ordinary leaves",flush=True)
    assert set(tables)=={s for k in (1,2,3) for s in combinations(range(26),k)}
    assert all(tables[(p,)]==44 for p in range(13))
    assert all(tables[(l,)]==43 for l in range(13,26))
    for a,b in combinations(range(26),2):
        expected = 58 if b<13 else 57
        if a<13<=b and a in LINES[b-13]:
            expected = 60
        assert tables[a,b]==expected
    assert [min(v for s,v in tables.items() if len(s)==k) for k in (1,2,3)]==[43,57,59]
    print("Cofactor lower bounds cover all 26 singletons, 325 pairs and 2,600 triples.")


if __name__=="__main__":
    main()
