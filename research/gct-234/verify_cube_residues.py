"""Check the three necessary cubic discriminants on normalized residue pairs."""
import argparse
from itertools import combinations
from math import isqrt, prod

import numpy as np


def nodes(pair, p):
    a, b = pair
    return tuple((3 * a + j * (b - a)) % p for j in range(4))


def discriminant(q, p):
    a, b, c, d = q
    h = (b*c-a*d) % p
    j = (b*b-a*c) % p
    k = (c*c-b*d) % p
    return (h*h-4*j*k) % p


def projective_test(triple, p):
    """Each nonzero real numerator L annihilates six binary quadratics."""
    equations = []
    for i, group in enumerate(triple):
        outside = triple[(i+1)%3] + triple[(i+2)%3]
        weights = [prod(s-x for x in outside) % p for s in group]
        for j in (0, 1):
            x,y,z = group[j:j+3]
            u,v,w = weights[j:j+3]
            row = ((u*w - v*v) % p,
                   (2*y*u*w - (x+z)*v*v) % p,
                   (y*y*u*w - x*z*v*v) % p)
            a,b,c = row
            for d,e,f in equations:
                if ((a*f-c*d)**2 - (a*e-b*d)*(b*f-c*e)) % p:
                    return False
            equations.append(row)
    return True


def nontrivial(p):
    if not 11 <= p <= 251 or any(p % i == 0 for i in range(2, isqrt(p) + 1)):
        raise ValueError("Use a prime between 11 and 251.")
    pairs = list(combinations(range(p), 2))
    blocks = np.array([nodes(pair, p) for pair in pairs], dtype=np.int64)
    base = blocks[0]
    faces = np.ones((len(blocks), 4), dtype=np.int64)
    collision = np.zeros(len(blocks), dtype=np.int64)
    for e in blocks.T:
        diff = base - e[:, None]
        faces = (faces * diff) % p
        collision += (diff == 0).sum(axis=1)
    candidates = np.flatnonzero(collision <= 1)
    unique = double = first_pass = disc_pass = 0
    survivors = []
    for offset, i in enumerate(candidates):
        later = candidates[offset+1:]
        if not len(later):
            continue
        matches = collision[i] + collision[later]
        for x in blocks[i]:
            matches += (blocks[later] == x).sum(axis=1)
        unique += np.count_nonzero(matches == 0)
        double += np.count_nonzero(matches == 1)
        later = later[matches <= 1]
        later = later[discriminant(((faces[i] * faces[later]) % p).T, p) == 0]
        first_pass += len(later)
        for j in later:
            triple = (tuple(map(int,base)),tuple(map(int,blocks[i])),tuple(map(int,blocks[j])))
            if all(discriminant([prod(z-x for group in (triple[(k+1)%3], triple[(k+2)%3])
                                         for x in group) % p for z in triple[k]], p) == 0
                   for k in (1,2)):
                disc_pass += 1
                if projective_test(triple, p):
                    survivors.append((pairs[i], pairs[j]))
    print(f"p={p} | 11 nodes={double} | 12 nodes={unique} | first zero={first_pass} | "
          f"three zeros={disc_pass} | all pairwise resultants zero={len(survivors)}",flush=True)
    return survivors


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("primes", type=int, nargs="+")
    parser.add_argument("--show", action="store_true")
    args = parser.parse_args()
    for prime in args.primes:
        survivors = nontrivial(prime)
        if args.show:
            print(survivors[:20], flush=True)
