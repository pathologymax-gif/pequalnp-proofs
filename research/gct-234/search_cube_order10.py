"""Exact necessary-condition sieve for order >=10 in three real binomial cubes.

Use python search_cube_order10.py --degree 45. Requires NumPy. Each original
binomial has nonzero endpoints x^a, x^b with 0<=a<b<=degree. Remove the common
monomial factor and order blocks lexicographically, so a of block 1 equals 0.
Zero/single-term blocks and triples with at most 10 distinct output exponents
are already impossible by the sparse support bound. The remaining triples must
satisfy a certain explicit integer quartic identity at each of the three
blocks. Nonzero modulo the chosen prime rules out that triple rigorously.
Final modular survivors are checked over the integers. Passing this necessary
test is never called a witness.
"""
import argparse
from itertools import combinations
from time import perf_counter

import numpy as np


def discriminant(u, v, w, x, prime):
    a = (v*w-u*x) % prime
    b = (v*v-u*w) % prime
    c = (w*w-v*x) % prime
    return (a*a-4*b*c) % prime


def cross_column(source, others, p):
    """Evaluate each other block's monic nodal quartic on source's four nodes."""
    cross = np.ones((len(others), 4), dtype=np.int64)
    collisions = np.zeros(len(others), dtype=np.int64)
    for other in others.T:
        delta = source - other[:, None]
        collisions += (delta == 0).sum(axis=1)
        cross = (cross*delta) % p
    return cross, collisions


def exact_disc(source, left, right):
    import math
    u, v, w, x = [math.prod(j-k for k in left+right) for j in source]
    return (v*w-u*x)**2-4*(v*v-u*w)*(w*w-v*x)


def run(degree, prime):
    if not 2 <= prime <= 100000 or 3*degree >= prime:
        raise ValueError("Choose a modulus >3*degree and <=100000.")
    blocks = list(combinations(range(degree+1), 2))
    supports = [tuple(3*a+j*(b-a) for j in range(4)) for a, b in blocks]
    nodes = np.asarray(supports, dtype=np.int64)
    n = len(nodes)
    # All pairwise overlap counts. An overcount for a common triple at one node
    # cannot affect the test for <=1 total coincidence.
    collision = np.empty((n,n), dtype=np.uint8)
    for i, source in enumerate(nodes):
        counts = np.zeros(n, dtype=np.uint8)
        for point in source:
            counts += (nodes == point).sum(axis=1).astype(np.uint8)
        collision[i] = counts
    possible = []
    tested = 0
    first_pass = 0
    start = perf_counter()
    for i,(a,b) in enumerate(blocks):
        if a:
            break
        ci, _ = cross_column(nodes[i], nodes, prime)
        for j in range(i+1,n-1):
            if collision[i,j] > 1:
                continue
            ks = np.flatnonzero(collision[i,j]+collision[i,j+1:]+collision[j,j+1:] <= 1) + j+1
            if not len(ks):
                continue
            tested += len(ks)
            qi = (ci[j]*ci[ks]) % prime
            ks = ks[discriminant(*qi.T,prime) == 0]
            first_pass += len(ks)
            if not len(ks):
                continue
            cj1, _ = cross_column(nodes[j],nodes[i:i+1],prime)
            cj2, _ = cross_column(nodes[j],nodes[ks],prime)
            qj = (cj1*cj2) % prime
            ks = ks[discriminant(*qj.T,prime) == 0]
            for k in ks:
                triple = (supports[i],supports[j],supports[k])
                if all(exact_disc(triple[r],triple[(r+1)%3],triple[(r+2)%3]) == 0
                       for r in range(3)):
                    possible.append((blocks[i],blocks[j],blocks[k]))
    print(f"degree={degree}, modulus={prime}, eligible triples={tested:,}, "
          f"pass first modular identity={first_pass:,}, pass all three exact identities={len(possible):,}",
          flush=True)
    print("necessary-condition survivors:",possible[:15],flush=True)
    print(f"elapsed={perf_counter()-start:.2f}s after overlap precomputation",flush=True)
    return possible


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree",type=int,default=35)
    parser.add_argument("--prime",type=int,default=1009)
    args=parser.parse_args()
    run(args.degree,args.prime)
