"""Independent finite checks for the three-binomial-cubes multiplicity problem.

Run with Python's standard library: python verify_cube_supports.py
Counts eligible support triples at degree 50 and 100, then checks every triple
at a smaller degree with arbitrary-precision integers. These are finite tests.
"""

from argparse import ArgumentParser
from itertools import combinations
from math import prod
from time import perf_counter


def supports(n):
    return [tuple(3*a + j*(b-a) for j in range(4))
            for a, b in combinations(range(n+1), 2)]


def count(n):
    start = perf_counter()
    blocks = supports(n)
    containing = [0] * (3*n+1)
    for i, group in enumerate(blocks):
        for exponent in group:
            containing[exponent] |= 1 << i
    all_blocks = (1 << len(blocks)) - 1
    zero, one = [], []
    for group in blocks:
        seen = repeated = 0
        for exponent in group:
            hits = containing[exponent]
            repeated |= seen & hits
            seen |= hits
        zero.append(all_blocks ^ seen)
        one.append(seen ^ repeated)
    total_11 = total_12 = 0
    for i in range(n):  # the smallest original exponent must be zero
        for j in range(i+1, len(blocks)-1):
            common = zero[i] & zero[j]
            if (zero[i] >> j) & 1:
                total_12 += (common >> (j+1)).bit_count()
                exactly_one = (zero[i] & one[j]) | (one[i] & zero[j])
                total_11 += (exactly_one >> (j+1)).bit_count()
            elif (one[i] >> j) & 1:
                total_11 += (common >> (j+1)).bit_count()
    print(f"N={n}: 11 distinct: {total_11:,}; 12 distinct: {total_12:,}; "
          f"total {total_11+total_12:,} ({perf_counter()-start:.2f}s)")
    return total_11 + total_12


def geometric_equation(nodes, weights):
    # If H(z)=A+Bz, the equation is
    # H(y)^2 S(x)S(z) - H(x)H(z) S(y)^2 = 0, where x,y,z are
    # consecutive support nodes and S is the product over the other blocks.
    x, y, z = nodes
    u, v, w = weights
    return u*w-v*v, 2*y*u*w-(x+z)*v*v, y*y*u*w-x*z*v*v


def resultant(f, g):
    # Homogeneous quadratic resultant; includes the projective point at infinity.
    a, b, c = f
    d, e, h = g
    return (a*h-c*d)**2 - (a*e-b*d)*(b*h-c*e)


def permitted(triple):
    only = set(triple[0]) | set(triple[1]) | set(triple[2])
    if len(only) < 11:
        return None
    collision = next((u for u in only if sum(u in g for g in triple) > 1), None)
    equations = []
    for i, group in enumerate(triple):
        if collision in group:
            continue  # division by S is valid only on the untouched block
        others = triple[(i+1)%3] + triple[(i+2)%3]
        weights = tuple(prod(x-y for y in others) for x in group)
        for pos in (0, 1):
            quad = geometric_equation(group[pos:pos+3], weights[pos:pos+3])
            if collision is not None:
                # H must vanish at the shared exponent, so use (A,B)=(-collision,1).
                a, b, c = quad
                if a*collision**2 - b*collision + c:
                    return False
            if any(resultant(quad, prior) for prior in equations):
                return False
            equations.append(quad)
    return True


def exact(n):
    start = perf_counter()
    blocks = supports(n)
    eligible = 0
    survivors = []
    for i in range(n):
        for second, third in combinations(blocks[i+1:], 2):
            triple = (blocks[i], second, third)
            status = permitted(triple)
            if status is None:
                continue
            eligible += 1
            if status:
                survivors.append(triple)
    print(f"N={n}: tested {eligible:,} eligible triples; {len(survivors)} "
          f"survive necessary moment tests ({perf_counter()-start:.2f}s)")
    if survivors:
        print("First survivors:", survivors[:3])
    return eligible


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--count", type=int, nargs="*", default=[50, 100])
    parser.add_argument("--exact", type=int, default=12)
    args = parser.parse_args()
    for n in args.count:
        count(n)
    if args.exact:
        if exact(args.exact) != count(args.exact):
            raise AssertionError("The two independent support counts disagree.")
