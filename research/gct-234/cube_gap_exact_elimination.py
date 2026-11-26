"""Check all translates at three prescribed exponent gaps, when certified.

The three discriminants must vanish at a counterexample. Fix the first block
start to zero and eliminate the third start from discriminants 1/2 and 1/3.
Recover each integer resultant polynomial by exact Newton interpolation; use
modular gcd only after dividing the actual integer polynomials by their common
factors at forbidden first/second-block collisions. The resultant degree bound
comes directly from column degrees of the Sylvester determinant.
"""
import argparse
from math import factorial, prod
from time import perf_counter
import sympy as sp
from sympy.polys.rings import ring


def equations(steps):
    polynomial_ring, b, c = ring('b,c', sp.ZZ)
    starts = (polynomial_ring.zero, b, c)
    blocks = [[a + j*d for j in range(4)] for a, d in zip(starts, steps)]
    parts = []
    for i, block in enumerate(blocks):
        outside = blocks[(i+1) % 3] + blocks[(i+2) % 3]
        u, v, w, z = [prod(x-y for y in outside) for x in block]
        d = (v*w-u*z)**2 - 4*(v*v-u*w)*(w*w-v*z)
        parts.append(d.primitive())
    return [int(P[0]) for P in parts], [P[1] for P in parts]


def numerical_eliminants(discriminants, b):
    x = sp.Symbol('x')
    specialized = []
    for f in discriminants:
        values = [0] * (f.degree(1) + 1)
        powers = [b**i for i in range(f.degree(0) + 1)]
        for (i, j), coefficient in f.items():
            values[j] += int(coefficient) * powers[i]
        specialized.append(sp.Poly.from_list(values[::-1], x, domain=sp.ZZ))
    for j in (1, 2):
        m, n = discriminants[0].degree(1), discriminants[j].degree(1)
        A, B = specialized[0], specialized[j]
        if A.is_zero or B.is_zero or (A.degree() < m and B.degree() < n):
            yield 0
            continue
        # Always pass the greater degree first. This also avoids older SymPy
        # versions' sign convention when swapping two odd degrees internally.
        if A.degree() < B.degree():
            r = (-1)**(A.degree()*B.degree()) * int(B.resultant(A))
        else:
            r = int(A.resultant(B))
        if A.degree() < m:
            yield r * ((-1)**n * int(B.LC()))**(m-A.degree())
        else:
            yield r * int(A.LC())**(n-B.degree())


def exact_interpolation(values, first):
    # For an integer-coefficient polynomial every forward difference divided
    # by its order factorial is an integer.
    newton = []
    while values:
        a, r = divmod(values[0], factorial(len(newton)))
        assert r == 0
        newton.append(a)
        values = [y - x for x, y in zip(values, values[1:])]
    coefficients = []
    for k in range(len(newton) - 1, -1, -1):
        center = first + k
        coefficients = [a - center*b for a, b in zip([0]+coefficients, coefficients+[0])]
        coefficients[0] += newton[k]
    return sp.Poly.from_list(coefficients[::-1], sp.Symbol('b'), domain=sp.ZZ)


def check(steps, prime=1009):
    if not sp.isprime(prime) or not all(x > 0 for x in steps):
        raise ValueError('Expected three positive steps and a prime modulus.')
    start_time = perf_counter()
    contents, fs = equations(steps)
    bounds = []
    for f in fs[1:]:
        m, n = fs[0].degree(1), f.degree(1)
        bounds.append(n*fs[0].degree(0) + m*f.degree(0))
    # Start above first/second collisions. Confirm the interpolation against
    # additional exact determinants beyond the maximum degree bounds.
    first = 4*max(steps) + 1
    maximum = max(bounds)
    samples = [list(numerical_eliminants(fs, i)) for i in range(first, first+maximum+4)]
    resultants = [exact_interpolation([v[j] for v in samples[:n+1]], first)
                  for j, n in enumerate(bounds)]
    for j, A in enumerate(resultants):
        for i in range(maximum+1, maximum+4):
            assert A.eval(first+i) == samples[i][j]
    print('Exact integer resultant degrees:', [A.degree() for A in resultants], flush=True)
    b = sp.Poly(sp.Symbol('b'), sp.Symbol('b'), domain=sp.ZZ)
    collisions = sorted({i*steps[0]-j*steps[1] for i in range(4) for j in range(4)})
    factors = []
    for t in collisions:
        order = 0
        while all(A.degree() > 0 and A.eval(t) == 0 for A in resultants):
            resultants = [A.exquo(b-t) for A in resultants]
            order += 1
        if order:
            factors.append((t, order))
    mod = [A.set_modulus(prime) for A in resultants]
    gcd = sp.gcd(*mod)
    # If a primitive common nonconstant factor over Q[b] existed, preserving
    # this leading coefficient would keep it nonconstant after reduction.
    preserved = any(not a.is_zero and a.degree() == m.degree() for a, m in zip(resultants, mod))
    print('Common collision factors (root, order):', factors)
    print('Residual gcd degree modulo', prime, '=', gcd.degree(), '| Leading degree preserved:', preserved)
    if not factors and [f.degree(1) for f in fs] == [16,16,26] and all(f.degree() == 576 for f in mod):
        # Restore the discarded integer contents to compare the literal raw
        # discriminant with the independent direct finite-field calculation.
        scales = [contents[0]**fs[j].degree(1) * contents[j]**fs[0].degree(1) for j in (1,2)]
        raw_value = int(mod[0].resultant(mod[1])) * pow(prod(scales), 576, prime) % prime
        print('Final raw resultant modulo', prime, '=', raw_value)
    certified = preserved and gcd.degree() == 0
    print('Certified exclusion outside listed collisions:', certified)
    print('Elapsed seconds:', round(perf_counter() - start_time, 2))
    return certified


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('steps', nargs=3, type=int)
    parser.add_argument('--prime', type=int, default=1009)
    args = parser.parse_args()
    check(args.steps, args.prime)
