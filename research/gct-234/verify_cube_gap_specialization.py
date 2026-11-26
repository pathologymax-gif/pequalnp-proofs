"""Independently evaluate the nested resultant at gaps (1,2,4) in F_1009.

Uses only the Python standard library. The offset degree bounds 16,16,26 for
the three discriminants and 576 for the inner resultants are proved in the
companion note. This program samples the original exponent nodes directly.
Polynomials are coefficient lists in ascending order.
"""

from math import prod


def trim(poly):
    while poly and not poly[-1]:
        poly.pop()
    return poly


def remainder(a, b, p):
    a = a[:]
    inverse = pow(b[-1], -1, p)
    while len(a) >= len(b):
        start = len(a) - len(b)
        quotient = a[-1] * inverse % p
        for i, coefficient in enumerate(b):
            a[start+i] = (a[start+i] - quotient*coefficient) % p
        trim(a)
    return a


def resultant(a, b, p):
    if not a or not b:
        return 0
    factor = 1
    while len(b) > 1:
        m, n = len(a)-1, len(b)-1
        rem = remainder(a, b, p)
        if not rem:
            return 0
        sign = -1 if m*n % 2 else 1
        factor = factor * sign * pow(b[-1], m-len(rem)+1, p) % p
        a, b = b, rem
    return factor * pow(b[0], len(a)-1, p) % p


def padded_resultant(a, b, m, n, p):
    # The original Sylvester matrix keeps its size if leading coefficients
    # specialize to zero. Its homogeneous forms may acquire roots at infinity.
    if not a or not b or (len(a)-1 < m and len(b)-1 < n):
        return 0
    r = resultant(a, b, p)
    if len(a)-1 < m:
        return r * pow((-1)**n * b[-1], m-len(a)+1, p) % p
    return r * pow(a[-1], n-len(b)+1, p) % p


def interpolate(values, p):
    # Consecutive arguments 0,1,...; Newton coefficients are the normalized
    # forward differences. Fewer than p samples keep all factorials invertible.
    diffs = values[:]
    newton = []
    factorial = 1
    while diffs:
        newton.append(diffs[0] * pow(factorial, -1, p) % p)
        factorial = factorial * len(newton) % p
        diffs = [(b-a) % p for a,b in zip(diffs, diffs[1:])]
    result = []
    for k in range(len(newton)-1, -1, -1):
        result = [(a-k*b) % p for a,b in zip([0]+result, result+[0])]
        result[0] = (result[0] + newton[k]) % p
    return trim(result)


def evaluate(poly, x, p):
    value = 0
    for coefficient in reversed(poly):
        value = (value*x + coefficient) % p
    return value


def discriminants(b, c, p):
    blocks = [[a + j*gap for j in range(4)]
              for a,gap in zip((0,b,c), (1,2,4))]
    out = []
    for i, block in enumerate(blocks):
        other = blocks[(i+1) % 3] + blocks[(i+2) % 3]
        u,v,w,z = [prod(x-y for y in other) % p for x in block]
        out.append(((v*w-u*z)**2 - 4*(v*v-u*w)*(w*w-v*z)) % p)
    return out


def main():
    p = 1009
    r = [[], []]
    observed = [-1]*3
    for b in range(580):
        samples = [discriminants(b,c,p) for c in range(29)]
        f = []
        for j, degree in enumerate((16,16,26)):
            poly = interpolate([x[j] for x in samples[:degree+1]],p)
            observed[j] = max(observed[j], len(poly)-1)
            assert all(evaluate(poly,c,p) == samples[c][j] for c in range(degree+1,29))
            f.append(poly)
        r[0].append(padded_resultant(f[0],f[1],16,16,p))
        r[1].append(padded_resultant(f[0],f[2],16,26,p))
    inner = [interpolate(y[:577],p) for y in r]
    for seq, poly in zip(r,inner):
        assert all(evaluate(poly,b,p)==seq[b] for b in range(577,580))
    degrees = [len(poly)-1 for poly in inner]
    certificate = resultant(*inner,p)
    print('Observed degrees in the third start:', observed)
    print('Degrees of inner resultants in the second start:', degrees)
    print('Final raw resultant at gaps (1,2,4) modulo 1009:', certificate)
    assert observed == [16,16,26] and degrees == [576,576] and certificate != 0


if __name__ == '__main__':
    main()
