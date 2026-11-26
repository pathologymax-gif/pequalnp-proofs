"""Exact jet identities for sums of three real binomial cubes.

Run: python verify_cube_common_mean.py   (requires SymPy)

Normalize a proposed positive root to 1 and write x=exp(t). A binomial
nonzero there, divided by its value, is the exponential moment series of a
two-point signed measure of mass 1. Cubing takes its threefold convolution.
After centering a cube at its mean, v denotes its variance; w is the sum of
the two centered single-copy support points. The single-copy points satisfy
y^2=w*y+v/3, even for signed weights. This gives the recurrence below.

At a zero of the sum, there are two normalized cubes on one side and one on
the other; their equation is p*M1+(1-p)*M2=M3 through the relevant order,
with 0<p<1. A genuinely two-term binomial has v != 0. If any term is instead
a monomial or zero, the original polynomial has at most nine monomials.

Case 1: All three means agree. Factor out their common exponential. The
following checks give a contradiction to matching jets through order six
unless all three exponential series coincide. In the coincident case the
original sum is identically zero.

Case 2: The two components are reflections about the target mean and carry
equal weight. Translate and rescale to means +/-1/2, with parameters
(v,w) and (v,-w). The checks rule out matching through order eight.
"""

from math import comb

import sympy as sp


def require_equal(left, right):
    if sp.cancel(left - right) != 0:
        raise AssertionError(f"Identity failed: {left} == {right}")


variance, skew = sp.symbols("v w")
single = [sp.Integer(1), sp.Integer(0)]
for n in range(2, 9):
    single.append(sp.expand(skew * single[-1] + variance * single[-2] / 3))

cube = []
for n in range(9):
    moment = sum(
        comb(n, i) * comb(n - i, j) * single[i] * single[j] * single[n - i - j]
        for i in range(n + 1) for j in range(n - i + 1)
    )
    cube.append(sp.factor(moment))


def moment(n, v, w):
    return cube[n].subs({variance: v, skew: w}, simultaneous=True)


def common_mean():
    p, a, u, W, dv = sp.symbols("p a u W dv")
    q, b = 1 - p, 1 - a
    # u=v3=p*v1+q*v2; a=p*v1/u, b=q*v2/u. Both a and b are nonzero.
    # The third-moment equation gives W=w3=a*w1+b*w2. If w1=w2, the
    # fourth-moment discrepancy is (7/3)*p*q*(v1-v2)^2: all parameters agree.
    v1, v2 = u + q * dv, u - p * dv
    require_equal(
        p * moment(4, v1, W) + q * moment(4, v2, W) - moment(4, u, W),
        sp.Rational(7, 3) * p * q * dv**2,
    )

    # Otherwise scale the t-coordinate so w1-w2=1. Then w1=W+b, w2=W-a.
    # E4=0 forces a!=p and determines the nonzero variance u.
    v1, v2 = u * a / p, u * b / q
    def residual(n):
        return p * moment(n, v1, W + b) + q * moment(n, v2, W - a) - moment(n, u, W)

    require_equal(residual(4), u*a*b + sp.Rational(7, 3)*p*q*(v1-v2)**2)
    solved_u = -3 * p * q * a * b / (7 * (a - p)**2)
    require_equal(residual(4).subs(u, solved_u), 0)

    # E5 fixes W linearly; its coefficient cannot vanish on this branch.
    fifth = sp.factor(residual(5).subs(u, solved_u))
    solved_W = (8*a**2 + 14*a*p - 15*a - 7*p) / (a-p)
    require_equal(fifth.subs(W, solved_W), 0)
    require_equal(sp.diff(fifth, W), -3*a**2*p*(a-1)**2*(p-1) / (49*(a-p)**2))

    sixth = sp.factor(residual(6).subs({u: solved_u, W: solved_W}))
    quadratic = (
        (783*a*a - 783*a + 196)*p*p
        + (782*a**3 - 1956*a*a + 782*a)*p
        + 196*a**4 - 783*a**3 + 783*a*a
    )
    # All removed factors are nonzero. A quadratic of negative discriminant
    # has no real root because a^2-a+1=(a-1/2)^2+3/4 is strictly positive.
    prefactor = sp.factor(sixth / quadratic)
    numerator, denominator = sp.fraction(prefactor)
    for expression in [numerator, denominator]:
        for factor, _ in sp.factor_list(expression, a, p)[1]:
            if sp.expand(factor) not in (a, a-1, p, p-1, a-p, p-a):
                raise AssertionError(f"Unexpected sixth-moment factor: {factor}")
    require_equal(sp.discriminant(quadratic, p), -2348*a*a*(a-1)**2*(a*a-a+1))
    print("Common mean: orders 2–6 force identical cubes or a negative discriminant.")


def reflected_means():
    v, w = variance, skew
    half = sp.Rational(1, 2)
    # The variance equation gives target variance v+1/4. Reflection symmetry
    # makes its skew parameter zero, since the target variance is nonzero.
    even_residuals = []
    for order in (4, 6, 8):
        shifted = sum(comb(order, i) * half**(order-i) * cube[i] for i in range(order+1))
        diff = shifted - moment(order, v + half**2, 0)
        even_residuals.append(sp.primitive(sp.expand(diff), v, w)[1])
    fourth, sixth, eighth = even_residuals
    require_equal(fourth, 12*v*w**2 + 24*v*w + 4*v - 1)
    factors = [sp.resultant(fourth, other, w) for other in (sixth, eighth)]
    require_equal(sp.Poly(sp.gcd(*factors), v).monic().as_expr(), v*v)
    print("Reflected means: orders 4, 6, 8 would force v=0, contrary to order 4.")


if __name__ == "__main__":
    common_mean()
    reflected_means()
