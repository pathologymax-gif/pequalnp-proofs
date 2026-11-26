"""Verify the exact moment and discriminant identities in ThreeCubeMultiplicity.md.

Run with Python 3 and SymPy: python verify_three_cubes.py
The checks cover the stated special cases and the general necessary condition.
"""

from math import comb, factorial

import sympy as sp


def require_identity(left, right=0):
    difference = sp.factor(left - right)
    if difference != 0:
        raise AssertionError(f"Nonzero residual: {difference}")


def truncated_product(left, right, degree):
    return [sum(left[j] * right[k-j] for j in range(k+1)) for k in range(degree+1)]


def sinhc_moments():
    # Coefficients of sinh(t)/t, followed by the cube's derivatives at zero.
    coefficients = [sp.Rational(1, factorial(k+1)) if k % 2 == 0 else 0 for k in range(7)]
    square = truncated_product(coefficients, coefficients, 6)
    cube = truncated_product(square, coefficients, 6)
    return [factorial(k) * cube[k] for k in range(7)]


def shifted_moment(order, mean, variance, standard):
    return sum(comb(order, k) * mean**(order-k) * variance**(k//2) * standard[k]
               for k in range(0, order+1, 2))


def check_three_vanishing():
    standard = sinhc_moments()
    expected = [1, 0, 1, 0, sp.Rational(13, 5), 0, sp.Rational(205, 21)]
    for actual, expected_value in zip(standard, expected):
        require_identity(actual, expected_value)

    p, m, delta = sp.symbols("p m delta")
    q, r = 1-p, p*(1-p)
    variance1, variance2 = m+q*delta, m-p*delta
    variance3 = m+r

    def residual(order):
        return (p*shifted_moment(order, q, variance1, standard)
                + q*shifted_moment(order, -p, variance2, standard)
                - shifted_moment(order, 0, variance3, standard))

    require_identity(residual(2))
    require_identity(residual(3), r*(q-p+3*delta))
    delta_value = (p-q)/3
    m_value = (8-14*r)/9
    require_identity(residual(4).subs(delta, delta_value), sp.Rational(4, 5)*r*(m-m_value))
    substitutions = {delta: delta_value, m: m_value}
    require_identity(residual(5).subs(substitutions), -4*p*(p-2)*(p-1)*(p+1)*(2*p-1)/27)
    require_identity(residual(6).subs(substitutions).subs(p, sp.Rational(1, 2)), sp.Rational(1, 42))


def centered_unit_cube(c, variance):
    # B(0)=1, B'(0)=0, B''=c B'+variance B. Cubing uses ordinary Taylor coefficients.
    derivatives = [sp.Integer(1), sp.Integer(0)]
    for _ in range(2, 10):
        derivatives.append(sp.expand(c*derivatives[-1] + variance*derivatives[-2]))
    coefficients = [value/factorial(k) for k, value in enumerate(derivatives)]
    square = truncated_product(coefficients, coefficients, 9)
    return truncated_product(square, coefficients, 9)


def check_one_vanishing():
    z, v = sp.symbols("z v")
    first, second = centered_unit_cube(z+1, v), centered_unit_cube(z-1, v)
    difference = [sp.expand(a-b) for a, b in zip(first, second)]
    for value in difference[:3]:
        require_identity(value)
    require_identity(difference[3], v)
    raw = [sp.cancel(factorial(k)*difference[k+3]/v) for k in range(7)]
    centered = [sp.factor(sum(comb(k, j)*raw[j]*(-raw[1])**(k-j) for j in range(k+1)))
                for k in range(7)]

    fifth_bracket = 1568*v**2 + (168*v+1)*z**2 + 508*v + 2
    require_identity(centered[3], z*(40*v+1)/20)
    require_identity(centered[5], z*fifth_bracket/56)
    require_identity(fifth_bracket.subs(v, -sp.Rational(1, 40)),
                     -sp.Rational(16, 5)*z**2 - sp.Rational(243, 25))

    fourth = centered[4] - sp.Rational(13, 5)*centered[2]**2
    sixth = centered[6] - sp.Rational(205, 21)*centered[2]**3
    a = 7344*v**2 - 7596*v - 9
    b = 380736*v**3 - 420336*v**2 - 44388*v - 18
    require_identity(-3500*fourth.subs(z, 0), a)
    require_identity(-8400*sixth.subs(z, 0), b)
    require_identity(sp.resultant(a, b, v), -994245331968000000)
    require_identity(fourth.subs(v, -sp.Rational(1, 40)),
                     -(400*z**4+14720*z**2+18549)/350000)
    total_variance = sp.Symbol("V")
    quadratic = 272*total_variance**2 - 844*total_variance - 3
    require_identity(a.subs(v, total_variance/3), 3*quadratic)
    require_identity(sp.discriminant(quadratic, total_variance), 715600)
    if not 845**2 < 715600 < 846**2:
        raise AssertionError("Expected the discriminant to lie strictly between consecutive squares.")


def check_midpoint_and_discriminant():
    a, b = sp.symbols("a b")
    require_identity(3*(b**3-a**3)*(b+a) - (b-a)*(b**3+a**3), 2*(b-a)*(a+b)**3)

    base, gap, t = sp.symbols("base gap t")
    values = sp.symbols("a:4")
    terms = [comb(3, j)*v*t**j for j, v in enumerate(values)]
    polynomial = sum(terms)
    weighted = sum((base+j*gap)*term for j, term in enumerate(terms))
    require_identity(weighted-base*polynomial, gap*t*sp.diff(polynomial, t))
    a, b, c, d = values
    require_identity(sp.discriminant(polynomial, t),
                     27*(3*b**2*c**2-4*a*c**3-4*b**3*d-a**2*d**2+6*a*b*c*d))


if __name__ == "__main__":
    check_three_vanishing()
    print("Verified three vanishing binomials, including the sixth-moment residual 1/42.")
    check_one_vanishing()
    print("Verified one vanishing binomial, including the nonzero resultant -994245331968000000.")
    check_midpoint_and_discriminant()
    print("Verified the common-midpoint identity and the general cubic discriminant test.")
