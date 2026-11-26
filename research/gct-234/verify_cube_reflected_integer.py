"""Sharp distinction for reflected cubes with integer or real exponent gaps.

Run with Python and SymPy alongside verify_cube_common_mean.py.

In the previously considered reflection-symmetric distinct-mean family, the
two sources have equal weights and parameters (mean,v,w) = (+1/2,v,w) and
(-1/2,v,-w). The target has mean zero, skew zero and variance v+1/4. Every
odd moment vanishes after centering. Multiplicity at least seven would force
the even moments through order six to match. Solve the fourth moment for v,
then eliminate w between the sixth moment and the square ratio R of a source
exponent gap to the target gap. Since all original exponents are integers,
R is rational, even after the common affine change of exponent coordinates.

The eliminated sextic has no root in F_13, and its leading coefficient is a
unit there. A rational root in lowest terms would have denominator prime to
13, by the rational root theorem, and reduce to a root in that field. Thus a
nonzero signed three-cube polynomial in this family has multiplicity <= 6.

In contrast, unconstrained real exponent gaps admit order exactly eight.
The sixth moment equation has a real solution with w in (-759/1000,-758/1000)
and with both source and target squared gaps positive. The two centered
single-copy nodes are roots of X^2-wX-v/3, and the weights of masses summing
to one with zero first moment are real. Shifting those two nodes by 1/6 gives
source cube mean 1/2, and reflection supplies the other source. The target
uses the two symmetric nodes with equal masses. The eighth-moment exclusion
in verify_cube_common_mean.py makes their centered difference order eight.
"""

from math import comb

import sympy as sp
from verify_cube_common_mean import cube, moment, require_equal, variance, skew


def main():
    v, w = variance, skew
    R = sp.symbols("R")
    half = sp.Rational(1, 2)

    def difference(n):
        shifted = sum(comb(n, i) * half**(n-i) * cube[i] for i in range(n+1))
        return sp.factor(shifted - moment(n, v+half**2, 0))

    K = 12*w**2 + 24*w + 4
    require_equal(difference(4), (v*K - 1)/12)
    h = 27*w**6 + 135*w**5 + 243*w**4 + 180*w**3 + 63*w**2 + 15*w + 2
    sixth = sp.factor(difference(6).subs(v, 1/K))
    # No denominator vanishes: v*K=1 and a genuine target has v+1/4 != 0.
    reduced_sixth = sp.factor(sixth/h)
    numerator, denominator = sp.fraction(reduced_sixth)
    assert numerator.is_number and numerator != 0
    assert sp.cancel(denominator/K**2).is_number

    ratio_equation = R*(K+4) - (3*w**2*K + 4)
    sextic = 2*R**6 - 39*R**5 + 435*R**4 - 1551*R**3 + 2013*R**2 - 1020*R + 435
    require_equal(sp.resultant(h, ratio_equation, w), -19591041024*sextic)
    assert sp.LC(sp.Poly(sextic, R)) % 13 != 0
    residues = [int(sextic.subs(R, x) % 13) for x in range(13)]
    assert 0 not in residues

    lo, hi = sp.Rational(-759, 1000), sp.Rational(-758, 1000)
    assert h.subs(w, lo)*h.subs(w, hi) < 0
    # K is strictly increasing on this interval, since K'=24(w+1)>0.
    assert K.subs(w, lo) < K.subs(w, hi) < -4
    assert hi**2 + 4/(3*K.subs(w, hi)) > 0
    print("No integer exponent configuration in the reflected family has order above six.")
    print("Sextic residues at 0,...,12 modulo 13:", residues)
    print("A reflection-symmetric exponential sum with real exponent gaps attains order eight.")


if __name__ == "__main__":
    main()
