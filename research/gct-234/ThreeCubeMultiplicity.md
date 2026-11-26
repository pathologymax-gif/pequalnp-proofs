# Positive-root multiplicity of three cubes of binomials

For the project question `L-gct-234`, let \(F(X)=\sum_{i=1}^3 s_i g_i(X)^3\), where \(s_i=\pm1\), each real polynomial \(g_i\) has at most two monomials, and \(F\ne0\). These arguments prove multiplicity at most nine at every positive root shared by at least one \(g_i\). They also prove bounds for several families in which all three binomials are nonzero at the root. The general case with no vanishing binomial remains unresolved by this note.

The calculations were developed and independently cross-checked by the collaborating project agents. The accompanying `verify_three_cubes.py` reproduces the polynomial identities with exact rational arithmetic in SymPy. The proofs below explain why the identities apply.

## Normalization and finite moments

At a positive point \(x_0\), substitute \(X=x_0e^t\). The Taylor order at \(t=0\) equals the original root multiplicity because \(x_0e^t-x_0\) has a simple zero. Absorb \(s_i\) into \(g_i\). Each binomial becomes \(a e^{ut}+b e^{vt}\), allowing arbitrary nonzero real coefficients and nonnegative integer exponents \(u<v\). The coefficient rescaling absorbs \(x_0\).

For an exponential polynomial \(\sum_{e\in S}c_e e^{et}\), Taylor order at least \(k\) is equivalent to \(\sum_e c_e P(e)=0\) for every polynomial \(P\) of degree below \(k\). A Vandermonde determinant gives order at most \(|S|-1\) for a nonzero sum. In particular, if one of the three polynomials is a monomial or zero, there are at most nine distinct exponents after cubing and adding. Whenever the combined support has at most ten exponents, the desired bound already follows. We may therefore assume all three binomials have two distinct terms.

## All three binomials vanish

Each vanishing cube has Taylor order three. After division by \(t^3\) and its resulting nonzero constant coefficient, its normalized function is

\[
H(t)=e^{ut}\left(\frac{\sinh(ht)}{ht}\right)^3,\qquad h>0.
\]

Here \(h\) is half the difference of the original exponents. Write \(v=h^2\). Interpret Taylor derivatives as moments. Multiplication by \(e^{ut}\) shifts the mean by \(u\), and after that shift the centered moments of orders zero through six are \(1,0,v,0,13v^2/5,0,205v^3/21\). They follow by Taylor expansion of \((\sinh(ht)/(ht))^3\).

Multiplicity at least ten forces the three normalized functions to be linearly dependent through degree six. Their constant terms are all one, so the three nonzero coefficients can be rearranged into a mixture \(pH_1+qH_2=H_3\) through this degree, with \(0<p<1\) and \(q=1-p\). If the first two means agree, the third shares this mean. Equality in the second and fourth moments gives \(p v_1+qv_2=v_3\) and \(p v_1^2+qv_2^2=v_3^2\), hence \(v_1=v_2=v_3\). The three normalized functions then coincide identically, contrary to \(F\ne0\).

For distinct means, shift all three by the third mean and rescale \(t\) so that the means become \(q,-p,0\). Let \(r=pq\) and \(m=pv_1+qv_2\). Equality of moments two, three and four successively gives

\[
v_3=m+r,\quad v_1=m-q(q-p)/3,\quad v_2=m+p(q-p)/3,\quad m=(8-14r)/9.
\]

With these substitutions the fifth moment of the mixture minus that of the third function equals

\[
-4p(p-2)(p-1)(p+1)(2p-1)/27.
\]

Its only zero for \(0<p<1\) is \(p=1/2\). At that value the sixth moment difference is \(1/42\), contradicting equality.

## Exactly one binomial vanishes

The other two cubes have nonzero constant coefficients of equal magnitude and opposite sign. Normalize both underlying binomials to have constant coefficient one. Their cubes must agree through degree two because the vanishing cube has order three. Factoring the difference of cubes shows that the two normalized binomials themselves agree through degree two.

Remove their common linear moment \(\mu\) by multiplying both by \(e^{-\mu t}\). Each resulting two-term function \(B\) has \(B(0)=1\), \(B'(0)=0\) and the same \(B''(0)=v\). Its two exponents \(\alpha,\beta\) give the constant-coefficient equation

\[
B''=cB'+vB,\qquad c=\alpha+\beta,\quad v=-\alpha\beta.
\]

If \(v=0\) or the two values of \(c\) agree, uniqueness of this recurrence makes the normalized binomials identical. Their cubes cancel, leaving the third cube of order three. Otherwise a nonzero real rescaling of \(t\) makes the two parameters \(c=z+1,z-1\). The rescaling also rescales \(v\), which denotes their common value in the new coordinate. The third derivative of \(B_1^3-B_2^3\) is \(6v\ne0\).

Divide this difference by \(t^3\) and normalize its constant term to one, obtaining \(J\). If the original multiplicity is at least ten, \(J\) agrees through degree six with the normalized vanishing cube from the preceding section, up to a shift of the mean. Its centered moments \(M_j\) therefore obey

\[
M_3=M_5=0,\qquad M_4=13M_2^2/5,\qquad M_6=205M_2^3/21.
\]

The recurrence for \(B\) gives

\[
M_3=z(40v+1)/20,\qquad
M_5=z\bigl(1568v^2+(168v+1)z^2+508v+2\bigr)/56.
\]

If \(z\ne0\), the first equality forces \(v=-1/40\). The bracket in the second then equals \(-16z^2/5-243/25<0\). For \(z=0\), the fourth and sixth moment equations give

\[
7344v^2-7596v-9=0,\qquad
380736v^3-420336v^2-44388v-18=0.
\]

Their resultant is \(-994245331968000000\), so they have no common root. Exactly two vanishing binomials cannot occur at a root of \(F\), because the remaining cube would be nonzero there.

The integer exponents in the project give the stronger bound **seven** in the exactly-one-vanishing case. Multiplicity at least eight would already force the third and fourth centered-moment equations. For \(z\ne0\), the third gives \(v=-1/40\). The fourth residual becomes \(-(400z^4+14720z^2+18549)/350000\), which is strictly negative. For \(z=0\), before the rescaling the sum of the two recurrence parameters is zero. If the original exponent pairs were \((A_i,B_i)\), this gives \(4\mu=A_1+B_1+A_2+B_2\). Moreover the difference between the recurrence parameters is the nonzero integer \(A_1+B_1-A_2-B_2\), so the rescaling factor is rational. Both centered exponents and \(v\) are therefore rational. The fourth-moment equation above reduces in \(V=3v\) to \(272V^2-844V-3=0\), whose discriminant \(715600\) lies strictly between \(845^2\) and \(846^2\). This excludes a rational root.

## Two restrictions on nonvanishing binomials

**Coefficients of one sign within each binomial.** Each cubed binomial contributes a signed measure supported on at most four exponents, whose atomic weights all have the same sign. If the total has a root, move the single term of one sign to the other side so that two positive measures sum to a third through the known moments. For the set \(S\) supporting that third measure, test with \(P(z)=\prod_{s\in S}(z-s)^2\). Its degree is at most eight. If the root has multiplicity at least nine, the integral of \(P\) against the two positive measures is zero. Their supports are therefore contained in \(S\). The Vandermonde bound makes the entire sum zero. This proves multiplicity at most eight in this family.

**Common midpoint of the exponent pairs.** Remove the common exponential factor from the three cubes. Their frequencies are now \(\pm d_i,\pm3d_i\), with \(d_i>0\). If any positive frequencies coincide, their negatives do too, and there are at most ten distinct atoms. Otherwise, the six positive frequencies are distinct. Write \(c_s,c_{-s}\) for each pair of coefficients. At multiplicity ten, the five even moment equations and the five odd ones independently annihilate the vectors with coordinates \(c_s+c_{-s}\) and \(s(c_s-c_{-s})\) against the powers \((s^2)^k\), \(0\le k\le4\). This Vandermonde matrix has a one-dimensional kernel. In the nonvanishing stratum the even vector is nonzero, so the second vector is a scalar multiple of the first.

For each underlying pair \(a e^{-d t}+b e^{dt}\), neither \(a\), \(b\) nor \(a+b\) vanishes. Equating that scalar at \(s=d\) and \(s=3d\) gives

\[
3\frac{b^3-a^3}{b^3+a^3}=\frac{b-a}{b+a}.
\]

If \(b\ne a\), cancelling the nonzero factors gives \(2(a+b)^2=0\). Thus every pair has \(a=b\), and the preceding argument applies.

**Common gap of the exponent pairs.** If the gaps equal \(d>0\), write \(y=X^d\). The summands have the form \(f_i=y^{\alpha_i}(a_i+b_i y)^3\), analytic at positive \(y\). For \(E=y\,d/dy\), the quotient \(E^k f_i/f_i\) has denominator \((a_i+b_i y)^k\) and numerator of degree at most \(k\). For \(r\) linearly independent summands spanning the original three, with \(1\le r\le3\), take the Wronskian with derivative orders \(0,\dots,r-1\). In each column factor out \(f_i/(a_i+b_i y)^{r-1}\). These factors are units at the point, and the remaining determinant has polynomial entries of degree at most \(r-1\), hence degree at most \(r(r-1)\). The Wronskian is nonzero because linearly independent real-analytic functions have nonzero ordinary Wronskian and \(E\) changes it by a nonzero factor at positive \(y\). Replacing a column by \(F\) with nonzero coefficient preserves the determinant up to a nonzero scalar. This yields \(\operatorname{ord} F\le r(r-1)+r-1\le8\) when the binomials are nonvanishing.

## An exponent-only necessary condition for the remaining case

Write the cube exponents in block \(i\) as \(e_{ij}=A_i+jD_i\), \(0\le j\le3\), \(D_i>0\). The corresponding coefficients have the form \(w_i\binom3j r_i^j\), with \(w_i r_i\ne0\). Define

\[
P_i(z)=\prod_{k\ne i}\prod_{j=0}^3(z-e_{kj}),\qquad H_i(T)=\sum_{j=0}^3\binom3j P_i(e_{ij})T^j.
\]

Multiplicity at least ten annihilates both \(P_i(z)\) and \(zP_i(z)\), whose degrees are eight and nine. The other blocks make zero contributions. The first condition gives \(H_i(r_i)=0\). Subtracting \(A_i\) times the first from the second gives \(D_i r_i H_i'(r_i)=0\). Thus every \(H_i\) has a repeated nonzero root or is identically zero. This proof allows collisions between blocks, because the factors of \(P_i\) may repeat. If \(H_i\) is nonzero, its repeated real root is rational: its coefficients are integers, and a repeated irrational algebraic root would require degree at least four.

In particular, if \((a,b,c,d)=(P_i(e_{i0}),\ldots,P_i(e_{i3}))\), a necessary condition is

\[
3b^2c^2-4ac^3-4b^3d-a^2d^2+6abcd=0
\]

for each of the three blocks. This is the discriminant of \(a+3bT+3cT^2+dT^3\) divided by 27, interpreted as a polynomial identity even when the cubic degenerates. The three tests provide an exact way to reject candidate exponent patterns. Simultaneous vanishing of the discriminants alone does not establish multiplicity ten. The unresolved case still requires excluding every admissible pattern or constructing and checking a counterexample.
