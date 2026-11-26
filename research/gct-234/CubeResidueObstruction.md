# A congruence test for unbounded exponents

This note concerns the positive-root multiplicity problem L-gct-234. It gives a sufficient condition for the proposed bound of nine which can be checked without restricting the degrees of the input polynomials.

**Claim.** Form the twelve exponents of the three cubed binomials before combining equal terms. If these exponents occupy at least eleven residue classes modulo any prime from 11 through 101, then the root multiplicity is at most nine. The finite arithmetic in this claim can be reproduced with the accompanying Python program. The separate Lean file checks the finite discriminant exclusion at 11 and 13.

For example, the three pairs of input exponents can reduce modulo 13 to \((0,1),(2,3),(4,10)\). The twelve cubed exponents occupy all classes except 10. The input exponents here can be arbitrarily large, and the coefficients can be arbitrary real numbers. If a coefficient vanishes, the support bound already applies.

## From a tenfold root to integer identities

Write \(e_{ij}=3a_i+jd_i\) for \(0\leq j\leq3\), where \(d_i=b_i-a_i>0\). Substituting \(X=x_0e^t\) for a positive root \(x_0\) preserves its multiplicity. Write the exponential polynomial as \(\sum_{ij}w_{ij}\exp(e_{ij}t)\). Within each block the four weights have the form \(w_{ij}=c_i\binom3j r_i^j\), with nonzero real \(c_i,r_i\). A term with fewer than two input monomials leaves at most nine combined exponents, and a nonzero polynomial on \(n\) exponents has order at most \(n-1\) by the Vandermonde determinant.

Multiplicities at least ten force the first ten moments \(\sum_{ij}w_{ij}e_{ij}^k\) to vanish for \(0\leq k<10\). Set

\[
P(z)=\prod_{i,j}(z-e_{ij}),\qquad
L(z)=\sum_{i,j}w_{ij}\frac{P(z)}{z-e_{ij}}.
\]

Use all twelve labeled exponents in the product, including a repeated exponent if one occurs. The Laurent expansion of \(L/P\) at infinity starts no earlier than \(z^{-11}\), so \(L\) has degree at most one. It is nonzero, since the residue of \(L/P\) at any exponent is the corresponding combined coefficient and the given polynomial is nonzero.

For block \(i\), let \(Q_i(z)\) be the product of the eight factors belonging to the other two blocks and set \(q_j=Q_i(e_{ij})\). Evaluating the displayed formula for \(L\) gives

\[
L(e_{ij})=-6c_i d_i^3(-r_i)^j q_j.
\]

At a collision, both sides vanish. At an unshared node this follows by multiplying the three differences within the block, which gives \((-1)^{3-j}d_i^3 j!(3-j)!\). Consequently, for each of the two consecutive triples \(x,y,z\) in the block with outside products \(u,v,w\), the same affine polynomial \(L(t)=A+Bt\) satisfies

\[
u w (A+By)^2-v^2(A+Bx)(A+Bz)=0.
\]

These are six homogeneous quadratic equations in the same nonzero pair \((A,B)\). Their coefficients are integers. For any two quadratics with coefficient triples \((a,b,c)\) and \((d,e,f)\) in the order \(A^2,AB,B^2\), the existence of a common projective root forces the integer

\[
(af-cd)^2-(ae-bd)(bf-ce)
\]

to vanish. Each of the fifteen integers must therefore be zero modulo every prime. This argument passes polynomial identities to the finite field. It requires no reduction of a real coefficient.

A smaller calculation can eliminate most cases first. Both \(Q_i\) and \(zQ_i\) have degree less than ten, so testing the moment equations on these two polynomials shows that \(q_0+3q_1T+3q_2T^2+q_3T^3\) has a repeated nonzero root or is the zero polynomial. Its necessary discriminant identity is

\[
(q_1q_2-q_0q_3)^2-4(q_1^2-q_0q_2)(q_2^2-q_1q_3)=0.
\]

The projective tests and this identity allow zero outside products. Neither test divides by a value at a support node.

## Finite enumeration

If at least eleven distinct cubed residues occur, each input pair consists of two distinct residues. An affine coordinate change of the input exponents over the field takes the first pair to \((0,1)\). This changes each cubed exponent by the same invertible affine map. Outside products scale by a common nonzero eighth power and the homogeneous quadratics undergo an invertible change of the two variables. Reversing the two ends of a block only reverses its four entries, so the remaining two input pairs can be unordered and the two remaining blocks can be interchanged.

The program enumerates every such pair of pairs. It retains configurations with at least eleven distinct nodes, evaluates the three cubic discriminants, and tests all pairwise quadratic resultants on every survivor. Its arithmetic reduces integers modulo the specified prime throughout. The signed 64-bit vectorized operations are safe for the documented range up to 251. The per-survivor integer products use arbitrary precision.

| Prime | Eleven nodes | Twelve nodes | All three cubic discriminants zero | All fifteen quadratic resultants also zero |
|---:|---:|---:|---:|---:|
| 11 | 9 | 0 | 0 | 0 |
| 13 | 63 | 9 | 0 | 0 |
| 23 | 8,748 | 2,004 | 0 | 0 |
| 29 | 30,237 | 10,566 | 6 | 0 |
| 41 | 145,635 | 86,703 | 0 | 0 |
| 101 | 4,189,425 | 7,713,648 | 12 | 0 |

Across all twenty-two primes, 50,925,347 normalized configurations had at least eleven distinct residues. Exactly 164 survived the three cubic tests and none survived all fifteen quadratic tests. An independent C# program obtained the same counts by enumerating factorizations of cubics with a repeated factor and matching the explicit projective roots of the quadratics over the quadratic extension field, including the point at infinity. See [CheckCubeResidues.cs](CheckCubeResidues.cs) and the [per-prime transcript](cube-residues-independent.csv). The kernel-checked [Lean certificate for 11 and 13](CubeResidueCertificate.lean) establishes the finite arithmetic for those two primes.

To reproduce the complete Python calculation, run

```sh
python verify_cube_residues.py 11 13 17 19 23 29 31 37 41 43 47 53 59 61 67 71 73 79 83 89 97 101
```

An integer tuple may occupy at most ten residue classes for every prime on this list. The calculation leaves those tuples unresolved. A proof that infinitely many primes always exclude every configuration having at least eleven distinct nodes would settle the general case, since any given nonzero difference of exponents has only finitely many prime divisors.

## A test using the gaps alone

The same cubic discriminants also yield a different sufficient condition, even when several support residues coincide. Suppose the three input exponent differences reduce modulo 17, up to permutation and independent sign changes, to \(k,2k,4k\) for some nonzero \(k\). Then every positive root has multiplicity at most nine, whatever the three starting exponents are.

Reverse the endpoints of any block whose sign needs changing. An affine change of input exponents over the field now takes the first block to \((0,1)\). The other two have the form \((a,a+2),(b,b+4)\) modulo 17. Of the 289 possible choices of \((a,b)\), 70 make the first cubic discriminant zero. None makes all three zero. The theorem `gaps_one_two_four_mod_seventeen` in the accompanying Lean file states this last exclusion directly for every pair of offsets. There is no condition on node collisions or on how large the original integer gaps are. For example, the criterion simultaneously covers gap triples \((1,2,4)\), \((18,36,55)\), and \((1,19,174)\).
