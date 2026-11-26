# Eliminating the translations of three binomial cubes

Let $F$ be a nonzero real polynomial that is a signed sum of cubes of three binomials. For a genuine binomial $aX^u+bX^v$ with $u<v$, call $v-u$ its gap. Its cube has exponents $3u+j(v-u)$ for $0\le j\le3$. A monomial or zero summand gives at most nine distinct exponents in the entire sum, hence positive-root multiplicity at most eight by the Vandermonde determinant.

**Results.** For gaps proportional to $1,2,3$ or $1,2,4$, every positive root has multiplicity at most nine, for all starting exponents and all real coefficients. More generally, there is an explicit nonzero polynomial $E(1,u,v)$ such that every counterexample with gap ratios $1:u:v$ satisfies $E(1,u,v)=0$. Thus potential exceptions are confined to a proper algebraic subset of the two-dimensional ratio space. The argument leaves the points on that set to be examined separately. The general project target remains outside the scope of these results. [Project row L-gct-234](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-gct-234)

## Three polynomial conditions

At a candidate root $r>0$, put $X=r e^t$. This preserves the order at the root and absorbs $r$ into the coefficients. Subtract a common number from all exponents by multiplying by a nonvanishing exponential. Rescale $t$ by a nonzero constant to rescale all gaps. We may use starts $0,b,c$ and positive steps $d_0,d_1,d_2$, allowing arbitrary real starts. Write $e_{ij}=a_i+jd_i$ with $(a_0,a_1,a_2)=(0,b,c)$.

Fix block $i$. Let $Q_i(z)=\prod_{h\ne i}\prod_{k=0}^3(z-e_{hk})$ and write $q_j=Q_i(e_{ij})$. Applying $Q_i(d/dt)$ kills both other blocks. If $F$ vanishes to order at least ten, the resulting exponential polynomial vanishes to order at least two. After removing its exponential prefactor, it is proportional to $q_0+3q_1 y+3q_2 y^2+q_3 y^3$ with $y=(B_i/A_i)e^{d_i t}$, where $A_i,B_i$ are the two nonzero coefficients after rescaling. Since $y'(0)\ne0$, this cubic must have a multiple root or vanish identically. Therefore the following polynomial vanishes:

$$D_i=(q_1q_2-q_0q_3)^2-4(q_1^2-q_0q_2)(q_2^2-q_1q_3).$$

Indeed $-27D_i$ is the ordinary discriminant of the corresponding binary cubic. A shared exponent among blocks simply makes one or more $q_j$ zero. The differential argument and the necessary discriminant equation remain valid there.

## Exact tests at two gap ratios

Use the Sylvester resultants $A=\operatorname{Res}_c(D_0,D_1)$ and $B=\operatorname{Res}_c(D_0,D_2)$. A common finite zero of the three $D_i$ gives $A(b)=B(b)=0$. The following computations use the primitive integer parts of the specialized $D_i$; dividing by a nonzero integer preserves the common zeros. In each line, $A,B$ have degree 576 in $b$. The listed pairs are the roots and orders of their common factors over $\mathbb Q$.

| Ordered gaps | Common factors, given as (root, order) |
|---|---|
| $(1,2,4)$ | None |
| $(1,2,3)$ | $(-6,2),(-4,9),(-3,16),(-2,17),(-1,17),(0,16),(1,9),(3,2)$ |
| $(1,3,2)$ | $(-9,2),(-8,5),(-7,4),(-6,6),(-5,6),(-4,7),(-3,6),(-2,7),(-1,6),(0,6),(1,4),(2,5),(3,2)$ |

Every listed root is a collision between the first two blocks, since it equals $j d_0-k d_1$ for some $0\le j,k\le3$. For gaps $(1,2,4)$ there is no possible common root. For $(1,2,3)$, a putative counterexample must have at least eleven distinct nodes by the Vandermonde bound. There is then at most one collision among the twelve slots. At least one of the first pairs in the orderings $(1,2,3)$ and $(1,3,2)$ is disjoint. Its row in the table excludes the candidate. This proves both fixed-ratio statements even when exponents from different blocks coincide.

The SymPy verifier forms the integer resultants by interpolation. The coefficient degree bounds in a Sylvester determinant bound the required number of samples. Exact division removes the listed linear factors from both polynomials. The residuals have gcd one modulo 1009, with a leading degree preserved. By Gauss's lemma any nonconstant common rational factor would retain positive degree after this reduction, so there is no further common factor. [Integer verification script](cube_gap_exact_elimination.py)

## A nonzero polynomial for arbitrary gap ratios

Regard the $D_i$ as raw polynomials in $b,c,d_0,d_1,d_2$ with integer coefficients. The following degree bounds hold with respect to the offsets $b,c$ over the coefficient ring $\mathbb Z[d_0,d_1,d_2]$.

| Polynomial | Maximum degree in $b$ | Maximum degree in $c$ | Maximum total degree in $b,c$ |
|---|---:|---:|---:|
| $D_0$ | 16 | 16 | 26 |
| $D_1$ | 26 | 16 | 26 |
| $D_2$ | 16 | 26 | 26 |

To see the last column, fix $i$ and write $w_j=\Delta^j q_0$, where $\Delta$ is the forward difference in the four sample values. Each $w_j$ has total offset degree at most $8-j$. Indeed $Q_i(a_i+z)$ is a product of eight linear factors in $b,c,z$ over the gap coefficient ring, and a difference of order $j$ at $z=0,d_i,\ldots,jd_i$ kills all powers $z^k$ with $k<j$. Under $q_j=\sum_{k=0}^j\binom{j}{k}w_k$, the binary cubic in $q_j$ is the cubic in $w_k$ after $(U,V)\mapsto(U+V,V)$. This substitution has determinant one and preserves the discriminant, as one can also check by expanding the displayed formula. Each term of the discriminant in the $w_j$ consists of four factors with index sum six. This gives $4\cdot8-6=26$. If the moving offset belongs to a foreign block, each $q_j$ has degree at most four in that offset, giving the individual bounds of sixteen.

Form $A,B$ over the gap coefficient ring with respective $c$-degree pairs $(16,16)$ and $(16,26)$. Both have degree **at most 576** in $b$. Here is a determinant proof. Index columns by $s$ starting at zero and let $r$ be the shift of a row in the Sylvester matrix. Its entry at $s=r+j$ is the coefficient of $c^j$. For $A$, this entry has $b$-degree at most $26-j=(26+r)-s$. Summing row and column bounds gives

$$32\cdot26+2\sum_{r=0}^{15}r-\sum_{s=0}^{31}s=576.$$

For $B$, both input polynomials have $b$-degree at most 16. Put $z_+=\max(z,0)$. The entry degree is at most $16-(j-10)_+$. Assign row bound $16+(r-9)_+$ and column bound $-(s-19)_+$. Their sum dominates the entry bound because $(r+j-19)_+\le(r-9)_++(j-10)_+$. The two row-shift ranges are $0,\ldots,25$ and $0,\ldots,15$. The column range is $0,\ldots,41$. Every determinant term therefore has degree at most $42\cdot16+136+21-253=576$.

Define $E(d_0,d_1,d_2)=\operatorname{Res}_b(A,B)$ using these fixed degree bounds $(576,576)$. All three resultant matrices have entries in integer polynomial rings and can be specialized before taking their determinants. A common finite zero forces a zero determinant even if a leading degree drops in that specialization. To prove that $E$ itself is nonzero, the converse requires care with roots at infinity. At gaps $(1,2,4)$ the actual $c$-degrees are $16,16,26$, and both actual inner $b$-degrees are 576. An independent evaluation of the original, unscaled discriminants gives

$$E(1,2,4)\equiv 631 \pmod {1009}.$$

This nonzero integer residue establishes that the specialization has no spurious zero from a degree drop at either elimination stage. In particular $E(1,u,v)$ is a nonzero polynomial and its zero set is proper. Among positive integer gap triples with all entries at most $H$, at most $\deg(E)H^2$ can be exceptional, by the polynomial zero bound on a Cartesian grid. Thus the proportion of gap triples requiring further work tends to zero, uniformly over all starting exponents for each of the other triples. The exceptional set includes possible zeros of $E$ caused solely by eliminating variables or by degeneracies. Membership alone does not produce a counterexample.

The independent verifier samples the original four-node progressions modulo 1009, interpolates the discriminants and inner resultants with the proved degree bounds, and computes univariate resultants by Euclidean remainders. It retains the fixed Sylvester degrees when a sampled fiber loses a leading term. It uses only the Python standard library. [Independent nonvanishing certificate](verify_cube_gap_specialization.py)

## Reproduce

```sh
python cube_gap_exact_elimination.py 1 2 4
python cube_gap_exact_elimination.py 1 2 3
python cube_gap_exact_elimination.py 1 3 2
python verify_cube_gap_specialization.py
```
