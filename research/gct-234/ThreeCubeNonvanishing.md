# Three binomial cubes with nonzero values at a candidate root

These are partial results for PEqualNP step L-gct-234. They concern a nonzero polynomial $F=\sum_{i=1}^3 s_i g_i^3$ with $s_i\in\{-1,1\}$ and each real $g_i$ supported on at most two exponents. The requested upper bound is multiplicity nine at any positive root. The unrestricted case remains open in this note.

## Two support reductions

Put $x=r e^t$ for the positive candidate root $r$. This substitution preserves order of vanishing, and absorbs powers of $r$ into the nonzero coefficients. A polynomial with $k$ nonzero terms has order at most $k-1$ at a positive root: its first $k$ Euler moments would otherwise give an invertible Vandermonde system. Thus $k\le10$ resolves the target, as does any input polynomial containing fewer than two nonzero terms, since the sum then has at most nine terms.

There is also an exact exclusion based on the coefficient signs, even if exponent collisions occur. Write the combined expression as $\sum_{j} c_j e^{u_jt}$ with distinct $u_j$ and nonzero $c_j$. If the first nine moments vanish, $\sum_j c_j P(u_j)=0$ for every polynomial $P$ of degree at most eight. If one sign occurs on at most four nodes, choose $P$ as the square of the product of the linear factors vanishing on those nodes. It is strictly positive on every remaining node, and the sum has the other sign. Consequently every order-ten candidate needs at least five distinct nodes of each sign after combination.

Assume all $g_i(r)$ are nonzero. Divide each input by its value and move one signed cube to the other side. Equality of the constant terms permits writing the jet-matching problem as $pM_1+qM_2=M_3$, with $p,q>0$ and $p+q=1$. Here $M_i=(A_i e^{a_i t}+B_i e^{b_i t})^3$, with $A_i+B_i=1$. Its second cumulant, denoted by $v_i$, equals $3A_iB_i(b_i-a_i)^2$, which can be negative for signed coefficients. A positive $v_i$ contributes four positive coefficients before the outside sign is applied. A negative $v_i$ contributes two positive and two negative coefficients. Before collisions there are twelve coefficients and each sign count is even. Having at least five nodes of each sign forces six positive and six negative before collisions. In the orientation $pM_1+qM_2-M_3$, the only possible variance sign patterns up to reversing the first two terms are $(-,+,+)$ and $(-,-,-)$.

## Equal means

Here the mean is the first derivative of the normalized cube at zero. It is a signed moment, with no probabilistic assumption on the coefficients. If two of the three means agree, the mean equation and $p,q>0$ imply that all three agree. Factor out the common exponential. The centered cube is now determined by two real parameters $v,w$. The variance is $v$ and $w$ is the sum of the two centered single-copy exponent nodes. Centered single-copy moments obey

$$
U_0=1,\qquad U_1=0,\qquad U_j=wU_{j-1}+(v/3)U_{j-2}.
$$

Indeed the two nodes have product $-v/3$. The centered moments $T_j(v,w)$ of the cube are obtained by multiplying the three exponential generating series. In particular

$$
\begin{aligned}
T_2&=v,&T_3&=vw,&T_4&=v(w^2+7v/3),\\
T_5&=vw(w^2+22v/3),&
T_6&=v(w^4+53vw^2/3+61v^2/9).
\end{aligned}
$$

Suppose the moments through order six agree. Set $u=v_3=pv_1+qv_2$, $a=pv_1/u$, and $b=qv_2/u=1-a$. These quantities are nonzero for genuine binomials. The third-moment equation gives $W=w_3=aw_1+bw_2$. When $w_1=w_2$, the fourth-moment discrepancy equals $7pq(v_1-v_2)^2/3$. Consequently all parameters coincide and $F$ vanishes identically.

Otherwise rescale $t$ to give $w_1-w_2=1$. Then $w_1=W+b$, $w_2=W-a$. The fourth-moment discrepancy becomes $uab+7pq(v_1-v_2)^2/3$. Since $uab\ne0$, we have $a\ne p$, and the fourth and fifth equations give

$$
u=-\frac{3pqab}{7(a-p)^2},\qquad
W=\frac{8a^2+14ap-15a-7p}{a-p}.
$$

After substitution and removal of nonzero factors, the sixth equation is

$$
(783a^2-783a+196)p^2+(782a^3-1956a^2+782a)p+196a^4-783a^3+783a^2=0.
$$

Its discriminant in $p$ is $-2348a^2(a-1)^2(a^2-a+1)<0$. There is no real solution. Thus for three nonvanishing inputs with equal means a nonzero sum has multiplicity **at most six**. The companion script [verify_cube_common_mean.py](verify_cube_common_mean.py) checks the displayed algebra exactly in SymPy.

## Symmetric distinct means

One further case allows distinct means. Suppose the two mixture components are reflections about the target mean and have equal weight. Shift and rescale the three means to $1/2,-1/2,0$. Their variance and skew parameters are $(v,w)$ and $(v,-w)$. The variance equation forces $v_3=v+1/4$. The third moment of the reflection-symmetric mixture is zero, so $w_3=0$ for a genuine target binomial. For each $j=4,6,8$, take the difference between the mixture's $j$th moment and $T_j(v+1/4,0)$, and clear rational denominators, obtaining polynomials $B_j(v,w)$. The companion script constructs all three.

The first is $B_4=12vw^2+24vw+4v-1$. The monic greatest common divisor of $\operatorname{Res}_w(B_4,B_6)$ and $\operatorname{Res}_w(B_4,B_8)$ is $v^2$. A common real solution would require $v=0$, contradicting $B_4=0$. This subcase has multiplicity **at most eight**.

## An exact bounded-exponent test

Each cubed binomial has four possible exponent nodes $u_j=3a+j(b-a)$ for $0\le j\le 3$. To test one block $i$, let $Q_i(z)$ be the monic polynomial of degree eight whose roots are the eight exponent nodes of the other two blocks, counted with repetitions. Apply $Q_i(d/dt)$ to the exponential polynomial for $F$. This kills those two blocks because each exponential is an eigenfunction of $d/dt$. If $F$ has order at least ten, the transformed expression has order at least two. For $q_j=Q_i(u_j)$, remove the nonvanishing exponential and scalar factors in the remaining block. In the new coordinate $y=(B_i/A_i)e^{(b-a)t}$ the residual cubic is

$$
C(y)=q_0+3q_1 y+3q_2 y^2+q_3 y^3.
$$

The coordinate has nonzero derivative at $t=0$. Hence $C$ and $C'$ vanish at the same nonzero argument. Subtracting $yC'(y)/3$ from $C(y)$ leaves $q_0+2q_1 y+q_2 y^2$. Eliminating $y$ between this polynomial and $C'(y)/3$ yields the necessary integer identity

$$
(q_1q_2-q_0q_3)^2-4(q_1^2-q_0q_2)(q_2^2-q_1q_3)=0.
$$

This resultant condition remains necessary if a leading coefficient vanishes or a block overlaps another. It must hold for each of the three choices of surviving block. When the three blocks have at most ten distinct exponent nodes, the Vandermonde bound already suffices.

### A necessary interlacing condition in every exponent window

In an order-ten candidate, each surviving block interval $[u_0,u_3]$ must contain at least two strictly interior exponent occurrences from the other two blocks, counting repetitions. To see this, rescale that interval to $[0,3]$. Write the eight rescaled external exponents as $\lambda_k$, and put $D=y\,d/dy$. Up to a nonzero constant the projected cubic becomes

$$
\prod_{k=1}^8(D-\lambda_k)(1+y)^3.
$$

For a polynomial $h$ with entirely negative roots $r_j$, its logarithmic derivative $Dh/h=\sum_j y/(y-r_j)$ is strictly increasing between successive roots. Each summand has derivative $-r_j/(y-r_j)^2>0$. A strict outside operator $D-\lambda$ with $\lambda<0$ or $\lambda>3$ therefore produces one simple negative root between every two distinct roots, and one new simple negative root on an exterior interval. Indeed the left exterior branch ranges from the degree to $+\infty$, and the portion of the right branch ending at zero ranges from $-\infty$ to zero. Each old root loses one unit of multiplicity. Accordingly two such operators turn $(1+y)^3$ into a cubic with three simple negative roots, and further strict outside operators preserve this property.

Suppose at most one of the $\lambda_k$ lies strictly inside the interval. Since the candidate uses at least eleven distinct nodes out of twelve, at most one external occurrence coincides with either endpoint. Thus there are at least six strict outside operators. They commute, so apply them first. An endpoint operator, if present, leaves simple negative roots and may introduce a simple zero root ($\lambda=0$) or drop the degree by one ($\lambda=3$). This follows from the same between-root count. Apply the possible strictly interior operator last. If the current polynomial has a zero of multiplicity $z$ and simple negative roots, then

$$
Dh/h=z+\sum_{r_j<0} y/(y-r_j).
$$

The right side has strictly positive derivative wherever defined. Every new nonzero real root of $(D-\lambda)h$ is simple, and no old simple negative root survives. As a result the projected cubic has no nonzero real double root, contradicting the necessary projection condition.

More generally let $I$ consist of those external occurrences lying strictly inside $(0,3)$, and set $h_I=\prod_{\lambda\in I}(D-\lambda)(1+y)^3$, with the empty product interpreted as the identity. Whenever at least two other occurrences lie strictly outside $[0,3]$, **$h_I$ must have a nonreal pair of roots** in an order-ten candidate. In fact $h_I$ has degree three and nonzero constant term. If all its roots were real, a strict outside operation would preserve the numbers of positive and negative roots with multiplicity and reduce each old nonzero root multiplicity by one. For $\lambda<0$, apply Rolle's theorem to $|y|^{-\lambda}h(y)$ on each half-axis. The function tends to zero at the origin, so its derivative supplies a new root between the origin and the nearest root on that side and between every two consecutive distinct roots on that side. Its derivative away from zero is $|y|^{-\lambda}(D-\lambda)h/y$. Together with the old roots of lowered multiplicity, these intervals account for the full degree and every new root is simple. For $\lambda>3$, the weighted function tends to zero at infinity and the same argument supplies the exterior root between the furthest root and infinity on each occupied half-axis. This last interval contains a derivative zero because the function vanishes at the finite end, tends to zero at the infinite end, and is nonzero somewhere between them. Two strict outside operations therefore leave three simple nonzero real roots. A possible endpoint operator goes last. For $\lambda=0$ ordinary differentiation interlaces these roots, and multiplication by $y$ introduces no repeated nonzero root. For $\lambda=3$ applying ordinary differentiation to the reciprocal polynomial gives the same conclusion after inversion. There can be at most one endpoint occurrence among eligible supports.

For example, when there are exactly two interior occurrences $\lambda,\mu$, $h_I$ factors into $(1+y)$ times the quadratic

$$
(3-\lambda)(3-\mu)y^2+\bigl(3-3\lambda-3\mu+2\lambda\mu\bigr)y+\lambda\mu .
$$

The quadratic discriminant is $3[3(1-\lambda-\mu)^2-8\lambda\mu]$. Thus a necessary strict inequality in this case is $3(1-\lambda-\mu)^2<8\lambda\mu$.

[search_cube_order10.py](search_cube_order10.py) enumerates all three binomial support pairs in a prescribed common exponent window. Subtract the smallest input exponent from all six exponents, which multiplies $F$ by a monomial and preserves multiplicity at positive roots. Choose the first block lexicographically and order the two others. A repeated input support produces at most eight exponent nodes and needs no test. For three distinct supports, discard triples with more than one pairwise node coincidence, since they have at most ten distinct nodes. Checking the exact quartic identity modulo an integer can exclude a support triple. The program checks survivors over the integers, so passage through a modular test is never treated as a witnessing example. The test allows arbitrary real coefficients and positive root locations.

Run each companion from its directory:

    python verify_cube_common_mean.py
    python search_cube_order10.py --degree 50
    python search_cube_order10.py --degree 100
    python verify_cube_supports.py --exact 16
    node verify_cube_supports_modular.js 100

| Common window width | Eleven exponent nodes | Twelve exponent nodes | Eligible triples | Pass first identity modulo 1009 | Pass all three exact identities |
|---:|---:|---:|---:|---:|---:|
| 50 | 11,556,652 | 25,550,907 | 37,107,559 | 36,521 | 0 |
| 100 | 219,978,451 | 1,012,666,929 | 1,232,645,380 | 1,220,126 | 0 |

Thus the order-nine bound holds throughout the width-100 window, uniformly over real coefficients and positive roots. The independent standard-library program [verify_cube_supports.py](verify_cube_supports.py) reproduces both eligible counts using graph bitsets. Through a common width of 16 it also checks all 88,763 eligible triples with an exact integer test derived from the rational function of the vanishing moments. It obtains zero survivors.

A second full-width enumerator [verify_cube_supports_modular.js](verify_cube_supports_modular.js) derives the common affine numerator of the moment rational function for twelve nodes, and the constant numerator for eleven. It tests necessary projective equations for this numerator modulo a prime, then checks modular survivors by exact integer arithmetic. At width 50, 194 triples survive the modular test at prime 251. At width 100, 910 survive at prime 503. Exact checks eliminated every survivor in each run, independently confirming the full width-100 conclusion. Multiplying all exponent differences by a common positive integer preserves root multiplicity after a power substitution, so the same bound holds for any configuration obtained by translating or dilating a configuration in this window.
