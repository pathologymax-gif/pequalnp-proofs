# Replacing two stars in the order-three plane costs nine gates

In the canonical 64-gate separator for the 52 incident pairs and 234 quadrangle inputs of the projective plane of order three, choose any two point-stars. Keep the eleven other stars. Even if their intermediate OR values are free to reuse, any monotone binary circuit that supplies the two missing stars' positive rows and rejects the quadrangle inputs needs at least **nine additional gates**. Two ordinary stars and the OR combining them attain nine. This rules out a specific source of a 63-gate counterexample to the project's nested-AND question. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## The eighteen signals

Let the chosen points be $p,q$, with common line $c$. Each center has three private lines, meaning lines through that point and different from $c$. Keep the two point variables and all seven line variables. For each private line $a$ through $p$ and each private line $b$ through $q$, also supply $a\lor b$ for free. There are eighteen signals in total. Each of the nine extra signals can appear in an untouched star because its two lines meet at an outside point. Distinct pairs have distinct outside points.

On the eight positive rows belonging to the selected stars, every OR wire from an untouched star has the same value as its OR after deleting irrelevant lines. Removing those lines can only lower the wire's value on a negative input. An outside point lies on just one line through each of the two centers. Hence every resulting OR is either zero or one of the eighteen supplied signals. The other point inputs, the eleven complete stars and all ORs of their outputs are zero on the selected positives. They too may be replaced by zero. In a monotone circuit, these replacements keep every required positive and preserve rejection of every negative. All zero constants can then be simplified away.

## Geometry forces the raw inputs

Three nonconcurrent lines form a triangle. Their union has nine points, so its complement has four. Every other line meets the triangle's sides in at least two distinct points, as a line through two triangle vertices is itself a side. The four complementary points thus form a quadrangle whose exterior lines are exactly the triangle's sides. Given a point outside two lines, a third line through neither the point nor the intersection of those two lines completes such a triangle while keeping the point in the quadrangle. The third line exists since two point-pencils together contain only seven of the thirteen lines.

Signals $p,q,c$ must all reach the output. Without $p$, the positive row $(p,c)$ sets only $c$ among the eighteen signals, and some negative has $c$ as an exterior line. The same argument applies to $q$. Without $c$, the positive row $(p,c)$ sets only $p$, which occurs in a negative.

Suppose a private line $a$ through $p$ is absent as a direct source. All three signals $a\lor b$, with $b$ a private line through $q$, must then be used. If at most two were used, choose two such private lines $b_1,b_2$ covering the selected choices. Both miss $p$. Complete them to a triangle missing $p$ as above. The resulting quadrangle contains $p$ and has both $b_1,b_2$ as exterior lines. On every used source, the positive row $(p,a)$ is therefore bounded above by this negative, contrary to monotonicity. The same argument applies with the centers exchanged.

Let $x,y$ count the absent direct private lines on the two sides. We must use the $6-x-y$ remaining direct private lines and at least $3x+3y-xy$ distinct pair signals incident with a missing line. Their total is $6+2x+2y-xy$. For $0\le x,y\le3$, it exceeds six whenever $x+y>0$. Indeed, when $x\le2$ its excess is $2x+(2-x)y$; when $x=3$ the excess is $6-y$. Including $p,q,c$, any circuit using at most nine sources must therefore use exactly the nine raw inputs.

## Eight gates would give a read-once formula

If a connected output circuit has $s$ distinct reachable input signals and $g$ reachable nonconstant binary gates, each nonoutput vertex supplies at least one outgoing wire occurrence. There are at most $2g$ input occurrences at gates, so $s+g-1\le2g$. At $g\le8$ the nine necessary sources force equality. Every nonoutput vertex then has one outgoing occurrence, giving a formula in which each of the nine raw variables appears once.

For a monotone read-once formula that rejects each singleton and contains no constants, its accepted pairs of distinct variables form a disjoint union of complete bipartite graphs and isolated vertices. At a root OR, both children reject singletons and their variable sets are disjoint, so their accepted-pair graphs form a disjoint union. At a root AND, each child rejects the empty input. A true pair must therefore have one variable on each side, and it is accepted exactly when both individual variables are accepted by their respective child. This gives one complete bipartite graph. These cases prove the claim inductively.

Here every raw singleton is contained in a negative input. The graph must contain $(p,a),(p,c),(q,c)$ for every private $a$ through $p$. It cannot contain $(q,a)$, since a triangle with side $a$ avoiding $q$ has a complementary quadrangle containing $q$. In a disjoint union of complete bipartite graphs, the common neighbor $c$ puts $p$ and $q$ in the same part of the same component; they must have identical neighbors. This contradiction proves the nine-gate lower bound.

## Independent finite verification

For a separate computational proof, the verifier excludes all $\binom{15}{5}=3003$ selections of five additional sources alongside $p,q,c$ by testing whether a projected positive row is contained in a projected negative.

Label each signal by the vector of its values on the eight positives and the inclusion-maximal projected negatives. Removing contained negative rows preserves rejection by monotonicity. There are 34 maximal negative rows for each pair of centers. Applying AND or OR to two vectors evaluates the corresponding gate on all 42 rows at once.

Enumerate formulas in increasing gate count. Every binary formula of cost $k$ joins two smaller formulas whose costs sum to $k-1$. For formulas with identical accepted positives, discard any one that accepts a superset of the negative rows accepted by another formula of equal or smaller size. Substituting the more restrictive formula preserves all required positives and cannot introduce false positives. A subformula that accepts no positive can likewise be replaced by zero and its parent simplified. The search finds no separator with eight or fewer binary gates. It checks all twelve choices $q\ne0$ with $p=0$. Simultaneous translation of the two center indices and all line indices covers all pairs.

The standalone verifier performs both finite checks using integer bit operations in the Python standard library. Run `python verify_two_stars.py`. [Verifier](verify_two_stars.py)
