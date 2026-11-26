# Replacing two stars in the order-three plane costs nine gates

In the canonical 64-gate separator for the 52 incident pairs and 234 quadrangle inputs of the projective plane of order three, choose any two point-stars. Keep the eleven other stars. Even if their intermediate OR values are free to reuse, any monotone binary circuit that supplies the two missing stars' positive rows and rejects the quadrangle inputs needs at least **nine additional gates**. Two ordinary stars and the OR combining them attain nine. This rules out a specific source of a 63-gate counterexample to the project's nested-AND question. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## The eighteen signals

Let the chosen points be $p,q$, with common line $c$. Each center has three private lines, meaning lines through that point and different from $c$. Keep the two point variables and all seven line variables. For each private line $a$ through $p$ and each private line $b$ through $q$, also supply $a\lor b$ for free. There are eighteen signals in total. Each of the nine extra signals can appear in an untouched star because its two lines meet at an outside point. Distinct pairs have distinct outside points.

On the eight positive rows belonging to the selected stars, every OR wire from an untouched star has the same value as its OR after deleting irrelevant lines. Removing those lines can only lower the wire's value on a negative input. An outside point lies on just one line through each of the two centers. Hence every resulting OR is either zero or one of the eighteen supplied signals. The other point inputs, the eleven complete stars and all ORs of their outputs are zero on the selected positives. They too may be replaced by zero. In a monotone circuit, these replacements keep every required positive and preserve rejection of every negative. All zero constants can then be simplified away.

## Distinct inputs bound the amount of sharing

A proposed circuit must refer to at least nine of the eighteen signals on paths to the output. To check a set of available signals, project the eight positive rows and all negative rows onto its coordinates. If any projected positive is contained in a projected negative, monotonicity prevents separation. Each individual omission of $p,q,c$ fails this test even with all other signals available. Among sets retaining those three, all $\binom{15}{5}=3003$ choices of five more signals fail as well. This also excludes every smaller source set.

If a connected output circuit has $s$ distinct reachable input signals and $g$ reachable nonconstant binary gates, the underlying undirected graph has at least $s+g-1$ edges. Its gates supply at most $2g$ incoming wire occurrences. Thus $s\le g+1$. At $g\le8$, the previous paragraph forces equality, so every nonoutput vertex has exactly one outgoing occurrence. Such a circuit is a formula.

## Exhaustion of the formulas

Label each signal by the vector of its values on the eight positives and the inclusion-maximal projected negatives. Removing contained negative rows preserves rejection by monotonicity. There are 34 maximal negative rows for each pair of centers. Applying AND or OR to two vectors evaluates the corresponding gate on all 42 rows at once.

Enumerate formulas in increasing gate count. Every binary formula of cost $k$ joins two smaller formulas whose costs sum to $k-1$. For formulas with identical accepted positives, discard any one that accepts a superset of the negative rows accepted by another formula of equal or smaller size. Substituting the more restrictive formula preserves all required positives and cannot introduce false positives. A subformula that accepts no positive can likewise be replaced by zero and its parent simplified. The search finds no separator with eight or fewer binary gates. It checks all twelve choices $q\ne0$ with $p=0$. Simultaneous translation of the two center indices and all line indices covers all pairs.

The standalone verifier performs both finite checks using integer bit operations in the Python standard library. Run `python verify_two_stars.py`. [Verifier](verify_two_stars.py)
