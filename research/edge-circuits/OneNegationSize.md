# A single negation can save an unbounded factor in circuit size

For a monotone Boolean function $f$ with one output, let $C_j(f)$ be the minimum number of gates in an acyclic circuit for $f$ with at most $j$ NOT gates. AND and OR have fan-in two, NOT is unary, every gate costs one, and a wire may be used repeatedly. An input wire can itself be the output. Use paid nullary AND and OR for true and false.

**Theorem.** For every fixed $K\ge1$, there is a finite monotone $f$ with $C_0(f)>K C_1(f)$. In particular, some circuit containing exactly one NOT has no monotone circuit of equal or smaller size computing the same output.

## Two monotone functions with one fewer negation

Take a circuit of size $s$ computing monotone $f$, with $t\ge1$ negations. Let $q$ be its first NOT in topological order and $g$ the value entering $q$. The prefix computing $g$ uses only monotone gates. Let $h_0$ and $h_1$ be the circuit outputs obtained by forcing the **output** of $q$ to one and zero, respectively. Every other use of $g$ remains intact. On inputs satisfying $g=i$, we have $h_i=f$.

Define $A=h_0\lor g$ and $B=h_1\land g$. When $g=0$, these are $f$ and zero. When $g=1$, they are one and $f$. Thus $A=f\lor g$ and $B=f\land g$ are monotone on the entire cube, even if $h_0$ or $h_1$ fails to be monotone. In each copy replace $q$ in place by one paid constant and add one binary gate using the existing $g$ wire. Each copy has size at most $s+1$ and at most $t-1$ negations.

Conversely, given arbitrary monotone circuits for $A,B$, compute

$$f=B\lor(\neg g\land A).$$

For $g=0$ this returns $A=f$ and for $g=1$ it returns $B=f$. The prefix computing $g$ costs at most $s$ gates. Besides the two supplied circuits and this prefix, the construction costs three gates, exactly one of which is NOT. Every intermediate construction has one designated output.

## Gate-count recurrence

Suppose some constant $K\ge1$ satisfies $C_0(f)\le K C_1(f)$ for every monotone single-output $f$. Write $M(t,s)$ for the largest monotone size needed for a monotone function having a circuit of at most $s$ gates and at most $t$ negations, for fixed input length. We have $M(0,s)\le s$. The two copies, followed by the one-NOT reconstruction and the hypothetical simulation, give

$$M(t,s)\le K\bigl(2M(t-1,s+1)+s+3\bigr).$$

An input circuit with zero negations already costs at most $s$, which fits the same bound. By induction, $M(t,s)\le (3K)^t(s+t+3)$. Indeed, $s+t+3$ is unchanged in the recursive calls, and $s+3\le s+t+3$. When $K=1$ the sharper bound $(2^{t+1}-1)(s+t+3)$ also follows by induction. In either case, polynomial size and $O(\log n)$ negations would imply polynomial monotone size in the number $n$ of inputs. This inference uses existence of the smaller circuits and requires no efficient procedure for finding them.

Fischer's Theorem 16 converts any polynomial-size circuit on $n$ inputs into a polynomial-size circuit using at most $\lceil\log_2(n+1)\rceil$ NOT gates. His bound is $2C^\Delta(f)+O(n^2\log^2n)$, with $\Delta$ the AND/OR/NOT basis. His source constants are free. Two shared nullary gates implement both of them in the paid model. Conversely, making constants free can only reduce monotone size. Constants in a monotone circuit for a nonconstant function can also be folded away, so monotone lower bounds apply under either convention. [Michael J. Fischer, Theorem 16 (1975)](https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TM-065.pdf)

Tardos gives a family of single-output monotone Boolean graph properties computable in polynomial time with superpolynomial monotone circuit size. Polynomial time supplies polynomial-size ordinary Boolean circuits, and a fixed finite bounded-fan-in Boolean basis translates to AND/OR/NOT with constant overhead. Applying Fischer and then the recurrence would give polynomial monotone size for the same family. This contradiction proves the theorem. A witnessing optimal circuit allowed one NOT must use exactly one, since otherwise it is a monotone circuit of size $C_1(f)$. [Éva Tardos, *The Gap Between Monotone and Non-Monotone Circuit Complexity Is Exponential* (1987)](https://www.cs.cornell.edu/~eva/Gap.Between.Monotone.NonMonotone.Circuit.Complexity.is.Exponential.pdf)

## Scope of the result

The two padded cofactors and their reconstruction come from the proof of Theorem 11 of Koroth and Sarma. Their Remark 3 states a one-negation separation for **depth**. The gate-count recurrence above derives a **size** consequence from that construction and the cited size theorems. The proof establishes an unbounded ratio and leaves open here the size of the smallest witness and whether a polynomial-size one-negation family has superpolynomial monotone size. [Sajin Koroth and Jayalal Sarma, §4.2, Theorem 11 and Remark 3 (2014)](https://eccc.weizmann.ac.il/report/2014/072/revision/1/download/)

Project row `L-meta-17828` quantifies over all input lengths and all monotone single-output Boolean functions, and requests a monotone fan-in-two circuit of no greater size for every fan-in-two circuit with exactly one indexed NOT. The case $K=1$ refutes that universal assertion. A circuit witnessing the theorem can be encoded as an ordinary well-formed project gate list. Conversely, to interpret any proposed project monotone simulation, resolve each wire at its point of use. An unavailable wire means false, an invalid output means false, an empty AND or OR is a constant, and a singleton gate is a copy. Propagate those constants and bypass copies. For a nonconstant output, this yields an ordinary binary monotone circuit with no increase in size. Constants and input projections cannot witness the separation. A constant replacement for a witnessing NOT must change the output function for each choice of constant, or that replacement gives a monotone circuit of the original size. [Project row L-meta-17828](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-17828)

This existence proof supplies neither a concrete truth table nor an exhaustive smaller-circuit certificate for a particular instance. It has no Lean formalization in this note. The separate result for circuits of size at most one above the number of essential inputs remains compatible with this conclusion. [Bounded-size result](TwoExtraGates.md)
