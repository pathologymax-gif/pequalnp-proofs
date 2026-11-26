# Exact size of a single-level circuit for the four projections

For each of the four assigned tables, an AND/OR circuit with at most one AND on every input-to-output path needs exactly 19 binary gates. Fan-out is unrestricted. A second consequence is that every circuit of size at most 18 computing any one of the four tables would have to produce a false positive at an intermediate AND gate. The constructions in `star_upper.json` attain 19.

## Counting gates on a graph without a four-cycle

Let G be a finite simple graph with at least one edge, m edges and minimum vertex cover size t. Let its output be one when the input includes both endpoints of some edge. Assume G contains no cycle of length four, including cycles with chords. Its minimum single-level monotone circuit size is m+t−1. Here the inputs are the vertex bits, an optional zero is free, and every binary AND and OR has unit cost. This argument counts gates even when several gates read the same wire.

First fold constants and idempotent gates, trim gates outside the output cone, and bypass any OR with singleton support that merely repeats its input variable. Every AND has two OR-only operands with nonempty supports A and B. Every path above this AND consists of OR gates. Thus A and B are disjoint (otherwise a singleton would be accepted), and every pair in A×B is an edge. If both supports had two different vertices, they would give a four-cycle. One operand is therefore a vertex, called the center. If both operands are singletons, choose either as the center. No path made entirely of OR gates can connect a vertex input to the output, since its singleton would be accepted.

Write k for the number of AND gates. For every center v, let k_v count its product gates and U_v be the union of their other operands' supports. The stars at the centers cover every edge, so ∑|U_v|≥m and k≥t. Above the products at least k−1 OR gates are required to connect their k outputs to one output. This follows from counting edges in a connected undirected graph of gates with at most two incoming edges per OR.

Below the products at center v, the OR network connects each of the |U_v| input vertices to at least one of k_v neighbor operands. This network has at most k_v connected components. If it contains b_v OR gates, its undirected connectivity requires at least |U_v|+b_v−k_v edges, while fan-in two allows at most 2b_v. Thus b_v≥|U_v|−k_v. The lower OR gates counted for different centers are disjoint. Indeed a gate feeding centers v and w would have a support with at least two vertices, both common neighbors of v and w, giving a four-cycle. A singleton input itself costs zero. Upper and lower OR gates are disjoint by the single-level condition. Adding the three counts gives

$$\mathrm{size}\ \ge\ k+(k-1)+\sum_v (|U_v|-k_v) = k-1+\sum_v|U_v|\ \ge\ m+t-1.$$

For the upper bound, orient each edge toward one endpoint in a minimum cover. Every cover vertex has an incident edge going outside the cover and thus receives at least one edge. At each cover vertex combine all its assigned neighbors by OR, then AND that result with the center. OR the resulting t outputs. This uses (m−t)+t+(t−1) gates.

## Lifting an AND that has no false positives

This argument also applies when the original circuit has many AND levels. Suppose it is correct on a specified table of positive and negative inputs, every AND gate is zero on every negative input, and every nonconstant primary input is one on some negative. Then there is a single-level circuit of at most the same size correct on that table.

Keep the current output as an OR of already extracted terms and one residual circuit. Initially there are no extracted terms. Work in the trimmed residual circuit, selecting the earliest live AND h. Its ancestors are OR-only. If h is the residual output, it is already a final product. Otherwise substitute zero at every use of h in the residual, keep its own computation, and replace the old residual output r by h OR r[h:=0]. When h=0, this gives exactly r. When h=1 the input is positive, so the full output, including the previously extracted terms, is correctly one. Substitution can only decrease gate values. All remaining ANDs are consequently still zero on every negative input.

Every direct reader of h in the residual folds away because one operand is now constant. At least one such reader existed, paying for the new OR. Readers are distinct from h's ancestors. Keep any OR-only ancestors also used by previously extracted terms. No reader of h can be a gate in a previously extracted term, because those terms were frozen with OR-only ancestors. The residual now contains strictly fewer AND gates. If only OR gates remain, the residual must be zero. An OR-only residual containing any primary input would accept some negative input. Fold away this zero and its reader. The resulting circuit is single-level, since every extracted product has OR-only ancestors and goes into the final disjunction. The treatment of zero here is just constant folding and introduces no gates.

## Application to the assigned tables

Each table uses ten nonzero primary inputs. Its fourteen positive columns are the graph edges, and its negative columns include every maximal independent set. Monotonicity therefore determines the output on every subset of the ten vertices. Direct enumeration finds no four-cycle in any graph and finds maximum independent-set size four in all of them. This gives m=14 and t=10−4=6. Every vertex belongs to some maximal independent set, as required by the lifting argument.

The counting argument yields a necessary condition useful in an unrestricted search: at least one AND must be one on a negative input in any circuit of size at most 18. The independently checked rectangle-partition certificate in `FormulaLowerBound.md` also requires at least one reused intermediate wire. The two conditions can refer to different wires.

For context, Jukna studies the single-level model and its separation from unrestricted monotone circuits. The host's first note discusses related lower bounds for graphs without four-cycles. This note supplies its own counting and lifting arguments. [Jukna, SIAM Journal on Computing](https://doi.org/10.1137/S0097539705447001) · [Host's first note, section 7](https://pequalnp.com/papers/note-1)
