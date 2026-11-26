# Two independent shared OR trees

Consider any of the four tables in L-meta-17121. Suppose a binary monotone circuit has exactly two distinct shared intermediate gates. Suppose their input cones use only OR, and neither gate occurs in the other gate's input cone. If either inner tree uses at least three distinct nonconstant raw inputs, the circuit needs **at least 19 gates**. The four 19-gate upper bounds are exhibited separately. The case in which both ORs are binary operations on raw inputs is covered by a separate calculation.

## Cutting both trees

Delete unused gates and simplify repeated operands. The two inner cones contain disjoint sets of gates. An intersection would either exhibit a third shared gate at the fork or put one shared gate upstream of the other. The cones therefore form two formula trees. Write $A,B$ for their raw-variable supports. Syntactic repeats and the constant zero are allowed. The two positive-size ORs compute $h_A=\bigvee_{a\in A}x_a$ and $h_B=\bigvee_{b\in B}x_b$. Their combined gate cost is at least $q=|A|+|B|-2$, by counting the leaves of the two trees. Overlap between the two sets of raw variables is allowed.

If a support is empty or singleton, replace its gate by the corresponding constant or raw input. If the supports coincide, replace the two trees by one tree for their common OR. In each case the previously checked one-shared lower bound applies. The computation therefore considers distinct supports of size at least two and $q\ge3$.

In a circuit of size at most 18, cutting the two trees leaves an outer formula of at most $19-q$ leaves. Each shared gate gives at least two occurrences in this formula. Fix both helper inputs to one. The resulting formula still accepts every positive test, by monotonicity, and rejects every negative test where both helpers were already one. Folding constants removes at least four helper leaves. Hence this ordinary-variable formula has at most $15-q$ leaves. If only one helper is fixed, the analogous bound is $17-q$ leaves with the other helper still available.

## Forced raw labels

The formula game table has a row for each edge and a column for each selected negative test. A raw or helper label is available if it is one on the positive and zero on the negative. A formula gives a partition into rectangles with available labels. For every raw vertex, collect its cells where it is the unique available label. A single occurrence of this label must cover the Cartesian product of their row and column projections. If the products for two vertices meet, at least one of these labels needs a second occurrence. The resulting lower bound on ordinary leaves is the number of forced labels plus a minimum vertex cover of these conflicts. Conflicting vertices must be adjacent because their two row projections have to share an edge. The computation finds the cover by branching on the endpoints of an uncovered edge.

Apply the forced-label bound to the double cofactor with ordinary labels only. When that fails, some tables have integer dual certificates for the same $15-q$ threshold. In the original table both helpers are available to label cells, and four helper leaves must be charged in addition to the forced ordinary leaves. For the few remaining cases a single cofactor with the other helper retained as an extra label has an integer dual bound above $17-q$.

| Projection | Double-cofactor forced labels | Double-cofactor dual | Original forced labels | Single-cofactor dual | Support pairs |
|---|---:|---:|---:|---:|---:|
| 0 | 511,061 | 261 | 263 | 3 | 511,588 |
| 1 | 510,583 | 472 | 526 | 7 | 511,588 |
| 2 | 510,670 | 533 | 377 | 8 | 511,588 |
| 3 | 509,840 | 733 | 989 | 26 | 511,588 |

Each row has $2^{10}-11=1{,}013$ eligible supports. The count is $\binom{1013}{2}-\binom{45}{2}=511{,}588$ after reserving the cases in which both supports have size two. Every one of the 2,046,352 remaining support pairs is excluded.

## A dependent pair

The companion [common-cofactor certificates](SerialShared.md) also exclude the case of exactly two comparable shared gates with OR-only input cones. Their supports are nested, say $A\subseteq B$. After bypassing a singleton or constant support, choose any pair $P\subseteq A$. On every negative test meeting $P$, both helpers are one. This allows us to fix both helpers to one, retaining every positive test and every negative meeting $P$.

Let $m$ denote the private gate count and $d$ the number of outer helper leaves. Then $m+d\ge5$. If $m\ge3$, the final shared gate alone has at least two outer readers. If $m=2$, the two gates are the entire private part and the earlier shared gate has at least one outer reader beyond the later shared gate. Thus a circuit of size at most 18 would leave an ordinary formula with at most $19-m-d\le14$ leaves. All 180 raw-pair tables, 45 per projection, require at least 15. In fact the same argument applies to any two shared gates whose values are both one on every negative meeting some fixed pair, irrespective of their operators. With at least three shared gates the same condition on every exposed helper still suffices, since $m\ge3$ and the last shared gate contributes at least two outer leaves.

Run `python verify_two_or_trees.py` with `two_or_trees.json.gz`, `seed_tables.json`, and `verify_kw_first_shared.py` in the same directory. Replay uses standard-library Python and integer arithmetic throughout. The certificate generator used SciPy/HiGHS. This is a bound for the indicated two-helper class. The unrestricted 18-gate question remains open here.
