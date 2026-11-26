# Exact monotone formula size for the four G11 projections

Each of the four 32-bit tables in the assigned row requires exactly 19 gates in a formula over binary AND and OR. Thus any proposed circuit of 18 gates needs at least one intermediate gate whose output feeds more than one other gate. The full desk question includes such circuits. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-17121)

## Interpreting the masks

Read bit position $j$ across the eleven seed words as the set of vertices with input value one on test $j$. One seed is the constant zero. In every projection, positions 0 through 13 are the fourteen edges of a graph on the ten surviving vertices. The remaining nonempty tests are precisely its inclusion-maximal independent sets. This can be checked over the 1,024 subsets. The additional tests are empty inputs. A monotone formula that gives the requested projected outputs therefore computes the graph's edge function on every input.

Every graph has an independent set of size four and none of size five. Its minimum vertex cover has six vertices. Assign each edge to one incident cover vertex. At each of the six centers take the AND of the center and the OR of its assigned neighbors, then OR the six stars. Every center has an edge to a vertex outside the cover, by minimality, so every star is nonempty. This gives fourteen neighbor leaves and six center leaves, hence 19 binary gates.

## Necessary rectangle partition

Index a table by positive edges $e$ and negative maximal independent sets $M$. Every cell must receive a vertex $v\in e\setminus M$. A monotone formula with $L$ variable leaves partitions this table into at most $L$ labeled rectangles. At an OR send each edge row to one child true on that row, keeping all negative columns. At an AND send each negative column to one child false on that column, keeping all positive rows. Fix the choice in a tie. At a variable leaf $v$, every remaining row contains $v$, and every remaining column omits $v$. The constant-zero seed can receive no positive rows. This is the usual monotone Karchmer–Wigderson correspondence. [Karchmer and Wigderson, 1988](https://doi.org/10.1145/62212.62265)

Merge rectangles with the same label $v$ and the same nonempty row set $S$ by taking the union of their column sets. For each $v$ and nonempty $S\subseteq\{e:v\in e\}$, let $y_{v,S}$ select that rectangle. For each $M$ omitting $v$, let $z_{v,S,M}$ select its use on column $M$. The variables are binary, $z_{v,S,M}\le y_{v,S}$, and the sum of the $z_{v,S,M}$ that cover each cell $(e,M)$ must equal one. Every partition of at most $L$ rectangles gives a feasible assignment with $\sum y\le L$.

## How the exact certificate is checked

The verifier establishes that $\sum y\le19$ is impossible in each projection. For generation, add a variable $s_{e,M}\in[0,1]$ to each cell sum and give it cost 32. A genuine partition sets all of these variables to zero. The resulting linear model has objective $c^Tx=\sum y+32\sum s$, cell equalities $Ax=1$, and inequalities $Bx\le0$ from $z-y\le0$.

The certificate splits a binary variable into its two values at each internal node. At a leaf, use the supplied integer multipliers $p$ for the equalities and $q\le0$ for the inequalities. Put $D=100000$ and $r=Dc-A^Tp-B^Tq$. Every feasible assignment within the branch bounds $l\le x\le u$ satisfies

$$
D c^Tx\ \ge\ \sum p+\sum_j\min(r_jl_j,r_ju_j).
$$

Every stored lower bound exceeds $19D$, using only integer addition and multiplication. The proof uses weak duality. The separate generator used HiGHS to find the multipliers and branches.

| Deleted vertex | Maximal independent sets | Certificate leaves | Least verified numerator, denominator 100000 |
|---|---:|---:|---:|
| 0 | 18 | 52 | 1,902,217 |
| 1 | 16 | 79 | 1,901,190 |
| 2 | 17 | 92 | 1,902,083 |
| 3 | 15 | 105 | 1,900,332 |

Run `python verify_kw_formulas.py` with `seed_tables.json` and `kw_formula_certificates.json.gz` in the same directory. The verifier uses Python's standard library and arbitrary-precision integers. The four checks are independent of the SAT encoding for the unrestricted circuit problem. To regenerate the trees with SciPy 1.17.1, run `python kw_certify.py` in the directory containing `kw_integral_partition.py`.
