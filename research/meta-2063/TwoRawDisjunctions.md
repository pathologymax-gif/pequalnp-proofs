# Two shared binary disjunctions in the order-three plane

On the 52 positive flags and 234 negative quadrangles of L-meta-2063, any pruned binary monotone circuit whose only two shared intermediate gates are disjunctions of distinct raw pairs with different supports has **at least 65 gates**. Each shared gate may have arbitrary fanout. All 52,650 unordered support families are covered. The unrestricted desk statement remains open in this argument. [Desk statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

Cut the two shared outputs into helper leaves. The remaining gates form an outer formula. Denote its ordinary leaf count by $L$ and its helper leaf count by $d$. Both cut gates have at least two live reads, hence $d\ge4$. The gate count is $2+L+d-1$. We show $L\ge60$.

Follow the monotone Karchmer–Wigderson protocol down that formula. At each OR the positive input chooses a true child, and at each AND the negative input chooses a false child, breaking ties in a fixed order. Leaf transcripts partition the flag/quadrangle matrix into rectangles. A raw leaf with label $v$ uses rows in the four-flag star of $v$ and only columns omitting $v$. A helper can take cell $(e,M)$ only when one of its two raw pairs meets the flag $e$ and misses the quadrangle input $M$. Call these cells optional. Every other cell is mandatory and receives charge one. Every leaf occurrence gives at most one rectangle; each mandatory cell must belong to a raw rectangle. The argument permits every optional cell to go uncovered.

## Local row families

At vertex $v$, the raw rectangles labeled $v$ have nonempty row sets contained in its four incident flags. For a fixed column their active row sets are disjoint. We record a state $i$ with cost $n_v(i)$ and a menu of all unions of disjoint subfamilies. Duplicate row sets can be merged by taking the union of their columns. Four singleton row sets allow every row union, so a vertex with at least four raw rectangles can always be represented at cost four. For up to three row sets we enumerate all families. If another state has a superset of the menus at equal or lower cost, the checker retains the larger menu. Every actual raw partition therefore has a representing state at each vertex, with $\sum_v n_v(i_v)\le L$.

For a column $M$, vertex $v$ must choose an empty union if $v\in M$. Its union must include each mandatory flag $vw$ with $w\in M$, since the other endpoint cannot cover it. For adjacent $p,l$, additionally require exactly one of their unions to cover flag $e=pl$ on every mandatory column cell, and at most one on every optional cell. For fixed states $i,j$, let $A_e(i,j)$ denote the sum over columns of the minimum total charge of their two unions satisfying these tests. If any column has no admissible choices, the pair of states is infeasible. In a genuine partition the actual row unions are admissible everywhere. When summing over the 52 flags, the charge at every vertex is counted four times. Consequently $\sum_e A_e(i_p,i_l)\le4N$, where $N$ counts the mandatory cells.

## Integer lower bound

The certificate supplies integers $B>0$, $w\ge0$, and a potential $b_{e,v,i}$ for each incidence of a flag $e$ with a vertex $v$ and one of its states $i$. The following number is at most $BL$:

$$
\sum_v\min_i\left(Bn_v(i)+\sum_{e\ni v} b_{e,v,i}\right)
+\sum_{e=pl}\min_{i,j\ \mathrm{feasible}}\left(wA_e(i,j)-b_{e,p,i}-b_{e,l,j}\right)-4wN.
$$

Indeed, insert the actual representing states into the two sums. Each potential cancels with its contribution at the other minimum. The remaining area term is nonpositive by the preceding counting argument. This supplies a directly verifiable lower bound for any integer potentials.

The checker constructs two explicit incidence-preserving point permutations and their induced line permutations. Breadth-first search partitions all unordered pairs of distinct supports into 59 orbits of total size $\binom{\binom{26}{2}}2=52{,}650$. For $B=10{,}000$, the smallest verified numerator across those representatives is $592{,}177$. Thus $L\ge60$, giving the claimed 65-gate lower bound.

Run `python verify_two_raw_ors.py` alongside `two_raw_ors_certificates.json.gz` and the existing `verify_plane_formula.py`. The checker uses only Python's standard library. To split the replay across processes, pass disjoint lists of orbit indices from 0 to 58. The reported bounds certify the restricted circuit class independently of the program used to choose the integer potentials.
