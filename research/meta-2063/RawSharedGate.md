# One shared gate on two raw inputs

On the 52 incidence and 234 quadrangle tests of the order-three projective plane, every monotone binary circuit whose only shared intermediate is an AND or OR of two raw coordinates needs **at least 64 gates**. The intermediate can have any fanout. When it is the OR of an incident point and line, the lower bound is **66 gates**. Here a gate is shared if at least two downstream input pins in the output cone read its value. The usual point-star formula uses 64 gates, so the minimum in the class *allowing* one shared raw-input gate is 64. The desk problem allows arbitrary shared computations. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## From a circuit to ordinary rectangles

Discard dead gates. For the conjunction case, fold constants and remove repeated operands first. If the shared gate disappears, the [known formula lower bound](QuadrangleFormula.md) applies. A raw conjunction of distinct variables is either false on every positive row or tests for one incidence edge. In the first case, replacing it by zero preserves correctness. In the second, it is zero on every negative input. Write the output context as $C[h]$. The formula $h\lor C[0]$ accepts every positive and rejects every negative. Folding the inserted zeros eliminates at least one reader, and the final OR adds at most one gate. Both constructions yield an ordinary formula within the original gate budget.

For $h=x\lor y$, cut its output wire in the original reachable circuit, counting repeated pins separately. The exterior is a formula with raw variables and a new variable $h$. Write $L$ for its number of ordinary leaves and $d\ge2$ for its number of $h$ leaves. The entire circuit has $1+(L+d-1)=L+d$ gates. We bound $L$ while granting the helper as many uses as desired.

A positive row $e$ is an incident point–line pair. A negative column $M$ consists of a quadrangle and its three exterior lines. The monotone formula protocol assigns every cell to a leaf whose variable is true on $e$ and false on $M$. The helper can claim a cell precisely when $e$ meets $\{x,y\}$ and $M$ misses $\{x,y\}$. Call these cells optional. Every other cell must be assigned to exactly one of the two endpoints of $e$. On optional cells, the ordinary endpoints may both remain unused. This relaxation drops all restrictions on the rectangles claimed by the helper.

Merge ordinary rectangles at each label $v$ having the same row set. Record their distinct nonempty row sets in a family $F_v$ on the four flags through $v$. If its size is at least four, replace it with the four singleton row sets, preserving each cell's original assignment. Write $t_v=|F_v|$ and $L'=\sum_v t_v\le L$. In a given column, each label selects a disjoint union of its sets. A label present in $M$ selects nothing. Whenever the other endpoint of a nonoptional flag is in $M$, that flag must be selected at $v$.

## The finite bound

Define $a_v$ as the number of nonoptional cells assigned to $v$, so $\sum_v a_v=A$, the total nonoptional area. To distinguish possible four-flag families, use a bit $P_v(f)$. It equals one if, for every other flag $j$ at $v$, some set in $F_v$ contains $j$ and omits $f$. This feature comes from the earlier formula proof. Its use here relies only on its being fixed when $F_v$ is fixed. [Earlier private-flag argument](https://github.com/Great-Leader-of-ISLAND/pequalnp-proofs/blob/f6fb2e9c13cefb02a20dfb98505d8368a510bad5/research/CoFormula1963Private.lean)

Tag each flag $f=(p,\ell)$ by the sorted pair of distance vectors $(d(p,s),d(\ell,s))$ for $s=x,y$ in the incidence graph. Each certificate specifies an integer $B>0$ and coefficients $c_v(f),b_v(f)$ depending only on the tag of $f$ and whether $v$ is a point or line. For an incident flag $e$, assign its endpoint the score

$$
S(v,e)=Bt_v+a_v+\sum_{f\ni v}\big(4\mathbf{1}_{e=f}-1\big)
       \big(c_v(f)t_v+b_v(f)P_v(f)\big).
$$

For each fixed $v,f$, the four multipliers sum to zero over $e\ni v$. Thus summing $S(p,e)+S(\ell,e)$ over all flags gives exactly $4(BL'+A)$.

For each flag, enumerate the two endpoint families of at most three nonempty row sets, or the four singletons. The checker considers all locally allowed unions independently in each column. It minimizes the sum of the two areas conditional on exactly one endpoint taking the common flag, also allowing neither endpoint on optional cells. The count and private terms are fixed by the two families. The minimum over family pairs is a lower bound on the true flag score. If the sum of these 52 minima is $T$, then $L\ge (T-4A)/(4B)$.

| Inputs of the shared OR | Pairs | Nonoptional area $A$ | Lower bound on ordinary leaves | Integer lower bound |
|---|---:|---:|---:|---:|
| Two points | 78 | 11,304 | 59,578 / 972 | 62 |
| Two lines | 78 | 11,088 | 54,622 / 892 | 62 |
| Incident point and line | 52 | 11,412 | 82,989 / 1,304 | 64 |
| Nonincident point and line | 117 | 11,112 | 69,744 / 1,140 | 62 |

Two explicit permutations preserving the thirteen lines generate the four displayed orbits on the 325 unordered pairs. The [integer verifier](verify_raw_shared_gate.py) checks the permutations, orbit coverage and each fraction, using the sibling [plane definitions](verify_plane_formula.py). Run `python verify_raw_shared_gate.py` with Python 3.10 or later. The coefficients are provided in the source and can be verified without an optimizer. Adding the two mandatory helper occurrences proves the gate bounds.
