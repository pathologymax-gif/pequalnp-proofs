# Two independent shared computations still require 19 gates

For each of the four projected edge functions in L-meta-17121, a binary monotone circuit with exactly two shared internal gates, neither upstream of the other, needs at least 19 gates. Both private computations may mix AND and OR, and their outputs may have arbitrary fanout. Consequently, if an 18-gate circuit exists, it has at least three shared gates or has two shared gates with a directed path between them. This combines with the [one-shared-gate bound](OneSharedGate.md). A formula supplies the 19-gate upper bound for the class allowing up to two independent shared gates.

## Private and exterior costs

Remove unused gates and simplify constants and repeated operands. The private input cones of the two shared gates have disjoint internal gates and are formula trees. A common internal gate would create another branch before reaching the two incomparable outputs. Cutting the outputs leaves an exterior formula in the ten ordinary variables and the two helper signals $h,j$. If the private trees have $g,d$ gates, an 18-gate circuit has at most $19-g-d$ exterior leaves. At least two of them use each helper, so at most $15-g-d$ ordinary occurrences remain.

Let $T$ denote the target. For any downstream context $C$, a helper with $h\le T$ can be removed as a shared signal using $T=h\lor C[0]$. The analogous identity for $T\le h$ is $T=h\land C[1]$. Constant folding removes at least two distinct readers and only one final gate is added. A helper with no true positive can also be replaced by zero. These operations leave at most one shared gate. Hence both surviving helpers have a false positive and a false negative.

**Each private cost is at most ten.** Choose a negative maximal independent set $M$ with $h(M)=1$. For each vertex $v$ outside $M$, maximality supplies a neighbor $u\in M$. On the positive edge $vu$ and the negative test $M$, the only ordinary variable equal to one on the former and zero on the latter is $v$. The helper $h$ cannot distinguish this pair in that direction. If $v$ occurs neither in the exterior as an ordinary variable nor inside the private formula for $j$, then every exterior leaf is at most its value on $M$, contradicting the required output by monotonicity. The complement of $M$ has at least six vertices. Counting ordinary leaves in the two available places gives $6\le (15-g-d)+(d+1)=16-g$. Interchanging the helpers also gives $d\le10$.

**The sum of private costs is at most thirteen.** If $g+d\ge14$, at most one exterior occurrence is an ordinary variable. With none, the exterior computes a monotone function of two arguments, which uses each argument at most once after simplification. If an ordinary variable $x$ occurs, there are exactly five exterior leaves and four gates. For its monotone formal function $F$, write

$$
F(h,j,x)=F(0,j,x)\lor\bigl(h\land F(1,j,x)\bigr).
$$

Each cofactor is a monotone function of the two formal variables $j,x$, hence a constant, projection, AND or OR. Each costs at most one gate. The replacement uses at most four gates and contains a single occurrence of $h$. In either case, at most one shared gate remains.

## Formula representatives and edge corrections

The [inner-formula recurrence](OneSharedGate.md) keeps, at each cost, representatives whose error sets contain no error set of an earlier representative of equal or lower cost. Replacing a private formula by a dominating representative preserves the target because it can only turn on additional positive bits and turn off negative bits. This applies to every occurrence at once. The two trees can be replaced independently. If one replacement is an input, or a shared signal disappears, the one-shared bound applies.

For a pure disjunction $w$ of $s$ raw variables, suppose $w\le h$ on every negative test. Let $P$ consist of target edges on which $h$ is one and $w$ is zero. If $C[h]$ was exact, so is $F_P\lor C[w]$, where $F_P$ is the ordinary edge function of $P$. Outside $P$, the replacement preserves each required positive value. On a negative test, $C[w]\le C[h]=0$ and $F_P=0$.

For nonempty $P$, assign each of its edges to an endpoint in a minimum vertex cover. A formula taking the OR of the resulting stars has at most $|P|+\tau(P)-1$ gates. Including the final OR and the private disjunction therefore costs at most $(s-1)+|P|+\tau(P)$. This also covers empty $P$ by omitting the correction. When the cost does not exceed $g$, the old mixed helper can be replaced by a private disjunction. For $w=0$, two distinct exterior readers disappear after substitution, so the sufficient test is $|P|+\tau(P)-2\le g$. All star corrections are unshared formulas and can be appended independently. If simplifying the first replacement leaves only one genuinely shared helper, its existing lower bound applies immediately. Otherwise the second helper retains the reader multiplicity required by the same argument.

After these reductions, a pair can contain two residual mixed representatives, or one residual representative and a nontrivial ordinary disjunction. The case of two pure disjunctions is established by the [two binary OR calculation](TwoRawHelpers.md) and [the two independent OR-tree calculation](TwoOrTrees.md). If either remaining helper's error set contains the other's, the dominated signal can instead be replaced everywhere by its partner; this again reduces to one shared gate.

## Testing the remaining pairs

For distinct helper words of combined private cost $q$, the exterior has at most $15-q$ ordinary leaves. The underlying [rectangle partition argument](FormulaLowerBound.md) assigns a positive-edge/negative-independent-set cell to a leaf whose label distinguishes it. If the only available label at some cells is $v$, then the exterior must have a $v$ leaf. A single such leaf must cover the product of all forced row and column projections for $v$. When two forced products intersect, at least one of their vertex labels needs a second occurrence. Therefore the number of mandatory labels plus the minimum vertex cover of these conflicts is a lower bound on ordinary leaves.

Compute this bound on the negative columns where both helpers equal one, after fixing both to one. Every positive test stays positive, and the retained negatives are unchanged. If needed, compute it on the full table with both helpers available as extra leaf labels. Every residual pair violates the ordinary-leaf budget in one of the two tests.

| Deleted vertex | Candidate pairs | Dominance | All-ones cofactor | Full table |
|---:|---:|---:|---:|---:|
| 0 | 79,282,117 | 178,624 | 78,901,491 | 202,002 |
| 1 | 74,636,301 | 246,007 | 74,176,924 | 213,370 |
| 2 | 78,356,275 | 195,645 | 77,987,959 | 172,671 |
| 3 | 59,428,750 | 252,541 | 58,946,430 | 229,779 |

**291,703,443 pairs were checked.** Run `python -I verify_independent_mixed.py` with `SharedGateFrontier.cs`, `MixedHelperPairs.cs`, and `seed_tables.json` in the same directory. It compiles both programs, regenerates all private formula frontiers in a temporary directory, and checks the cumulative pair counts independently from the residual population at each cost. Both formula generation and screening use integer operations. Replay requires Python and a C# compiler, with no optimizer or external certificate file. The linked earlier results provide the one-helper and pure-disjunction prerequisites.

For an independent replay, `audit_mixed_numpy.py` uses NumPy to screen all pairs and `AuditSharedFrontier.cs` to verify the coverage of the private formula frontiers; this check also requires a C# compiler.
