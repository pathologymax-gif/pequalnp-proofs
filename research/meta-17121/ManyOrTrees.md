# Independent shared OR trees of arbitrary support size

For each of the four projections, every binary monotone circuit with pairwise incomparable shared gates, all of whose input cones contain only ORs, requires **at least 19 gates**. Here two gates are incomparable if neither feeds the other, even indirectly. The rest of the circuit may compute arbitrary monotone formulas. The star formula attains this bound. This note completes the cases with at least three shared gates, at least one of which uses three or more distinct primary variables. The other cases are covered in [OneSharedGate.md](OneSharedGate.md), [TwoRawHelpers.md](TwoRawHelpers.md), [TwoOrTrees.md](TwoOrTrees.md), and [ManyRawHelpers.md](ManyRawHelpers.md).

## The counting bound

Cut the outputs of the $r$ shared gates. Their input cones are pairwise gate-disjoint OR trees, since a fork within their union would introduce another shared gate below one of them. The exterior is a formula. Write $A_i$ for the distinct nonconstant raw variables under tree $i$. Empty and singleton supports can be replaced by zero or a raw variable, and repeated equal supports can be combined, reducing the number of shared gates without increasing size. Apply the result for one or two shared gates or repeat this reduction as needed. Assume the supports are distinct and all have size at least two.

Let $t=\sum_i(|A_i|-2)$ and $q=r+t$. The inner trees require at least $q$ gates. Each shared gate has at least two outer readers, so the exterior formula uses at least $2r$ helper leaves.

Every vertex $v$ appearing in at most one support also needs its own ordinary outer leaf. If no support contains $v$, choose any graph neighbor $u$ and a maximal independent set $M$ containing $u$. Every helper true on $vu$ is true on $M$. If there is a unique support containing $v$, choose another element $w$ in it. We can choose a neighbor $u$ of $v$ equal or nonadjacent to $w$. Indeed, $v$ has at least two neighbors and two distinct vertices have at most one common neighbor, because the projection contains no four-cycle. Extend $\{u,w\}$ to a maximal independent set, allowing $u=w$. The unique helper containing $v$ is true on $M$. Every other helper true on $vu$ contains $u$ and is also true there. In either case only the ordinary variable $v$ can distinguish $vu$ from $M$. The verifier checks that every maximal independent set really occurs among the negative samples.

There are $2r+t$ variable incidences across the supports. At most $\lfloor(2r+t)/2\rfloor$ vertices can appear at least twice. Counting the forced ordinary leaves, the $2r$ helper leaves and the $q$ inner gates gives a total size of at least

$$
9+q+2r-\left\lfloor\frac{2r+t}{2}\right\rfloor
=9+2r+\left\lceil\frac{t}{2}\right\rceil.
$$

This excludes $r\ge5$ at every support size. It also excludes $r=4,t\ge3$ and $r=3,t\ge7$. The all-binary case $t=0$ is established in [ManyRawHelpers.md](ManyRawHelpers.md).

## Remaining support families

The verifier enumerates every triple with $1\le t\le6$ and every quadruple with $1\le t\le2$. It first counts the vertices that belong to at most one support in the actual family. Next it fixes all cut helpers to one, keeping all positive edges and the negative tests where all helpers were one. If that restricted table needs more than $19-q-2r$ ordinary leaves, an 18-gate circuit is impossible. The final screen uses the full table with all helper labels present and counts the forced ordinary leaves. Both screens use the forced-rectangle argument in [TwoOrTrees.md](TwoOrTrees.md).

| Shared trees | Total support excess $t$ | Unordered families per projection |
|---:|---:|---:|
| 3 | 1 | 118,800 |
| 3 | 2 | 529,200 |
| 3 | 3 | 1,664,320 |
| 3 | 4 | 4,055,625 |
| 3 | 5 | 8,066,880 |
| 3 | 6 | 13,471,540 |
| 4 | 1 | 1,702,800 |
| 4 | 2 | 10,048,500 |

Of 158,630,660 families across all projections, just three survive these screens. They are triples with $t=1$ in projection 3. Their support masks, indexed by the order of the ten nonzero seeds, are $(144,384,274)$, $(144,384,280)$ and $(272,384,208)$. Fix the middle helper to one. The remaining formula may have at most $19-(3+1)-2=13$ leaves. Four integer-dual branch leaves across the three cases certify a larger lower bound.

Run **python verify_many_or_trees.py** with **ManyOrTrees.cs**, **many_or_trees.json.gz**, **seed_tables.json**, and **verify_kw_first_shared.py** in this directory. The Python verifier checks the graph hypotheses, builds the C# enumerator, verifies all family counts independently via a generating-function recurrence, and replays the residual integer duals. Replay uses Python's standard library plus .NET SDK, Windows .NET Framework, or Mono. This restricted optimum leaves open circuits with mixed shared input cones or with dependencies among shared gates.
