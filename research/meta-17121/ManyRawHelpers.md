# Three or more shared ORs of input pairs

On every projection of L-meta-17121, a circuit whose output computation uses at least three distinct shared internal gates, each the OR of two original variables, needs at least 19 binary gates. All other internal gates may be either AND or OR and have fanout one. Inputs may have arbitrary fanout. The graphs have ten vertices, fourteen edges, minimum degree two, and no cycle of length four.

Discard unused gates. Repeated identical operands and duplicate computed words can be replaced by the existing input or gate; the desk's dominance condition also prohibits them. Write $r$ for the number of shared gates. Cut their outputs and consider the remaining formula. An 18-gate circuit gives it at most $19-r$ leaves, of which at least $2r$ are occurrences of the cut signals. At most $19-3r$ ordinary variable occurrences remain.

## Five or more helpers

Form a graph $H$ on the ten variables, using the pair in each shared OR as an edge. Each vertex $v$ of degree at most one in $H$ must occur as an ordinary leaf. If $v$ has no incident helper, take any neighbor $u$ in the target graph $G$ and extend $\{u\}$ to a maximal independent set $M$ of $G$. Compare the positive test $vu$ to the negative test $M$. An input-pair OR that is true on $vu$ contains $u$, so it is true on $M$ too. The only raw variable that distinguishes the two tests in the required direction is $v$.

If the unique helper containing $v$ has partner $w$, choose a neighbor $u$ of $v$ with $u=w$ or $u$ nonadjacent to $w$. Such a choice exists because $v$ has at least two neighbors and two vertices have at most one common neighbor in a graph with no four-cycle. The set $\{u,w\}$ is independent, allowing equality of the two elements. Extend it to a maximal independent set $M$. On the positive edge $vu$, every true helper contains $u$ or equals $v\lor w$. Both alternatives are true on $M$. Again only the ordinary input $v$ can distinguish the tests. The verifier checks that all maximal independent sets occur in the row.

The total degree of $H$ is $2r$, so at most $r$ vertices have degree at least two. The exterior formula must have at least $10-r$ ordinary leaves and $2r$ helper leaves. Including the $r$ cut gates, the circuit therefore has at least $9+2r$ gates. This gives 19 as soon as $r\ge5$.

## Three or four helpers

For each of the 45 possible input pairs compute its OR word. Consider every triple and quadruple of these pairs. Use the positive-edge/negative-maximal-independent-set rectangle partition associated to the exterior formula, with the additional helper leaf labels. At a cell where only raw label $v$ can distinguish the tests, a $v$-labeled leaf must occur. If $v$ occurs once, its rectangle must contain the product of all rows and columns forced to that single leaf. Join mandatory raw labels whose forced rectangles overlap. At least one label at each conflict edge must appear twice. The number of mandatory labels plus the minimum vertex cover of these conflict edges, plus $2r$ helper occurrences, is a lower bound on all exterior leaves. [One shared gate](OneSharedGate.md)

| Deleted vertex | Triple families | Triples needing an additional certificate | Quadruple families | Quadruples needing an additional certificate |
|---:|---:|---:|---:|---:|
| 0 | 14,190 | 0 | 148,995 | 0 |
| 1 | 14,190 | 39 | 148,995 | 0 |
| 2 | 14,190 | 8 | 148,995 | 0 |
| 3 | 14,190 | 49 | 148,995 | 0 |

For the remaining triples, removing the helper rectangles leaves at most ten ordinary rectangles, mutually disjoint. At every cell where no helper can distinguish the tests, exactly one ordinary rectangle must remain. At each other cell, zero or one can remain. We encode the ordinary rectangles as in the [formula lower bound](FormulaLowerBound.md) and add a cell slack between zero and one. An uncovered cell costs zero where a helper is eligible and 32 otherwise. Every putative exterior formula yields a feasible solution with total cost at most ten. An integer dual bound above ten therefore excludes it.

The other certificate option fixes a set of $j$ helpers to one. All positive tests remain true by monotonicity. Retain only negative tests on which every fixed helper already was one. The reduced formula has at most $16-2j$ leaves, and the remaining helpers may be leaf labels. An integer lower bound above this budget excludes the family. The ordinary-rectangle bound excluded 93 triples using one dual leaf each. The remaining three triples required 11 dual leaves in total. One used the full table and two fixed one helper.

Run `python many_raw_helpers.py` with `seed_tables.json`, `many_raw_helpers.json.gz`, and `verify_kw_first_shared.py` in the same directory. Replay needs only Python's standard library. It verifies the graph hypotheses, enumerates all 652,740 triple and quadruple families, checks that exactly the unresolved family keys have stored evidence, and verifies each certificate using Python integers. Optional regeneration with SciPy uses `python many_raw_helpers.py --generate` and the two adjacent generator modules `kw_integral_partition.py` and `kw_first_shared.py`.
