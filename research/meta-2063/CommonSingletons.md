# Cofactor bounds for a circuit with any number of shared gates

On the order-three projective-plane quadrangle tests, suppose that all shared values exposed when expanding a circuit's output accept the **same three singleton inputs**. The circuit then needs **at least 64 binary AND/OR gates**, allowing arbitrary sharing and nesting inside and between the private computations. The test is a sufficient structural condition. A shared value is evaluated on singleton inputs of the full Boolean cube, even though these singletons are absent from the project's test table. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## Cutting the shared wires

Use the reachable part of the DAG. Expand the output towards the inputs but stop at each encountered intermediate whose value has at least two outgoing uses. Call the values where expansion stops the *exposed shared values*. A shared gate behind another shared gate might also appear here if it has a separate path to the output. The exposed gates can depend on each other. All remaining gates in the outer expansion occur once, so the exterior is a binary formula in ordinary inputs and the exposed values.

Let $d$ count occurrences of exposed shared values in the exterior, $L$ its ordinary input leaves, and $q$ all reachable gates outside this exterior formula. The physical size is $q+L+d-1$. For any circuit with sharing, $d\ge2$. Take a shared gate with no shared gate downstream. Every gate downstream of it is expanded, so each outgoing use of that shared value produces its own leaf occurrence. Circuits with no shared gate have the [known 64-gate formula bound](QuadrangleFormula.md).

Suppose a set $S$ of raw indices satisfies the common-singleton hypothesis. On every negative input $M$ containing an index from $S$, all exposed values are one by monotonicity. Substitute the constant one at every exposed occurrence. All 52 positive rows still pass, and those negative rows retain their original values. After folding constants, the ordinary formula has at most $L$ leaves. This reasoning applies whenever all exposed values are one on the specified negative rows, even if their singleton behavior is unknown.

## Finite cofactor bounds

The [adjacent-star argument](RawSharedGate.md) bounds the number of ordinary leaves on exactly these retained columns. The numbers below are certified lower bounds. A negative set for a smaller $S$ can also be used when the known common set is larger.

| Common singleton witnesses | Minimum number of ordinary leaves |
|---|---:|
| One point | 44 |
| One line | 43 |
| Two points | 58 |
| Two lines | 57 |
| One incident point and line | 60 |
| One nonincident point and line | 57 |
| Any three distinct vertices | 59 |
| Any four distinct vertices | 60 |

The [integer verifier](verify_common_singletons.py) checks [ten new coefficient records](common_singleton_certificates.json) and six cofactor records from the [disjunction certificate](shared_disjunction_certificates.json). It verifies the one-, two- and three-element bounds on all 2,951 sets under incidence-preserving permutations. The [four-element replay](verify_shared_disjunctions.py) checks all 14,950 sets exclusively with cofactor certificates. These proofs have no assumptions on the internal circuit used to produce an exposed value.

## Why three common witnesses suffice

Let $t$ be the number of distinct nonconstant exposed values, counted by gate. If $t=0$, folding the exposed constant ones yields an ordinary formula. Otherwise the earliest nonconstant exposed value depends essentially on every common singleton variable. It rejects the empty input, and changing only any one of those coordinates makes it true. Three such variables require at least two gates in its connected cone, all outside the exterior. The other $t-1$ nonconstant exposed gates are later and add distinct private gates. Thus $q\ge t+1$. We also have $d\ge t+1$, since every exposed gate appears at least once and a downstream-maximal shared gate appears at least twice.

If $t\ge2$, the size is at least $3+59+3-1=64$. If $t=1$ and $q\ge4$, it is at least $4+59+2-1=64$. In the remaining case, fold all constant exposed signals in the exterior. The sole nonconstant signal is computed by at most three gates. Any single-output monotone network of at most three gates can be made into a formula of no greater size. After bypassing repeated inputs, internal reuse would require the first gate $u$ to feed both later gates. The resulting output has the form $u\mathbin{\circ}(u\mathbin{\star}z)$, where $\circ,\star$ are AND or OR. Idempotence or absorption removes the repeated use. With at most this one shared output remaining, the [three-gate private formula result](SharedDisjunctions.md) proves the bound.

The same calculation constrains smaller common sets through $q+d$. With two common witnesses, $q+d\ge8$ suffices in every geometric case. With one, $q+d\ge22$ suffices. In particular, a circuit with a sole shared signal that accepts two singleton inputs and whose private cone has at least six gates also requires 64 gates.
