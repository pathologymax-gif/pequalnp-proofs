# A sole shared helper with five private gates

On the 52 incidence flags and 234 quadrangle tests of $\mathrm{PG}(2,3)$, every binary monotone circuit with a single shared intermediate computed by a private formula of at most five gates needs **at least 64 gates**. The shared output may have arbitrary fanout. The matching 64-gate construction is the point-star formula. The result extends the [four-gate bound](FourGateMixedHelper.md) on the [project's quadrangle instance](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063).

## The private formula

In a hypothetical circuit with at most 63 gates, remove unused gates, fold constants and simplify repeated operands. If no internal output has two readers, the [ordinary formula lower bound](QuadrangleFormula.md) applies. Otherwise cut the sole shared intermediate $h$. Its ancestors form a private binary formula and the exterior is a formula $C[h]$ with at least two occurrences of $h$. Replace the private formula by any minimum-size formula for its full Boolean function. This preserves the tested outputs and its reader set. Private cost at most four is already covered, so take its minimum cost to be five. The exterior has at most 59 leaves, including at least two occurrences of $h$. Therefore it has **at most 57 ordinary leaves**.

A five-gate binary formula has at most six input occurrences. A constant or an inessential input can be fixed and simplified. For each support of size $k\le6$, enumerate monotone truth functions by splitting the root into child costs $a,b$ with $a+b+1=g$ and applying AND and OR. Distinct functions are represented by their inclusion-minimal true assignments. An independent computation uses AND and Boolean duality by leaf count. Both computations give the following numbers of functions of *minimum* private cost five.

| Essential variables | Functions on a fixed support | Labeled functions on 26 inputs |
|---:|---:|---:|
| 1–3 | 0 | 0 |
| 4 | 44 | 657,800 |
| 5 | 600 | 39,468,000 |
| 6 | 5,504 | 1,267,185,920 |
| Total | | 1,307,311,720 |

The two verified incidence-preserving generators give a group of order 5,616 that preserves every test family. Enumerate support orbits, then use the stabilizer of each support to identify geometric copies of the same formula. The independent checker verifies disjointness and coverage and counts the labeled functions by multiplying the orbit size of the support by its formula-orbit size under the stabilizer.

## What the reductions leave

The [four-gate proof](FourGateMixedHelper.md) establishes the following replacements at any private cost $g$. If $h$ is bounded above or below by the target on all tests, fixing $h$ and adding one final operation gives an ordinary formula within the original gate budget. A helper rejecting all positives can be replaced by zero. For a set $P$ of positive incidence flags, a formula accepting those flags and rejecting every negative costs at most $|P|+\tau(P)-1$ gates when $P$ is nonempty, where $\tau$ is minimum vertex cover. Assign each edge to one of its endpoints in a minimum cover and take the OR of these stars.

If $P$ comprises the positives accepted by $h$ and $|P|+\tau(P)-2\le5$, substitute zero and add this correction. Otherwise try a disjunction $w$ of $s$ raw variables with $w\le h$ on every negative. If $D$ comprises the positive flags with $h=1,w=0$, the replacement $C[w]\lor F_D$ fits whenever $s-1+|D|+\tau(D)\le5$. An empty correction can simply be omitted. The only possible shared output after this replacement is [a disjunction of raw variables](SharedDisjunctions.md). The independent checker obtains cover costs by maximum matching in the bipartite incidence graph.

| Outcome | Formula orbits |
|---|---:|
| Pure disjunction | 128 |
| One-sided or rejects all positives | 153,622 |
| Replace by zero and correct | 119,962 |
| Replace by one raw input and correct | 21,075 |
| Replace by a disjunction of two and correct | 6,658 |
| Replace by a disjunction of three and correct | 3,530 |
| Replace by a disjunction of four and correct | 863 |
| Require direct rectangle bound | 64 |
| Total | 305,902 |

Every residual uses six distinct raw variables. Thirty-four have two singleton minterms and four pair minterms, 26 have one singleton and six pair minterms, and four have no singleton and nine pair minterms. The proof below evaluates the full collection of minterms for each case.

## Counting ordinary leaves

For an incidence flag $e$ and a negative quadrangle input $M$, an occurrence of $h$ can distinguish them precisely when $h(e)=1$ and $h(M)=0$. Mark exactly these cells optional. Every other cell must be covered by a rectangle labeled with one of the two raw endpoints of $e$ absent from $M$. A monotone formula gives a disjoint partition into such leaf rectangles, by following an accepting branch at each OR and a rejecting branch at each AND. Raw rectangles may also handle optional cells. Thus the [weighted adjacent-star lower bound](RawSharedGate.md) applies to the number of ordinary leaves, irrespective of the number of helper occurrences.

The checker reconstructs $h(e)$ and $h(M)$ from each formula's minterms. For each of the 52 flags it minimizes the integer score over the two incident four-edge stars with this optional-cell predicate. Required cells each contribute their row weight once, and the count and private-row transfers cancel across the four flags at a vertex. The smallest of the 64 exact rational bounds is $22{,}837{,}826/400{,}000=57.094565$. Since the number of ordinary leaves is integral, every residual requires at least **58**, contradicting the exterior budget. This proves the claimed result for a single shared intermediate whose private function costs at most five gates.

## An upper cutoff on the private cost of a possible counterexample

The mandatory raw variables also rule out every sole helper with private cost $g\ge44$. If $h$ never accepts a negative, the one-sided formula reduction applies. Otherwise let $M$ be any negative accepted by $h$. Each of the 19 vertices $v$ outside $M$ has a neighbor $u$ in $M$, since the seven-element quadrangle test is a maximal independent set. The accepted input $e=uv$ and rejected input $M$ can only be distinguished in the outer formula by a raw occurrence of $v$. The other endpoint already belongs to $M$, and $h(M)=1$ prevents the helper from distinguishing the pair. Thus $L\ge19$. Two occurrences of $h$ give circuit size at least $g+L+1\ge64$.

With $m$ negative inputs accepted by $h$, every vertex outside their intersection must occur as an ordinary leaf. For $k=0,\ldots,7$, the largest numbers of quadrangle tests containing a fixed $k$-vertex set are $234,72,24,9,4,2,1,1$, as the verifier checks by counting subcollections of each of the 234 seven-vertex sets. Separately, both endpoints of each positive flag $e$ rejected by $h$ must occur. For either endpoint $v$ of $e$, some negative contains the other endpoint and omits $v$. On this pair the helper is ineligible because $h(e)=0$. These bounds leave private costs **6 through 43** as the unsettled range for a possible one-helper counterexample, subject to the stronger restrictions below.

| Negative inputs accepted by the helper | Minimum number of distinct ordinary leaves | Largest private cost still compatible with size 63 |
|---:|---:|---:|
| At least 1 | 19 | 43 |
| At least 2 | 21 | 41 |
| At least 3 | 22 | 40 |
| At least 5 | 23 | 39 |
| At least 10 | 24 | 38 |
| At least 25 | 25 | 37 |
| At least 73 | 26 | 36 |

There is also a size-independent consequence for a helper accepting **two distinct singleton inputs** of the full Boolean cube. The [common-singleton cofactor bound](CommonSingletons.md) gives $L\ge57$ for every geometric pair, with no assumption on the private computation. At $g\ge6$ this gives at least $57+6+2-1=64$ gates. The five-gate theorem covers all smaller $g$. If the helper accepts just one known point singleton, $L\ge44$ rules out $g\ge19$. For a line singleton, $L\ge43$ rules out $g\ge20$.

## Replaying the finite proof

Use Python 3.10 or later with assertions enabled. The following commands use the standard library.

```sh
python mixed_five_orbits.py
python audit_five_orbits.py
python verify_mixed_five.py
```

The [first enumeration](mixed_five_orbits.py) and [independent orbit audit](audit_five_orbits.py) both check the [64 residual records](mixed_five_orbits.json). The [integer replay](verify_mixed_five.py) matches those records by support and minterms and checks every [coefficient certificate](mixed_five_certificates.json). All three use the [plane data](verify_plane_formula.py). The rectangle replay also imports the [weighted scorer](verify_raw_shared_gate.py). Floating-point optimization was used in discovery. Verification uses the stored integers.
