# One shared helper with a private formula of at most four gates

On the 52 positive incidence flags and 234 negative quadrangle tests of $\mathrm{PG}(2,3)$, every binary monotone circuit with a sole shared internal gate computed by a private formula of at most four gates has size at least **64**. Its fanout is arbitrary. A separate result in this proof concerns the ordinary formula problem: after deleting the three positive flags of any three-edge path, and keeping all 234 negatives, the remaining table requires at least **61 leaves**.

## Formula reductions

Suppose the circuit has at most 63 gates. Discard unused gates, simplify constants and use idempotence on repeated operands. Cutting its only shared output $h$ leaves an exterior formula in the 26 raw variables and $h$. A private cost of $g$ leaves at most $64-g$ exterior leaves. At least two are occurrences of $h$ with distinct readers.

Let $T$ be the target on the tests and write $C[h]$ for the exterior computation. If $h\le T$, then $T=h\lor C[0]$. If $T\le h$, then $T=h\land C[1]$. Fixing the indicated constant removes at least two reader gates, so the final operation leaves a formula no larger than the original circuit. A helper with no positive flag may also be replaced by zero. These cases contradict the [64-gate formula lower bound](QuadrangleFormula.md).

More generally, try a disjunction $w$ of $s\ge1$ raw variables with $w\le h$ on every negative test. Let $P$ be the positive flags accepted by $h$ but missed by $w$. Then $T=F_P\lor C[w]$ on the tests, where $F_P$ is the ordinary incidence-edge function of $P$. Outside $P$ no required positive is lost. On the negatives, $C[w]\le C[h]=0$, and every incidence edge term is zero.

Assign each edge of $P$ to an endpoint in a minimum vertex cover. Taking the OR of these stars uses at most $|P|+\tau(P)-1$ gates for nonempty $P$. Including $w$ and the final OR costs at most $s-1+|P|+\tau(P)$. When $P$ is empty, omit the correction and the final gate. If the bound does not exceed $g$, the result has at most one shared gate, a [pure disjunction](SharedDisjunctions.md). For $w=0$ there is no new shared gate and at least two old readers disappear, so it suffices that $|P|+\tau(P)-2\le g$.

## Exhausting four-gate private formulas

A formula of at most four binary gates has at most five variable leaves. The verifier constructs every monotone Boolean function expressible at each private cost from one through four. It splits the two child costs as $a+b+1=g$ and takes AND and OR on their complete truth tables. Equivalent truth functions can be computed using their minimum cost. The support of a monotone function is the union of its inclusion-minimal true assignments. Variables outside that support can be set to zero and simplified.

Two explicit incidence-preserving permutations generate 5,616 projectivities on the 26 input literals. For each support of size two through five modulo this group, the verifier also quotients formal Boolean functions by the subgroup permuting that support. It checks the orbit multiplicities against the labeled count $\binom{26}{k}$ times the number of full-support functions on $k$ variables, independently at every private cost. All positive and negative tests are preserved by both generators. Constants and singleton functions were already simplified.

| Minimum private cost | Pure OR | One-sided or no positive | Replace by zero and correct | Replace by a raw input and correct | Replace by OR of two and correct | Replace by OR of three and correct | Further check |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 1 | 4 | 4 | 0 | 0 | 0 | 0 | 0 |
| 2 | 10 | 22 | 6 | 18 | 0 | 0 | 0 |
| 3 | 25 | 290 | 205 | 46 | 74 | 0 | 0 |
| 4 | 56 | 5,349 | 3,835 | 902 | 860 | 262 | 6 |

## Deleting three flags

All six remaining helpers have the form $x\lor((a\lor b)\land(c\lor d))$. On the positive tests the second term adds exactly three incidence flags to those containing $x$. These three flags form a path on four vertices. Replacing the helper throughout by the single raw input $x$ gives a formula that still rejects every negative and accepts all 49 flags outside that path. With $g=4$, it would have at most 60 leaves.

Take the three flags on raw vertices $\{1,2,13,14\}$, where $0$ through $12$ are points and $13$ through $25$ are lines. The verifier computes that their orbit contains all $52\cdot3\cdot3=468$ distinct three-edge paths. Mark every cell of the three deleted flag rows optional, and require ordinary variables to label the other cells. A formula solving the 49-row problem gives such a partial rectangle partition by placing its rectangles only on those rows. The existing local weighted rectangle verifier checks the supplied integer transfer coefficients and the optional-cell predicate. It gives

$$
L\;\ge\; \frac{24{,}214{,}508}{400{,}000}=60.53627.
$$

Thus the ordinary formula requires at least 61 leaves, excluding all six cases. The same certificate applies at any private cost $g\ge4$ whenever replacing the sole helper by one raw variable preserves the negatives and loses positives contained in a three-edge path.

Run `python mixed_four_orbits.py` with `mixed_four_p4_certificate.json`, `verify_plane_formula.py`, and `verify_raw_shared_gate.py` in the same directory. Replay uses Python's standard library and checks the unrestricted support orbit counts, the six remaining truth words, and the integer certificate. The linked formula and pure-disjunction bounds provide the prerequisites.
