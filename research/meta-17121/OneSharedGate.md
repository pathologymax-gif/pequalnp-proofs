# A circuit with one shared intermediate still needs 19 gates

For each of the four projections in L-meta-17121, the minimum size of a binary monotone circuit with at most one distinct intermediate gate of fanout greater than one is **19**. The shared gate may feed arbitrarily many readers. The star formula attains 19 in all four cases. Thus an 18-gate solution to the unrestricted problem would need at least two distinct shared intermediates. This research result is computationally checked with ordinary integer arithmetic. [Assigned problem](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-17121) · [Formula lower bound and rectangle model](FormulaLowerBound.md)

## Cutting the shared computation

Suppose a circuit of size at most 18 exists in this class. Choose a smallest one and remove unused gates. Gates with repeated identical operands can be removed by idempotence. The formula lower bound excludes the case without sharing. Cut the output of the unique shared gate and denote its truth word by $h$. Its input cone is a formula of $g$ gates. Its only outgoing connections to the rest are from $h$ itself, since any other such connection would create a second shared intermediate. The remainder is therefore an outer formula in the original inputs and a new input $h$, with $k\le18-g$ gates. Its distinct readers use at least two $h$ leaves. Primary variables can occur repeatedly on both sides.

Write $T$ for the target word and $C[t]$ for the outer formula with $h$ replaced by $t$. If $h\le T$ pointwise, then $T=h\lor C[0]$. If $T\le h$, then $T=h\land C[1]$. In either case at least two distinct readers disappear by constant folding, and at most one gate recombines the two formulas. The result is a smaller formula. A helper accepting no positive test can likewise be replaced by zero. Thus $h$ has a false positive and a false negative.

The ordinary inputs read by the outer formula must form a vertex cover. Otherwise, on an uncovered positive edge all ordinary leaves are zero. The formula cannot output one there at $h=0$, and outputting one at $h=1$ with all those leaves zero forces it to output one wherever $h=1$, by monotonicity. This contradicts a false positive of $h$. Since a minimum cover has six vertices, the outer formula has at least six ordinary leaves and two $h$ leaves. Hence $k\ge7$ and $1\le g\le11$.

## Enumerating inner formulas

The error set of a truth word $u$ is the bit support of $u\mathbin{\mathrm{xor}}T$. If the error set of $u'$ is contained in that of $u$, replacing $u$ by $u'$ everywhere in a monotone expression preserves each already correct bit. This follows separately on the rows requiring one and on the rows requiring zero. It applies to repeated uses. Therefore a helper can be replaced by a dominating helper of no greater cost. A raw input replacement yields a formula, already excluded. A one-sided replacement is handled by the cut identities above.

Starting with the seed words at cost zero, form all AND and OR combinations of retained words at costs $a,b$ with $a+b+1=g$. Discard any candidate whose error set contains the error set of a previously retained word of equal or lower cost. Within a cost, visit candidates in order of increasing error-set cardinality. Structural induction on a formula proves that a retained word of no greater cost dominates its root. The C# verifier implements the subset test with a binary trie. Restricting to the retained helpers therefore preserves completeness.

## Necessary outer leaves

Use the rectangle table from the formula proof, with positive edge rows $e$ and negative maximal independent set columns $M$. The new leaf label $h$ is available only if $h(e)=1$ and $h(M)=0$. For each vertex $v$, gather cells for which $v$ is the unique available label. These are exactly the cells where $e=vw$, $w\in M$, and the helper label is unavailable. If this set is nonempty, the outer formula must use a $v$ leaf. If it uses only one, that leaf's rectangle contains the Cartesian product of all gathered rows and columns.

Join two mandatory vertices when their resulting rectangles intersect. A pair of single leaves cannot both realize such intersecting rectangles in a partition. The vertices whose labels are repeated consequently cover every conflict edge. Counting the mandatory vertices, the conflict graph's minimum cover, and the two helper occurrences gives a lower bound on outer leaves. The verifier computes the cover exactly by branching on either endpoint of an uncovered edge.

Any surviving outer formula has at most $k+1\le19-g$ leaves. Two alternative integer certificates suffice to exclude it:

- **Full table.** Add the helper as an extra leaf label, preserving its value on each row and column. The rectangle-partition lower bound exceeds $19-g$.
- **Cofactor at one.** Substitute one at every helper occurrence. At least two distinct reader gates disappear. This formula accepts every edge by monotonicity. It rejects every negative test on which the helper is one, because the substitution leaves that test unchanged. For that restricted table, the ordinary-label rectangle lower bound exceeds $k-1$'s upper bound of $17-g$.

Both bounds use the integer weak-duality verifier explained in the formula note. Discarding duplicate columns or an empty negative test only weakens the necessary condition.

| Deleted vertex | Retained helpers, costs 1–11 | Helpers needing a rectangle certificate |
|---|---:|---:|
| 0 | 156,118 | 563 |
| 1 | 142,083 | 781 |
| 2 | 151,731 | 701 |
| 3 | 133,285 | 1,151 |

Of 583,217 cost-indexed helpers, 3,196 required a certificate. The full table excluded 2,389, and the cofactor excluded 807. The integer certificates contain 6,915 terminal dual bounds. All cost-8 through cost-11 cases were eliminated before the integer certificate stage. An independent replay used an enumeration of all vertex subsets for the conflict-cover calculation and checked every numerical certificate.

## Replay

Run **python verify_one_shared_gate.py** in this directory. The script replays the original formula result, compiles **SharedGateFrontier.cs** in a temporary directory, recomputes all helper words, and independently replays **one_shared_gate_certificates.zip**. Use **--row 0**, **--row 1**, **--row 2**, or **--row 3** to check projections separately. Replay requires Python 3 and either .NET SDK, Windows .NET Framework, or Mono. The generator used SciPy and HiGHS to find dual weights. Replay uses a C# word enumeration and Python arbitrary-precision integers.
