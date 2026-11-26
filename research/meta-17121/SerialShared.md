# Two shared gates with a common cofactor

On each projection of L-meta-17121, consider a circuit with exactly two distinct shared non-input gates. Suppose one is the raw-variable disjunction $h=x_a\lor x_b$, and the other, $j$, is one on every negative test where $h$ is one. Such a circuit needs at least 19 gates. In particular this excludes a raw OR followed by its OR with any third variable.

Remove unused gates and repeated identical operands. Cut both shared outputs out of the circuit. The component leading to the output is now a formula in the ten variables and the two cut signals. The private part used to compute the cut signals contains at least two gates. The second signal $j$ has at least two occurrences in the outer formula, because the raw gate $h$ cannot depend on it.

If $h$ appears in the outer formula, that formula has at least three helper occurrences. An 18-gate circuit would give it at most 17 leaves, hence at most 14 ordinary leaves. If $h$ never appears there, both its readers lie upstream of $j$ or coincide with $j$. Since they are distinct, the private part then contains at least three gates. The outer formula has at most 16 leaves, again allowing at most 14 ordinary leaves.

Now fix both helper leaves to one. Every original positive test stays positive by monotonicity. All negative tests meeting the pair $\{a,b\}$ stay negative because both helper values were already one. Constant folding gives an ordinary-input formula with at most 14 leaves for this restricted table. For every projected pair, the table contains both positive and negative tests. The supplied integer certificates prove that it requires at least 15 leaves. This argument uses only the stated values of $j$ on negative tests.

## A dependent AND

Suppose instead that $j=(x_a\lor x_b)\land x_c$ for a third variable $c$. If neither $ac$ nor $bc$ is a graph edge, $j$ accepts no positive test and it can be replaced by zero. If both are graph edges, $j$ is zero on every negative test. A clean signal $p$ with this property can be extracted as a final OR branch: the target is $p\lor C[0]$, where $C[0]$ fixes all of its downstream uses to zero. At least two readers disappear. Retaining the private computation of $p$ can leave $h$ shared, but it makes $p$ a single-use signal.

If exactly one pair is an edge, say $ac$, replace $j$ by $x_a\land x_c$. The new gate agrees on every positive test, and its negative values can only decrease. Monotonicity preserves the target in the whole circuit. This replacement has the same cost and gives a clean signal to extract. The cases $c=a$ and $c=b$ are immediate by absorption. In each case the result is a circuit with at most one shared internal gate and at most the original cost. The [one-shared-gate bound](OneSharedGate.md) excludes size 18.

## Replay

Run `python serial_shared.py` alongside `serial_shared.json.gz`, `seed_tables.json`, and `verify_kw_first_shared.py`. Replay uses Python's standard library. The four projections have 45 pairs apiece. A total of 990 branch leaves certify all 180 restricted tables. For 118 tables the certificate proves at least 17 ordinary leaves, for 52 it proves at least 16, and for the remaining 10 it proves at least 15. Optional regeneration uses `python serial_shared.py --generate` and the SciPy-based generator described in [FirstShared.md](FirstShared.md).
