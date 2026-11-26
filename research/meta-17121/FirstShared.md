# A first gate with arbitrary fanout cannot save a gate

For each of the four projections in L-meta-17121, an 18-gate circuit that reaches the target must either share at least two internal gate outputs or have its sole shared gate depend on another internal gate. This statement covers arbitrary fanout of a shared gate computed directly from the original inputs. The unrestricted 18-gate case remains open.

## From a circuit to a formula

Prune gates outside the target's computation, and regard the ten nonzero inputs as free variables. With no shared internal gate the result is a formula with at most 19 leaves. The four base certificates show that every formula for these tables needs at least 20 leaves. The 19-gate formula upper bounds and the original rectangle argument are described in [FormulaLowerBound.md](FormulaLowerBound.md).

The Lean theorem [attainable_at_nineteen](NineteenGateWitness.lean) supplies four concrete 19-gate lists. For each prefix it proves that two available words produce the next word by AND or OR and that every earlier word passes the posted error-mask test. It checks that the target occurs in each completed list. Lean 4.36.0 accepted the theorem using the standard axioms `propext`, `Classical.choice`, and `Quot.sound`. From the upstream `lean/` directory, run `lake env lean /path/to/NineteenGateWitness.lean` to replay the kernel check. The [gate-by-gate traces](star_upper.json) identify operands by their zero-based indices in the eleven inputs followed by the new gates.

Suppose instead that the only shared internal output is a binary operation $h$ on two original inputs. Pay once for $h$ and treat its word as an additional free input. The remaining at most 17 binary gates form a formula with at most 18 variable leaves. Any number of those leaves may use $h$. The same leaf argument applies if an equivalent circuit contains redundant gates, since they can be removed first.

The row's dominance condition excludes constants and repeated inputs as first gates. It also excludes an AND of nonadjacent vertices, whose word has no positive bit and is dominated by the zero seed. Of the 45 pairs of distinct nonzero inputs in each projection, all 45 ORs and precisely the 14 ANDs on edges pass the condition. The verifier checks these counts directly from the seed words. It stores the new input in the former zero slot. A zero leaf cannot distinguish any positive-negative pair, so omitting it leaves the rectangle argument valid.

## The 236 finite bounds

Index rows by the 14 positive tests and columns by the distinct nonempty negative tests. A leaf labeled by an input covers a rectangle on which that input is one in every row and zero in every column. A formula partitions the table into such rectangles by routing positive rows at OR gates and negative columns at AND gates. This remains valid for the added input even though its truth word is a specified function of the ordinary inputs.

For each label and each nonempty subset of rows on which it is one, a binary variable $y$ pays for that row subset. A variable $z \le y$ records its use on each eligible column. Every cell must receive exactly one selected $z$. Rectangles with identical label and row subset can be merged, so any formula with 18 leaves gives a partition with $\sum y \le 18$. Duplicating an occurrence of the same label is allowed.

Each stored proof branches on binary variables. At its leaves the verifier independently reconstructs the coefficient of every $y$, $z$, and optional slack variable from integer multipliers for the model rows. It checks the inequality signs and takes the minimum of each reduced term over the branch's allowed values. Every resulting lower bound exceeds 18 for the augmented tables, and 19 for the base tables. A slack has cost 32 and a genuine partition sets it to zero. Thus the verified lower bounds hold for all genuine partitions. [FormulaLowerBound.md](FormulaLowerBound.md) gives the multiplier inequality.

| Deleted vertex | First-gate cases | Base certificate leaves | Augmented certificate leaves |
|---:|---:|---:|---:|
| 0 | 59 | 52 | 436 |
| 1 | 59 | 79 | 902 |
| 2 | 59 | 92 | 707 |
| 3 | 59 | 105 | 1,382 |

From this directory run `python -I verify_kw_first_shared.py`. Replay uses only the Python standard library, `seed_tables.json`, `kw_formula_certificates.json.gz`, and the four `kw_first_shared_0.json.gz` through `kw_first_shared_3.json.gz` bundles. The verifier checks the complete case sets and both children of every branch. Optional regeneration of the four new bundles uses `python kw_first_shared.py ROW` in a fresh output directory containing that script, the seeds, and `kw_integral_partition.py`, with SciPy 1.17.1 installed.
