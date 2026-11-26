# Two shared binary OR gates on primary inputs

For each of the four G11 projections, 19 gates are necessary and sufficient if at most two intermediate values are reused and each reused value is the OR of a pair of primary inputs. A reusable value can have any number of readers. The pairs may overlap. The earlier one-shared result covers zero or one reused value. The star formula supplies the 19-gate upper bound.

To see the lower bound, suppose an 18-gate circuit in this class exists. Delete unused gates, bypass redundant copies, and replace identical operands using idempotence. Equal helper pairs can be merged, leaving just one shared value, already excluded. A genuinely shared result must occur at least twice. Cutting the two distinct shared gates leaves a formula over the original ten nonzero variables and two new input variables for the helper values. That formula has at most 16 binary gates, hence at most 17 leaves. At least two leaves have each helper label.

For every positive edge and every negative maximal independent set, a formula must identify a variable true on the edge and false on the negative test. The rectangle partition argument and the integer certificate arithmetic are given in [the formula proof](FormulaLowerBound.md). For a vertex v, collect all table cells where only v can serve as the label, even after allowing both helper labels. If v is used only once, its rectangle must contain the product of those cells' row indices and column indices. When two such products intersect, at least one of the two labels must occur at least twice. Counting the mandatory ordinary labels, a minimum vertex cover of these conflicts, and four helper leaves gives the first lower bound. A proof of the corresponding argument for one helper appears in [the one-shared-gate proof](OneSharedGate.md).

For the remaining pairs use the whole rectangle table, or fix one or both helpers to one. Fixing a helper preserves every positive output. It preserves every negative output on a row where that helper was already one. Delete all other negative rows. A cofactor that still has a positive and a negative test is nonconstant. Constant folding leaves at most 17−2j variable leaves if j helpers were fixed, since each fixed helper had at least two occurrences and new variable occurrences are never introduced. Every stored certificate proves a strict lower bound above the relevant limit using integer arithmetic.

| Deleted vertex | Pairs of helpers | Excluded by mandatory leaves | Further certificates | Terminal integer bounds |
|---|---:|---:|---:|---:|
| 0 | 990 | 911 | 79 | 125 |
| 1 | 990 | 783 | 207 | 1,045 |
| 2 | 990 | 871 | 119 | 425 |
| 3 | 990 | 716 | 274 | 2,147 |
| Total | 3,960 | 3,281 | 679 | 3,742 |

Run `python two_raw_helpers.py 0 replay` in this directory, then use 1, 2 and 3 for the other rows. Replay uses only the Python standard library, the four `kw_two_raw_*.json.gz` files, `kw_first_shared.py` and the original seed data. The program enumerates every pair and checks that the keys in each archive match precisely the cases requiring certificates. SciPy/HiGHS is needed only for regeneration with `generate`. The generator's rectangle model ranges over the supplied number of variable labels, which is twelve for the full table in this proof.
