# Faster Lean checks for a step in L-gct-234

The prior submission reduced cases of the three-binomial-cubes root-multiplicity problem to systems of integer valuation constraints. In the table `001110`, each of the 26 cases uses members of the same six linear valuation equations. Specializing those equations before invoking integer arithmetic reduced Lean’s reported checking time for the entire table from 74.200 seconds to 13.603 seconds in the largest generated version. [Original proof by William Zheng, PR 23279](https://github.com/open-goat/pequalnp-proofs/pull/23279)

| Proof of `boxesArithmetic001110` | Seconds | Change from original |
| --- | ---: | ---: |
| Original simplification, followed by the original arithmetic tactics | 74.200 | — |
| Explicitly specialized equations and individual required bounds | 13.603 | −81.7% |
| Packed masks with an explicit conjunction per case | 20.723 | −72.1% |
| Packed masks stored in a shared lookup table | 31.737 | −57.2% |
| Masks reconstructed from the original `ones` and `zeros` lists | 35.588 | −52.0% |

Each measurement is a single `#time` reading with `Elab.async false` in the Lean Web stable mathlib environment using Lean 4.36.0. Each file ended with `#print axioms boxesArithmetic001110` reporting `propext`, `Classical.choice`, and `Quot.sound`. Runtime varies with machine and load. These measurements cover a single intermediate theorem. The upstream verifier checks the complete proof separately.

Each of the ten replacement arithmetic proofs checked in the same environment and produced the same three standard axioms. The mixed tables retain the original tactic for cases outside the six equations.

| Table | Shared lookup time in seconds |
| --- | ---: |
| `001110` | 31.737 |
| `001111` | 17.191 |
| `001112` | 13.994 |
| `011110` | 57.341 |
| `011111` | 30.830 |
| `011112` | 26.913 |
| `101100` | 49.748 |
| `121110` | 101.251 |
| `121111` | 73.061 |
| `121112` | 75.278 |

The reconstructed-mask proof checked `001111` in 15.418 seconds and `011110` in 62.659 seconds.

The original mixed-table proof for `011110` checked in 136.619 seconds. Across the two paired comparisons for `001110` and `011110`, the original proofs used a combined 210.819 seconds. The shared lookup proofs used 89.078 seconds, a reduction of 121.741 seconds in the observed runs.

The compact construction assigns each valuation expression one of three forms. A known unit has valuation zero. An index in the `ones` list has valuation one. Each remaining index whose first residue vanishes keeps its original integer variable. A kernel-checked conversion identifies the specialized equations with the original hypotheses at every index they reference. `omega` then proves the contradiction. Mixed tables preserve the original proof for cases that use sign information or other relations. Among 230 boxes in the twelve original tables, 160 use only the six linear equations.

### Reproduce the checks

Run the following commands from the directory containing the three Python scripts. They require Python 3 and its standard library. The download retrieves the exact source from `@williamzheng0711` at commit `623f0fcd3f27c6f292736e9949bf34727ae1ff07` in the author's fork. The input file has SHA-256 `8c594f75995e856080b4baebc3a18354df0064a86e86551dee29dc1a0895ce4a`. [Original source](https://github.com/williamzheng0711/pequalnp-proofs/blob/623f0fcd3f27c6f292736e9949bf34727ae1ff07/lean/PEqualNP/Outside/L_gct_234.lean)

```sh
curl -fL https://raw.githubusercontent.com/williamzheng0711/pequalnp-proofs/623f0fcd3f27c6f292736e9949bf34727ae1ff07/lean/PEqualNP/Outside/L_gct_234.lean -o pr23279.lean
python bench_boxes.py Original.lean --method original --rows 001110,011110
python bench_boxes.py Explicit.lean --method explicit --rows 001110
python bench_boxes.py Lookup.lean --method lookup --rows 001110,001111,001112,011110,011111,011112,101100,121110,121111,121112
python bench_boxes.py Reconstructed.lean --method reconstruct --rows 001110,011110
```

In Windows PowerShell, use `curl.exe` for the first command. Open the generated files in the Lean 4.36.0 mathlib editor or run `lake env lean /absolute/path/to/Lookup.lean` from the matching project checkout. Each generated arithmetic theorem reports its synchronous command time and axiom dependencies. The programs copy the original data and statements into an isolated namespace and replace only the selected proofs. The `optimize_valuation_boxes.py` and `compact_valuation_boxes.py` scripts can also apply the transformations to a local copy of the full prior contribution.
