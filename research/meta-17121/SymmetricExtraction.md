# Extracting both types of correct one-sided signals

Let a finite set of sampled inputs be labeled by a nonconstant Boolean target T. Treat a wire as the set of samples on which it is true. A **lower** wire is contained in T, an **upper** wire contains T, and a **mixed** wire both misses a positive and accepts a negative. Assume the nonconstant usable raw inputs are mixed. This holds in all four assigned G11 rows. Binary AND and OR have unit cost, constants can be simplified, and earlier wires may be shared arbitrarily.

**Theorem.** There is a minimum circuit with a prefix of d gates producing only mixed signals. From those signals and the raw inputs form the following terminal expressions. Each lower terminal is the intersection of two available signals. Each upper terminal is their union. No terminal feeds another terminal. The resulting circuit has one of the following forms.

| Output | Gate count |
|---|---:|
| Union of a≥2 lower terminals | d+2a−1 |
| Intersection of b≥2 upper terminals | d+2b−1 |
| An available mixed wire R, together with a≥1 lower and b≥1 upper terminals, giving (R ∪ L₁ ∪ … ∪ Lₐ) ∩ U₁ ∩ … ∩ Uᵦ | d+2(a+b) |

R may be a raw input, a prefix gate, or a prefix gate already read elsewhere. A lone terminal cannot equal T. At an AND giving T both parents would be upper; at an OR giving T both would be lower, contradicting their mixed status.

## Extraction and size

Start with a minimum circuit and empty lists of extracted lower and upper guards. In a residual circuit write C for the union of the extracted lowers and F for the intersection of the uppers. The invariant is that the original target on all samples equals (residual ∪ C) ∩ F. Each extracted wire is computed from mixed earlier signals, and C ⊆ T ⊆ F. Previously recorded guards never depend on a later residual gate.

Process the residual circuit in its original topological order. Remove unused residual gates, keeping the predecessors needed for the extracted guards. Fold constant gates and simplify their readers. At the first remaining nonmixed residual gate, both inputs are mixed, because earlier nonmixed gates have already been removed. An OR of mixed wires cannot be lower, and an AND of mixed wires cannot be upper. Thus any nonconstant lower first occurs at an AND and any nonconstant upper first occurs at an OR. Preserve that gate as an additional guard, but replace its outgoing uses in the residual by zero for a lower guard and by one for an upper guard.

For a lower guard L, samples where L=0 do not change in the residual. Where L=1 the target is positive and restoring L in the final union forces the correct value. The corresponding upper restoration is valid for the same reason: where an upper U is zero the target is negative, and setting U to one in the residual does not affect samples where U was already one. A new lower can commute past a previously recorded upper since (s ∪ L) ∩ U = (s ∩ U) ∪ L whenever L ⊆ U. Thus the stated invariant holds throughout. Later substitutions cannot change an already recorded guard or its predecessors.

If the extracted gate has a reader in the residual, at least one binary reader disappears by constant folding. Its gate cost pays for the one corrective OR or AND restoring the guard at the output. These deleted readers are distinct over different extraction steps. More than one reader or additional simplification can only decrease the total cost. Equivalently, track the residual plus all guard predecessors and the current outer circuit: add one guard-combining gate and remove at least one reader. A gate already used only by extracted guards is an earlier predecessor; it is mixed and cannot be newly extracted.

If the residual output itself is the extracted gate, end the extraction there. For a lower residual L, the output is L ∪ C, because this union is contained in T and accepts all positives. Thus the uppers and their outer gates are redundant. For an upper residual U the output is U ∩ F and the lowers are redundant. The same simplifications apply if the final residual is the constant zero or one. These terminal cases do not need a restoring gate for the final residual. If the residual instead remains mixed and no nonmixed gates remain, both families of guards must be nonempty. Without lowers the mixed residual's missed positive would still be missed; without uppers an accepted negative would remain accepted.

Starting from a minimum, the size of the resulting circuit cannot fall below that minimum. Trim any newly unused prefix gates. Counting the mixed prefix, terminal gates and the outer binary operations gives the three exact formulas above. In the mixed-residual case the a+b terminal operations and the a+b outer operations contribute exactly a+b ANDs and a+b ORs, independent of the split between the two terminal types.

## Consequences for enumeration

In a minimum circuit each lower must have a private positive missed by every other lower and, in the mixed case, by R. Each upper must have a private negative accepted by every other upper and, in the mixed case, by R. Otherwise the terminal and its restoring operation can be removed. In the mixed form R also covers a positive missed by all lowers and rejects a negative accepted by all uppers. Otherwise the lowers alone, or the uppers alone, would compute T. Terminals can be sorted within each type using their private positions. When counting fanout, R has a reader in the outer circuit even if it is also read in the prefix. A raw input used only as R requires separate care in any restrictions on once-read variables.

For the four G11 samples there are two useful lower bounds on a terminal's own input cone. If an upper terminal rejects the maximal independent set Q, every raw vertex outside Q is needed in a zero-certificate whose signals together cover all positives. Thus the mixed prefix has at least 10−|Q|−2 OR gates zero on Q. The upper terminal itself accounts for the only other OR in that cone. For a lower terminal accepting an edge set E, connect two maximal independent sets Q and Q′ when their union contains an edge of E. The signature argument colors this graph using at most 2^(k+1) colors if there are k prefix ANDs. A clique of size 2^j+1 forces k≥j. The finite checker enumerates minimal edge sets reaching each clique threshold; the generator uses those implications only on the lower terminal involved.

An optional `--reader-patterns` cut reuses the G11 once-read-variable test from `reader_preorder.py`. In the mixed prefix and at upper terminals, a reader of a once-used raw variable must accept some negative. It can therefore be added as a dirty reader in that relaxation. Its other operand is an earlier signal; a pair of once-used raw variables cannot be each other's unique reader by the degree and maximal-negative conditions. A lower terminal containing a once-read raw is precisely the clean-star exception in that test. If the residual R is itself a once-read variable, take R ∩ U₁ as its first outer operation, then union the lowers and apply the remaining uppers. This equals the stated output because every lower is contained in U₁. Its other operand is a tracked upper terminal. This additional AND is either a dirty reader or another clean star. Raw fanout counts are the same under this bracketing. Consequently an edge below a negative under the relaxation's final comparison relation still requires a possible clean star containing that edge. The 176 reported certificates omit this optional cut.

## Checked G11 subclass and reproduction

**If an 18-gate minimum exists for any projection, every realization of that minimum in the stated normal form uses at least seven mixed prefix gates.** At size 17 every form needs at least six. The only surviving size-17 layout with exactly six mixed prefix gates is a union of six lower products; its feasibility remains open. Across the four projections, 176 satisfiability instances cover all positive a,b and all d from zero through six satisfying d+2(a+b) ∈ {17,18}. Another 24 instances cover both pure forms of exact size 18 for all d≤6. Finally, 28 instances cover the pure upper forms of size 17 through d=6 and pure lower forms through d=4. Each clause set was independently refuted by reverse unit propagation after CaDiCaL generated its proof. Glucose checked 4,501,214 additions, including all 228 terminal empty clauses.

At size 18 the parity of the three size formulas sharpens the remaining search. A pure form can use at most six terminals. A mixed-residual form needs at least eight mixed prefix gates and can use at most five lower and upper terminals combined.

| Projection | Mixed-residual cases | RUP additions | Additional pure cases | RUP additions |
|---|---:|---:|---:|---:|
| 0 | 44 | 679,839 | 13 | 296,101 |
| 1 | 44 | 1,033,873 | 13 | 248,805 |
| 2 | 44 | 598,610 | 13 | 281,854 |
| 3 | 44 | 1,075,232 | 13 | 286,900 |

For pure lower terminals, `subset_terminal_synthesis.py` chooses a set of unordered operand pairs from the raw inputs and mixed prefix. A pair may be selected only if its AND is false on all negatives; for each positive at least one selected pair must have both inputs true. The exact cardinality fixes the number of terminal products. Two terminal products with the same operands would be redundant in a minimum, so this representation includes every minimum pure-lower circuit. It removes the permutations of terminal slots. The 24 pure-lower certificates use the existing once-read-variable restriction, its original pure-lower setting. The other 204 certificates use no reader-pattern exclusions.

`extract_guards.py` implements the sequential extraction on concrete circuits, rechecks the sampled target at each step, and checks that the resulting circuit has no more gates than the original. The small-table audit compares the three normal forms with independent exhaustive enumeration of arbitrary circuits. It also inserts redundant gates before rerunning the constructive extractor. Among 103 eligible optima, 62 required a mixed residual. The four known 19-gate constructions remain satisfiable under the G11-specific constraints and replay on the original 32-bit inputs.

From the research directory with the pinned SAT package installed:

```sh
python audit_symmetric_extraction.py
python symmetric_controls.py
for row in 0 1 2 3; do
  python audit_mixed_prefix.py "$row" --max-prefix 6 --out "symmetric-audit-$row.json"
  python audit_pure_prefix.py "$row" --reader-patterns --out "pure-audit-$row.json"
  python audit_pure_prefix.py "$row" --size 17 --max-lower-prefix 4 --reader-patterns --out "pure17-audit-$row.json"
done
```

The twelve reports in `symmetric_layout_reports.zip` contain each proof's SHA-256 and checked addition count. The regenerated proofs are checked before a report is written. This is a mathematical normalization proof with SAT certificates for the stated subclass; the full normalization and SAT encoding have not been formalized in Lean.
