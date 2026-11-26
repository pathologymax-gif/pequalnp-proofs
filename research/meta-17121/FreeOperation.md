# Counting one gate type in the four projected G11 circuits

The four sample tables assigned to `L-meta-17121` each require six AND gates when OR gates are free, according to exact synthesis. The known 19-gate programs attain six ANDs and thirteen ORs in every case. A second synthesis run excludes circuits with six OR gates even when AND gates are free. These bounds apply to arbitrary reuse of earlier wires and to all monotone circuits producing the target on the samples. The question of excluding all circuits with eighteen gates remains open in this work.

## From a circuit to a bounded list of binary ANDs

An input is a 32-bit sample column. An OR-only circuit feeding a counted AND gate can be flattened into two sets of wires. Each set is drawn from the original inputs and the outputs of earlier counted ANDs. The value of each set is the bitwise OR of its members. The output is another such set. This gives the normal form with one binary AND instruction per counted gate. Conversely every instruction gives an ordinary binary monotone circuit by expanding its finite ORs. The empty OR supplies zero for padding. Any introduced constant at either polarity can be removed by constant folding for a nonconstant target on the samples.

The two operand sets can be taken disjoint. If they share a set of wires with OR equal to C, write the two operands as A ∨ C and B ∨ C. Distributivity gives (A ∧ B) ∨ C. Use A ∧ B for the counted gate and retain all wires of C wherever the old result was selected downstream. Process the counted gates in topological order. Commutativity then permits ordering the two disjoint sets by their first selected wire.

For the OR budget, complement every input and the target, and interchange the two operations by De Morgan's laws. This reuses the same grammar. The encoder includes the intersection and union of bit columns explicitly, along with the OR of the selected final wires. Every reported satisfying model is independently replayed using integers on all 32 positions.

## Necessary conditions used to speed up the search

* **Pairs of negative positions.** Suppose target-true position p and target-false positions q,r have no raw seed that is true at p and false at q and r. Trace any wire with the pattern (1,0,0) backwards. At each free OR, one selected input has the same pattern. At an AND, both operands are true at p. If one operand is false at q and r it inherits the pattern. Otherwise the operand values at q,r must be opposite, one (0,1) and the other (1,0). A backward trace has to stop at such a counted gate because no seed has the pattern. Each excluded seed pattern therefore requires opposite operand values at some counted gate. The optional `--aligned` version additionally requires that same gate to be true at the specified p.
* **First positive occurrence.** For a target-positive position that no eligible raw output seed covers, take the first counted gate that is true there. Both its operands must contain a raw seed true at that position, since every earlier counted gate is false there. Thus the raw-seed portions of the two operands must intersect at that positive position in some counted gate.
* **Dominance by a free union.** At an active gate collect every old wire whose negative-position ones are a subset of the new gate's negative-position ones. Their free union must miss a positive position where the new gate is true. Otherwise that union can replace the new gate. At every positive coordinate the replacement can only increase the bit; at every negative coordinate it can only decrease it. Subsequent AND and OR preserve both coordinatewise orders and the final target is already optimal on every bit. This would yield the target with one fewer counted gate. A minimum circuit therefore passes this test. Shorter circuits may pad the remaining gate slots with empty operand sets.

The plain variant omits all three search conditions. `test_free_operation.py` compares the grammar with an independent exhaustive closure over small bit-vector pools, evaluating every budget from zero through two. There are 552 consistent target/budget instances across twelve fixed random tables. The test compares all three encoding variants against the reference on each instance.

## A shorter independent obstruction for four ANDs

For each maximal-independent-set row q, allow one bit per counted gate. If the two operand values differ at q, the bit selects the false operand. Otherwise allow both values of the bit. All compatible signatures for q form a subcube of the Boolean k-cube. The backward argument above guarantees that the subcubes for two separated negatives are disjoint. The verified pairwise separations are in `AndSignature.lean`.

If k=4, the 16 maximal independent sets in case 1 consume all 16 points even if every subcube has size one. Thus every gate has different operand bits on each of those negative positions. In case 3 there are 15 maximal independent sets and at most one extra point. At most one gate-position pair can have equal operand bits, since a d-dimensional subcube has at least 1+d points. A padding row tests the empty input and has zero on every nonempty monotone subcircuit.

For each AND, intersect the unions of raw seeds in its respective operands. The raw intersection is contained bitwise in the gate output. Since every true negative in a gate output makes its operand bits equal, these raw rectangles have at most zero total negative incidences in case 1 and at most one in case 3. By the first-positive argument, their union must cover all fourteen positive edge positions. `rectangles_with_errors.py` enumerates the two raw seed unions and computes the minimum number of such rectangles by exact set cover. Case 1 requires six even under a one-incidence allowance. Case 3 also requires six. Consequently both cases need at least five ANDs by this smaller argument. Cases 0 and 2 already need five by the simple cardinality bound in `AndSignature.lean`.

## Reproduction

From this directory with the pinned `python-sat` package installed, run the following for case 0. Repeat for cases 1, 2 and 3. CaDiCaL can emit the clauses and a DRAT proof, which an independent implementation can verify.

```sh
python -m unittest -v test_free_operation
python free_operation.py 0 and 5 --conflicts 2400000 --proof and5.drat
drat-trim and5.cnf and5.drat
python free_operation.py 0 or 6 --conflicts 2400000 --proof or6.drat
drat-trim or6.cnf or6.drat
```

| Case | Five ANDs, unlimited ORs | Conflicts | Six ORs, unlimited ANDs | Conflicts |
|---|---|---:|---|---:|
| 0 | UNSAT | 551,730 | UNSAT | 322,416 |
| 1 | UNSAT | 116,822 | UNSAT | 274,783 |
| 2 | UNSAT | 91,954 | UNSAT | 399,713 |
| 3 | UNSAT | 53,845 | UNSAT | 462,766 |

These are the unaligned, strengthened CaDiCaL 1.9.5 run results. A proof of UNSAT for the emitted clauses and an end-to-end Lean formalization of this mathematical translation are different results. The translation above is justified on paper and checked on small tables.

The optional `check_rup.py` uses Glucose 4.2 exclusively for Boolean unit propagation to check the certificate additions and terminal empty clause. It leaves all earlier verified clauses present and rejects an addition if the negated clause fails to cause a conflict. The pinned Actions workflow uses DRAT-trim at commit `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`, which can also validate the broader RAT proof format. The eight instances run sequentially in one job.
