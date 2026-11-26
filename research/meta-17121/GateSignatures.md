# Gate counts and reverse search for the four G11 projections

Any AND/OR circuit reaching `16383` from the four seed lists requires the following gate counts. The proof allows all earlier wires to be reused, including in circuits of more than 18 gates.

| Deleted vertex | Distinct maximal independent sets | Minimum ANDs established | Minimum ORs established |
| ---: | ---: | ---: | ---: |
| 0 | 18 | 5 | 6 |
| 1 | 16 | 4 | 6 |
| 2 | 17 | 5 | 6 |
| 3 | 15 | 4 | 6 |

The proof records one bit per AND gate at every negative test coordinate, using the value of that gate’s first operand. If two negative coordinates have the same record, then for every positive output coordinate there is a seed that is true on the positive coordinate and false on both negatives. At an OR gate, choose an operand true at the positive coordinate. At an AND gate, the two negatives agree on the first operand and therefore have an operand in common that is false on both. This justifies the induction even when wires have multiple consumers.

The verified finite check finds a positive edge that prevents this common seed for every pair of distinct maximal independent sets. Thus a circuit with $a$ AND gates needs at least as many binary records as there are maximal independent sets, and has at most $2^a$ records. Complementing every truth bit and exchanging AND with OR gives the dual bound of four OR gates from the fourteen positive edges. These are restricted lower bounds. The question whether every circuit needs at least 19 total gates remains separate. [AndSignature.lean](AndSignature.lean)

The stronger bound of six OR gates uses one three-vertex maximal independent set in each projection. Its negative test coordinate is respectively 14, 25, 20, or 27. Work backwards from an output that is zero there and one on all positive edges. For an AND gate, select one operand that is zero there. For an OR gate, retain both operands. The resulting set of wires continues to cover every positive edge, and only an OR gate can increase its size, by at most one. The finite check identifies seven distinct seeds forced into the final set, giving at least six OR gates whose outputs are zero at the selected negative test. At least five also miss a positive edge. The Lean file proves both counts for unrestricted shared circuits and connects them to the exact trace format. The Python script checks the corresponding certificates in each known nineteen-gate construction. [ZeroFrontier.lean](ZeroFrontier.lean) · [or_certificates.py](or_certificates.py)

The second file proves a reverse description of the same gate calculus. An outstanding requirement records coordinates that must be true and coordinates that must be false. When several requirements use the same gate, their required true sets and false sets are united. At an OR gate the positive requirements can be divided between its operands while the negative requirements go to both operands. AND exchanges these roles. The theorem proves that a reverse derivation with a given gate budget exists exactly when a forward circuit of that budget can satisfy all outstanding requirements. It also maps the assignment’s `BitVec 32` trace format to the reverse calculus. [BackwardRectangles.lean](BackwardRectangles.lean)
