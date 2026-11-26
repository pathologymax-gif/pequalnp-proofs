# Minimum-circuit SAT search on the four G11 projections

The bounded searches in this note left the 18-gate question unresolved in all four projections. The encoder exploits minimum-circuit structure, vertex sensitivity and required gate witnesses on triples of tests. CaDiCaL found models for all four fixed 19-gate constructions, and the independent bitwise evaluator checked their circuits. [Original SAT encoding](Synthesis.md) · [Desk problem](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-17121)

## Size-preserving restrictions

If a circuit of size at most $s$ exists on the test rows, take a smallest one. Delete unused gates and identify repeated operands. With operands sorted by wire number, choose a topological numbering greedily by largest operand, then smallest operand, then AND before OR. A newly eligible gate depends on the newly numbered output, so its largest operand exceeds every previously eligible gate's largest operand. This gives the required order for adjacent gates. A gate dominated by an earlier available word could be removed by replacing it everywhere with that word. The target remains correct on every sample by monotonicity, contradicting minimality.

- A gate consuming another gate and one of that gate's operands can be removed by idempotence or absorption. The clause applies to any operand wire.
- A word $h$ with no false positive cannot feed an AND in a smallest circuit. Replacing that AND by $h$ preserves correct zeros and can only help on positive tests. Dually, a word with no false negative cannot feed an OR.
- A shared intermediate must have a false positive and a false negative. If $h\le T$, the target is $h\lor C[h:=0]$. Removing at least two distinct readers and adding at most one OR saves a gate. If $T\le h$, apply the dual cut with one. The 18-gate instances additionally need two distinct shared intermediates and an AND that is true on a negative row. These two size-specific clauses are omitted in the 19-gate positive controls. [One shared gate](OneSharedGate.md) · [Single-level bound](SingleLevel.md)
- Every nonzero primary $v$ is essential. The negative tests are all maximal independent sets, and the positive tests are all edges, so monotonicity determines the entire edge function. If the unique reader of $v$ is an AND, that reader must output one on every positive edge containing $v$. Removing $v$ from the edge changes the target, while its other operand cannot depend on $v$. If its unique reader is an OR, it must output zero on every maximal independent set $M$ omitting $v$. Adding $v$ to $M$ creates an edge, so the reader must be able to change. The empty padding test is excluded from this sensitivity rule.

The AND lower bounds are 5, 4, 5 and 4, respectively. The earliest gate true on every positive edge must be an OR. For each nonempty maximal independent set $M$, at least $10-|M|-1$ different OR gates are zero on $M$, and at least $10-|M|-2$ of these also miss a positive edge. To see both counts, take the earliest wire that is one on every edge and zero on $M$. Follow both parents of each OR and one zero parent of each AND. Each vertex outside $M$ is a required leaf because adding it makes this wire one. After contracting unary choices, a connected certificate with $l$ distinct leaves has at least $l-1$ binary gates. Only its root can be true on every edge. [Gate signatures and zero certificates](GateSignatures.md)

## Optional witnesses on three tests

Let $e$ be a positive edge and $M,N$ two negative tests such that $e\subseteq M\cup N$. No primary can be true on $e$ and false on both $M,N$. Start at the output and seek an earlier wire with those three values. At an OR, one parent is true on $e$, and both are zero on $M,N$. At an AND, both parents are true on $e$. If either is zero on both negatives, continue there. Otherwise the operands have values $(1,0)$ on one negative and $(0,1)$ on the other. Descent must find an AND of this kind since it cannot terminate at a suitable primary.

Dually, for positive edges $e,f$ and negative $M$ with $e\cap f\subseteq M$, an OR is zero on $M$ and has the two opposite operand patterns on $e,f$. The optional clauses require one such gate for each incompatible triple. They apply to arbitrary sharing and do not assume size minimality. The small test suite checks the separation property directly on all three-variable, two-gate AND/OR constructions with distinct operand positions.

## Recorded searches

The minimum-circuit clauses alone yielded UNKNOWN for each projection after 25,000 conflicts. The following independent runs enabled all three-test witnesses and used a limit of 200,000 conflicts per projection. CaDiCaL can finish the current conflict before reporting an expired budget.

| Deleted vertex | CNF variables | Clauses | Search seconds | 18-gate result | Fixed 19-gate circuit |
|---|---:|---:|---:|---|---|
| 0 | 65,715 | 244,843 | 69.406 | UNKNOWN | SAT |
| 1 | 59,059 | 223,572 | 59.906 | UNKNOWN | SAT |
| 2 | 62,702 | 235,565 | 63.828 | UNKNOWN | SAT |
| 3 | 54,453 | 208,631 | 52.484 | UNKNOWN | SAT |

Run the following from this directory with the Python SAT dependency listed in **solver-requirements.txt** installed. The solver also reports decisions, propagations and restarts in its JSON output.

~~~sh
python refined_synthesis.py --case 0 --gates 18 --conflicts 200000 --separations
python refined_synthesis.py --case 0 --gates 19 --separations --fixed-star
python -m unittest test_synthesis test_refined_synthesis
~~~
