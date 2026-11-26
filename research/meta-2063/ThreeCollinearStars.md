# Three collinear point-stars require fourteen replacement gates

Fix three collinear points in the projective plane of order three. A replacement circuit must accept their twelve incident point–line input pairs and reject all 234 quadrangle inputs of the project. It can use all original variables, and every OR of any subset of the four lines in each of the ten untouched point-stars is free. Even with arbitrary sharing and nested AND gates, it needs **fourteen additional binary monotone gates**. The three ordinary stars use twelve gates, and combining their outputs uses two more. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## Which inputs a small circuit must read

Write $c$ for the line through the three centers. Each center has three private lines. On the twelve positives, only the three point variables, $c$, and the nine private line variables can be true. A free OR at an outside point can be replaced by its restriction to these relevant line variables. This keeps all twelve positive values and can only lower values on negatives. Outside points on $c$ give no additional signal. At each of the nine outside points off $c$ the useful line sets are triples, one private line from each center. All two- and three-element subsets give four additional OR signals there. This allows a total of $13+9\cdot4=49$ sources. Signals of complete untouched stars and their combined outputs are zero on the twelve positives and can be replaced by zero.

For a positive row $P$ and a negative row $N$, some used source must be true on $P$ and false on $N$. Form the set of all such sources for every pair of rows. Every circuit must select at least one source in each set, since its output is monotone in its sources. The verifier checks the following finite statement for all 52 possible collinear triples: **omitting any one of the thirteen raw variables makes every selection of fourteen or fewer sources fail**. It enumerates the $12\cdot234$ row pairs per triple and discards redundant supersets. It then branches on the available choices for an unhit set. Pairwise disjoint unhit sets require distinct remaining sources, providing a sound early exit.

If a circuit with $g$ binary gates reads $s$ sources on paths to its output, then $s\le g+1$. Every reachable nonoutput vertex needs an outgoing wire; the gates supply at most $2g$ incoming wire occurrences. Thus a candidate of at most thirteen gates must use every raw variable and can use at most one additional source. If it uses that extra source, it has fourteen sources and exactly thirteen gates. Equality in the count makes every nonoutput vertex have one outgoing occurrence, so the circuit is a read-once formula in the fourteen source signals.

## Restriction to seven raw inputs

Keep the three point variables, $c$, and one chosen private line for each center. Set the other six private lines to zero. A remaining incidence is still accepted. On a negative row this restriction can only lower values, so every original negative, projected onto the seven remaining signals, is still rejected.

The verifier finds representatives for which all three common-line incidences and the three private incidences must be accepted and the same ten maximal negative patterns must be rejected. These seven-input tests work for all 52 triples. For each possible extra source, it finds representatives having at most one of that source's private lines. The source therefore reduces to either zero or one surviving variable.

With only the thirteen raw sources, restrict the six variables one by one. Each variable about to be set to zero remains essential: the positive input consisting of that line and its center must be distinguished from the center alone, which is contained in a negative. A gate reading this essential variable can be removed when it becomes zero, by replacing a binary AND by zero or a binary OR by its other operand. Each restriction saves at least one gate. This leaves at most seven gates.

With a fourteenth source, the original circuit was a read-once formula in its source signals. The six deleted raw leaves disappear, reducing the surviving formula to at most eight leaves. The additional source collapses to zero or to an already available raw input. Again, at most seven gates survive.

## Exhausting circuits with one extra wire use

Every surviving raw variable in the seven-input problem is essential, as witnessed by a positive incidence and a singleton below a negative. A connected output circuit on these seven inputs with at most seven binary gates can have at most one outgoing use beyond the one required for each nonoutput vertex. Consequently it is either read-once or it has a single vertex with two outgoing uses.

In the latter case the subcircuit producing this vertex is a read-once formula on a nonempty subset of the inputs, including the possibility that the vertex is itself a raw input. Those inputs have no other uses. Collapsing the shared vertex gives a read-once formula on the complementary inputs and two copies of its output. The integer verifier exhausts this description by partitioning leaves between the children of each binary gate and evaluating both AND and OR. A trace may be discarded when another trace on the same leaf set accepts identical positives and fewer negatives; substitution is valid even for both copies of the shared vertex. A subformula accepting no positive can be replaced by zero and simplified. The resulting smaller passing circuit would still have to use all seven essential raw inputs and would be covered by the same enumeration. No seven-gate circuit passes the tests. This proves the fourteen-gate lower bound.

The proof concerns replacing three collinear stars while the other ten supply ordinary precomputed ORs. The unrestricted project question also permits a circuit to reorganize all thirteen stars together.

Run `python verify_three_stars.py` beside `quadrangle_faces.py` using Python 3.10 or later. Both use only the standard library. [Verifier](verify_three_stars.py)
