# Four collinear point-stars require nineteen replacement gates

For the projective plane of order three, take all four points on any one line. A binary monotone circuit that accepts their sixteen point–line incidences and rejects all 234 quadrangle tests requires **nineteen additional gates**, even with arbitrary fan-out and every OR of a subset of the lines through each of the nine other points supplied for free. Four ordinary stars and three gates combining their outputs attain the bound. The unrestricted assignment allows all thirteen stars to be reorganized. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## Restricting the inputs

Write $c$ for the common line. Each center has three private lines, and every line besides $c$ is private to one center. The raw inputs that affect a positive row are the four centers, $c$, and the twelve private lines. Replace every other raw input by zero. The sixteen positives persist, and every negative stays negative by monotonicity. Each useful free OR comes from one outside point and includes at most one private line from each center. The nine outside points supply $9(6+4+1)=99$ additional signals, for 116 sources in all. A complete untouched star contributes zero on every retained positive and may be replaced by zero.

After keeping $c$, the four center variables and only one of each center's three private lines, nine raw variables survive. The positive pairs form a tree with eight edges. Each center is joined to $c$ and its chosen private line. For all $3^4=81$ choices, every singleton and every one of the 28 other pairs is contained in the projection of an original negative. The verifier checks this from the plane incidence masks. Consequently every passing restriction accepts the eight edges and rejects those 28 pairs.

The eight-edge tree is connected and its nine open neighborhoods are distinct. The exhaustive two-extra-wire argument for such pair graphs from the three-noncollinear-star proof applies to the 36 pair tests here. On these tests the program finds that no circuit with ten gates and nine essential inputs passes. It checks possible repeated raw inputs and the one surviving form of repeated internal gate. The upper bound on these nine-input tests is eleven, from the four terms $p_i\land(c\lor a_i)$ combined with three ORs. [Two-extra-wire proof and verifier](ThreeTriangleStars.md)

## Sources with a budget of eighteen gates

A circuit reading $s$ sources and using $g$ gates has $s\le g+1$. Thus an eighteen-gate candidate uses at most nineteen sources. Each of the sixteen positive rows and 234 negative rows induces a clause of source variables. The clause says to choose at least one signal true on the positive and false on the negative, a necessary condition for any monotone circuit. Removing duplicate clauses and supersets leaves 869 clauses. Five unit clauses force the four centers and $c$.

If every raw variable is chosen, at most two extra ORs are chosen. Select a private line at each center outside those two signals, which exclude at most two of the three choices. During restriction, both extra ORs become zero. The connected undirected multigraph of a live binary circuit has cycle rank $g-s+1$, here at most two. Constant propagation deletes dead vertices and contracts unary gates with their nonzero input. These operations cannot increase cycle rank, including when parallel wire occurrences are retained. Hence the circuit on at most nine surviving sources has at most $9-1+2=10$ gates, contrary to the pair tests. Distinct surviving vertices never have to be identified during this argument.

Otherwise a private raw line $x$ is absent. Two incidence-preserving permutations listed in the verifier act transitively on all $13\cdot 12$ ordered pairs $(c,x)$ of distinct lines. It suffices to test one representative. The source clauses and budget then leave precisely fifteen possible source selections. Twelve consist of the sixteen remaining raw variables plus three pairwise ORs containing $x$. In the other three, all four raw lines through one of the three outside points on $x$ are missing, and their six pairwise ORs replace them. Each of the fifteen selections has nineteen sources.

The verifier constructs these selections from the plane, checks their source clauses, rules out further selections with the independently checkable finite refutation described below, and tries all 81 private-line restrictions for each selection. For each there is a restriction on which expanding the surviving inputs of all source ORs takes at most ten raw leaf occurrences in total, counting retained raw leaves as well. With nineteen sources and at most eighteen gates the original circuit is a read-once formula in its source signals. Expanding those leaves on the chosen restriction yields a formula with at most nine gates, which again violates the nine-input pair test.

## Reproducing the certificate

Place the verifier beside the research branch's `quadrangle_faces.py`, `verify_three_stars.py`, and `verify_triangle_stars.py`. Run the following commands in a temporary directory with these scripts available. The first command checks the geometry and pair-graph calculation and emits the deterministic DIMACS source-selection problem. Passing `--proof` also generates a DRAT refutation using the Glucose solver from `python-sat`.

```sh
python verify_four_collinear.py four.cnf --proof four.drat
drat-trim four.cnf four.drat
```

The 708-variable, 3,588-clause formula asserts the separating clauses, the absent representative line, a unary bound of nineteen sources and fifteen clauses excluding the listed selections. Each exclusion forbids containing every member of its corresponding nineteen-element set, which at this budget forbids exactly that set. In the balanced unary counter, the $j$-th output of each subtree is forced when it contains at least $j$ selected leaves. Choosing precisely the count-implied outputs extends every selection of at most nineteen. The empty clause was independently checked by reverse unit propagation after 178,391 clause additions. [Verifier](verify_four_collinear.py)
