# Graph edge functions one gate above the minimum

## Result and model

Let $G$ be a finite simple graph with at least one edge. Discard isolated vertices and let $n$ be the number of remaining vertices. The edge function $f_G$ accepts a set of vertices if it contains both ends of at least one edge. Inputs are free. Each binary AND, binary OR, or unary NOT costs one gate. Wires can be reused at no cost. A circuit is acyclic and has one output.

A **biclique** is a complete bipartite graph with both sides nonempty. An **independent blow-up** of a graph replaces each vertex by a nonempty independent set and each edge by all edges between its endpoint sets.

**Theorem.** The minimum circuit size of $f_G$ is determined at the first two possible sizes as follows.

| Minimum size | Components of $G$, after removing isolated vertices |
|---|---|
| $n-1$ | Every component is a biclique. |
| $n$ | Exactly one component is an independent blow-up of the four-vertex path $P_4$ or the five-vertex path $P_5$. Every other component is a biclique. |
| At least $n+1$ | Every remaining graph. |

For example, the path $a-b-c-d-e$ has a five-gate circuit computing $b(a\lor c)\lor d(c\lor e)$. Here juxtaposition denotes AND. Replacing $c$ by three independent vertices with identical neighbors costs two more OR gates. The theorem shows that seven gates are necessary for the resulting seven-vertex graph.

## Proof

**The read-once case.** A minterm is an inclusion-minimal set of true inputs that makes a monotone function true. The minterms of $f_G$ are its edges. Consider an AND/OR formula in which each variable occurs exactly once. At an OR the children use disjoint variables, so their minterms survive separately. At an AND every pair of child minterms combines to a minterm. If all resulting minterms have size two, both children have only singleton minterms and each is the OR of its variables. This AND represents one biclique. Induction through OR gates gives a disjoint union of bicliques. Conversely, take the AND of the two side-disjunctions for each biclique and join the components by OR.

**A set of inputs represented by one wire.** Suppose $f_G=h(g(x_S),y)$, where $S$ is a nonempty set of inputs, $y$ comprises the remaining inputs, and both functions are monotone. Each member of $S$ is essential to $f_G$, hence essential to $g$. If there is a crossing edge $uv$ with $u$ outside $S$ and $v$ inside, set exactly $u$ true outside. As a function of the bit $g$, the output is then nonconstant and monotone, hence the identity. In particular $g$ is true on the singleton $\{v\}$. With all exterior inputs false, the output cannot equal $g$, since $f_G$ rejects every singleton. It must be constant zero, since it also rejects the empty input. Thus $S$ is independent. Returning to the assignment with just $u$ true outside shows that $g$ is the OR of the neighbors of $u$ in $S$. Essentiality makes these all of $S$. The same argument applies to every exterior neighbor. The vertices of $S$ therefore have identical open neighborhoods and are independent copies of a single vertex. If there is no crossing edge, $S$ contains an edge by essentiality, and at the all-zero exterior assignment the output is nonconstant. It equals $g$, so $g$ computes the edge function on $S$.

**The circuit with one extra gate.** Discard gates that cannot reach the output and propagate constants, if supplied, using the identities for AND, OR, and NOT. The $n$ essential inputs survive. With $b$ binary gates and $u$ unary gates, the underlying connected multigraph has $n+b+u$ vertices and $2b+u$ wires. Counting parallel wires separately gives $b\ge n-1$. At $b=n-1$ the graph is a tree. Under the budget of $n$ gates there is at most one NOT. If present, the output would be decreasing in any variable below that NOT, contrary to its being increasing and essential. This leaves the read-once case.

At $b=n$ there is no NOT. Every vertex except the output has at least one outgoing wire. Their total outdegree exceeds this minimum by one, so exactly one vertex has two outgoing wires. The subcircuit feeding that vertex is a read-once formula $g$ on private inputs $S$. If $S$ has no crossing edge, $g$ computes the edge function there. Setting its output to zero leaves a read-once formula for the exterior graph after constant propagation. Both parts are biclique unions. Otherwise the one-wire argument permits contracting $S$ to a single variable $r$, whose two outgoing wires now account for all sharing. Expansion at the end simply enlarges a vertex group in a biclique or a path blow-up.

Follow the two paths out of $r$ to their first common gate $M$. Such a gate exists because all gates reach the output, and each path has a unique continuation. The inputs feeding $M$ influence the exterior only through $M$. If some graph edge crosses this set, $M$ computes a disjunction by the one-wire argument. Substituting that disjunction into the exterior read-once formula makes the whole graph read-once. Otherwise $M$ computes the edge function on its own inputs, and setting $M=0$ leaves only bicliques outside. This includes $M$ being the output. Write $M=A(r,X)\circ B(r,Y)$. The two branches are read-once, $X$ and $Y$ are disjoint, and only $r$ occurs in both.

*If $M$ is OR,* neither branch can have a singleton minterm. Every branch minterm survives the OR, since a minterm of the other branch contained in it would have to lie inside $\{r\}$. Thus all branch minterms have size two, and each branch is a biclique union. The two bicliques containing $r$ meet at that vertex. Each further biclique forms a separate component. In each joined biclique, the side opposite $r$ is one group of independent copies. Any additional vertices on $r$'s own side form another such group. If neither branch has this additional group, the joined component is a biclique. If one branch has it, the component is a blow-up of $P_4$. If both have it, the component is a blow-up of $P_5$.

*If $M$ is AND,* put $A_i=A(i,X)$ and $B_i=B(i,Y)$. If $A_0B_0$ is identically zero, every edge contains $r$, giving a star. Otherwise $A_0$ and $B_0$ are both nonzero, vanish on their respective empty inputs, and have disjoint variables. Their product has only two-element minterms. Thus $A_0=\bigvee X_0$ and $B_0=\bigvee Y_0$ for nonempty subsets, and the edges away from $r$ are exactly $X_0\times Y_0$. The restricted function $A_1B_1$ accepts a singleton because $r$ has a neighbor, and it rejects the empty input. Exactly one factor is true on its empty input and therefore identically true. By symmetry take $A_1=1$. The restricted function is then independent of $X$, so $r$ has no neighbor in $X$. Essentiality gives $X=X_0$. For each $y\in Y_0$, the edge from any $x\in X_0$ to $y$ still suffices when $r=1$. Independence from $x$ gives $B_1(\{y\})=1$, so $r$ is also adjacent to $y$. Every $y\in Y\setminus Y_0$ must be adjacent to $r$ by essentiality. This graph has edge sets $X\times Y_0$ and $\{r\}\times Y$. It is a biclique if $Y_0=Y$. If $Y_0$ is a proper subset of $Y$, its four ordered groups $X,Y_0,\{r\},Y\setminus Y_0$ form a blow-up of $P_4$.

**Attainment and exactness.** A biclique on $m$ vertices costs $m-1$ gates. Formulas for the exceptional paths are $b(a\lor c)\lor cd$ and $b(a\lor c)\lor d(c\lor e)$, costing four and five gates respectively. For each group of $t$ independent copies substitute their disjunction, using $t-1$ further gates and sharing the resulting wire where needed. Combining components with OR gives the claimed budgets. A path blow-up contains an induced $P_4$, which no biclique union contains. The read-once case therefore excludes the smaller budget for every exceptional graph.

## Finite checks and formal scope

Each row counts labeled simple graphs with no isolated vertices. Two enumerations checked the first two gate budgets through six inputs. One enumerates read-once formulas and circuits with one shared wire using truth tables. The other enumerates circuit topologies. A separate gate-by-gate search cross-checks the counts through four inputs. The 1,860 labeled six-vertex graphs of minimum size six fall into ten isomorphism classes.

| Inputs | Eligible graphs | Minimum $n-1$ | Minimum $n$ |
|---:|---:|---:|---:|
| 2 | 1 | 1 | 0 |
| 3 | 4 | 3 | 0 |
| 4 | 41 | 10 | 12 |
| 5 | 768 | 45 | 180 |
| 6 | 27,449 | 241 | 1,860 |

The accompanying Lean theorem formalizes the read-once structural step. In `EdgeShape.lean`, `EdgeShape.Formula.minimal_two_iff_bicliqueUnion` proves that every inclusion-minimal satisfying Boolean assignment has exactly two true inputs if and only if the read-once formula has the syntax of a disjoint union of bicliques. Lean 4.37.0-rc1 checked this theorem using only `propext`, `Classical.choice`, and `Quot.sound`. The general circuit reduction and the classification at size $n$ are proved above on paper.

## Relation to earlier work

The size-$n-1$ case is a consequence of Gurvich's classical characterization. In the formulation of Karchmer, Linial, Newman, Saks, and Wigderson, Theorem 2.6, the minterms of a monotone read-once function are the maximal cliques of a graph with no induced $P_4$. For an edge function, this graph is $G$ itself. The condition becomes triangle-freeness together with the absence of an induced $P_4$. [Combinatorial Characterization of Read-Once Formulae, Discrete Mathematics 114 (1993), 275–282](https://www.math.ias.edu/~avi/PUBLICATIONS/MYPAPERS/KLNSW93/paper.pdf)

The P vs NP project's path formula gives minimum gate counts four and five for $P_4$ and $P_5$. Its forest lower bound together with its vertex-cover upper bound gives minimum size $|E|+\tau(G)-1$ on forests, where $\tau(G)$ is the minimum vertex-cover size. The characterization above also covers blow-ups containing four-cycles and allows additional disjoint bicliques. [Lower bounds for the edge function, rows L-meta-102, L-meta-104, and L-meta-105](https://pequalnp.com/papers/note-1)
