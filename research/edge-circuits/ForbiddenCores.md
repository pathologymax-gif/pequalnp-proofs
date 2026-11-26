# Eight induced obstructions for the first two circuit sizes

Let $G$ be a finite simple graph with at least one edge, and let $n$ count its nonisolated vertices. Its edge function $f_G$ accepts exactly those vertex sets containing an edge. Inputs and wire reuse are free. Each binary AND, binary OR, and unary NOT costs one gate.

**Certificate.** The minimum circuit size is at least $n+1$ if and only if $G$ contains an induced copy of one of the eight graphs below. An induced copy requires checking both the listed edges and the absent edges among its chosen vertices. Every certificate uses at most eight vertices. The seven connected minimal obstructions have at most six vertices.

| Graph | Vertices | Edges on labeled vertices | Check mask |
|---|---:|---|---:|
| Triangle | 3 | 01 02 12 | 7 |
| Five-cycle | 5 | 01 12 23 34 40 | 220 |
| Six-cycle | 6 | 01 12 23 34 45 50 | 1880 |
| Six-vertex path | 6 | 01 12 23 34 45 | 6800 |
| Domino, two squares sharing an edge | 6 | 01 12 23 30 34 45 52 | 21812 |
| Square with leaves attached to adjacent vertices | 6 | 01 12 23 30 04 15 | 23184 |
| Tree with arms of lengths 1, 2 and 2 | 6 | 01 02 23 04 45 | 25232 |
| Two disjoint four-vertex paths | 8 | 01 12 23 45 56 67 | 50628672 |

In the edge column, 01 joins vertices 0 and 1. The final column is invariant under relabeling. Sort vertices by nondecreasing degree, permute vertices within equal-degree groups, assign bit positions to unordered pairs in lexicographic order starting at zero, and take the smallest resulting integer. Each check uses the pair of vertex count and mask.

## Derivation

Use the circuit classification in [Graph edge functions one gate above the minimum](EdgeCircuitNote.md). Discarding isolated vertices, the graphs of minimum size at most $n$ have biclique components and at most one exceptional component. A biclique has two nonempty independent sides and every possible edge across them. An exceptional component is obtained from $P_4$ or $P_5$ by replacing each vertex with a nonempty independent group and replacing each edge with every possible edge between the two groups. Include edgeless graphs in this structural class. They require zero gates under the project's missing-output convention.

**Vertex deletion preserves the class.** A vertex deletion shrinks a group, removes a group, or removes an isolated vertex. Removing groups from a path leaves path segments, with isolated vertices allowed. A segment on two or three groups gives a biclique. A segment on four or five groups remains exceptional. A path on at most five groups cannot yield two such segments. This proves that every induced subgraph of an allowed graph is allowed. Consequently an excluded graph contains a minimal excluded induced subgraph, obtained by deleting vertices while exclusion persists. If a minimal excluded graph occurs as an induced subgraph, this same closure proves exclusion of the larger graph, with $n$ measured on the larger graph.

**Disconnected exclusions.** In a disconnected minimal excluded graph, each component belongs to the class individually, since otherwise that component is a smaller exclusion. There must then be at least two exceptional components. Each contains an induced $P_4$, obtained by taking one vertex from each of four consecutive groups. The resulting induced $2P_4$ is excluded. Minimality forces the entire graph to equal $2P_4$. Deleting any vertex from this graph leaves at most one exceptional component.

**Connected exclusions.** False twins are distinct vertices with identical open neighborhoods. They are nonadjacent in a simple graph. Duplicating a nonisolated vertex as a false twin preserves membership in the class by enlarging its group. A connected minimal excluded graph $H$ therefore has no false twins. It has at least three vertices. Choose a leaf $v$ of any spanning tree of $H$. Deleting $v$ keeps the remaining graph connected and, by minimality, puts it in the class. The remaining connected graph has at least two vertices, so it is a blow-up of $K_2$, $P_4$, or $P_5$.

Each group in this blow-up is one false-twin class. Distinct vertices of each of the three templates have distinct open neighborhoods, and all groups are nonempty. Members of one group in $H-v$ can acquire only two different neighborhoods when $v$ is restored, distinguished by whether they are adjacent to $v$. As $H$ has no false twins, each group has exactly one of three possible forms.

- A singleton adjacent to $v$.
- A singleton nonadjacent to $v$.
- A pair with exactly one member adjacent to $v$.

These choices also cover every possible partial neighborhood. Selecting either member of a pair yields isomorphic graphs. Enumerating ordered choices over the three templates gives $3^2+3^4+3^5=333$ candidates, each with at most eleven vertices. Orientation duplicates are harmless. Discard disconnected candidates and those still having false twins. Test that the candidate is excluded and that every one-vertex deletion is allowed. Because the class is hereditary, these tests capture induced minimality. The remaining connected graphs yield the first seven rows after removing isomorphic duplicates.

**An independent bound on connected obstructions.** Every connected minimal exclusion on at least four vertices is triangle-free, because the triangle is already excluded. Mark a group of $H-v$ if it contains a neighbor of $v$. Consecutive groups cannot both be marked, since that would create a triangle. Every two-vertex group is marked. It follows that templates on two or four groups can yield at most seven vertices including $v$. With five groups, a candidate on eight or more vertices must have at least two groups of size two. Take any two such groups. Their positions on the path differ by two, three, or four.

- At distance three, take the two representatives adjacent to $v$ and one representative in each intervening group. Both intermediate representatives miss $v$. These four vertices and $v$ induce a five-cycle.
- At distance four, take the adjacent representatives from the two end groups and one representative from each other group. The second and fourth groups miss $v$. If the middle group has a representative missing $v$, use it to obtain a six-cycle. Otherwise take a middle representative adjacent to $v$ to obtain a domino.
- At distance two, the two adjacent representatives, a representative of the middle group, and $v$ give a square. At least one selected endpoint has a path neighbor outside this three-group segment. Take a representative from that outside group. It misses $v$ and becomes a pendant leaf at that endpoint. Use the representative missing $v$ from the opposite size-two group as a pendant leaf at the middle vertex. This gives the square with leaves at adjacent vertices.

Each case produces a smaller exclusion on at most six vertices. A connected minimal exclusion therefore has order at most seven, independently of the eleven-vertex candidate bound.

**Membership test.** For each connected component with an edge, group vertices by equality of their open neighborhoods and retain one representative per group. Adjacency between two groups is uniform by symmetry, so the representative graph determines the component up to its group sizes. Accept a quotient of $K_2$, or a path on four or five vertices, allowing at most one path quotient across the graph. Connectivity of the quotient follows from connectivity of the component. Thus a path quotient is recognized by its order and degree sequence: exactly two vertices of degree one, all others of degree two. This test shows both why each listed graph is excluded and why deleting any one of its vertices makes it allowed. The executable check runs those tests separately for every named graph.

## Reproducing the finite checks

[verify_forbidden_cores.py](verify_forbidden_cores.py) uses only Python's standard library. Running it reproduces the 333 candidates, checks all eight edge encodings, and compares the quotient test with a direct induced-subgraph test on every labeled graph through six vertices. It also tests 2,048 deterministically sampled graphs at each of orders seven and eight. The direct test compares the induced edge mask with all relabelings of each explicitly listed obstruction.

[verify_forbidden_seven.py](verify_forbidden_seven.py) makes a second exhaustive check by constructing the class from paths, isolated vertices, disjoint edges, and false-twin duplications. It checks all 2,097,152 labeled graphs on seven vertices, including isolated vertices. Exactly 39,397 belong to the class and none of the seven-vertex exclusions are induced-minimal. On six vertices, this construction finds 1,320 labeled minimal exclusions, split into 60 six-cycles, 180 dominoes, and 360 each of the other three shapes. Together with the independent bound of seven for connected minimal exclusions, this reconstructs the same connected list without the 333-candidate enumeration.

    python verify_forbidden_cores.py
    python verify_forbidden_seven.py
    python verify_circuit_topologies.py --max-n 8

As a separate count, let $B_n$ count labeled disjoint unions of bicliques without isolates and set $B_0=1$. The component of a distinguished vertex gives

$$
B_n=\sum_{k=2}^{n}\binom{n-1}{k-1}(2^{k-1}-1)B_{n-k}.
$$

For a connected exceptional component on $k$ labels, there are $12S(k,4)+60S(k,5)$ possibilities, where $S(k,j)$ counts partitions into (j) nonempty sets. The factors are $4!/2$ and $5!/2$, since reversing the order of path groups preserves the graph. Different partitions cannot describe the same graph because the false-twin groups are recovered from its neighborhoods. To count graphs of minimum size $n$, choose the labels of the exceptional component and use $B$ on the remaining labels.

| Nonisolated vertices | All eligible labeled graphs | Minimum $n-1$ | Minimum $n$ |
|---:|---:|---:|---:|
| 7 | 1,887,284 | 1,428 | 17,640 |
| 8 | 252,522,481 | 9,325 | 169,092 |

The independent [circuit topology enumerator](verify_circuit_topologies.py) yields the same two rows by evaluating circuits on every input assignment. It does not use the obstruction list or the graph classification. The obstruction theorem combines the paper circuit classification with the finite enumeration above. Its Lean verification and its historical novelty have not been established.
