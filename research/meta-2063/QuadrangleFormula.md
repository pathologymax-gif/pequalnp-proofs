# The exact formula size on the projective-plane quadrangle tests

Every monotone binary formula that accepts the 52 incident point–line pairs of \(\mathrm{PG}(2,3)\) and rejects the 234 quadrangle test inputs has at least **64 gates**. A point-star formula attains the bound. The proof also determines the minimum size of a monochromatic rectangle partition of the associated communication problem, namely **65 rectangles**. The project desk asks about circuits with unrestricted gate reuse. This result covers the formula case and implies that every smaller correct circuit must reuse a reachable intermediate gate. [Project statement](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-2063)

## The rectangle problem

Line \(\ell\) has points \(\ell+\{0,1,3,9\}\) modulo 13. A positive row is a flag \(e=(p,\ell)\) with \(p\in\ell\), viewed as the input containing just these two vertices. A negative column \(M\) consists of a four-point set \(Q\) with no three collinear, together with its three exterior lines (the lines disjoint from \(Q\)). A rectangle with label \(v\) may contain cell \((e,M)\) only if \(v\in e\setminus M\).

A correct formula partitions the entire table into at most one rectangle per leaf. At an OR gate, the positive row chooses a true child with fixed tie-breaking. At an AND gate, the negative column chooses a false child. These choices preserve the Cartesian-product form and the two opposite values until reaching a variable in \(e\setminus M\). Constant leaves have empty rectangles. This is the monotone Karchmer–Wigderson argument. [Karchmer and Wigderson](https://doi.org/10.1145/62212.62265)

For each label \(v\), merge rectangles with identical nonempty row sets. Their column sets can be united. Write \(F_v\) for the resulting family of row sets, each drawn from the four flags incident with \(v\), and put \(t_v=|F_v|\). In a column \(M\), the subset \(U_v(M)\) assigned to \(v\) is a disjoint union of members of \(F_v\). It is empty if \(v\in M\). Otherwise it must include each flag whose other endpoint is in \(M\). Every flag is eventually forced to each of its endpoints, since every vertex occurs in some negative column and an incident pair never occurs together. Thus \(F_v\) covers the four flags. If \(t_v\ge4\), use the four singleton row sets instead, assigning each its original cells. This preserves the partition and never raises its cost. We may therefore assume \(1\le t_v\le4\), with four singletons when \(t_v=4\). Write \(L=\sum_v t_v\).

## A charge that can be checked one flag at a time

Give cell \(((p,\ell),M)\) weight zero unless \(p\notin Q\) and \(\ell\) meets \(Q\) in two points. In that case its weight is 1 or 5 according as one or two lines through \(p\) meet \(Q\) twice. There are 1,404 cells of each positive weight, of total weight 8,424. Define the score \(s_v\) as \(216t_v\) plus the total weight of cells assigned to \(v\). Then \(\sum_v s_v=216L+8424\).

The following table gives lower bounds for \(s_p+s_\ell\) on every flag. The left column gives \(t_p\), the headings give \(t_\ell\).

| \(t_p\) | 1 | 2 | 3 | 4 |
|---:|---:|---:|---:|---:|
| 1 | impossible | 1782 | 1728 | 1728 |
| 2 | 1755 | 1809 | 1755 | 1755 |
| 3 | 1710 | 1764 | 1710 | 1773 |
| 4 | 1728 | 1782 | 1728 | 1890 |

Two single-vertex bounds will also be needed. Every line has score at least 864. If \(t_p=3\) and \(F_p\) does not partition the four flags into block sizes \(2,1,1\), then \(s_p\ge891\).

These inequalities follow by finite enumeration. [The standalone integer checker](verify_plane_formula.py) requires only the Python standard library. For each family of one, two or three distinct nonempty subsets of four flags, or the four singleton sets, it forms all disjoint unions. For each column it keeps the unions satisfying the local conditions on \(U_v(M)\). To check a flag and two families, it minimizes the two local costs subject to **exactly one endpoint** claiming the common flag. Explicitly, if the point’s minimum local weights with the flag excluded or included are \(a_0,a_1\), and the line’s are \(b_0,b_1\), the column minimum is \(\min(a_0+b_1,a_1+b_0)\). An unavailable choice has infinite cost. Summing over columns and adding \(216(t_p+t_\ell)\) gives the bound for those two families. Taking the minimum over the families gives the table. Translation modulo 13 preserves every definition, so the four flags on line zero suffice. Run with \(\texttt{python verify_plane_formula.py}\).

## Excluding 64 rectangles

Summing the table bound of 1710 over the 52 flags counts each vertex four times. Thus \(4(216L+8424)\ge52\cdot1710\), giving \(L\ge64\). At \(L=64\), the **entire excess** of the 52 flag scores over 1710 is 72.

A point of cost 2 would spend at least \(4\cdot45>72\) of the excess. A point of cost 1 or 4 spends at least \(4\cdot18=72\), so at most one point is exceptional. Each line consequently meets at least three points of cost 3. A line of cost 2 or 4 would spend at least \(3\cdot54>72\) on these flags. Every line therefore costs 1 or 3. Each point of cost 3 uses a genuine \(2,1,1\) partition. Otherwise its four flags each have score at least \(891+864=1755\), again impossible. An exceptional point of cost 4 would make the point total 40, whereas the sum of 13 odd line costs is odd, contradicting \(L=64\). The remaining possibilities are 13 cost-3 points and seven cost-1 lines, or twelve cost-3 points, one cost-1 point and six cost-1 lines.

Let \(\ell\) be a cost-1 line. Whenever \(\ell\) meets \(Q\), some incident flag is forced to \(\ell\), so its sole rectangle takes all four flags. At each point \(p\) on \(\ell\), the row \((p,\ell)\) must be a singleton of the point partition. Indeed, if it shared a block with \((p,m)\) for another line \(m\), choose a quadrangle with \(m\) exterior and \(\ell\) meeting it. Such a quadrangle exists for every ordered pair of distinct lines, as verified by the checker. Now \((p,m)\) is forced to \(p\), making the point’s entire block active, while the line \(\ell\) also claims \((p,\ell)\). This violates disjointness.

Each point partition has at most two singleton blocks, hence lies on at most two cost-1 lines. But among any six distinct lines, five others meet the first at its four points, forcing three concurrent lines. This contradiction gives \(L\ge65\).

For the upper bound, take the OR over all 13 points \(p\) of \(x_p\) AND the OR of its four incident line variables. These 13 stars use four gates each and their final OR uses twelve, giving 64 gates and 65 leaves. It accepts each incident pair. A quadrangle contains no incidence between its selected points and exterior lines, so it rejects every negative test. This establishes both optima. The finite inequalities were checked with integer Python arithmetic.

