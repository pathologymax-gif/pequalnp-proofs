# An 18-gate solution would have to reuse a signal that depends on an AND

On each of the four 10-variable projections in L-meta-17121, **19 gates are necessary and sufficient if every shared intermediate signal has only OR gates in its input cone**. The downstream part of the circuit may contain arbitrarily nested AND and OR gates. The OR preprocessing gates may depend on each other, and each may have any fanout. The [four explicit 19-gate witnesses](NineteenGateWitness.lean) attain the bound. The unrestricted size-18 question also allows reuse after an AND and remains open in this note.

## Counting the raw variables in the preprocessing

Remove dead gates. If an operand of an OR is redundant by idempotence or absorption, delete it in the private tree. A shared gate that becomes a raw input, constant zero, or duplicate of an earlier shared gate can be bypassed. If simplifying a private tree reduces a shared gate's fanout to one, count it as an ordinary private gate. These changes preserve all sample outputs and the OR-only condition on every remaining shared gate. We can take a minimum circuit with normalized private trees.

Let $r$ count the distinct shared non-input gates. Cut their output wires. Each private component now computes one of the $r$ helpers by a binary OR tree with leaves that are raw variables or earlier helpers. Its interior cannot be shared with any other component because every shared gate was cut. The remaining outer component is a monotone formula in the raw variables and cut labels. The zero input in an OR tree can be folded away. Write $R$ for the total number of raw leaves across all private trees and $Y$ for the total number of earlier-helper leaves. The private gates number $m=R+Y-r$. If $D$ counts occurrences of helper labels in the outer formula, then $Y+D\ge2r$ by the fanout requirement. Hence $m+D\ge R+r$.

Let $k$ count the distinct raw variables appearing in the private trees, and let $u$ count those appearing there at least twice. Then $R\ge k+u$. Every one of the other $10-u$ raw variables must occur as an ordinary outer leaf. To check this, consider a raw variable $v$ with at most one entrance into the preprocessing.

* If there is no entrance, choose a neighbor $z$ of $v$ and extend $\{z\}$ to a maximal independent set $M$. Every helper true on the positive edge $vz$ is true on $M$. Only the raw label $v$ distinguishes these two inputs.
* If there is a single entrance, the first OR combining $v$ has another raw variable $w\ne v$ in its other operand. The single-entrance assumption rules out another occurrence of $v$ in that operand. Since the preprocessing contains only ORs, every helper containing $v$ contains $w$. Choose a neighbor $z$ of $v$ equal or nonadjacent to $w$. This is possible because $v$ has at least two neighbors and distinct vertices have at most one common neighbor. Extend $\{z,w\}$ to a maximal independent set $M$, allowing $z=w$. Every helper true on $vz$ either contains $z$ or contains $v$ and therefore $w$. All are true on $M$. Again only the raw label $v$ distinguishes the positive and negative tests.

Every maximal independent set occurs among the sampled negatives. The companion checker verifies this and the two graph hypotheses on each projection. The outer formula needs at least $D+10-u$ leaves. A circuit of size at most 18 must therefore satisfy

$$
18\ \ge\ m+D+10-u-1\ \ge\ 9+r+R-u\ \ge\ 9+r+k.
$$

In particular $k\le9-r$. For $r\ge6$ there are at most three raw variables in the entire private network. Those variables admit only four distinct OR supports of size at least two, too few to supply six shared gates.

## Exhausting the dependence patterns

The previous [single-helper bound](OneSharedGate.md), [two binary helper bounds](TwoRawHelpers.md), [arbitrary two-tree and dependent-pair bounds](TwoOrTrees.md), and the [independent-tree bounds](ManyOrTrees.md) cover up to two shared gates and all cases without mutual dependencies. If all helper supports contain the same pair $P$, fixing every outer helper to one retains every positive edge and every negative meeting $P$. With $r\ge3$, at least three private gates were charged and the last shared gate contributes at least two outer helper leaves. At most 14 ordinary leaves remain. The [180 checked pair-cofactor bounds](SerialShared.md) require at least 15.

For $r=3,4,5$, enumerate all sets of $r$ distinct OR supports of size at least two on a raw universe of size at most $9-r$. Order supports by size, breaking ties by their numeric masks. A direct parent must have strictly smaller support. For each helper support $A_i$, choose any subset of eligible direct helper parents. Its direct raw operands must be exactly the elements of $A_i$ outside their union, since either omitting an uncovered element or adding a redundant operand contradicts the normalized representation. Each chosen parent must contribute some element not already supplied by the others. The normalized private cost is the number of chosen helper and raw operands minus one. This exhausts possible private constructions without assuming any particular parenthesization of the ORs.

If helper $i$ is read $y_i$ times inside other private components, it must occur at least $d_i=\max(0,2-y_i)$ times outside. An 18-gate counterexample would therefore have at most $19-m-\sum_i d_i$ ordinary outer leaves. Three screens compare that budget to the count of variables with at most one raw entrance, the forced ordinary labels in the full rectangle table with every helper available, and the forced ordinary labels after all helpers are fixed to one. The construction of forced rectangles and their conflict graph is given in [TwoOrTrees.md](TwoOrTrees.md). Fixing all helpers to one keeps all positive edges and the negatives on which every helper was already one.

| Shared gates | Largest raw universe | Support families per projection | Dependent configurations tested per projection | Further certificates over all 4 projections |
|---:|---:|---:|---:|---:|
| 3 | 6 | 3,860,700 | 1,668,690 | 73 |
| 4 | 5 | 3,422,700 | 10,909,380 | 0 |
| 5 | 4 | 97,020 | 1,711,920 | 0 |

The support-family column counts every family before the common-pair and incomparable-family reductions. A support family can have several normalized dependence patterns. The 73 residual cases all have three shared helpers. For each case fix the indicated helper labels to one and restrict the negative columns accordingly. The remaining labels are the ten ordinary variables and the unfixed helpers. The appropriate exterior leaf cap is $19-m-\sum_{i\text{ fixed}} d_i$. Each of the 73 integer-dual certificates proves a strict lower bound above its cap. The four projections required 2, 21, 9 and 41 certificates respectively.

## Replay

Run **python verify_or_library.py** with **AllOrLibrary.cs**, **or_library.json.gz**, **seed_tables.json**, **verify_many_or_trees.py**, and **verify_kw_first_shared.py** in this directory. Replay requires standard-library Python and a C# compiler through .NET SDK, Windows .NET Framework, or Mono. The Python code independently counts normalized dependence patterns over small abstract alphabets and checks the C# enumeration counts. It reconstructs each uncertain formula table, charging the actual private gate count and the required outside occurrences of precisely the fixed helpers, and verifies its arithmetic dual using Python integers.

The supporting cases can be replayed separately through **verify_one_shared_gate.py**, **two_raw_helpers.py**, **serial_shared.py**, **many_raw_helpers.py**, **verify_two_or_trees.py**, and **verify_many_or_trees.py**. The unrestricted 18-gate problem requires handling shared signals with at least one AND in their input cone.
