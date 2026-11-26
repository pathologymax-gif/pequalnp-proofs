# Graph edge functions at two gates above the support bound

We enumerated one-output acyclic circuits on the nonisolated vertices of labeled simple graphs. Each AND, OR, and NOT gate costs one. AND and OR have two inputs, NOT has one, and sharing an output costs zero. A graph accepts exactly the sets of vertices containing both ends of an edge.

| Inputs | Eligible graphs | Minimum $n-1$ | Minimum $n$ | Minimum $n+1$ | Isomorphism classes at $n+1$ |
|---:|---:|---:|---:|---:|---:|
| 2 | 1 | 1 | 0 | 0 | 0 |
| 3 | 4 | 3 | 0 | 1 | 1 |
| 4 | 41 | 10 | 12 | 18 | 2 |
| 5 | 768 | 45 | 180 | 275 | 8 |
| 6 | 27,449 | 241 | 1,860 | 4,620 | 24 |

At six inputs, 6,721 labeled graphs admit circuits of at most seven gates. The results with and without NOT agreed graph by graph at every tested budget.

The [independent C# enumerator](VerifyTwoExtraGates.cs) builds circuits gate by gate in nondecreasing depth order and checks the same counts through six inputs. The Python program counts rooted ordered circuit templates with repetitions and symmetries, including interchangeable orientations and different names for the same labeled output under a permutation. The number of generated templates measures the search work. The graph counts in the table deduplicate by truth table and restore every vertex labeling.

The program `verify_two_extra_gates.py` generates the data. Consider the connected output cone of a circuit with $n$ essential inputs, $b$ binary gates and $u$ unary gates. It has $n+b+u$ vertices and $2b+u$ wires, so $b\ge n-1$. Depth-first expansion from the output visits each vertex once. Each later reference to it points to an already completed vertex, since a reference to an active ancestor would form a directed cycle. Replacing the later references by placeholder leaves gives an ordered tree with $b+1$ leaves, precisely $b+1-n$ of them placeholders. Under the $n+1$ gate budget there are at most two. The program enumerates all the trees, all placeholder assignments to previously completed inputs and gates, all paid NOT placements, and all AND/OR labels. Restoring all permutations of the inputs gives labeled counts. A separate straight-line search that adds one new truth table at a time checked the same results through four inputs. Run with `--classes` to print edge lists and labeling counts for every exact-$n+1$ isomorphism class.

## Why negation cannot help at these budgets

**Proposition.** If a monotone Boolean function on $n$ essential inputs has a circuit of at most $n+1$ gates in this basis, it has a monotone circuit of at most the same size.

Discard dead gates and propagate constants. With two NOT gates, the wire bound forces $b=n-1$ and a read-once tree. Pushing negations down the tree by De Morgan's laws leaves one literal per input. A negative literal would make the function nonincreasing in that essential input, contradicting monotonicity. The resulting positive tree uses only its $n-1$ binary gates. The same argument applies to a read-once tree containing one NOT.

It remains to treat one NOT gate $N$ and $b=n$ binary gates. There is a unique vertex $z$ with two outgoing wires. Its two paths reconverge before or at the output. Every input reaching $N$ must also have a path to the output bypassing $N$. If all its paths traverse $N$, its only influence is through the negation of a nondecreasing function, making the output nonincreasing in that essential input. Consequently $N$ lies on one branch after $z$ and before the first merge. Moreover $N$ reads $z$ directly. Any intervening binary gate would introduce a second input. A second path from $z$ to that gate would already merge both branches. Any other source would supply a private essential variable whose only output path traversed $N$.

Write the first merge as $A(\neg z,X)\circ B(z,Y)$, where $\circ$ is AND or OR. The branches have disjoint private variables and are positive read-once formulas in their displayed arguments. The outer tree can transmit the merge unchanged by setting its private variables to neutralize every side branch. Varying the private inputs upstream of $z$ from all zero to all one changes $z$ from zero to one, so monotonicity of the original function makes the merge nondecreasing in $z$ for every fixed $X,Y$.

Choose $X$ for which $A(1,X)=1$ and $A(0,X)=0$. Such an assignment exists because a positive read-once formula depends on every input. At an OR merge, nondecrease from $z=0$ to $z=1$ forces $B(1,Y)=1$ for all $Y$. Replacing $\neg z$ by constant one leaves the output unchanged at $z=0$ and is masked by $B$ at $z=1$. At an AND merge, the same comparison forces $B(0,Y)=0$ for all $Y$. Replacing $\neg z$ by constant zero leaves the output unchanged at $z=1$ and is masked by $B$ at $z=0$. Propagating the constant removes the NOT gate. This proves the proposition.

The Lean theorem `MonotoneMerge.replace_complement` checks the replacement identity at the first merge. The same file checks the neutral setting for a positive path and the inference of local monotonicity from a sensitized outer context. [MonotoneMerge.lean](MonotoneMerge.lean)

Project row L-meta-17828 asks for an AND/OR circuit of the same or smaller size whenever a circuit with one NOT computes the specified monotone output, with no upper limit on the starting size. For the one-output model, the proposition proves that conclusion whenever the circuit has at most one more gate than the number of essential input variables. An unused input can be fixed before applying the result and the resulting circuit can ignore that input on the original domain. A separate argument proves that larger circuits yield counterexamples to the universal statement. [One-negation size proof](OneNegationSize.md) · [Project row L-meta-17828](https://pequalnp-desk.pequalnp.workers.dev/desk/row?gap=L-meta-17828)

## A lower bound for the project's essential NOT

**Corollary.** Let a project gate list in the basis `Basis2` compute one monotone Boolean output depending on all $n$ input bits. If the list satisfies `EssentialOneNot`, it contains at least $n+2$ gates. This is a lower bound on every qualifying list, including when no such list exists.

The project's test designates a NOT gate at position $q$ and replaces that same gate by a constant while preserving every wire index. Essentiality requires a change to the computed function under each of the two replacements. The assignments witnessing the changes may differ. The following normalization preserves both experiments.

Interpret the list in its original order. A reference to a wire that does not yet exist means false, even if that index names a later gate. The same default applies to an invalid output index. An empty AND is true and an empty OR is false. A singleton AND or OR copies its input, and a repeated binary operand can also be copied. At the unique NOT, let $g(x)$ be its first input, taking false if that input is absent. A second operand at a NOT has no effect.

Cut only the output of gate $q$ and use a fresh formal bit $t$ in its place. Write $H(x,t)$ for the output of this cut circuit. All other gates are positive and $g$ depends only on $x$. The original output is $F(x)=H(x,\neg g(x))$. Replacing $q$ by constant $b$ produces $H(x,b)$ for every $x$. If $g$ is constant, one of these replacements reproduces $F$ identically. If $H$ ignores $t$, both reproduce $F$. Thus an essential NOT requires $g$ nonconstant and $H$ dependent on $t$.

Keep **both** $g$ and $H$ as outputs during simplification. With $t$ free, propagate constant inputs, bypass copies, and discard gates outside both output cones. Each operation preserves $g(x)$ and $H(x,t)$ for every $x,t$. In particular, a wire can be shared between the two cones without duplication. Now reconnect the occurrences of $t$ to one unary NOT with input $g$. Every gate retained solely to compute $g$ now feeds the output through the NOT. Every gate retained for $H$ also reaches the output. The reconnected circuit uses no more gates than the original list and preserves the original function and both replacement functions.

If the original list had length at most $n+1$, this normalized circuit would have one NOT in a tree or one NOT with one vertex of fan-out two. The tree case contradicts essential monotonicity. In the latter case the first-merge argument above supplies a fixed bit $b$ which can replace that particular NOT without changing the output on **any** assignment. Thus $H(x,b)=F(x)$ for all $x$, contradicting the project's essentiality test. For $n=0$ the input $g$ is constant, so there is no qualifying list.

The corollary concerns a single output. In a family of outputs, different members can witness the failures of the two constant replacements. [Project definitions of essentiality and gate lists](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/NotPremium.lean) · [Project evaluation of gates, wires, and outputs](https://github.com/open-goat/pequalnp-proofs/blob/main/lean/PEqualNP/Defs/CircuitLowerBounds.lean)

The circuit arguments are written proofs. The enumeration and its independent cross-check are computational checks on the stated finite ranges.
