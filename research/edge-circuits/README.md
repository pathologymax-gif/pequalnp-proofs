# Small circuits for graph edge functions

Given a graph and a set of selected vertices, the edge function asks whether two selected vertices share an edge. These notes study the minimum number of gates needed to answer that question. Each AND, OR and NOT costs one gate. AND and OR have two inputs. Wires can be reused for free.

| Question | Result and evidence |
|---|---|
| Which graphs on $n$ nonisolated vertices need exactly $n-1$ or $n$ gates? | The written classification identifies disjoint unions of complete bipartite graphs and a second family with one component obtained from a four- or five-vertex path. An independent topology search reproduces the counts through eight vertices. [Proof and counts](EdgeCircuitNote.md) |
| What certifies that at least $n+1$ gates are necessary? | An induced copy of any one of eight small graphs suffices. Every graph requiring at least $n+1$ gates contains such a copy. The derivation includes an exhaustive finite check. [Eight obstructions and their encodings](ForbiddenCores.md) |
| Can negation help a monotone function at these gate counts? | A written proof eliminates negation from any circuit of size at most $n+1$ for a monotone function with $n$ essential inputs. Two implementations independently count 4,620 six-vertex graphs of minimum size seven. [Proof and exhaustive synthesis](TwoExtraGates.md) |

Three Lean files formalize steps in the written arguments. [EdgeShape.lean](EdgeShape.lean) characterizes read-once formulas whose minimal satisfying assignments have weight two. [OneWire.lean](OneWire.lean) characterizes the signals that can represent all the inputs on one side of a cut crossed by an edge. [MonotoneMerge.lean](MonotoneMerge.lean) proves the identity used to remove a complemented wire where two branches rejoin. The general circuit classifications above have written proofs.

## Reproduce the calculations

Run these commands from this directory. The Python programs use the standard library. The independent [C# enumerator](VerifyTwoExtraGates.cs) includes build and run instructions.

```sh
python verify_edge_circuits.py
python verify_one_extra_gate.py
python verify_circuit_topologies.py --max-n 8
python verify_forbidden_cores.py
python verify_forbidden_seven.py
python verify_two_extra_gates.py --max-n 6
```

The model and the comparison with the known results on paths, forests, and four-cycles are set out in the project's [paper on graph edge functions](https://pequalnp.com/papers/note-1).
