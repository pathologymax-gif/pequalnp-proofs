# Partial results for L-gct-234

The assignment asks whether a nonzero signed sum of the cubes of three real polynomials, each supported on at most two monomials, has positive-root multiplicity at most nine. These files establish special cases and give reproducible finite certificates. The unrestricted upper bound remains open in this work.

| File | Result |
| --- | --- |
| [ThreeCubeMultiplicity.md](ThreeCubeMultiplicity.md) | Proves the sharp upper bound of seven when at least one input polynomial vanishes at the positive root. It also treats several other families. |
| [ThreeCubeNonvanishing.md](ThreeCubeNonvanishing.md) | Treats special cases with three nonvanishing inputs and derives an exact finite test. It excludes multiplicity ten or higher for every exponent configuration of width at most 100. |
| [ReductionGct234.lean](ReductionGct234.lean) | Formally proves the case of at most ten output monomials and normalizes the remaining problem to the root one under two explicit hypotheses about larger supports. |
| [ThreeCubeSharpWitness.lean](ThreeCubeSharpWitness.lean) | Formally proves an explicit polynomial factorization and root multiplicity seven. The first note explains how real cube-root scalings place the example in the signed problem. |
| [CubeResidueObstruction.md](CubeResidueObstruction.md) | Proves the upper bound of nine whenever the twelve exponents in the expanded cubes occupy at least eleven residue classes modulo some prime from 11 through 101. This applies at any exponent width. Two independent implementations check 50,925,347 configurations across 22 primes. |
| [CubeResidueCertificate.lean](CubeResidueCertificate.lean) | Formally checks the finite exclusions for primes 11 and 13 and derives the exclusion for each eligible pair from the aggregate computation. The note gives the argument for arbitrary exponents and links the independent [C# verifier](CheckCubeResidues.cs) and its [per-prime output](cube-residues-independent.csv). |

The Lean checker uses the assignment's exact [upstream revision](https://github.com/open-goat/pequalnp-proofs/commit/d82dd4d5ddc53bfc09def53d92781e0ff866726f), Lean 4.36.0, and its pinned Mathlib. The research workflow treats warnings as errors and prints the axiom dependencies of the principal lemmas.

The symbolic checks require Python, NumPy and SymPy. The short independent support check uses Python's standard library. From this directory, run the commands below. The Python and Node.js width-100 runs independently exclude all 1,232,645,380 eligible exponent triples in that range.

```sh
python verify_three_cubes.py
python verify_cube_common_mean.py
python verify_cube_supports.py --count 50 100 --exact 12
python search_cube_order10.py --degree 100
node verify_cube_supports_modular.js 100
python verify_cube_residues.py 11 13
```

Prepared by Brett Snodgrass and collaborating research agents. The small-support Lean proof adapts an argument by [williamzheng0711 in pull request 23279](https://github.com/open-goat/pequalnp-proofs/pull/23279). The source file records the original commit.
