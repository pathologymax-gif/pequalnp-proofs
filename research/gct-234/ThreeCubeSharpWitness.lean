import Mathlib

/-!
An integer-coefficient sum of three weighted binomial cubes has a root of
multiplicity seven at one. Over the reals, take signs `+1, -1, +1` and
multiply the second and third binomials by the real cube roots of 9 and 45.
This changes their cube coefficients to 9 and 45 and preserves their two
monomials. The example therefore gives a lower bound for the signed problem.
-/

namespace ThreeCubeSharpWitness

open Polynomial

noncomputable section

variable (R : Type*) [CommRing R]

def witness : R[X] :=
  (X ^ 6 - 1) ^ 3 - 9 * (X * (X ^ 4 - 1)) ^ 3 +
    45 * (X ^ 2 * (X ^ 2 - 1)) ^ 3

def cofactor : R[X] :=
  (X + 1) ^ 3 * (X ^ 8 + 4 * X ^ 7 + 13 * X ^ 6 + 23 * X ^ 5 +
    35 * X ^ 4 + 23 * X ^ 3 + 13 * X ^ 2 + 4 * X + 1)

theorem factorization : witness R = cofactor R * (X - C (1 : R)) ^ 7 := by
  simp only [witness, cofactor, map_one]
  ring

theorem cofactor_at_one : (cofactor R).eval 1 = 936 := by
  norm_num [cofactor, eval_mul, eval_add, eval_pow]

theorem multiplicity_seven [CharZero R] : (witness R).rootMultiplicity 1 = 7 := by
  have hn : (cofactor R).eval 1 ≠ 0 := by rw [cofactor_at_one]; norm_num
  have hp : cofactor R ≠ 0 := fun h => hn (by rw [h, eval_zero])
  rw [factorization, rootMultiplicity_mul_X_sub_C_pow hp, rootMultiplicity_eq_zero hn]

end

end ThreeCubeSharpWitness

#print axioms ThreeCubeSharpWitness.multiplicity_seven
