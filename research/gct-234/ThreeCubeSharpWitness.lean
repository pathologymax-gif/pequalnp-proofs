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

private theorem scaled_binomial_support (u : ℝ) (m n : ℕ) :
    (C u * (X^m - X^n) : ℝ[X]).support.card ≤ 2 := by
  have sub : (C u * (X^m - X^n) : ℝ[X]).support ⊆ {m, n} := by
    intro j hj
    by_contra h
    have h₁ : j ≠ m := by aesop
    have h₂ : j ≠ n := by aesop
    simp [mem_support_iff, coeff_C_mul, coeff_X_pow, h₁, h₂] at hj
  apply (Finset.card_le_card sub).trans
  by_cases h : m = n <;> simp [h]

/-- A nonzero signed sum in the project's exact Fin 3 model attains seven at 1. -/
theorem exists_signed_binomials_seven :
    ∃ (s : Fin 3 → ℝ) (g : Fin 3 → ℝ[X]),
      (∀ i, s i = 1 ∨ s i = -1) ∧
      (∀ i, (g i).support.card ≤ 2) ∧
      (∑ i, C (s i) * (g i)^3) ≠ 0 ∧
      (∑ i, C (s i) * (g i)^3).rootMultiplicity 1 = 7 := by
  let u : ℝ := (9 : ℝ) ^ (3 : ℝ)⁻¹
  let v : ℝ := (45 : ℝ) ^ (3 : ℝ)⁻¹
  have hu : u^3 = 9 := Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have hv : v^3 = 45 := Real.rpow_inv_natCast_pow (by norm_num) (by norm_num)
  have hu' : (C u : ℝ[X])^3 = 9 := by
    rw [← map_pow, hu]
    exact map_natCast (C : ℝ →+* ℝ[X]) 9
  have hv' : (C v : ℝ[X])^3 = 45 := by
    rw [← map_pow, hv]
    exact map_natCast (C : ℝ →+* ℝ[X]) 45
  let s : Fin 3 → ℝ := ![1, -1, 1]
  let g : Fin 3 → ℝ[X] :=
    ![C 1 * (X^6-X^0), C u * (X^5-X^1), C v * (X^4-X^2)]
  have hs : ∀ i, s i = 1 ∨ s i = -1 := by intro i; fin_cases i <;> simp [s]
  have hg : ∀ i, (g i).support.card ≤ 2 := by
    intro i
    fin_cases i <;> apply scaled_binomial_support
  have hsum : (∑ i, C (s i) * (g i)^3) = witness ℝ := by
    simp [Fin.sum_univ_three, s, g, mul_pow, hu', hv', witness]
    ring
  refine ⟨s, g, hs, hg, ?_, ?_⟩
  · intro hz
    have hm := multiplicity_seven ℝ
    rw [← hsum, hz] at hm
    simp at hm
  · rw [hsum, multiplicity_seven]

/-- Two binomial cubes can attain multiplicity five at one. -/
theorem two_cube_multiplicity_five [CharZero R] :
    (((X^4 - 1)^3 + (-2 * X * (X^2 - 1))^3 : R[X]).rootMultiplicity 1) = 5 := by
  let q : R[X] := (X+1)^3 * ((X^2+1)^2 + 2*X*(X^2+1) + 4*X^2)
  have factor : ((X^4-1)^3 + (-2*X*(X^2-1))^3 : R[X]) = q * (X-C 1)^5 := by
    simp only [q, map_one]
    ring
  have hval : q.eval 1 = 96 := by norm_num [q, eval_pow, eval_mul, eval_add]
  have hn : q.eval 1 ≠ 0 := by rw [hval]; norm_num
  have hq : q ≠ 0 := fun h => hn (by rw [h, eval_zero])
  rw [factor, rootMultiplicity_mul_X_sub_C_pow hq, rootMultiplicity_eq_zero hn]

end

end ThreeCubeSharpWitness

#print axioms ThreeCubeSharpWitness.multiplicity_seven
#print axioms ThreeCubeSharpWitness.exists_signed_binomials_seven
#print axioms ThreeCubeSharpWitness.two_cube_multiplicity_five
