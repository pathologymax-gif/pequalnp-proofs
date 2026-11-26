import Mathlib

/-!
Algebraic obstructions for the three-binomial-cubes multiplicity problem.
The moment hypothesis below is the vanishing of monomial tests. Multiplying
by one factor for every foreign exponent isolates any selected block, even
if several exponent slots coincide.
-/

namespace CubeMomentObstructions

section Resultants

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Sylvester resultant of two binary quadratic forms. -/
def quadRes (a b c d e f : R) : R :=
  (a*f-c*d)^2 - (a*e-b*d)*(b*f-c*e)

/-- Either coordinate may vanish. The proof is division-free. -/
theorem quadRes_of_projective_zero (a b c d e f x y : R)
    (hxy : x ≠ 0 ∨ y ≠ 0)
    (hp : a*x^2 + b*x*y + c*y^2 = 0)
    (hq : d*x^2 + e*x*y + f*y^2 = 0) : quadRes a b c d e f = 0 := by
  rcases hxy with hx | hy
  · have h : quadRes a b c d e f * x^3 = 0 := by
      unfold quadRes
      linear_combination ((f*(a*f-c*d)-e*(b*f-c*e))*x-f*(b*f-c*e)*y)*hp +
        ((b*(b*f-c*e)-c*(a*f-c*d))*x+c*(b*f-c*e)*y)*hq
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 3 hx)
  · have h : quadRes a b c d e f * y^3 = 0 := by
      unfold quadRes
      linear_combination ((e*(a*e-b*d)-d*(a*f-c*d))*y+d*(a*e-b*d)*x)*hp +
        ((a*(a*f-c*d)-b*(a*e-b*d))*y-a*(a*e-b*d)*x)*hq
    exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero 3 hy)

/-- The integral quartic used by the exponent-block discriminant test. -/
def cubeDisc (q₀ q₁ q₂ q₃ : R) : R :=
  (q₁*q₂-q₀*q₃)^2 - 4*(q₁^2-q₀*q₂)*(q₂^2-q₁*q₃)

/-- The weights are a normalized binomial cube, tested against Q and zQ.
No condition requires the four values of Q to be distinct or nonzero. -/
theorem cubeDisc_of_two_tests [CharZero R] (q₀ q₁ q₂ q₃ a d t : R)
    (hd : d ≠ 0) (ht : t ≠ 0)
    (h₀ : q₀ + 3*q₁*t + 3*q₂*t^2 + q₃*t^3 = 0)
    (h₁ : a*q₀ + 3*(a+d)*q₁*t + 3*(a+2*d)*q₂*t^2 + (a+3*d)*q₃*t^3 = 0) :
    cubeDisc q₀ q₁ q₂ q₃ = 0 := by
  have hprod : (3*d*t)*(q₁ + 2*q₂*t + q₃*t^2) = 0 := by
    linear_combination h₁ - a*h₀
  have hn : 3*d*t ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hd) ht
  have hder := (mul_eq_zero.mp hprod).resolve_left hn
  have hcut : q₀ + 2*q₁*t + q₂*t^2 = 0 := by linear_combination h₀ - t*hder
  have hr := quadRes_of_projective_zero q₀ (2*q₁) q₂ q₁ (2*q₂) q₃ 1 t
    (Or.inl one_ne_zero) (by simpa using hcut) (by simpa using hder)
  calc cubeDisc q₀ q₁ q₂ q₃ = quadRes q₀ (2*q₁) q₂ q₁ (2*q₂) q₃ := by
         unfold cubeDisc quadRes
         ring
       _ = 0 := hr

end Resultants

section Moments

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- The Euler moment for exponent slots `z` with coefficients `w`. -/
def moment (z w : ι → R) (k : ℕ) : R := ∑ i, w i * (z i)^k

/-- Value at z of the monic test with exactly the listed roots. -/
def foreignTest (roots : List R) (z : R) : R := (roots.map (fun r => z-r)).prod

theorem foreignTest_of_mem {z : R} {roots : List R} (hz : z ∈ roots) :
    foreignTest roots z = 0 := by
  induction roots with
  | nil => simp at hz
  | cons a roots ih =>
    rcases List.mem_cons.mp hz with eq | mem
    · subst a
      simp [foreignTest]
    · change (z-a) * foreignTest roots z = 0
      rw [ih mem, mul_zero]

/-- A list of r linear factors costs r vanishing moments. -/
theorem tested_moment_zero (z w : ι → R) (N : ℕ)
    (h : ∀ j < N, moment z w j = 0) (roots : List R) (k : ℕ)
    (bound : k + roots.length < N) :
    moment z (fun i => w i * foreignTest roots (z i)) k = 0 := by
  classical
  induction roots generalizing k with
  | nil => simpa [foreignTest] using h k (by simpa using bound)
  | cons a roots ih =>
    have h₀ := ih k (by simp at bound; omega)
    have h₁ := ih (k+1) (by simp at bound; omega)
    calc
      moment z (fun i => w i * foreignTest (a :: roots) (z i)) k =
          moment z (fun i => w i * foreignTest roots (z i)) (k+1) -
          a * moment z (fun i => w i * foreignTest roots (z i)) k := by
        unfold moment
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simp only [foreignTest, List.map_cons, List.prod_cons, pow_succ]
        ring
      _ = 0 := by rw [h₀, h₁]; ring

/-- Only slots in `keep` survive if the test lists every foreign exponent.
With eight listed nodes and ten zero moments this applies to both k=0 and k=1. -/
theorem isolated_moment_zero (z w : ι → R) (N : ℕ)
    (h : ∀ j < N, moment z w j = 0) (roots : List R) (keep : Finset ι)
    (covers : ∀ i, i ∉ keep → z i ∈ roots) (k : ℕ) (bound : k + roots.length < N) :
    (∑ i ∈ keep, w i * foreignTest roots (z i) * (z i)^k) = 0 := by
  classical
  calc
    _ = moment z (fun i => w i * foreignTest roots (z i)) k := by
      unfold moment
      refine Finset.sum_subset (Finset.subset_univ keep) ?_
      intro i _ outside
      simp [foreignTest_of_mem (covers i outside)]
    _ = 0 := tested_moment_zero z w N h roots k bound

end Moments

end CubeMomentObstructions

#print axioms CubeMomentObstructions.quadRes_of_projective_zero
#print axioms CubeMomentObstructions.cubeDisc_of_two_tests
#print axioms CubeMomentObstructions.isolated_moment_zero
