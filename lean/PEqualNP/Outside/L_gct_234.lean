import PEqualNP.Defs
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.IntervalCases



namespace PEqualNP.Outside.L_gct_234.Sparse

open Polynomial

theorem signVariations_lt_support (p : Polynomial ℝ) (nonzero : p ≠ 0) :
    p.signVariations < p.support.card := by
  have byCard (n : ℕ) : ∀ (q : Polynomial ℝ), q.support.card = n →
      q ≠ 0 → q.signVariations < q.support.card := by
    induction n with
    | zero =>
      intro q hq hn
      exact (hn (card_support_eq_zero.1 hq)).elim
    | succ n ih =>
      intro q hq hn
      by_cases erased : q.eraseLead = 0
      · have mono := eraseLead_add_monomial_natDegree_leadingCoeff q
        rw [erased, zero_add] at mono
        calc
          q.signVariations = 0 := by rw [← mono, signVariations_monomial]
          _ < q.support.card := hq ▸ Nat.succ_pos n
      · have count : q.eraseLead.support.card = n := by
          have eq := card_support_eraseLead_add_one hn
          omega
        have lower := ih q.eraseLead count erased
        have upper := signVariations_le_eraseLead_succ q
        omega
  exact byCard _ p rfl nonzero

theorem positive_rootMultiplicity_le_signVariations (p : Polynomial ℝ) (x : ℝ) (pos : 0 < x) :
    p.rootMultiplicity x ≤ p.signVariations := by
  classical
  rw [← count_roots p]
  calc
    p.roots.count x = (p.roots.filter (0 < ·)).count x :=
      (Multiset.count_filter_of_pos pos).symm
    _ ≤ (p.roots.filter (0 < ·)).card := Multiset.count_le_card _ _
    _ = p.roots.countP (0 < ·) := (Multiset.countP_eq_card_filter _ _).symm
    _ ≤ p.signVariations := roots_countP_pos_le_signVariations p

theorem positive_rootMultiplicity_lt_support (p : Polynomial ℝ) (nonzero : p ≠ 0)
    (x : ℝ) (pos : 0 < x) : p.rootMultiplicity x < p.support.card :=
  (positive_rootMultiplicity_le_signVariations p x pos).trans_lt
    (signVariations_lt_support p nonzero)

end PEqualNP.Outside.L_gct_234.Sparse
namespace PEqualNP.Outside.L_gct_234.Sparse

open Polynomial

theorem support_rescale (p : Polynomial ℝ) (x : ℝ) (nonzero : x ≠ 0) :
    (p.comp (C x * X)).support = p.support := by
  ext n
  simp [Polynomial.mem_support_iff, nonzero]

theorem rescale_ne_zero (p : Polynomial ℝ) (hp : p ≠ 0) (x : ℝ) (nonzero : x ≠ 0) :
    p.comp (C x * X) ≠ 0 := by
  intro vanishes
  have support := support_rescale p x nonzero
  rw [vanishes, support_zero] at support
  exact hp (support_eq_empty.1 support.symm)

theorem rootMultiplicity_rescale (p : Polynomial ℝ) (x : ℝ) (nonzero : x ≠ 0) :
    (p.comp (C x * X)).rootMultiplicity 1 = p.rootMultiplicity x := by
  simpa using rootMultiplicity_comp_C_mul_X_add_C p x 0 1 (IsUnit.mk0 x nonzero)

theorem signed_cubes_rescale (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ) (x : ℝ) :
    (∑ i, C (s i) * (g i)^3 : Polynomial ℝ).comp (C x * X) =
      ∑ i, C (s i) * ((g i).comp (C x * X))^3 := by
  simp [sum_comp, mul_comp, pow_comp]

theorem bound_from_center (bound :
    ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) →
      (∀ i, (g i).support.card ≤ 2) →
      (∑ i, C (s i) * (g i)^3 : Polynomial ℝ) ≠ 0 →
      (∑ i, C (s i) * (g i)^3 : Polynomial ℝ).rootMultiplicity 1 ≤ 9)
    (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ) (signs : ∀ i, s i = 1 ∨ s i = -1)
    (sparse : ∀ i, (g i).support.card ≤ 2)
    (nonzero : (∑ i, C (s i) * (g i)^3 : Polynomial ℝ) ≠ 0)
    (x : ℝ) (xne : x ≠ 0) :
    (∑ i, C (s i) * (g i)^3 : Polynomial ℝ).rootMultiplicity x ≤ 9 := by
  rw [← rootMultiplicity_rescale _ x xne, signed_cubes_rescale]
  apply bound s (fun i => (g i).comp (C x * X)) signs
  · intro i
    rw [support_rescale (g i) x xne]
    exact sparse i
  · rw [← signed_cubes_rescale]
    exact rescale_ne_zero _ nonzero x xne

end PEqualNP.Outside.L_gct_234.Sparse

namespace PEqualNP.Outside.L_gct_234.Moments

open Polynomial

noncomputable def euler (p : Polynomial ℝ) : Polynomial ℝ := X * p.derivative

@[simp] theorem euler_zero : euler 0 = 0 := by simp [euler]

theorem euler_coeff (p : Polynomial ℝ) (n : ℕ) :
    (euler p).coeff n = (n : ℝ) * p.coeff n := by
  cases n with
  | zero => simp [euler]
  | succ n =>
    rw [euler, coeff_X_mul, coeff_derivative]
    push_cast
    ring

theorem iterate_euler_coeff (k : ℕ) (p : Polynomial ℝ) (n : ℕ) :
    ((euler^[k]) p).coeff n = (n : ℝ)^k * p.coeff n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', euler_coeff, ih, pow_succ]
    ring

theorem eval_iterate_euler_one (k : ℕ) (p : Polynomial ℝ) :
    ((euler^[k]) p).eval 1 = ∑ n ∈ p.support, (n : ℝ)^k * p.coeff n := by
  rw [eval_eq_sum, Polynomial.sum_def]
  simp only [one_pow, mul_one, iterate_euler_coeff]
  apply Finset.sum_subset
  · intro n hn
    rw [mem_support_iff] at hn ⊢
    intro h
    exact hn (by simp [iterate_euler_coeff,h])
  · intro n _ hn
    simpa only [Polynomial.notMem_support_iff, iterate_euler_coeff] using hn

private theorem rootMultiplicity_euler_lower (p : Polynomial ℝ) (nonzero : euler p ≠ 0) :
    p.rootMultiplicity 1 - 1 ≤ (euler p).rootMultiplicity 1 := by
  unfold euler at nonzero ⊢
  rw [rootMultiplicity_mul nonzero]
  exact (rootMultiplicity_sub_one_le_derivative_rootMultiplicity p 1).trans (Nat.le_add_left _ _)

@[simp] private theorem iterate_euler_zero (k : ℕ) : (euler^[k]) 0 = 0 := by
  induction k with
  | zero => rfl
  | succ n h => rw [Function.iterate_succ_apply', h, euler_zero]

theorem eval_iterate_euler_eq_zero (k : ℕ) (p : Polynomial ℝ) (lt : k < p.rootMultiplicity 1) :
    ((euler^[k]) p).eval 1 = 0 := by
  induction k generalizing p with
  | zero =>
    exact (isRoot_iterate_derivative_of_lt_rootMultiplicity lt)
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    by_cases zero : euler p = 0
    · simp [zero]
    · have lower := rootMultiplicity_euler_lower p zero
      exact ih (euler p) (by omega)

theorem moment_zero_of_lt_rootMultiplicity (k : ℕ) (p : Polynomial ℝ)
    (lt : k < p.rootMultiplicity 1) :
    (∑ n ∈ p.support, (n : ℝ)^k * p.coeff n) = 0 := by
  rw [← eval_iterate_euler_one]
  exact eval_iterate_euler_eq_zero k p lt

theorem test_zero_of_lt_rootMultiplicity (p q : Polynomial ℝ)
    (lt : q.natDegree < p.rootMultiplicity 1) :
    (∑ n ∈ p.support, q.eval (n : ℝ) * p.coeff n) = 0 := by
  simp_rw [eval_eq_sum_range, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  simp only [mul_assoc, ← Finset.mul_sum]
  have h := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans_lt lt
  rw [moment_zero_of_lt_rootMultiplicity i p h, mul_zero]

noncomputable def testPolynomial (u : Finset ℕ) : Polynomial ℝ :=
  ∏ n ∈ u, (X - C (n : ℝ))

theorem testPolynomial_degree_le (u : Finset ℕ) :
    (testPolynomial u).natDegree ≤ u.card := by
  unfold testPolynomial
  refine (natDegree_prod_le u _).trans ?_
  simp only [natDegree_X_sub_C]
  simp

theorem testPolynomial_eval (u : Finset ℕ) (i : ℕ) :
    (testPolynomial u).eval (i : ℝ) = ∏ j ∈ u, ((i : ℝ) - (j : ℝ)) := by
  simp [testPolynomial, eval_prod]

theorem core_moment_sum_zero (p : Polynomial ℝ) (u : Finset ℕ)
    (hu : u ⊆ p.support) (hlt : p.support.card - u.card < p.rootMultiplicity 1) :
    (∑ n ∈ u, ((testPolynomial (p.support \ u)).eval (n : ℝ)) * p.coeff n) = 0 := by
  let q := testPolynomial (p.support \ u)
  have hq : q.natDegree < p.rootMultiplicity 1 := by
    exact (testPolynomial_degree_le _).trans_lt (by rwa [Finset.card_sdiff_of_subset hu])
  calc
    _ = ∑ n ∈ p.support, q.eval (n : ℝ) * p.coeff n := by
      apply Finset.sum_subset hu
      intro n hn hn'
      have hnq : n ∈ p.support \ u := Finset.mem_sdiff.mpr ⟨hn, hn'⟩
      change (testPolynomial (p.support \ u)).eval (n : ℝ) * p.coeff n = 0
      rw [testPolynomial_eval, Finset.prod_eq_zero hnq (sub_self _), zero_mul]
    _ = 0 := test_zero_of_lt_rootMultiplicity p q hq

noncomputable def baryWeight (p : Polynomial ℝ) (i : ℕ) : ℝ :=
  p.coeff i * ∏ j ∈ p.support.erase i, ((i : ℝ) - (j : ℝ))

private theorem pair_remove (s : Finset ℕ) (a b : ℕ) (hab : a ≠ b) (hb : b ∈ s) :
    s.erase a = insert b (s \ {a, b}) := by
  ext n
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
  by_cases hna : n = a <;> by_cases hnb : n = b <;> simp_all

private theorem triple_remove (s : Finset ℕ) (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hb : b ∈ s) (hc : c ∈ s) :
    s.erase a = insert b (insert c (s \ {a, b, c})) := by
  ext n
  simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_singleton]
  by_cases hna : n = a <;> by_cases hnb : n = b <;> by_cases hnc : n = c <;> simp_all

private theorem baryWeight_pair (p : Polynomial ℝ) (a b : ℕ) (hab : a ≠ b)
    (hb : b ∈ p.support) :
    baryWeight p a =
      p.coeff a * ((a : ℝ) - (b : ℝ)) * (testPolynomial (p.support \ {a, b})).eval (a : ℝ) := by
  rw [baryWeight, pair_remove _ _ _ hab hb, testPolynomial_eval, Finset.prod_insert]
  · ring
  · simp

private theorem baryWeight_triple (p : Polynomial ℝ) (a b c : ℕ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hb : b ∈ p.support) (hc : c ∈ p.support) :
    baryWeight p a =
      p.coeff a * ((a : ℝ) - (b : ℝ)) * ((a : ℝ) - (c : ℝ)) *
        (testPolynomial (p.support \ {a, b, c})).eval (a : ℝ) := by
  rw [baryWeight, triple_remove _ _ _ _ hab hac hb hc, testPolynomial_eval,
    Finset.prod_insert, Finset.prod_insert]
  · ring
  · simp
  · simp [hbc]

theorem baryWeight_eq_of_succ_card_le (p : Polynomial ℝ)
    (bound : p.support.card ≤ p.rootMultiplicity 1 + 1) (positive : 0 < p.rootMultiplicity 1)
    (a b : ℕ) (ha : a ∈ p.support) (hb : b ∈ p.support) :
    baryWeight p a = baryWeight p b := by
  by_cases same : a = b
  · simp [same]
  have subset : {a, b} ⊆ p.support := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact ha
    · exact hb
  have card : ({a,b} : Finset ℕ).card = 2 := by simp [same]
  have h := core_moment_sum_zero p {a,b} subset (by rw [card]; omega)
  rw [Finset.sum_insert (by simpa using same), Finset.sum_singleton] at h
  rw [baryWeight_pair p a b same hb, baryWeight_pair p b a (fun h => same h.symm) ha,
    show ({b,a}:Finset ℕ) = {a,b} by ext n; simp [or_comm]]
  linear_combination ((a : ℝ) - (b : ℝ)) * h

theorem baryWeight_triple_relation (p : Polynomial ℝ)
    (bound : p.support.card ≤ p.rootMultiplicity 1 + 2) (positive : 0 < p.rootMultiplicity 1)
    (a b c : ℕ) (ha : a ∈ p.support) (hb : b ∈ p.support) (hc : c ∈ p.support)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    baryWeight p a * ((b : ℝ) - (c : ℝ)) +
      baryWeight p b * ((c : ℝ) - (a : ℝ)) +
      baryWeight p c * ((a : ℝ) - (b : ℝ)) = 0 := by
  have subset : {a, b, c} ⊆ p.support := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have card : ({a,b,c} : Finset ℕ).card = 3 := by simp [hab, hac, hbc]
  have h := core_moment_sum_zero p {a,b,c} subset (by rw [card]; omega)
  rw [Finset.sum_insert (by simp [hab,hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton] at h
  rw [baryWeight_triple p a b c hab hac hbc hb hc,
    baryWeight_triple p b c a hbc hab.symm hac.symm hc ha,
    baryWeight_triple p c a b hac.symm hbc.symm hab ha hb,
    show ({b,c,a}:Finset ℕ) = {a,b,c} by ext n; simp [or_left_comm,or_comm],
    show ({c,a,b}:Finset ℕ) = {a,b,c} by ext n; simp [or_left_comm,or_comm]]
  linear_combination ((a : ℝ) - (b : ℝ)) * ((a : ℝ) - (c : ℝ)) * ((b : ℝ) - (c : ℝ)) * h

theorem exists_affine_baryWeight (p : Polynomial ℝ)
    (bound : p.support.card ≤ p.rootMultiplicity 1 + 2) (positive : 0 < p.rootMultiplicity 1)
    (two : 1 < p.support.card) :
    ∃ A B : ℝ, ∀ n ∈ p.support, baryWeight p n = A * (n : ℝ) + B := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 two
  have denom : (a : ℝ) - (b : ℝ) ≠ 0 := by exact sub_ne_zero.mpr (by exact_mod_cast hab)
  refine ⟨(baryWeight p a - baryWeight p b) / ((a : ℝ) - (b : ℝ)),
    baryWeight p b - (baryWeight p a - baryWeight p b) / ((a : ℝ) - (b : ℝ)) * (b : ℝ), ?_⟩
  intro c hc
  by_cases hac : a = c
  · subst c
    field_simp
    ring
  by_cases hbc : b = c
  · subst c
    ring
  have h := baryWeight_triple_relation p bound positive a b c ha hb hc hab hac hbc
  field_simp
  linear_combination h

end PEqualNP.Outside.L_gct_234.Moments

namespace PEqualNP.Outside.L_gct_234.CubeAP

open Polynomial

theorem exists_binomial_form (p : Polynomial ℝ) (h : p.support.card ≤ 2) :
    ∃ (a b : ℝ) (m d : ℕ), p = C a * X ^ m + C b * X ^ (m + d) := by
  have hp := p.as_sum_support_C_mul_X_pow
  rcases Nat.eq_zero_or_pos p.support.card with card | card
  · rw [Finset.card_eq_zero.mp card, Finset.sum_empty] at hp
    exact ⟨0,0,0,0, by simp [hp]⟩
  by_cases one : p.support.card = 1
  · obtain ⟨m, hm⟩ := Finset.card_eq_one.1 one
    rw [hm, Finset.sum_singleton] at hp
    exact ⟨p.coeff m,0, m,0, by simpa using hp⟩
  obtain ⟨m, n, neq, support⟩ := Finset.card_eq_two.1 (by omega : p.support.card = 2)
  rw [support, Finset.sum_insert (by simpa using neq), Finset.sum_singleton] at hp
  by_cases le : m ≤ n
  · exact ⟨p.coeff m, p.coeff n, m, n - m, by rwa [Nat.add_sub_of_le le]⟩
  · have le' : n ≤ m := by omega
    exact ⟨p.coeff n, p.coeff m, n, m - n, by rwa [Nat.add_sub_of_le le', add_comm]⟩

def exp (m d : ℕ) (j : Fin 4) : ℕ := 3 * m + j.val * d

noncomputable def ampl (s a b : ℝ) (j : Fin 4) : ℝ :=
  ![s * a ^ 3,3 * s * a ^ 2 * b,3 * s * a * b ^ 2, s * b ^ 3] j

theorem expand_signed_cube (s a b : ℝ) (m d : ℕ) :
    C s * (C a * X ^ m + C b * X ^ (m+d)) ^ 3 =
      ∑ j : Fin 4, C (ampl s a b j) * X ^ exp m d j := by
  rw [Fin.sum_univ_four]
  change _ = C (s*a^3) * X ^ exp m d 0 +
    C (3*s*a^2*b) * X ^ exp m d 1 +
    C (3*s*a*b^2) * X ^ exp m d 2 +
    C (s*b^3) * X ^ exp m d 3
  have h0 : exp m d 0 = 3*m := by simp [exp]
  have h1 : exp m d 1 = 3*m+d := by simp [exp]
  have h2 : exp m d 2 = 3*m+d*2 := by simp [exp, Nat.mul_comm]
  have h3 : exp m d 3 = 3*m+d*3 := by simp [exp, Nat.mul_comm]
  simp only [h0,h1,h2,h3, Nat.mul_comm 3 m, pow_add, pow_mul, map_mul, map_pow, map_ofNat]
  ring

theorem coeff_expand_signed_cube (s a b : ℝ) (m d n : ℕ) :
    (C s * (C a * X ^ m + C b * X ^ (m+d)) ^ 3).coeff n =
      ∑ j : Fin 4, if exp m d j = n then ampl s a b j else 0 := by
  rw [expand_signed_cube, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  rw [coeff_C_mul_X_pow]
  by_cases h : exp m d j = n
  · simp [h]
  · rw [ite_eq_right h, ite_eq_right (fun eq => h eq.symm)]

theorem exp_injective (m d : ℕ) (hd : 0 < d) : Function.Injective (exp m d) := by
  intro j k h
  apply Fin.ext
  exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)

def exponents (m d : Fin 3 → ℕ) (i : Fin 3 × Fin 4) : ℕ :=
  exp (m i.1) (d i.1) i.2

noncomputable def amplitudes (s a b : Fin 3 → ℝ) (i : Fin 3 × Fin 4) : ℝ :=
  ampl (s i.1) (a i.1) (b i.1) i.2

noncomputable def sumCubes (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ) : Polynomial ℝ :=
  ∑ i : Fin 3, C (s i) * (g i) ^ 3

theorem coeff_sumCubes_eq (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ) (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i)) (n : ℕ) :
    (sumCubes s g).coeff n =
      ∑ i : Fin 3 × Fin 4, if exponents m d i = n then amplitudes s a b i else 0 := by
  simp_rw [sumCubes, hg, finsetSum_coeff, coeff_expand_signed_cube]
  rw [Fintype.sum_prod_type]
  rfl

theorem subset_exponents (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ) (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i)) :
    (sumCubes s g).support ⊆ Finset.univ.image (exponents m d) := by
  intro n hn
  by_contra h
  have eq : ∀ i, exponents m d i ≠ n := by
    intro i he
    exact h (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩)
  apply (mem_support_iff.mp hn)
  simp [coeff_sumCubes_eq s a b g m d hg, eq]

theorem sumCube_support_le_twelve (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ)
    (hg : ∀ i, (g i).support.card ≤ 2) : (sumCubes s g).support.card ≤ 12 := by
  choose a b m d h using fun i => exists_binomial_form (g i) (hg i)
  exact (Finset.card_le_card (subset_exponents s a b g m d h)).trans
    (Finset.card_image_le.trans (by simp))

theorem coefficient_of_unique_exponent (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ)
    (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i))
    (i : Fin 3 × Fin 4) (hi : ∀ j, exponents m d j = exponents m d i → j = i) :
    (sumCubes s g).coeff (exponents m d i) = amplitudes s a b i := by
  rw [coeff_sumCubes_eq s a b g m d hg]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ neq
    rw [ite_eq_right (fun h => neq (hi j h))]
  · simp

theorem injective_except_collision (m d : Fin 3 → ℕ)
    (large : 11 ≤ (Finset.univ.image (exponents m d)).card)
    (i j : Fin 3 × Fin 4) (hij : i ≠ j) (same : exponents m d i = exponents m d j) :
    Set.InjOn (exponents m d) {k | k ≠ j} := by
  let u : Finset (Fin 3 × Fin 4) := Finset.univ.erase j
  have image : u.image (exponents m d) = Finset.univ.image (exponents m d) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_univ, true_and, u, Finset.mem_erase, and_true]
    constructor
    · rintro ⟨k, _, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      by_cases eq : k = j
      · subst k
        exact ⟨i, hij, same⟩
      · exact ⟨k, eq, rfl⟩
  have size : u.card = 11 := by simp [u]
  have card : (u.image (exponents m d)).card = u.card := by
    apply le_antisymm Finset.card_image_le
    rw [size, image]
    exact large
  have inj := Finset.card_image_iff.mp card
  intro x hx y hy hxy
  exact inj (by simpa [u] using hx) (by simpa [u] using hy) hxy

theorem subset_nonzero_exponents (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ)
    (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i)) :
    (sumCubes s g).support ⊆
      (Finset.univ.filter fun i => amplitudes s a b i ≠ 0).image (exponents m d) := by
  classical
  intro n hn
  by_contra h
  apply (mem_support_iff.mp hn)
  rw [coeff_sumCubes_eq s a b g m d hg]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with eq
  · by_contra hi
    exact h (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, eq⟩)
  · rfl

private theorem no_two_zero_amplitudes (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ)
    (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i))
    (large : 11 ≤ (sumCubes s g).support.card)
    (i j : Fin 3 × Fin 4) (hij : i ≠ j) (hi : amplitudes s a b i = 0)
    (hj : amplitudes s a b j = 0) : False := by
  classical
  let u : Finset (Fin 3 × Fin 4) := Finset.univ.filter fun i => amplitudes s a b i ≠ 0
  let v : Finset (Fin 3 × Fin 4) := (Finset.univ.erase i).erase j
  have sub : u ⊆ v := by
    intro k hk
    have ne : amplitudes s a b k ≠ 0 := (Finset.mem_filter.mp hk).2
    simp only [v, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · rintro rfl
      exact ne hj
    · rintro rfl
      exact ne hi
  have card : v.card = 10 := by
    simp [v, Finset.card_erase_of_mem, Finset.mem_erase, hij.symm]
  have bound := Finset.card_le_card (subset_nonzero_exponents s a b g m d hg)
  change (sumCubes s g).support.card ≤ (u.image (exponents m d)).card at bound
  have := ((large.trans bound).trans Finset.card_image_le).trans (Finset.card_le_card sub)
  omega

theorem nondegenerate_of_large (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ)
    (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i))
    (large : 11 ≤ (sumCubes s g).support.card) (i : Fin 3) :
    0 < d i ∧ a i ≠ 0 ∧ b i ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra h
    have zero : d i = 0 := by omega
    have image_size := large.trans (Finset.card_le_card (subset_exponents s a b g m d hg))
    have inj := injective_except_collision m d image_size (i,0) (i,1) (by simp)
      (by simp [exponents, exp, zero])
    have h02 : (i, (0 : Fin 4)) = (i, (2 : Fin 4)) :=
      inj (by simp) (by simp) (by simp [exponents, exp, zero])
    exact (by decide : (0 : Fin 4) ≠ 2) (congrArg Prod.snd h02)
  · intro zero
    apply no_two_zero_amplitudes s a b g m d hg large (i,0) (i,1)
    · simp
    · simp [amplitudes, ampl, zero]
    · simp [amplitudes, ampl, zero]
  · intro zero
    apply no_two_zero_amplitudes s a b g m d hg large (i,2) (i,3)
    · simp
    · simp [amplitudes, ampl, zero]
    · simp [amplitudes, ampl, zero]

theorem support_eq_exponents_of_large (s a b : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ)
    (m d : Fin 3 → ℕ)
    (hg : ∀ i, g i = C (a i) * X ^ (m i) + C (b i) * X ^ (m i+d i))
    (hs : ∀ i, s i ≠ 0) (large : 11 ≤ (sumCubes s g).support.card) :
    (sumCubes s g).support = Finset.univ.image (exponents m d) := by
  have sub := subset_exponents s a b g m d hg
  have image_le : (Finset.univ.image (exponents m d)).card ≤ 12 :=
    Finset.card_image_le.trans (by simp)
  rcases (by omega : (Finset.univ.image (exponents m d)).card ≤ 11 ∨
      (Finset.univ.image (exponents m d)).card = 12) with small | twelve
  · exact Finset.eq_of_subset_of_card_le sub (small.trans large)
  have inj := Finset.card_image_iff.mp (by simpa using twelve :
      (Finset.univ.image (exponents m d)).card = (Finset.univ : Finset (Fin 3 × Fin 4)).card)
  apply Finset.Subset.antisymm sub
  intro n hn
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hn
  rw [mem_support_iff, coefficient_of_unique_exponent s a b g m d hg i]
  · obtain ⟨i, j⟩ := i
    have ⟨_, ha, hb⟩ := nondegenerate_of_large s a b g m d hg large i
    have hsign := hs i
    fin_cases j <;> simp [amplitudes, ampl, ha, hb, hsign]
  · intro j hj
    exact inj (Finset.mem_univ _) (Finset.mem_univ _) hj

end PEqualNP.Outside.L_gct_234.CubeAP

namespace PEqualNP.Outside.L_gct_234

open Polynomial

noncomputable def tableNumerator (s a b : Fin 3 → ℝ) (m d : Fin 3 → ℕ) (n : ℕ) : ℝ :=
  (∑ k : Fin 3 × Fin 4, if CubeAP.exponents m d k = n then CubeAP.amplitudes s a b k else 0) *
    ∏ y ∈ (Finset.univ.image (CubeAP.exponents m d)).erase n, ((n : ℝ) - (y : ℝ))

theorem bound_of_table_obstruction (obstruction :
    ∀ (s a b : Fin 3 → ℝ) (m d : Fin 3 → ℕ),
      (∀ i, s i = 1 ∨ s i = -1) → (∀ i,0 < d i ∧ a i ≠ 0 ∧ b i ≠ 0) →
      let u := Finset.univ.image (CubeAP.exponents m d)
      11 ≤ u.card →
      ∀ A B : ℝ, (u.card = 11 → A = 0) →
        (∀ n ∈ u, tableNumerator s a b m d n = A * (n : ℝ) + B) → False)
    (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ) (signs : ∀ i, s i = 1 ∨ s i = -1)
    (sparse : ∀ i, (g i).support.card ≤ 2)
    (nonzero : (∑ i, C (s i) * (g i)^3 : Polynomial ℝ) ≠ 0)
    (x : ℝ) (pos : 0 < x) :
    (∑ i, C (s i) * (g i)^3 : Polynomial ℝ).rootMultiplicity x ≤ 9 := by
  refine Sparse.bound_from_center ?_ s g signs sparse nonzero x (ne_of_gt pos)
  intro signs' g' hsigns hsparse hnonzero
  let p := CubeAP.sumCubes signs' g'
  change p.rootMultiplicity 1 ≤ 9
  by_contra hbound
  have lower := Sparse.positive_rootMultiplicity_lt_support p hnonzero 1 (by norm_num)
  have large : 11 ≤ p.support.card := by omega
  have pos : 0 < p.rootMultiplicity 1 := by omega
  choose a b m d form using fun i => CubeAP.exists_binomial_form (g' i) (hsparse i)
  have hsn : ∀ i, signs' i ≠ 0 := by
    intro i
    rcases hsigns i with h | h <;> rw [h] <;> norm_num
  have hs := CubeAP.support_eq_exponents_of_large signs' a b g' m d form hsn large
  change p.support = _ at hs
  let u := Finset.univ.image (CubeAP.exponents m d)
  change p.support = u at hs
  have hlarge : 11 ≤ u.card := hs ▸ large
  have hsmall : u.card ≤ 12 := hs ▸ CubeAP.sumCube_support_le_twelve signs' g' hsparse
  have bary (n : ℕ) : Moments.baryWeight p n = tableNumerator signs' a b m d n := by
    rw [Moments.baryWeight, hs, tableNumerator]
    rw [show p.coeff n = _ from CubeAP.coeff_sumCubes_eq signs' a b g' m d form n]
  have nd := CubeAP.nondegenerate_of_large signs' a b g' m d form large
  by_cases eleven : u.card = 11
  · obtain ⟨z, hz⟩ := Finset.card_pos.mp (show 0 < u.card by omega)
    refine obstruction signs' a b m d hsigns nd hlarge 0 (Moments.baryWeight p z)
      (fun _ => rfl) ?_
    intro n hn
    rw [← bary, zero_mul, zero_add]
    apply Moments.baryWeight_eq_of_succ_card_le p (by rw [hs]; omega) pos
    · simpa only [hs] using hn
    · simpa only [hs] using hz
  · obtain ⟨A, B, h⟩ := Moments.exists_affine_baryWeight p (by rw [hs]; omega) pos
      (by rw [hs]; omega)
    refine obstruction signs' a b m d hsigns nd hlarge A B (fun h => (eleven h).elim) ?_
    intro n hn
    rw [← bary]
    exact h n (by simpa only [hs] using hn)

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
namespace LocalFactor

open CubeAP

noncomputable def factorialFactor (j : Fin 4) : ℝ := ![-6,2, -2,6] j

private theorem internal_product (m d : ℕ) (j : Fin 4) :
    (∏ k ∈ (Finset.univ.erase j : Finset (Fin 4)), ((exp m d j : ℝ) - (exp m d k : ℝ))) =
      factorialFactor j * (d : ℝ)^3 := by
  have diff (k : Fin 4) : (exp m d j : ℝ) - (exp m d k : ℝ) =
      ((j.val : ℝ) - (k.val : ℝ)) * (d : ℝ) := by
    unfold exp
    push_cast
    ring
  simp_rw [diff]
  rw [Finset.prod_mul_distrib, Finset.prod_const, show (Finset.univ.erase j).card = 3 by simp]
  congr 1
  have removed : (Finset.univ.erase j : Finset (Fin 4)) =
      Finset.univ.filter (· ≠ j) := by ext k; simp
  rw [removed, Finset.prod_filter, Fin.prod_univ_four]
  fin_cases j <;> norm_num [factorialFactor]

noncomputable def outerProduct (m d : Fin 3 → ℕ) (i : Fin 3) (j : Fin 4) : ℚ :=
  ∏ y ∈ (Finset.univ.image (exponents m d)) \ (Finset.univ.image (exp (m i) (d i))),
    ((exp (m i) (d i) j : ℚ) - (y : ℚ))

theorem split_vandermonde_product (m d : Fin 3 → ℕ) (i : Fin 3) (j : Fin 4)
    (hd : 0 < d i) :
    let n := exponents m d (i, j)
    (∏ y ∈ (Finset.univ.image (exponents m d)).erase n, ((n : ℝ) - (y : ℝ))) =
      factorialFactor j * (d i : ℝ)^3 * (outerProduct m d i j : ℝ) := by
  let E := exp (m i) (d i)
  let n := E j
  let U := Finset.univ.image (exponents m d)
  let V := Finset.univ.image E
  have sub : V ⊆ U := by
    intro y hy
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_univ _, rfl⟩
  have hn : n ∈ V := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have split : U.erase n = V.erase n ∪ (U \ V) := by
    ext y
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
    by_cases h : y = n
    · subst y
      simp [hn]
    by_cases hV : y ∈ V
    · simp [h, hV, sub hV]
    · simp [h, hV]
  have disj : Disjoint (V.erase n) (U \ V) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2 (Finset.mem_of_mem_erase hx)
  have V' : V.erase n = (Finset.univ.erase j).image E := by
    ext y
    simp only [V, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and, and_true]
    constructor
    · rintro ⟨hne, k, rfl⟩
      exact ⟨k, fun hk => hne (congrArg E hk), rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨fun he => hk (exp_injective (m i) (d i) hd he), k, rfl⟩
  change (∏ y ∈ U.erase n, ((n : ℝ) - (y : ℝ))) =
      factorialFactor j * (d i : ℝ)^3 * (outerProduct m d i j : ℝ)
  rw [split, Finset.prod_union disj, V', Finset.prod_image (exp_injective (m i) (d i) hd).injOn]
  change (∏ k ∈ (Finset.univ.erase j : Finset (Fin 4)), ((exp (m i) (d i) j : ℝ) -
      (exp (m i) (d i) k : ℝ))) * _ = _
  rw [internal_product]
  congr 1
  unfold outerProduct
  push_cast
  rfl

theorem internal_weight (s a b : ℝ) (d : ℕ) (j : Fin 4) (ha : a ≠ 0) :
    ampl s a b j * (factorialFactor j * (d : ℝ)^3) =
      (-6*s*a^3*(d : ℝ)^3) * (-b/a)^j.val := by
  fin_cases j
  · change (s*a^3)*(-6*(d : ℝ)^3) = (-6*s*a^3*(d : ℝ)^3)*(-b/a)^0
    ring
  · change (3*s*a^2*b)*(2*(d : ℝ)^3) = (-6*s*a^3*(d : ℝ)^3)*(-b/a)^1
    field_simp
    ring
  · change (3*s*a*b^2)*(-2*(d : ℝ)^3) = (-6*s*a^3*(d : ℝ)^3)*(-b/a)^2
    field_simp
    ring
  · change (s*b^3)*(6*(d : ℝ)^3) = (-6*s*a^3*(d : ℝ)^3)*(-b/a)^3
    field_simp

theorem weighted_table_geometric (s a b : Fin 3 → ℝ) (m d : Fin 3 → ℕ)
    (i : Fin 3) (j : Fin 4) (hd : 0 < d i) (ha : a i ≠ 0) (θ : ℝ)
    (hθ : θ * (∑ k : Fin 3 × Fin 4,
      if exponents m d k = exponents m d (i,j) then amplitudes s a b k else 0) =
        amplitudes s a b (i,j)) :
    θ * tableNumerator s a b m d (exponents m d (i,j)) =
      (-6*s i*(a i)^3*(d i : ℝ)^3) * (-b i/a i)^j.val * (outerProduct m d i j : ℝ) := by
  unfold tableNumerator
  rw [← mul_assoc, hθ, split_vandermonde_product m d i j hd, ← mul_assoc]
  change (ampl (s i) (a i) (b i) j * (factorialFactor j * (d i : ℝ)^3)) *
    (outerProduct m d i j : ℝ) = _
  rw [internal_weight _ _ _ _ _ ha]

end LocalFactor
end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.RationalCoordinates

theorem ratio_is_rational (u₀ u₁ u₂ u₃ : ℚ) (h₂ : u₂ ≠ 0) (h₃ : u₃ ≠ 0)
    (t : ℝ)
    (q₀ : (u₀ : ℝ) - 2*u₁*t + u₂*t^2 = 0)
    (q₁ : (u₁ : ℝ) - 2*u₂*t + u₃*t^2 = 0) :
    ∃ q : ℚ, t = (q : ℝ) := by
  let A : ℚ := 2*(u₂^2-u₁*u₃)
  let B : ℚ := u₁*u₂-u₀*u₃
  have elim : (A : ℝ) * t = B := by
    dsimp [A, B]
    push_cast
    linear_combination (u₃ : ℝ)*q₀ - (u₂ : ℝ)*q₁
  by_cases zero : A = 0
  · have ra : (u₂ : ℝ)^2 - (u₁ : ℝ)*u₃ = 0 := by
      have h : (A : ℝ) = 0 := by simp [zero]
      dsimp [A] at h
      push_cast at h
      linear_combination h/2
    have rb : (u₁ : ℝ)*u₂ - (u₀ : ℝ)*u₃ = 0 := by
      rw [zero, Rat.cast_zero, zero_mul] at elim
      dsimp [B] at elim
      push_cast at elim
      exact elim.symm
    have rd : (u₀ : ℝ)*u₂ - (u₁ : ℝ)^2 = 0 := by
      have mul : (u₃ : ℝ)*((u₀ : ℝ)*u₂ - (u₁ : ℝ)^2) = 0 := by
        linear_combination (u₁ : ℝ)*ra - (u₂ : ℝ)*rb
      exact (mul_eq_zero.mp mul).resolve_left (by exact_mod_cast h₃)
    have sq : ((u₂ : ℝ)*t - u₁)^2 = 0 := by linear_combination (u₂ : ℝ)*q₀ - rd
    have rt : (u₂ : ℝ)*t - u₁ = 0 := by
      by_contra ne
      exact pow_ne_zero 2 ne sq
    refine ⟨u₁/u₂, ?_⟩
    push_cast
    apply (eq_div_iff (by exact_mod_cast h₂ : (u₂ : ℝ) ≠ 0)).mpr
    linear_combination rt
  · refine ⟨B/A, ?_⟩
    push_cast
    exact (eq_div_iff (by exact_mod_cast zero : (A : ℝ) ≠ 0)).mpr (by simpa [mul_comm] using elim)

theorem affine_pole_is_rational (x d u₀ u₁ u₂ u₃ : ℚ)
    (hd : d ≠ 0) (hu₀ : u₀ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (r t : ℝ) (hr : (x : ℝ) ≠ r) (ht : t ≠ 0)
    (step₁ : ((x : ℝ) + d - r)*u₀ = ((x : ℝ)-r)*u₁*t)
    (step₂ : ((x : ℝ) + 2*d - r)*u₀ = ((x : ℝ)-r)*u₂*t^2)
    (step₃ : ((x : ℝ) + 3*d - r)*u₀ = ((x : ℝ)-r)*u₃*t^3) :
    ∃ q : ℚ, r = (q : ℝ) := by
  have q₀ : (u₀ : ℝ) - 2*u₁*t + u₂*t^2 = 0 := by
    have prod : ((x : ℝ)-r) * ((u₀ : ℝ) - 2*u₁*t + u₂*t^2) = 0 := by
      linear_combination 2*step₁ - step₂
    exact (mul_eq_zero.mp prod).resolve_left (sub_ne_zero.mpr hr)
  have q₁ : (u₁ : ℝ) - 2*u₂*t + u₃*t^2 = 0 := by
    have prod : (((x : ℝ)-r)*t) * ((u₁ : ℝ) - 2*u₂*t + u₃*t^2) = 0 := by
      linear_combination 2*step₂ - step₁ - step₃
    exact (mul_eq_zero.mp prod).resolve_left (mul_ne_zero (sub_ne_zero.mpr hr) ht)
  obtain ⟨τ, hτ⟩ := ratio_is_rational u₀ u₁ u₂ u₃ hu₂ hu₃ t q₀ q₁
  let q : ℚ := u₁*τ/u₀
  have re₀ : (u₀ : ℝ) ≠ 0 := by exact_mod_cast hu₀
  have hscale : (q : ℝ)*u₀ = (u₁ : ℝ)*t := by
    dsimp [q]
    push_cast
    rw [hτ, div_mul_cancel₀ _ re₀]
  have equation : (x : ℝ) + d - r = (q : ℝ)*((x : ℝ)-r) := by
    have mul : (u₀ : ℝ) * ((x : ℝ) + d - r - (q : ℝ)*((x : ℝ)-r)) = 0 := by
      linear_combination step₁ - ((x : ℝ)-r)*hscale
    exact sub_eq_zero.mp ((mul_eq_zero.mp mul).resolve_left re₀)
  have ne : (q : ℝ) - 1 ≠ 0 := by
    intro zero
    have one : (q : ℝ) = 1 := by linear_combination zero
    rw [one, one_mul] at equation
    exact (by exact_mod_cast hd : (d : ℝ) ≠ 0) (by linear_combination equation)
  refine ⟨(q*x-x-d)/(q-1), ?_⟩
  push_cast
  apply (eq_div_iff ne).mpr
  linear_combination equation

private theorem ratio_of_rational_values (u v t : ℝ) (hu : u ≠ 0) (step : v = u*t)
    (a b : ℚ) (ha : u = (a : ℝ)) (hb : v = (b : ℝ)) :
    ∃ q : ℚ, t = (q : ℝ) := by
  refine ⟨b/a, ?_⟩
  push_cast
  apply (eq_div_iff (by rwa [← ha] : (a : ℝ) ≠ 0)).mpr
  rw [← ha, ← hb, step, mul_comm]

theorem geometric_missing_value_is_rational (u : Fin 4 → ℝ) (t : ℝ)
    (ht : t ≠ 0) (nonzero : ∀ j, u j ≠ 0)
    (step₀ : u 1 = u 0*t) (step₁ : u 2 = u 1*t) (step₂ : u 3 = u 2*t)
    (missing : Fin 4) (values : ∀ j, j ≠ missing → ∃ q : ℚ, u j = (q : ℝ)) :
    ∃ q : ℚ, u missing = (q : ℝ) := by
  have ratio : ∃ q : ℚ, t = (q : ℝ) := by
    by_cases at₀ : missing = 0
    · subst missing
      obtain ⟨a, ha⟩ := values 1 (by decide)
      obtain ⟨b, hb⟩ := values 2 (by decide)
      exact ratio_of_rational_values _ _ _ (nonzero 1) step₁ a b ha hb
    by_cases at₁ : missing = 1
    · subst missing
      obtain ⟨a, ha⟩ := values 2 (by decide)
      obtain ⟨b, hb⟩ := values 3 (by decide)
      exact ratio_of_rational_values _ _ _ (nonzero 2) step₂ a b ha hb
    obtain ⟨a, ha⟩ := values 0 (fun h => at₀ h.symm)
    obtain ⟨b, hb⟩ := values 1 (fun h => at₁ h.symm)
    exact ratio_of_rational_values _ _ _ (nonzero 0) step₀ a b ha hb
  obtain ⟨q, hq⟩ := ratio
  have first : ∃ a : ℚ, u 0 = (a : ℝ) := by
    by_cases at₀ : missing = 0
    · subst missing
      obtain ⟨b, hb⟩ := values 1 (by decide)
      refine ⟨b/q, ?_⟩
      push_cast
      exact (eq_div_iff (by rwa [← hq] : (q : ℝ) ≠ 0)).mpr (by rw [← hq, ← hb, step₀])
    exact values 0 (fun h => at₀ h.symm)
  obtain ⟨a, ha⟩ := first
  have h₁ : u 1 = ((a*q : ℚ) : ℝ) := by rw [step₀, ha, hq]; push_cast; rfl
  have h₂ : u 2 = ((a*q*q : ℚ) : ℝ) := by rw [step₁, h₁, hq]; push_cast; rfl
  have h₃ : u 3 = ((a*q*q*q : ℚ) : ℝ) := by rw [step₂, h₂, hq]; push_cast; rfl
  fin_cases missing
  · exact ⟨a, ha⟩
  · exact ⟨a*q, h₁⟩
  · exact ⟨a*q*q, h₂⟩
  · exact ⟨a*q*q*q, h₃⟩

end PEqualNP.Outside.L_gct_234.RationalCoordinates

namespace PEqualNP.Outside.L_gct_234.TableGeometry

open CubeAP LocalFactor

noncomputable def linearValue {K : Type*} [Field K] (root : Option ℚ) (n : ℕ) : K :=
  match root with
  | none => 1
  | some r => (n : K) - (r : K)

private noncomputable def coeffAt (s a b : Fin 3 → ℝ) (m d : Fin 3 → ℕ) (n : ℕ) : ℝ :=
  ∑ k : Fin 3 × Fin 4, if exponents m d k = n then amplitudes s a b k else 0

private def Single (m d : Fin 3 → ℕ) (i : Fin 3 × Fin 4) : Prop :=
  ∀ j, exponents m d j = exponents m d i → j = i

private theorem coeffAt_single (s a b : Fin 3 → ℝ) (m d : Fin 3 → ℕ) (i : Fin 3 × Fin 4)
    (h : Single m d i) : coeffAt s a b m d (exponents m d i) = amplitudes s a b i := by
  unfold coeffAt
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    rw [ite_eq_right (fun he => hji (h j he))]
  · simp

private theorem single_of_injective (m d : Fin 3 → ℕ)
    (h : Function.Injective (exponents m d)) (i : Fin 3 × Fin 4) : Single m d i :=
  fun _ he => h he

private theorem single_other (m d : Fin 3 → ℕ)
    (large : 11 ≤ (Finset.univ.image (exponents m d)).card)
    {i j k : Fin 3 × Fin 4} (hij : i ≠ j) (same : exponents m d i = exponents m d j)
    (hki : k ≠ i) (hkj : k ≠ j) : Single m d k := by
  have inj := injective_except_collision m d large i j hij same
  intro r h
  by_cases hr : r = j
  · subst r
    exact (hki (inj (by exact hkj) (by exact hij) (h.symm.trans same.symm))).elim
  · exact inj (by exact hr) (by exact hkj) h

private theorem exists_single (m d : Fin 3 → ℕ)
    (large : 11 ≤ (Finset.univ.image (exponents m d)).card) :
    ∃ i, Single m d i := by
  classical
  by_cases injective : Function.Injective (exponents m d)
  · exact ⟨(0,0), single_of_injective m d injective _⟩
  unfold Function.Injective at injective
  push Not at injective
  obtain ⟨i,j,same,hij⟩ := injective
  let u : Finset (Fin 3 × Fin 4) := (Finset.univ.erase i).erase j
  have size : u.card = 10 := by simp [u, Finset.card_erase_of_mem, Finset.mem_erase, hij.symm]
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < u.card)
  have hki := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
  have hkj := Finset.ne_of_mem_erase hk
  exact ⟨k, single_other m d large hij same hki hkj⟩

private theorem outerProduct_ne_zero (m d : Fin 3 → ℕ) (i : Fin 3) (j : Fin 4) :
    outerProduct m d i j ≠ 0 := by
  classical
  unfold outerProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro n hn
  have nf := (Finset.mem_sdiff.mp hn).2
  intro h
  have eq : exp (m i) (d i) j = n := by exact_mod_cast sub_eq_zero.mp h
  exact nf (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, eq⟩)

private theorem denominator_ne_zero (m d : Fin 3 → ℕ) (n : ℕ) :
    (∏ y ∈ (Finset.univ.image (exponents m d)).erase n, ((n : ℝ) - (y : ℝ))) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  exact sub_ne_zero.mpr (by exact_mod_cast (Finset.ne_of_mem_erase hy).symm)

private theorem amplitude_ne_zero (s a b : Fin 3 → ℝ)
    (hs : ∀ i, s i ≠ 0) (ha : ∀ i, a i ≠ 0) (hb : ∀ i, b i ≠ 0) (i : Fin 3 × Fin 4) :
    amplitudes s a b i ≠ 0 := by
  obtain ⟨i,j⟩ := i
  fin_cases j <;> simp [amplitudes, ampl, hs i, ha i, hb i]

private theorem affine_pole_of_four_values (x d : ℚ) (R : Fin 4 → ℚ)
    (hd : d ≠ 0) (hR : ∀ j, R j ≠ 0) (r C t : ℝ) (hr : (x : ℝ) ≠ r) (ht : t ≠ 0)
    (g : ∀ j : Fin 4, (x : ℝ) + (j.val : ℝ)*(d : ℝ) - r = C*t^j.val*(R j : ℝ)) :
    ∃ q : ℚ, r = (q : ℝ) := by
  have h₀ : (x : ℝ)-r = C*(R 0 : ℝ) := by simpa using g 0
  have h₁ : ((x : ℝ)+d-r) = C*t*(R 1 : ℝ) := by simpa using g 1
  have h₂ : ((x : ℝ)+2*d-r) = C*t^2*(R 2 : ℝ) := g 2
  have h₃ : ((x : ℝ)+3*d-r) = C*t^3*(R 3 : ℝ) := g 3
  apply RationalCoordinates.affine_pole_is_rational x d (R 0) (R 1) (R 2) (R 3)
    hd (hR 0) (hR 2) (hR 3) r t hr ht
  · linear_combination (R 0 : ℝ)*h₁ - (R 1 : ℝ)*t*h₀
  · linear_combination (R 0 : ℝ)*h₂ - (R 2 : ℝ)*t^2*h₀
  · linear_combination (R 0 : ℝ)*h₃ - (R 3 : ℝ)*t^3*h₀

structure RationalTable (m d : Fin 3 → ℕ) where
  root : Option ℚ
  share : Fin 3 × Fin 4 → ℚ
  scale : Fin 3 → ℚ
  ratio : Fin 3 → ℚ
  share_ne : ∀ k, share k ≠ 0
  scale_ne : ∀ i, scale i ≠ 0
  ratio_ne : ∀ i, ratio i ≠ 0
  linear_ne : ∀ n ∈ Finset.univ.image (exponents m d), linearValue (K := ℚ) root n ≠ 0
  constant_if_overlap : (Finset.univ.image (exponents m d)).card = 11 → root = none
  fiber_sum : ∀ n ∈ Finset.univ.image (exponents m d),
    (∑ k : Fin 3 × Fin 4, if exponents m d k = n then share k else 0) = 1
  geometry : ∀ (i : Fin 3) (j : Fin 4),
    share (i,j) * linearValue (K := ℚ) root (exp (m i) (d i) j) =
      scale i * (ratio i)^j.val * outerProduct m d i j

theorem RationalTable.geometry_cast {K : Type*} [Field K] [CharZero K]
    {m d : Fin 3 → ℕ} (T : RationalTable m d) (i : Fin 3) (j : Fin 4) :
    (T.share (i,j) : K) * linearValue T.root (exp (m i) (d i) j) =
      (T.scale i : K) * (T.ratio i : K)^j.val * (outerProduct m d i j : K) := by
  have cast := congrArg (Rat.castHom K) (T.geometry i j)
  cases h : T.root <;> simpa [linearValue, h] using cast

private theorem rational_parameters (l q : Fin 4 → ℚ) (hq : ∀ j, q j ≠ 0)
    (c t : ℝ) (hc : c ≠ 0) (ht : t ≠ 0)
    (h : ∀ j : Fin 4, (l j : ℝ) = c*t^j.val*(q j : ℝ)) :
    ∃ C T : ℚ, C ≠ 0 ∧ T ≠ 0 ∧ ∀ j : Fin 4, l j = C*T^j.val*q j := by
  let C : ℚ := l 0/q 0
  let T : ℚ := l 1/(C*q 1)
  have hc' : (C : ℝ) = c := by
    dsimp [C]
    push_cast
    apply (div_eq_iff (by exact_mod_cast hq 0 : (q 0 : ℝ) ≠ 0)).mpr
    simpa using h 0
  have ht' : (T : ℝ) = t := by
    dsimp [T]
    push_cast
    rw [hc']
    apply (div_eq_iff (mul_ne_zero hc (by exact_mod_cast hq 1 : (q 1 : ℝ) ≠ 0))).mpr
    calc
      _ = c*t*(q 1 : ℝ) := by simpa using h 1
      _ = _ := by ring
  refine ⟨C, T, ?_, ?_, ?_⟩
  · exact_mod_cast (hc' ▸ (show c ≠ 0 from hc))
  · exact_mod_cast (ht' ▸ (show t ≠ 0 from ht))
  · intro j
    have eq : (l j : ℝ) = (C : ℝ)*(T : ℝ)^j.val*(q j : ℝ) := by
      rw [hc', ht']
      exact h j
    exact_mod_cast eq

theorem exists_rational_table (s a b : Fin 3 → ℝ) (m d : Fin 3 → ℕ)
    (hs : ∀ i, s i = 1 ∨ s i = -1) (nd : ∀ i,0 < d i ∧ a i ≠ 0 ∧ b i ≠ 0)
    (large : 11 ≤ (Finset.univ.image (exponents m d)).card)
    (A B : ℝ) (hconst : (Finset.univ.image (exponents m d)).card = 11 → A=0)
    (hcurve : ∀ n ∈ Finset.univ.image (exponents m d),
      tableNumerator s a b m d n = A*(n : ℝ)+B) :
    Nonempty (RationalTable m d) := by
  classical
  let e := exponents m d
  let u := Finset.univ.image e
  have hlarge : 11 ≤ u.card := large
  have hsmall : u.card ≤ 12 := Finset.card_image_le.trans (by simp)
  have ein (k : Fin 3 × Fin 4) : e k ∈ u := Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have inj_when_twelve (no : u.card ≠ 11) : Function.Injective e := by
    have twelve : u.card = (Finset.univ : Finset (Fin 3 × Fin 4)).card := by simp; omega
    have inj := Finset.card_image_iff.mp twelve
    intro i j h
    exact inj (Finset.mem_univ i) (Finset.mem_univ j) h
  have sign_ne (i) : s i ≠ 0 := by rcases hs i with h|h <;> rw [h] <;> norm_num
  have ampne := amplitude_ne_zero s a b sign_ne (fun i => (nd i).2.1) (fun i => (nd i).2.2)
  have single_nonzero (k) (h : Single m d k) : A*(e k : ℝ)+B ≠ 0 := by
    rw [← hcurve _ (ein k)]
    change coeffAt s a b m d (e k) * _ ≠ 0
    rw [coeffAt_single s a b m d k h]
    exact mul_ne_zero (ampne k) (denominator_ne_zero m d (e k))
  have B_nonzero (eleven : u.card = 11) : B ≠ 0 := by
    obtain ⟨k,hk⟩ := exists_single m d large
    simpa [hconst eleven] using single_nonzero k hk
  have curve_nonzero (n) (hn : n ∈ u) : A*(n : ℝ)+B ≠ 0 := by
    by_cases eleven : u.card = 11
    · simpa [hconst eleven] using B_nonzero eleven
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hn
    exact single_nonzero k (single_of_injective m d (inj_when_twelve eleven) k)
  have coef_ne (n) (hn : n ∈ u) : coeffAt s a b m d n ≠ 0 := by
    intro z
    apply curve_nonzero n hn
    rw [← hcurve n hn]
    change coeffAt s a b m d n * _ = 0
    rw [z, zero_mul]
  let θ : Fin 3 × Fin 4 → ℝ := fun k => amplitudes s a b k / coeffAt s a b m d (e k)
  have θ_ne (k) : θ k ≠ 0 := div_ne_zero (ampne k) (coef_ne _ (ein k))
  have θ_single (k) (hk : Single m d k) : θ k = 1 := by
    dsimp [θ,e]
    rw [coeffAt_single s a b m d k hk, div_self (ampne k)]
  let C : Fin 3 → ℝ := fun i => -6*s i*(a i)^3*(d i : ℝ)^3
  let t : Fin 3 → ℝ := fun i => -b i/a i
  have C_ne (i) : C i ≠ 0 := by
    have hd : (d i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (nd i).1)
    simp [C, sign_ne i, (nd i).2.1, hd]
  have t_ne (i) : t i ≠ 0 := by simp [t, (nd i).2.1, (nd i).2.2]
  have weight (i : Fin 3) (j : Fin 4) : θ (i,j) * (A*(e (i,j) : ℝ)+B) =
      C i*(t i)^j.val*(outerProduct m d i j : ℝ) := by
    rw [← hcurve _ (ein (i,j))]
    apply weighted_table_geometric s a b m d i j (nd i).1 (nd i).2.1
    change θ (i,j) * coeffAt s a b m d (e (i,j)) = amplitudes s a b (i,j)
    exact div_mul_cancel₀ _ (coef_ne _ (ein (i,j)))
  have θ_rational (k : Fin 3 × Fin 4) : ∃ q : ℚ, θ k = (q : ℝ) := by
    by_cases hk : Single m d k
    · exact ⟨1, by simpa using θ_single k hk⟩
    have eleven : u.card = 11 := by
      by_contra no
      exact hk (single_of_injective m d (inj_when_twelve no) k)
    have hA : A=0 := hconst eleven
    have hB : B ≠ 0 := B_nonzero eleven
    obtain ⟨i,j⟩ := k
    unfold Single at hk
    push Not at hk
    obtain ⟨r,he,hr⟩ := hk
    have diff : r.1 ≠ i := by
      obtain ⟨i',j'⟩ := r
      intro hh
      change i'=i at hh
      subst i'
      have hh : j' = j := exp_injective (m i) (d i) (nd i).1 he
      exact hr (Prod.ext rfl hh)
    have other (k : Fin 4) (hne : k ≠ j) : Single m d (i,k) :=
      single_other m d large (fun h => hr h.symm) he.symm
        (fun h => hne (congrArg Prod.snd h)) (fun h => diff (congrArg Prod.fst h.symm))
    let z : Fin 4 → ℝ := fun k => (C i/B)*(t i)^k.val
    have z_ne (k) : z k ≠ 0 := mul_ne_zero (div_ne_zero (C_ne i) hB) (pow_ne_zero _ (t_ne i))
    have zeq (k : Fin 4) : θ (i,k) = z k*(outerProduct m d i k : ℝ) := by
      have g := weight i k
      rw [hA, zero_mul, zero_add] at g
      calc
        θ (i,k) = θ (i,k)*B/B := (mul_div_cancel_right₀ _ hB).symm
        _ = _ := by rw [g]; dsimp [z]; ring
    have z_q (k : Fin 4) (hne : k ≠ j) : ∃ q : ℚ, z k = (q : ℝ) := by
      refine ⟨1/(outerProduct m d i k), ?_⟩
      push_cast
      apply (eq_div_iff (by exact_mod_cast outerProduct_ne_zero m d i k :
        (outerProduct m d i k : ℝ) ≠ 0)).mpr
      rw [← zeq, θ_single (i,k) (other k hne)]
    have z0 : z 1 = z 0*t i := by simp [z]
    have z1 : z 2 = z 1*t i := by change (C i/B)*(t i)^2 = (C i/B)*(t i)^1*t i; ring
    have z2 : z 3 = z 2*t i := by change (C i/B)*(t i)^3 = (C i/B)*(t i)^2*t i; ring
    obtain ⟨q,hq⟩ := RationalCoordinates.geometric_missing_value_is_rational z (t i)
      (t_ne i) z_ne z0 z1 z2 j z_q
    exact ⟨q*outerProduct m d i j, by rw [zeq, hq, Rat.cast_mul]⟩
  choose share hsreal using θ_rational
  have shares_ne (k) : share k ≠ 0 := by
    intro z
    exact θ_ne k (by simp [hsreal k,z])
  have normalize :
      ∃ (root : Option ℚ) (scale : Fin 3 → ℝ), (∀ i, scale i ≠ 0) ∧
        (u.card = 11 → root = none) ∧
        (∀ n ∈ u, linearValue (K := ℝ) root n ≠ 0) ∧
        (∀ (i : Fin 3) (j : Fin 4), θ (i,j) * linearValue (K := ℝ) root (e (i,j)) =
          scale i*(t i)^j.val*(outerProduct m d i j : ℝ)) := by
    by_cases hA : A=0
    · obtain ⟨k,hk⟩ := exists_single m d large
      have hB : B ≠ 0 := by simpa [hA] using single_nonzero k hk
      refine ⟨none, fun i => C i/B, (fun i => div_ne_zero (C_ne i) hB),
        (fun _ => rfl), (by simp [linearValue]), ?_⟩
      intro i j
      have geom := weight i j
      rw [hA, zero_mul, zero_add] at geom
      rw [linearValue, mul_one]
      calc
        θ (i,j) = θ (i,j)*B/B := (mul_div_cancel_right₀ _ hB).symm
        _ = _ := by rw [geom]; ring
    have noteleven : u.card ≠ 11 := fun h => hA (hconst h)
    have inj := inj_when_twelve noteleven
    let r : ℝ := -B/A
    have scale_line (y : ℝ) : A*(y-r)=A*y+B := by
      dsimp [r]
      field_simp
      ring
    have affine_geom (i : Fin 3) (j : Fin 4) : (e (i,j) : ℝ)-r =
        (C i/A)*(t i)^j.val*(outerProduct m d i j : ℝ) := by
      have g := weight i j
      rw [θ_single (i,j) (single_of_injective m d inj (i,j)), one_mul, ← scale_line] at g
      apply (mul_left_cancel₀ hA)
      calc
        _ = _ := g
        _ = _ := by field_simp
    let x : ℚ := ((3*m 0 : ℕ) : ℚ)
    let step : ℚ := (d 0 : ℚ)
    have ex_cast (i : Fin 3) (j : Fin 4) :
        (e (i,j) : ℝ) = ((3*m i : ℕ) : ℝ) + (j.val : ℝ)*(d i : ℝ) := by
      simp [e, exponents, exp]
    have prim (j : Fin 4) : (x : ℝ) + (j.val : ℝ)*(step : ℝ)-r =
        (C 0/A)*(t 0)^j.val*(outerProduct m d 0 j : ℝ) := by
      have g := affine_geom 0 j
      rw [ex_cast] at g
      simpa [x,step] using g
    have step_ne : step ≠ 0 := by
      dsimp [step]
      exact_mod_cast (ne_of_gt (nd 0).1)
    have x_ne : (x : ℝ) ≠ r := by
      have hn := curve_nonzero _ (ein (0,0))
      rw [← scale_line, ex_cast] at hn
      intro hx
      apply hn
      simp [x] at hx
      simp [hx]
    obtain ⟨q,hq⟩ := affine_pole_of_four_values x step (outerProduct m d 0) step_ne
      (outerProduct_ne_zero m d 0) r (C 0/A) (t 0) x_ne (t_ne 0) prim
    refine ⟨some q, fun i => C i/A, (fun i => div_ne_zero (C_ne i) hA),
      (fun h => (noteleven h).elim), ?_, ?_⟩
    · intro n hn
      simpa [linearValue, ← hq, scale_line] using
        (show (n : ℝ)-r ≠ 0 from fun z => curve_nonzero n hn (by rw [← scale_line, z, mul_zero]))
    · intro i j
      rw [linearValue, ← hq, θ_single (i,j) (single_of_injective m d inj (i,j)), one_mul]
      exact affine_geom i j
  obtain ⟨root,c,hc,const,linne,geo⟩ := normalize
  let l (i : Fin 3) (j : Fin 4) : ℚ := share (i,j)*linearValue (K := ℚ) root (e (i,j))
  have cast_linear (n) : ((linearValue (K := ℚ) root n : ℚ) : ℝ) =
      linearValue (K := ℝ) root n := by cases root <;> simp [linearValue]
  have rgeo (i : Fin 3) (j : Fin 4) : (l i j : ℝ) = c i*(t i)^j.val*(outerProduct m d i j : ℝ) := by
    change ((share (i,j)*linearValue (K := ℚ) root (e (i,j)) : ℚ) : ℝ) = _
    rw [Rat.cast_mul, cast_linear, ← hsreal]
    exact geo i j
  choose scalar ratio scalar_ne ratio_ne geometry using fun i =>
    rational_parameters (l i) (outerProduct m d i) (outerProduct_ne_zero m d i)
      (c i) (t i) (hc i) (t_ne i) (rgeo i)
  refine ⟨⟨root, share, scalar, ratio, shares_ne, scalar_ne, ratio_ne, ?_, const, ?_, geometry⟩⟩
  · intro n hn z
    apply linne n hn
    rw [← cast_linear, z, Rat.cast_zero]
  · intro n hn
    have total (k : Fin 3 × Fin 4) : (if e k=n then θ k else 0) =
        (if e k=n then amplitudes s a b k else 0)/coeffAt s a b m d n := by
      by_cases h : e k=n <;> simp [h, θ]
    have sum : (∑ k : Fin 3 × Fin 4, if e k=n then θ k else 0) = 1 := by
      simp_rw [total, div_eq_mul_inv]
      rw [← Finset.sum_mul]
      change coeffAt s a b m d n * (coeffAt s a b m d n)⁻¹ = 1
      rw [← div_eq_mul_inv, div_self (coef_ne n hn)]
    have transfer : (((∑ k : Fin 3 × Fin 4, if e k=n then share k else 0 : ℚ) : ℝ)) = 1 := by
      rw [Rat.cast_sum]
      calc
        _ = ∑ k : Fin 3 × Fin 4, if e k=n then θ k else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          by_cases h : e k=n <;> simp [h, hsreal]
        _ = 1 := sum
    exact_mod_cast transfer

theorem RationalTable.share_eq_one_of_unique {m d : Fin 3 → ℕ} (T : RationalTable m d)
    (i : Fin 3 × Fin 4) (unique : ∀ k, exponents m d k = exponents m d i → k = i) :
    T.share i = 1 := by
  have h := T.fiber_sum (exponents m d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [Finset.sum_eq_single i] at h
  · simpa using h
  · intro k _ ne
    rw [ite_eq_right (fun eq => ne (unique k eq))]
  · simp

theorem RationalTable.shares_sum_one_of_exact_pair {m d : Fin 3 → ℕ} (T : RationalTable m d)
    (i j : Fin 3 × Fin 4) (hne : i ≠ j) (same : exponents m d i = exponents m d j)
    (only : ∀ k, exponents m d k = exponents m d i → k = i ∨ k = j) :
    T.share i + T.share j = 1 := by
  have h := T.fiber_sum (exponents m d i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  set f : Fin 3 × Fin 4 → ℚ := fun k =>
    if exponents m d k = exponents m d i then T.share k else 0
  have sub : ({i,j} : Finset (Fin 3 × Fin 4)) ⊆ Finset.univ := Finset.subset_univ _
  have sum := Finset.sum_subset (f := f) sub (by
    intro k _ ne
    apply ite_eq_right
    intro eq
    exact ne (by simpa only [Finset.mem_insert, Finset.mem_singleton] using only k eq))
  rw [Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at sum
  change (∑ k : Fin 3 × Fin 4, f k) = 1 at h
  rw [h] at sum
  simpa [f, same] using sum

end PEqualNP.Outside.L_gct_234.TableGeometry

namespace PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev K := ℚ_[3]
abbrev O := ℤ_[3]
abbrev F := ZMod 3
noncomputable abbrev val (x : K) := Padic.valuation x

private theorem three_ne : (3 : K) ≠ 0 := by norm_num
private theorem val_three : val (3 : K) = 1 := by
  exact Padic.valuation_p (p := 3)

private theorem scaled_val (x : K) (hx : x ≠ 0) (n : ℤ) :
    val (x * (3 : K)^(-n)) = val x - n := by
  calc
    _ = val x + val ((3 : K)^(-n)) :=
      Padic.valuation_mul hx (zpow_ne_zero _ three_ne)
    _ = val x + (-n) * val (3 : K) := by
      congr 1
      exact Padic.valuation_zpow (3 : K) (-n)
    _ = _ := by rw [val_three]; omega

noncomputable def scaled (x : K) (hx : x ≠ 0) (n : ℤ) (h : n ≤ val x) : O :=
  ⟨x * (3 : K)^(-n), (Padic.norm_le_one_iff_val_nonneg _).mpr (by
    change 0 ≤ val (x * (3 : K)^(-n))
    rw [scaled_val x hx n]
    omega)⟩

noncomputable def lead (x : K) (hx : x ≠ 0) : F :=
  PadicInt.toZMod (scaled x hx (val x) le_rfl)

private theorem residue_zero_iff (z : O) :
    PadicInt.toZMod z = 0 ↔ ‖z‖ < 1 := by
  change z ∈ RingHom.ker PadicInt.toZMod ↔ _
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton,
    PadicInt.norm_lt_one_iff_dvd]

theorem scaled_residue (x : K) (hx : x ≠ 0) (n : ℤ) (h : n ≤ val x) :
    PadicInt.toZMod (scaled x hx n h) = if n = val x then lead x hx else 0 := by
  by_cases eq : n = val x
  · subst n
    simp [lead]
  · rw [if_neg eq, residue_zero_iff, PadicInt.norm_def]
    change ‖x * (3 : K)^(-n)‖ < 1
    have scale := scaled_val x hx n
    change Padic.valuation (x * (3 : K)^(-n)) = val x - n at scale
    rw [Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hx (zpow_ne_zero _ three_ne)), scale]
    change (3 : ℝ) ^ (-(val x - n)) < (3 : ℝ) ^ (0 : ℤ)
    rw [zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)]
    omega

theorem lead_ne_zero (x : K) (hx : x ≠ 0) : lead x hx ≠ 0 := by
  intro h
  have lt := (residue_zero_iff _).mp h
  rw [PadicInt.norm_def] at lt
  change ‖x * (3 : K)^(- val x)‖ < 1 at lt
  have scale := scaled_val x hx (val x)
  change Padic.valuation (x * (3 : K)^(-val x)) = val x - val x at scale
  rw [Padic.norm_eq_zpow_neg_valuation (mul_ne_zero hx (zpow_ne_zero _ three_ne)),
    scale] at lt
  simp at lt

theorem lead_one_or_neg_one (x : K) (hx : x ≠ 0) :
    lead x hx = 1 ∨ lead x hx = -1 := by
  have finite : ∀ x : F, x ≠ 0 → x = 1 ∨ x = -1 := by decide +kernel
  exact finite _ (lead_ne_zero _ hx)

theorem lead_mul (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    lead (x*y) (mul_ne_zero hx hy) = lead x hx * lead y hy := by
  unfold lead
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  change x * y * (3 : K)^(-val (x*y)) =
    (x * (3 : K)^(-val x)) * (y * (3 : K)^(-val y))
  have vxy : val (x*y) = val x + val y := Padic.valuation_mul hx hy
  rw [vxy, neg_add, zpow_add₀ three_ne]
  ring

theorem residues_add3 (x y z : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (relation : x+y+z = 0) (n : ℤ)
    (nx : n ≤ val x) (ny : n ≤ val y) (nz : n ≤ val z) :
    (if n = val x then lead x hx else 0) +
    (if n = val y then lead y hy else 0) +
    (if n = val z then lead z hz else 0) = 0 := by
  rw [← scaled_residue x hx n nx, ← scaled_residue y hy n ny, ← scaled_residue z hz n nz,
    ← map_add, ← map_add]
  have sum : scaled x hx n nx + scaled y hy n ny + scaled z hz n nz = 0 := by
    apply Subtype.ext
    change x * (3 : K)^(-n) + y * (3 : K)^(-n) + z * (3 : K)^(-n) = 0
    rw [← add_mul, ← add_mul, relation, zero_mul]
  rw [sum, map_zero]

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.GeometricCorrection

private theorem product_expansion {R : Type*} [CommRing R] (h δ : R)
    (l : List (R × R)) :
    ∃ T : R, (l.map (fun x => 1 - h^2 * (x.1 + h*δ*x.2)^2)).prod =
      1 - h^2 * (l.map fun x => x.1^2).sum
        - 2*h^3*δ * (l.map fun x => x.1*x.2).sum + h^4*T := by
  induction l with
  | nil =>
    exact ⟨0, by simp⟩
  | cons x xs ih =>
    obtain ⟨T, ih⟩ := ih
    let S := (xs.map fun y => y.1^2).sum
    let B := (xs.map fun y => y.1*y.2).sum
    refine ⟨T - δ^2*x.2^2 + (x.1+h*δ*x.2)^2*(S+2*h*δ*B-h^2*T), ?_⟩
    simp only [List.map_cons, List.sum_cons, List.prod_cons, ih]
    change (1 - h^2 * (x.1 + h*δ*x.2)^2) * (1 - h^2*S - 2*h^3*δ*B + h^4*T)
      = 1 - h^2*(x.1^2+S) - 2*h^3*δ*(x.1*x.2+B) +
        h^4*(T - δ^2*x.2^2 + (x.1+h*δ*x.2)^2*(S+2*h*δ*B-h^2*T))
    ring

private theorem residue_cubes {R : Type*} [CommRing R] (φ : R →+* ZMod 3)
    (l : List (R × R)) (correction : ∀ x ∈ l, φ x.2 = -(φ x.1)^2) :
    φ (l.map fun x => x.1*x.2).sum = -(l.map fun x => (φ x.1)^3).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have head := correction x (List.mem_cons_self ..)
    have tail := ih (fun y hy => correction y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons, List.sum_cons, map_add, map_mul, tail, head]
    ring

theorem residues_of_two_geometric_steps {R : Type*} [CommRing R] [IsDomain R]
    (φ : R →+* ZMod 3) (h : R) (hne : h ≠ 0) (hh : φ h = 0)
    (l : List (R × R)) (b₀ c₀ : R)
    (correction : ∀ x ∈ l, φ x.2 = -(φ x.1)^2) (correction₀ : φ c₀ = -(φ b₀)^2)
    (base_eq : (l.map (fun x => 1 - h^2*x.1^2)).prod = 1 - h^2*b₀^2)
    (shift_eq : (l.map (fun x => 1 - h^2*(x.1+h*x.2)^2)).prod = 1 - h^2*(b₀+h*c₀)^2) :
    (l.map fun x => (φ x.1)^2).sum = (φ b₀)^2 ∧
      (l.map fun x => (φ x.1)^3).sum = (φ b₀)^3 := by
  obtain ⟨T₀, h₀⟩ := product_expansion h 0 l
  obtain ⟨T₁, h₁⟩ := product_expansion h 1 l
  simp only [mul_zero, zero_mul, add_zero, sub_zero] at h₀
  simp only [mul_one] at h₁
  rw [h₀] at base_eq
  rw [h₁] at shift_eq
  let S := (l.map fun x => x.1^2).sum
  let B := (l.map fun x => x.1*x.2).sum
  have sq_mul : h^2 * (S - b₀^2 - h^2*T₀) = 0 := by
    dsimp [S]
    linear_combination -base_eq
  have cu_mul : h^3 * (-2*(B-b₀*c₀) + h*(T₁ + c₀^2 - T₀)) = 0 := by
    dsimp [B]
    linear_combination shift_eq - base_eq
  have sq := congrArg φ ((mul_eq_zero.mp sq_mul).resolve_left (pow_ne_zero 2 hne))
  have cu := congrArg φ ((mul_eq_zero.mp cu_mul).resolve_left (pow_ne_zero 3 hne))
  constructor
  · have hS : φ S = (l.map fun x => (φ x.1)^2).sum := by
      simp [S, map_list_sum, List.map_map, Function.comp_def]
    have sq' : φ S - (φ b₀)^2 = 0 := by simpa [hh] using sq
    rw [hS] at sq'
    exact sub_eq_zero.mp sq'
  · have cu' : (-2 : ZMod 3) * (φ B - (φ b₀)*(φ c₀)) = 0 := by
      simpa [hh, map_ofNat] using cu
    have cu'' := sub_eq_zero.mp ((mul_eq_zero.mp cu').resolve_left (by decide))
    rw [show φ B = -(l.map fun x => (φ x.1)^3).sum from residue_cubes φ l correction,
      correction₀] at cu''
    exact neg_injective (cu''.trans (by ring))

theorem cube_zmod_three (z : ZMod 3) : z^3 = z :=
  (show ∀ a : ZMod 3, a^3 = a by decide +kernel) z

end PEqualNP.Outside.L_gct_234.GeometricCorrection

namespace PEqualNP.Outside.L_gct_234.UnitTriads

theorem equal_units_of_sum_zero :
    ∀ A B C : ZMod 3, A ≠ 0 → B ≠ 0 → C ≠ 0 → A+B+C=0 → A=B ∧ A=C := by
  decide +kernel

theorem eq_iff_unit_sign :
    ∀ A B : ZMod 3, A ≠ 0 → B ≠ 0 → (A=B ↔ (A = -1 ↔ B = -1)) := by
  decide +kernel

theorem neg_eq_iff_unit_sign :
    ∀ A B : ZMod 3, A ≠ 0 → B ≠ 0 → (A = -B ↔ ¬(A = -1 ↔ B = -1)) := by
  decide +kernel

theorem triad_of_minimum_sum (a b c : ℤ) (A B C : ZMod 3)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0)
    (h : let m := min a (min b c)
      (if m = a then A else 0) + (if m = b then B else 0) + (if m = c then C else 0) = 0) :
    (a=b ∧ a<c ∧ ¬(A = -1 ↔ B = -1)) ∨
      (a=c ∧ a<b ∧ ¬(A = -1 ↔ C = -1)) ∨
      (b=c ∧ b<a ∧ ¬(B = -1 ↔ C = -1)) ∨
      (a=b ∧ a=c ∧ (A = -1 ↔ B = -1) ∧ (A = -1 ↔ C = -1)) := by
  let m := min a (min b c)
  change (if m=a then A else 0) + (if m=b then B else 0) + (if m=c then C else 0) = 0 at h
  have ma : m ≤ a := min_le_left ..
  have mb : m ≤ b := (min_le_right ..).trans (min_le_left ..)
  have mc : m ≤ c := (min_le_right ..).trans (min_le_right ..)
  have mset : m=a ∨ m=b ∨ m=c := by
    unfold m
    simp only [min_def]
    split_ifs <;> simp
  by_cases ea : m=a <;> by_cases eb : m=b <;> by_cases ec : m=c
  · have heq := equal_units_of_sum_zero A B C hA hB hC (by simpa only [ite_eq_left ea, ite_eq_left eb, ite_eq_left ec, add_zero, zero_add] using h)
    exact Or.inr (Or.inr (Or.inr
      ⟨ea.symm.trans eb, ea.symm.trans ec, (eq_iff_unit_sign A B hA hB).mp heq.1,
        (eq_iff_unit_sign A C hA hC).mp heq.2⟩))
  · have heq : A+B=0 := by simpa only [ite_eq_left ea, ite_eq_left eb, ite_eq_right ec, add_zero, zero_add] using h
    exact Or.inl ⟨ea.symm.trans eb, by omega,
      (neg_eq_iff_unit_sign A B hA hB).mp (eq_neg_of_add_eq_zero_left heq)⟩
  · have heq : A+C=0 := by simpa only [ite_eq_left ea, ite_eq_right eb, ite_eq_left ec, add_zero, zero_add] using h
    exact Or.inr (Or.inl ⟨ea.symm.trans ec, by omega,
      (neg_eq_iff_unit_sign A C hA hC).mp (eq_neg_of_add_eq_zero_left heq)⟩)
  · exact False.elim (hA (by simpa only [ite_eq_left ea, ite_eq_right eb, ite_eq_right ec, add_zero, zero_add] using h))
  · have heq : B+C=0 := by simpa only [ite_eq_right ea, ite_eq_left eb, ite_eq_left ec, add_zero, zero_add] using h
    exact Or.inr (Or.inr (Or.inl ⟨eb.symm.trans ec, by omega,
      (neg_eq_iff_unit_sign B C hB hC).mp (eq_neg_of_add_eq_zero_left heq)⟩))
  · exact False.elim (hB (by simpa only [ite_eq_right ea, ite_eq_left eb, ite_eq_right ec, add_zero, zero_add] using h))
  · exact False.elim (hC (by simpa only [ite_eq_right ea, ite_eq_right eb, ite_eq_left ec, add_zero, zero_add] using h))
  · rcases mset with ha | hb | hc
    · exact (ea ha).elim
    · exact (eb hb).elim
    · exact (ec hc).elim

end PEqualNP.Outside.L_gct_234.UnitTriads
namespace PEqualNP.Outside.L_gct_234.Triadic

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def minusLead (x : K) (hx : x ≠ 0) : Prop := lead x hx = -1

theorem minusLead_mul (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    minusLead (x*y) (mul_ne_zero hx hy) ↔ ¬ (minusLead x hx ↔ minusLead y hy) := by
  unfold minusLead
  rw [lead_mul x y hx hy]
  have signs : ∀ u v : F, u ≠ 0 → v ≠ 0 →
      (u*v = -1 ↔ ¬ (u = -1 ↔ v = -1)) := by decide +kernel
  exact signs _ _ (lead_ne_zero x hx) (lead_ne_zero y hy)

def Triad (a b c : ℤ) (A B C : Prop) : Prop :=
  (a=b ∧ a<c ∧ ¬(A ↔ B)) ∨
  (a=c ∧ a<b ∧ ¬(A ↔ C)) ∨
  (b=c ∧ b<a ∧ ¬(B ↔ C)) ∨
  (a=b ∧ a=c ∧ (A ↔ B) ∧ (A ↔ C))

theorem triad_val (x y z : K) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (sum : x+y+z = 0) :
    Triad (val x) (val y) (val z) (minusLead x hx) (minusLead y hy) (minusLead z hz) := by
  let m := min (val x) (min (val y) (val z))
  have hxle : m ≤ val x := min_le_left ..
  have hyle : m ≤ val y := (min_le_right ..).trans (min_le_left ..)
  have hzle : m ≤ val z := (min_le_right ..).trans (min_le_right ..)
  exact PEqualNP.Outside.L_gct_234.UnitTriads.triad_of_minimum_sum _ _ _ _ _ _
    (lead_ne_zero x hx) (lead_ne_zero y hy) (lead_ne_zero z hz)
    (residues_add3 x y z hx hy hz sum m hxle hyle hzle)

end

end PEqualNP.Outside.L_gct_234.Triadic
namespace PEqualNP.Outside.L_gct_234.Triadic

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem val_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    val (x*y) = val x + val y := Padic.valuation_mul hx hy

theorem val_inv (x : K) : val x⁻¹ = -val x := Padic.valuation_inv x

theorem lead_one : lead (1 : K) one_ne_zero = 1 := by
  unfold lead
  have eq : scaled (1 : K) one_ne_zero (val 1) le_rfl = 1 := by
    apply Subtype.ext
    change 1 * (3 : K)^(-val 1) = 1
    change 1 * (3 : K)^(-Padic.valuation 1) = 1
    simp
  rw [eq, map_one]

theorem lead_inv (x : K) (hx : x ≠ 0) :
    lead x⁻¹ (inv_ne_zero hx) = (lead x hx)⁻¹ := by
  have mul := lead_mul x x⁻¹ hx (inv_ne_zero hx)
  have one : x * x⁻¹ = 1 := mul_inv_cancel₀ hx
  have lOne : lead (x*x⁻¹) (mul_ne_zero hx (inv_ne_zero hx)) = 1 := by
    simpa only [one] using lead_one
  exact inv_eq_of_mul_eq_one_right (mul.symm.trans lOne) |>.symm

theorem val_div (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    val (x/y) = val x - val y := by
  rw [div_eq_mul_inv, val_mul hx (inv_ne_zero hy), val_inv, sub_eq_add_neg]

private theorem val_neg_one : val (-1 : K) = 0 := by
  have nz : (-1 : K) ≠ 0 := by norm_num
  have mul := val_mul nz nz
  have one : (-1 : K) * (-1) = 1 := by ring
  rw [one] at mul
  have v : val (1 : K) = 0 := Padic.valuation_one
  omega

private theorem lead_neg_one : lead (-1 : K) (by norm_num) = -1 := by
  unfold lead
  have eq : scaled (-1 : K) (by norm_num) (val (-1 : K)) le_rfl = -1 := by
    apply Subtype.ext
    change (-1 : K) * (3 : K)^(-val (-1 : K)) = -1
    rw [val_neg_one]
    simp
  rw [eq, map_neg, map_one]

theorem split_fractions (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (total : a+b=1) :
    (val a < 0 ∧ val a = val b ∧ ¬(minusLead a ha ↔ minusLead b hb)) ∨
    (val a = 0 ∧ 0 < val b ∧ ¬ minusLead a ha) ∨
    (0 < val a ∧ val b = 0 ∧ ¬ minusLead b hb) ∨
    (val a = 0 ∧ val b = 0 ∧ minusLead a ha ∧ minusLead b hb) := by
  have s : a+b+(-1)=0 := by rw [total]; ring
  have tri := triad_val a b (-1) ha hb (by norm_num) s
  unfold Triad at tri
  rw [val_neg_one] at tri
  have last : minusLead (-1 : K) (by norm_num) := lead_neg_one
  simp only [last, iff_true] at tri
  rcases tri with h | ⟨h, lt, unit⟩ | ⟨h, lt, unit⟩ | ⟨h, e, u, nu⟩
  · exact Or.inl ⟨h.2.1,h.1,h.2.2⟩
  · exact Or.inr (Or.inl ⟨h, by omega, unit⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h, unit⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e, h.symm.trans e, nu, u.mp nu⟩))

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

abbrev red : O →+* F := PadicInt.toZMod

theorem unit_of_residue {x : O} (h : red x ≠ 0) : IsUnit x := by
  by_contra no
  exact h ((residue_zero_iff x).mpr (PadicInt.not_isUnit_iff.mp no))

private noncomputable def correctionUnit (h b : O) (small : red h = 0) : Oˣ :=
  (unit_of_residue (x := 1+h*b) (by simp [small])).unit

private theorem correctionUnit_val (h b : O) (small : red h = 0) :
    (correctionUnit h b small : O) = 1+h*b :=
  IsUnit.unit_spec _

noncomputable def correction (h b : O) (small : red h = 0) : O :=
  -b^2 * ((correctionUnit h b small)⁻¹ : Oˣ)

theorem residue_correction (h b : O) (small : red h = 0) :
    red (correction h b small) = -(red b)^2 := by
  unfold correction
  have unitOne : red (correctionUnit h b small : O) = 1 := by
    rw [correctionUnit_val]
    simp [small]
  have invOne : red ((correctionUnit h b small)⁻¹ : Oˣ) = 1 := by
    have prod := congrArg red (Units.mul_inv (correctionUnit h b small))
    simpa [unitOne] using prod
  simp [invOne]

theorem shifted_correction (h b : O) (small : red h = 0) :
    ((b + h*correction h b small : O) : K) =
      (b : K)/(1+(h : K)*(b : K)) := by
  let z := correctionUnit h b small
  have zval : (z : O) = 1+h*b := correctionUnit_val h b small
  have zne : (1+(h : K)*(b : K)) ≠ 0 := by
    have ne := PadicInt.coe_ne_zero.mpr z.ne_zero
    simpa [zval] using ne
  have iz : (((z⁻¹ : Oˣ) : O) : K) = (1+(h : K)*(b : K))⁻¹ := by
    symm
    apply (mul_eq_one_iff_inv_eq₀ zne).mp
    have eq := congrArg (fun t : O => (t : K)) z.inv_mul
    simpa [zval, mul_comm] using eq
  change (b : K) + (h : K) * (-(b : K)^2 * (((z⁻¹ : Oˣ) : O) : K)) = _
  rw [iz]
  apply (eq_div_iff zne).2
  rw [add_mul, mul_assoc (↑h : K), mul_assoc (-(↑b : K)^2), inv_mul_cancel₀ zne, mul_one]
  ring

theorem reduction_of_shifted_geometric_steps
    (h : O) (nonzero : h ≠ 0) (small : red h = 0) (B : List O) (b₀ : O)
    (base : (B.map (fun b => 1-h^2*b^2)).prod = 1-h^2*b₀^2)
    (shifted : (B.map (fun b => 1-h^2*(b+h*correction h b small)^2)).prod =
      1-h^2*(b₀+h*correction h b₀ small)^2) :
    (B.map fun b => (red b)^2).sum = (red b₀)^2 ∧
      (B.map fun b => (red b)^3).sum = (red b₀)^3 := by
  let l := B.map (fun b => (b,correction h b small))
  have ck : ∀ x ∈ l, red x.2 = -(red x.1)^2 := by
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact residue_correction h b small
  have both := PEqualNP.Outside.L_gct_234.GeometricCorrection.residues_of_two_geometric_steps
    red h nonzero small l b₀ (correction h b₀ small) ck
    (residue_correction h b₀ small)
    (by simpa [l, List.map_map, Function.comp_def] using base)
    (by simpa [l, List.map_map, Function.comp_def] using shifted)
  simpa [l, List.map_map, Function.comp_def] using both

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.CenteredRatio

theorem single {K : Type*} [Field K] (x d y : K) (hne : x ≠ y) :
    1 - (d / (x-y))^2 = ((x-d-y)*(x+d-y))/(x-y)^2 := by
  field_simp [sub_ne_zero.mpr hne]
  ring

end PEqualNP.Outside.L_gct_234.CenteredRatio

namespace PEqualNP.Outside.L_gct_234.Triadic

noncomputable section

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def signedResidue (u : Prop) [Decidable u] : F := if u then -1 else 1

theorem lead_as_signed (x : K) (hx : x ≠ 0) [Decidable (minusLead x hx)] :
    lead x hx = signedResidue (minusLead x hx) := by
  obtain h | h := lead_one_or_neg_one x hx
  · have opp : ¬minusLead x hx := by
      unfold minusLead
      rw [h]
      decide +kernel
    simp [signedResidue, opp, h]
  · simp [signedResidue, minusLead, h]

private theorem inverse_lead_eq (x : F) : x⁻¹ = x := by
  have finite : ∀ a : F, a⁻¹ = a := by decide +kernel
  exact finite x

private def scaledInverse (x : K) (hx : x ≠ 0) (m : ℤ) (hm : val x ≤ m) : O :=
  scaled (x⁻¹) (inv_ne_zero hx) (-m) (by rw [val_inv]; omega)

private theorem scaledInverse_coe (x : K) (hx : x ≠ 0) (m : ℤ) (hm : val x ≤ m) :
    (scaledInverse x hx m hm : K) = (3 : K)^m / x := by
  change x⁻¹ * (3 : K)^(-(-m)) = _
  rw [neg_neg, div_eq_mul_inv, mul_comm]

private theorem scaledInverse_red (x : K) (hx : x ≠ 0) (m : ℤ) (hm : val x ≤ m) :
    red (scaledInverse x hx m hm) = if val x = m then lead x hx else 0 := by
  unfold scaledInverse
  rw [scaled_residue, val_inv, lead_inv x hx, inverse_lead_eq]
  by_cases e : val x = m <;> simp [e, eq_comm (a := m)]

def Denom (r : Option K) (x : K) : K := r.elim 1 (x - ·)

def Outer (values : List K) (x : K) : K :=
  (values.map (fun y => x-y)).prod

def Quotient (values : List K) (r : Option K) (x : K) : K := Outer values x / Denom r x

private theorem center_product (values : List K) (x d : K)
    (h : ∀ y ∈ values, x-y ≠ 0) :
    (values.map (fun y => 1 - (d/(x-y))^2)).prod =
      Outer values (x-d) * Outer values (x+d) / (Outer values x)^2 := by
  classical
  let f := fun y => x-d-y
  let g := fun y => x+d-y
  let q := fun y => (x-y)^2
  have point : values.map (fun y => 1 - (d/(x-y))^2) =
      values.map (fun y => (f y * g y) * (q y)⁻¹) := by
    apply List.map_congr_left
    intro y hy
    have eq := PEqualNP.Outside.L_gct_234.CenteredRatio.single x d y (sub_ne_zero.mp (h y hy))
    simpa [f, g, q, div_eq_mul_inv] using eq
  have ips (l : List K) :
      (l.map (fun y => (q y)⁻¹)).prod = ((l.map q).prod)⁻¹ := by
    induction l with
    | nil => simp
    | cons y l ih => simp [ih, mul_inv_rev, mul_comm]
  have powers (l : List K) : (l.map q).prod = ((l.map (fun y => x-y)).prod)^2 := by
    induction l with
    | nil => simp
    | cons y l ih => simp [q, ih, mul_pow]
  rw [point, List.prod_map_mul, List.prod_map_mul, ips, powers]
  rfl

private theorem center_denominator (r : Option K) (x d : K)
    (nz : Denom r x ≠ 0) :
    1 - (r.elim 0 (fun y => d/(x-y)))^2 =
      Denom r (x-d) * Denom r (x+d) / (Denom r x)^2 := by
  cases r with
  | none => simp [Denom]
  | some y =>
    exact PEqualNP.Outside.L_gct_234.CenteredRatio.single x d y (sub_ne_zero.mp nz)

private theorem center_identity (outside : List K) (r : Option K) (x d : K)
    (ext0 : ∀ y ∈ outside, x-y ≠ 0)
    (roof : ∀ t ∈ [x-d,x,x+d], Denom r t ≠ 0)
    (geom : Quotient outside r (x-d) * Quotient outside r (x+d) =
      (Quotient outside r x)^2) :
    (outside.map (fun y => 1 - (d/(x-y))^2)).prod =
      1 - (r.elim 0 (fun y => d/(x-y)))^2 := by
  rw [center_product outside x d ext0, center_denominator r x d (roof x (by simp))]
  have prod0 : Outer outside x ≠ 0 := by
    clear geom
    unfold Outer
    induction outside with
    | nil => simp
    | cons a more ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_ne_zero (ext0 a (by simp)) (ih (fun y hy => ext0 y (by simp [hy])))
  have d₀ := roof (x-d) (by simp)
  have d₁ := roof x (by simp)
  have d₂ := roof (x+d) (by simp)
  unfold Quotient at geom
  field_simp [d₀,d₁,d₂] at geom
  field_simp [prod0,d₁]
  linear_combination geom

private theorem h_mul_inverse (d x : K) (hd : d ≠ 0) (hx : x ≠ 0) (m : ℤ)
    (h₁ : m ≤ val d) (h₂ : val x ≤ m) :
    (scaled d hd m h₁ : K) * (scaledInverse x hx m h₂ : K) = d/x := by
  rw [scaledInverse_coe]
  change d * (3 : K)^(-m) * ((3 : K)^m / x) = d/x
  have p : (3 : K)^(-m)*(3 : K)^m = 1 := by
    rw [← zpow_add₀ three_ne, neg_add_cancel, zpow_zero]
  rw [div_eq_mul_inv, ← mul_assoc, mul_assoc d, p, mul_one]
  rfl

private theorem h_mul_shifted_inverse (d x : K) (hd : d ≠ 0) (hx : x ≠ 0)
    (hxd : x+d ≠ 0) (m : ℤ) (h₁ : m ≤ val d) (h₂ : val x ≤ m)
    (hs : red (scaled d hd m h₁) = 0) :
    (scaled d hd m h₁ : K) *
      ((scaledInverse x hx m h₂ +
        scaled d hd m h₁ * correction (scaled d hd m h₁) (scaledInverse x hx m h₂) hs : O) : K)
      = d/(x+d) := by
  rw [shifted_correction, ← mul_div_assoc, h_mul_inverse]
  have ne : 1+d/x ≠ 0 := by
    rw [show 1+d/x=(x+d)/x by rw [add_div, div_self hx]]
    exact div_ne_zero hxd hx
  apply (div_eq_div_iff ne hxd).2
  rw [show 1+d/x=(x+d)/x by rw [add_div, div_self hx]]
  ring

private theorem coe_list_prod (xs : List O) : (↑xs.prod : K) = (xs.map (fun x : O => (x : K))).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

noncomputable def Impact (m : ℤ) (z : K) : F := by
  classical
  exact if hz : z ≠ 0 then (if val z = m then lead z hz else 0) else 0

theorem nearestResidue (outside : List K) (r : Option K) (x d : K) (m : ℤ)
    (hd : d ≠ 0) (small : m < val d)
    (ext : ∀ y ∈ outside, ∀ t ∈ [x-d,x,x+d,x+2*d], t-y ≠ 0)
    (roof : ∀ t ∈ [x-d,x,x+d,x+2*d], Denom r t ≠ 0)
    (bound : ∀ y ∈ outside, val (x-y) ≤ m)
    (boundR : ∀ y ∈ r, val (x-y) ≤ m)
    (left : Quotient outside r (x-d) * Quotient outside r (x+d) = (Quotient outside r x)^2)
    (right : Quotient outside r x * Quotient outside r (x+2*d) = (Quotient outside r (x+d))^2) :
    let a := outside.map (fun y => Impact m (x-y))
    let b := if r.isSome then Impact m (Denom r x) else 0
    (a.map (·^2)).sum = b^2 ∧ a.sum = b := by
  classical
  let h := scaled d hd m small.le
  have hn : h ≠ 0 := by
    intro hh
    have q := congrArg (fun z : O => (z : K)) hh
    exact (mul_ne_zero hd (zpow_ne_zero _ three_ne)) q
  have hs : red h = 0 := by rw [scaled_residue, ite_eq_right (by omega : m ≠ val d)]
  let b := outside.attach.map (fun y => scaledInverse (x-y.1) (ext y.1 y.2 x (by simp)) m (bound _ y.2))
  have roofZero := roof x (by simp)
  have roofBound : r.isSome → val (Denom r x) ≤ m := by
    cases r with
    | none => simp
    | some y => intro _; exact boundR y rfl
  let r₀ := if h : r.isSome then scaledInverse (Denom r x) roofZero m (roofBound h) else 0
  have byLeft := center_identity outside r x d (fun y hy => ext y hy x (by simp))
    (fun t ht => roof t (by simpa using List.mem_append_left [x+2*d] ht)) left
  have byRight := center_identity outside r (x+d) d (fun y hy => ext y hy (x+d) (by simp))
    (fun t ht => roof t (by
      have eq1 : x+d-d=x := by ring
      have eq2 : x+d+d=x+2*d := by ring
      simpa [eq1,eq2] using List.mem_cons_of_mem (x-d) ht))
    (by simpa only [show x+d-d=x by ring, show x+d+d=x+2*d by ring] using right)
  have hBase : (b.map (fun y => 1-h^2*y^2)).prod = 1-h^2*r₀^2 := by
    apply Subtype.ext
    rw [coe_list_prod, List.map_map]
    simp only [Function.comp_def, PadicInt.coe_sub, PadicInt.coe_one, PadicInt.coe_mul,
      PadicInt.coe_pow, ← mul_pow]
    simp only [b, List.map_map, Function.comp_def, h, h_mul_inverse]
    have leq := @List.attach_map_val K K outside (fun y => 1 - (d/(x-y))^2)
    rw [leq]
    have rEq : (h : K)*(r₀ : K) = r.elim 0 (fun y => d/(x-y)) := by
      cases r <;> simp [r₀, h, h_mul_inverse, Denom]
    dsimp only [h] at rEq
    rw [rEq]
    exact byLeft
  have hShift : (b.map (fun y => 1-h^2*(y+h*correction h y hs)^2)).prod =
      1-h^2*(r₀+h*correction h r₀ hs)^2 := by
    apply Subtype.ext
    rw [coe_list_prod, List.map_map]
    simp only [Function.comp_def, PadicInt.coe_sub, PadicInt.coe_one, PadicInt.coe_mul,
      PadicInt.coe_pow, ← mul_pow]
    have point (y : {a // a ∈ outside}) :
        (h : K) * ((scaledInverse (x-y.1) (ext y.1 y.2 x (by simp)) m (bound _ y.2) +
         h*correction h (scaledInverse (x-y.1) (ext y.1 y.2 x (by simp)) m (bound _ y.2)) hs : O) : K) =
          d/(x+d-y.1) := by
      rw [show x+d-y.1=x-y.1+d by ring]
      exact h_mul_shifted_inverse d (x-y.1) hd _ (by
        rw [show x-y.1+d=x+d-y.1 by ring]
        exact ext _ y.2 (x+d) (by simp)) _ _ _ hs
    simp only [b, List.map_map, Function.comp_def, point]
    have leq := @List.attach_map_val K K outside (fun y => 1 - (d/(x+d-y))^2)
    rw [leq]
    have rEq : (h : K) * ((r₀+h*correction h r₀ hs : O) : K) =
        r.elim 0 (fun y => d/(x+d-y)) := by
      cases r with
      | none => simp [r₀, correction]
      | some y =>
        have nx : x-y ≠ 0 := roofZero
        have nxd : x-y+d ≠ 0 := by
          rw [show x-y+d=x+d-y by ring]
          exact roof (x+d) (by simp)
        have shift := h_mul_shifted_inverse d (x-y) hd nx nxd m small.le (boundR y rfl) hs
        simpa [r₀, Denom, h, show x-y+d=x+d-y by ring] using shift
    rw [rEq]
    exact byRight
  have bounds := reduction_of_shifted_geometric_steps h hn hs b r₀ hBase hShift
  have otherRed : b.map (fun z => red z) = outside.map (fun y => Impact m (x-y)) := by
    simp only [b, List.map_map, Function.comp_def, scaledInverse_red]
    have rewrite : outside.attach.map (fun y => if val (x-y.1) = m then
        lead (x-y.1) (ext y.1 y.2 x (by simp)) else 0) =
        outside.attach.map (fun y => Impact m (x-y.1)) := by
      apply List.map_congr_left
      intro y _
      simp [Impact, ext _ y.2 x (by simp)]
    rw [rewrite]
    simp
  have roofRed : red r₀ = if r.isSome then Impact m (Denom r x) else 0 := by
    cases r <;> simp [r₀, scaledInverse_red, Impact, roofZero]
  change _ ∧ _
  rw [roofRed] at bounds
  simp only [PEqualNP.Outside.L_gct_234.GeometricCorrection.cube_zmod_three] at bounds
  refine ⟨?_, ?_⟩
  · rw [← otherRed, List.map_map]
    exact bounds.1
  · rw [← otherRed]
    exact bounds.2

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

open scoped BigOperators

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

structure APState where
  start : Fin 3 → K
  step : Fin 3 → K
  root : Option K

namespace APState

abbrev Slot := Fin 3 × Fin 4

def point (A : APState) (i : Fin 3) (j : Fin 4) : K := A.start i + (j.val : K) * A.step i

def otherBlockIndices (i : Fin 3) : Finset Slot := Finset.univ.filter fun j => j.1 ≠ i

def otherBlock (A : APState) (i : Fin 3) : List K :=
  (otherBlockIndices i).toList.map fun j => A.point j.1 j.2

def cross (A : APState) (i : Fin 3) (j : Fin 4) : K :=
  ∏ k ∈ otherBlockIndices i, (A.point i j - A.point k.1 k.2)

theorem otherBlockIndices_card (i : Fin 3) : (otherBlockIndices i).card = 8 := by
  fin_cases i <;> decide +kernel

def denom (A : APState) (i : Fin 3) (j : Fin 4) : K :=
  A.root.elim 1 fun r => A.point i j - r

def X (A : APState) (i : Fin 3) (j : Fin 4) : K := A.cross i j / A.denom i j

def Disjoint (A : APState) : Prop := Function.Injective fun j : Slot => A.point j.1 j.2

def Separate (A : APState) : Prop := ∀ i j, A.denom i j ≠ 0

def Geometric (A : APState) : Prop := ∀ i,
  A.X i 0 * A.X i 2 = A.X i 1 ^ 2 ∧ A.X i 1 * A.X i 3 = A.X i 2 ^ 2

theorem step_nonzero (A : APState) (disjoint : A.Disjoint) (i : Fin 3) : A.step i ≠ 0 := by
  intro zero
  have eq : A.point i 0 = A.point i 1 := by simp [point, zero]
  have diff : (0 : Fin 4) ≠ 1 := by decide
  have slotEq : ((i,0) : Slot) = (i,1) := disjoint eq
  exact diff (congrArg Prod.snd slotEq)

theorem X_nonzero (A : APState) (disjoint : A.Disjoint) (sep : A.Separate) (i : Fin 3) (j : Fin 4) :
    A.X i j ≠ 0 := by
  unfold X cross
  apply div_ne_zero _ (sep i j)
  apply Finset.prod_ne_zero_iff.2
  intro k hk
  have ho := (Finset.mem_filter.1 hk).2
  intro bad
  have slotEq : ((i,j) : Slot) = k := disjoint (sub_eq_zero.mp bad)
  exact ho (congrArg Prod.fst slotEq).symm

def orient (flip : Bool) : Equiv.Perm (Fin 4) := if flip then Fin.revPerm else Equiv.refl _

def slotMap (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) : Slot ≃ Slot where
  toFun x := (π x.1, orient (flip x.1) x.2)
  invFun x := (π.symm x.1, (orient (flip (π.symm x.1))).symm x.2)
  left_inv x := by rcases x with ⟨i,j⟩; simp
  right_inv x := by rcases x with ⟨i,j⟩; simp

theorem slotMap_outside (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (i : Fin 3) (j : Slot) :
    j ∈ otherBlockIndices i ↔ slotMap π flip j ∈ otherBlockIndices (π i) := by
  simp [otherBlockIndices, slotMap]

def transform (A : APState) (scale offset : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) : APState where
  start i := offset + scale * (A.start (π i) + if flip i then 3 * A.step (π i) else 0)
  step i := scale * (if flip i then -A.step (π i) else A.step (π i))
  root := A.root.map fun r => offset + scale * r

theorem point_transform (A : APState) (scale offset : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (i : Fin 3) (j : Fin 4) :
    (A.transform scale offset π flip).point i j =
      offset + scale * A.point (π i) (orient (flip i) j) := by
  cases h : flip i <;> fin_cases j <;> simp [point, orient, transform, h, Fin.revPerm, Fin.rev] <;> ring

theorem cross_transform (A : APState) (scale offset : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (i : Fin 3) (j : Fin 4) :
    (A.transform scale offset π flip).cross i j = scale^8 * A.cross (π i) (orient (flip i) j) := by
  unfold cross
  simp only [point_transform]
  simp_rw [show ∀ x y : K, offset + scale*x - (offset + scale*y) = scale * (x-y) by
    intro x y; ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const, otherBlockIndices_card]
  congr 1
  exact Finset.prod_bijective (slotMap π flip) (slotMap π flip).bijective
    (slotMap_outside π flip i) (fun _ _ => rfl)

def denomFactor (A : APState) (scale : K) : K := A.root.elim 1 fun _ => scale

theorem denom_transform (A : APState) (scale offset : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (i : Fin 3) (j : Fin 4) :
    (A.transform scale offset π flip).denom i j =
      A.denomFactor scale * A.denom (π i) (orient (flip i) j) := by
  unfold denom denomFactor
  rw [point_transform]
  cases h : A.root <;> simp [transform, h] <;> ring

theorem X_transform (A : APState) (scale offset : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (i : Fin 3) (j : Fin 4) :
    (A.transform scale offset π flip).X i j =
      (scale^8 / A.denomFactor scale) * A.X (π i) (orient (flip i) j) := by
  unfold X
  rw [cross_transform, denom_transform, mul_div_mul_comm]

theorem disjoint_transform (A : APState) (scale offset : K) (scale_ne : scale ≠ 0)
    (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (h : A.Disjoint) :
    (A.transform scale offset π flip).Disjoint := by
  intro i j eq
  simp only [point_transform, add_right_inj] at eq
  let f (x : Slot) := A.point (slotMap π flip x).1 (slotMap π flip x).2
  have same : f i = f j := mul_left_cancel₀ scale_ne eq
  have slotEq : slotMap π flip i = slotMap π flip j := h same
  exact (slotMap π flip).injective slotEq

theorem separate_transform (A : APState) (scale offset : K) (scale_ne : scale ≠ 0)
    (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (h : A.Separate) :
    (A.transform scale offset π flip).Separate := by
  intro i j
  rw [denom_transform]
  apply mul_ne_zero _ (h _ _)
  cases root : A.root <;> simp [denomFactor, root, scale_ne]

theorem geometric_transform (A : APState) (scale offset : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (h : A.Geometric) :
    (A.transform scale offset π flip).Geometric := by
  intro i
  simp only [X_transform]
  let a := scale^8 / A.denomFactor scale
  have G := h (π i)
  cases eq : flip i
  · simp only [orient, eq, Bool.false_eq_true, ite_false, Equiv.refl_apply]
    constructor
    · linear_combination a^2 * G.1
    · linear_combination a^2 * G.2
  · simp only [orient, eq, ite_true]
    have r0 : Fin.revPerm (0 : Fin 4) = 3 := by decide
    have r1 : Fin.revPerm (1 : Fin 4) = 2 := by decide
    have r2 : Fin.revPerm (2 : Fin 4) = 1 := by decide
    have r3 : Fin.revPerm (3 : Fin 4) = 0 := by decide
    rw [r0, r1, r2, r3]
    constructor
    · linear_combination a^2 * G.2
    · linear_combination a^2 * G.1

end APState

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

open scoped Classical

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def Negative (x : K) : Prop := ∃ h : x ≠ 0, minusLead x h

theorem negative_iff (x : K) (hx : x ≠ 0) :
    Negative x ↔ minusLead x hx := by
  constructor
  · rintro ⟨h,s⟩
    exact s
  · exact fun s => ⟨hx,s⟩

theorem negative_mul (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Negative (x*y) ↔ ¬(Negative x ↔ Negative y) := by
  simp only [negative_iff _ (mul_ne_zero hx hy), negative_iff x hx, negative_iff y hy]
  exact minusLead_mul x y hx hy

theorem negative_inv (x : K) (hx : x ≠ 0) : Negative x⁻¹ ↔ Negative x := by
  simp only [negative_iff _ (inv_ne_zero hx), negative_iff x hx, minusLead]
  rw [lead_inv, inverse_lead_eq]

theorem negative_div (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    Negative (x/y) ↔ ¬(Negative x ↔ Negative y) := by
  rw [div_eq_mul_inv, negative_mul x y⁻¹ hx (inv_ne_zero hy), negative_inv y hy]

private theorem lead_square (x : K) (hx : x ≠ 0) : lead (x^2) (pow_ne_zero 2 hx) = 1 := by
  have eq := lead_mul x x hx hx
  change lead (x*x) (mul_ne_zero hx hx) = lead x hx * lead x hx at eq
  have one : lead x hx * lead x hx = 1 := by
    rcases lead_one_or_neg_one x hx with h|h <;> simp [h]
  simpa only [pow_two] using eq.trans one

theorem order_affine {x y z : K} (nx : x ≠ 0) (ny : y ≠ 0) (nz : z ≠ 0)
    (h : x*z = y^2) :
    val x + val z = 2*val y ∧ (Negative x ↔ Negative z) := by
  have q := congrArg val h
  rw [val_mul nx nz, pow_two, val_mul ny ny] at q
  have sign : ¬ Negative (x*z) := by
    rw [h, negative_iff _ (pow_ne_zero 2 ny), minusLead, lead_square y ny]
    decide +kernel
  rw [negative_mul x z nx nz] at sign
  exact ⟨by omega, not_not.mp sign⟩

theorem val_list_prod (xs : List K) (nz : ∀ x ∈ xs, x ≠ 0) :
    xs.prod ≠ 0 ∧ val xs.prod = (xs.map val).sum := by
  induction xs with
  | nil => simp [val]
  | cons x xs ih =>
    have n := nz x (by simp)
    obtain ⟨np,hp⟩ := ih (fun y hy => nz y (by simp [hy]))
    exact ⟨mul_ne_zero n np, by simp only [List.map_cons, List.prod_cons, List.sum_cons, val_mul n np, hp]⟩

def xorProduct (xs : List Prop) : Prop := xs.foldl (fun a b => ¬(a ↔ b)) False

private theorem xorProduct_eq_foldr (xs : List Prop) :
    xorProduct xs = xs.foldr (fun a b => ¬(a ↔ b)) False := by
  have aux (xs : List Prop) (a : Prop) :
      xs.foldl (fun a b => ¬(a ↔ b)) a =
      (¬(a ↔ xs.foldr (fun a b => ¬(a ↔ b)) False)) := by
    induction xs generalizing a with
    | nil => simp
    | cons x xs ih =>
      rw [List.foldl_cons, List.foldr_cons, ih]
      apply propext
      tauto
  rw [xorProduct, aux]
  simp

theorem negative_list_prod (xs : List K) (nz : ∀ x ∈ xs, x ≠ 0) :
    Negative xs.prod ↔ xorProduct (xs.map Negative) := by
  rw [xorProduct_eq_foldr]
  induction xs with
  | nil =>
    simp [negative_iff _ one_ne_zero, minusLead, lead_one, show (1 : F) ≠ -1 by decide]
  | cons x xs ih =>
    have n := nz x (by simp)
    have ns : ∀ y ∈ xs, y ≠ 0 := fun y hy => nz y (by simp [hy])
    rw [List.prod_cons, negative_mul _ _ n (val_list_prod xs ns).1,
      List.map_cons, List.foldr_cons, ih ns]

theorem impact_value (m : ℤ) (z : K) (nz : z ≠ 0) :
    Impact m z = if val z = m then (if Negative z then -1 else 1) else 0 := by
  classical
  simp only [Impact, dif_pos nz, negative_iff z nz]
  split
  · exact lead_as_signed z nz
  · rfl

theorem impact_square (m : ℤ) (z : K) (nz : z ≠ 0) :
    (Impact m z)^2 = if val z = m then 1 else 0 := by
  classical
  rw [impact_value m z nz]
  split_ifs <;> simp

private theorem modThree_iff (x : ℤ) : (x : F) = 0 ↔ x % 3 = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.dvd_iff_emod_eq_zero]
  rfl

theorem impacts_modThree (zs : List K) (nz : ∀ z ∈ zs, z ≠ 0) (r : Option K)
    (rnz : ∀ z ∈ r, z ≠ 0) (m : ℤ)
    (squares : (zs.map fun z => (Impact m z)^2).sum =
      r.elim 0 (fun z => (Impact m z)^2))
    (units : (zs.map fun z => Impact m z).sum = r.elim 0 (Impact m)) :
    let count : K → ℤ := fun z => if val z = m then 1 else 0
    let unit : K → ℤ := fun z => if val z = m then (if Negative z then -1 else 1) else 0
    ((zs.map count).sum-r.elim 0 count) % 3 = 0 ∧
      ((zs.map unit).sum-r.elim 0 unit) % 3 = 0 := by
  classical
  let count : K → ℤ := fun z => if val z = m then 1 else 0
  let unit : K → ℤ := fun z => if val z = m then (if Negative z then -1 else 1) else 0
  have ct (z : K) (h : z ≠ 0) : ((count z : ℤ) : F) = (Impact m z)^2 := by
    rw [impact_square m z h]
    simp [count]
  have ut (z : K) (h : z ≠ 0) : ((unit z : ℤ) : F) = Impact m z := by
    rw [impact_value m z h]
    simp [unit]
  have to_sum (f : K → ℤ) (g : K → F) (q : ∀ z, z ≠ 0 → ((f z : ℤ) : F) = g z)
      (l : List K) (h : ∀ z ∈ l, z ≠ 0) : (((l.map f).sum : ℤ) : F) = (l.map g).sum := by
    induction l with
    | nil => simp
    | cons y l ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add]
      exact congrArg₂ (·+·) (q y (h y (by simp))) (ih (fun z hz => h z (by simp [hz])))
  have to_root (f : K → ℤ) (g : K → F) (q : ∀ z, z ≠ 0 → ((f z : ℤ) : F) = g z) :
      ((r.elim 0 f : ℤ) : F) = r.elim 0 g := by
    cases r with
    | none => simp
    | some z => exact q z (rnz z rfl)
  change ((zs.map count).sum-r.elim 0 count) % 3 = 0 ∧
    ((zs.map unit).sum-r.elim 0 unit) % 3 = 0
  constructor <;> apply (modThree_iff _).mp <;> rw [Int.cast_sub]
  · rw [to_sum count _ ct _ nz, to_root count _ ct, squares, sub_self]
  · rw [to_sum unit _ ut _ nz, to_root unit _ ut, units, sub_self]

namespace APState

theorem point_sub_nonzero (A : APState) (disjoint : A.Disjoint) {i j : Fin 3}
    (ij : i ≠ j) (p q : Fin 4) : A.point i p - A.point j q ≠ 0 := by
  intro h
  have equal : ((i,p) : Slot) = (j,q) := disjoint (sub_eq_zero.mp h)
  exact ij (congrArg Prod.fst equal)

theorem cross_two_blocks (A : APState) (i j k : Fin 3) (p : Fin 4)
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) :
    A.cross i p = (∏ q : Fin 4, (A.point i p - A.point j q)) *
      (∏ q : Fin 4, (A.point i p - A.point k q)) := by
  classical
  have covered : ∀ a b c q : Fin 3, a ≠ b → a ≠ c → b ≠ c → q ≠ a → q = b ∨ q = c := by
    decide +kernel
  have either (q : Fin 3) (eq : q ≠ i) : q = j ∨ q = k := covered i j k q ij ik jk eq
  have shape : otherBlockIndices i =
      ({j,k} : Finset (Fin 3)) ×ˢ (Finset.univ : Finset (Fin 4)) := by
    ext w
    rcases w with ⟨a,b⟩
    simp only [otherBlockIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, and_true, Finset.mem_insert, Finset.mem_singleton]
    exact ⟨either a, fun h => by rcases h with rfl | rfl; exact ij.symm; exact ik.symm⟩
  rw [cross, shape]
  calc
    _ = (∏ b ∈ ({j,k} : Finset (Fin 3)), (∏ q : Fin 4, (A.point i p - A.point b q))) :=
      Finset.prod_product' _ _ (fun b q => A.point i p - A.point b q)
    _ = _ := Finset.prod_pair jk

end APState

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

noncomputable section

open scoped Classical
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def pairOutside (A : APState) (j k : Fin 3) : List K :=
  (List.ofFn (A.point j)) ++ (List.ofFn (A.point k))

theorem quotient_of_pairOutside (A : APState) {i j k : Fin 3}
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k) (p : Fin 4) :
    Quotient (A.pairOutside j k) A.root (A.point i p) = A.X i p := by
  simp only [Quotient, Outer, pairOutside, List.map_append, List.prod_append,
    List.map_ofFn, List.prod_ofFn, Function.comp_apply, X, denom, Denom]
  rw [A.cross_two_blocks i j k p ij ik jk]

def effectiveDenom (A : APState) (useRoot : Bool) (p : K) : K :=
  if useRoot then Denom A.root p else 1

private theorem affine_offset_cancel (a b c v : ℤ)
    (h : (a-v) + (c-v) = 2 * (b-v)) : a+c = 2*b := by
  omega

private theorem affine_bit_cancel (a b bit : Prop)
    (h : (¬ (a ↔ bit)) ↔ (¬ (b ↔ bit))) : a ↔ b := by
  tauto

set_option maxHeartbeats 3000000 in
theorem affine_of_pairOutside (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) {i j k : Fin 3}
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (useRoot : Bool)
    (far : useRoot = false → ∀ r ∈ A.root, ∀ i p,
      val (A.point i p-r) = val r ∧
        (Negative (A.point i p-r) ↔ ¬Negative r)) :
    let V := fun p : Fin 4 => ((A.pairOutside j k).map fun q => val (A.point i p-q)).sum -
      val (A.effectiveDenom useRoot (A.point i p))
    let U := fun p : Fin 4 => ¬(xorProduct ((A.pairOutside j k).map fun q => Negative (A.point i p-q)) ↔
      Negative (A.effectiveDenom useRoot (A.point i p)))
    (V 0 + V 2 = 2 * V 1 ∧ (U 0 ↔ U 2)) ∧
      (V 1 + V 3 = 2 * V 2 ∧ (U 1 ↔ U 3)) := by
  let V := fun p : Fin 4 => ((A.pairOutside j k).map fun q => val (A.point i p-q)).sum -
    val (A.effectiveDenom useRoot (A.point i p))
  let U := fun p : Fin 4 => ¬(xorProduct ((A.pairOutside j k).map fun q => Negative (A.point i p-q)) ↔
    Negative (A.effectiveDenom useRoot (A.point i p)))
  have p0 (p : Fin 4) : ∀ t ∈ (A.pairOutside j k).map (A.point i p - ·), t ≠ 0 := by
    intro t mem
    obtain ⟨y, h, rfl⟩ := List.mem_map.mp mem
    simp only [pairOutside, List.mem_append] at h
    rcases h with h|h
    · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp h
      exact A.point_sub_nonzero disjoint ij p q
    · obtain ⟨q,rfl⟩ := List.mem_ofFn.mp h
      exact A.point_sub_nonzero disjoint ik p q
  have vFull (p : Fin 4) : val (A.X i p) =
      ((A.pairOutside j k).map fun q => val (A.point i p-q)).sum - val (A.denom i p) := by
    rw [← A.quotient_of_pairOutside ij ik jk p, Quotient, Outer]
    change val (((A.pairOutside j k).map (A.point i p - ·)).prod / A.denom i p) = _
    rw [val_div _ _ (val_list_prod _ (p0 p)).1 (sep i p)]
    rw [(val_list_prod _ (p0 p)).2, List.map_map]
    rfl
  have uFull (p : Fin 4) : Negative (A.X i p) ↔
      ¬(xorProduct ((A.pairOutside j k).map fun q => Negative (A.point i p-q)) ↔ Negative (A.denom i p)) := by
    rw [← A.quotient_of_pairOutside ij ik jk p, Quotient, Outer]
    change Negative (((A.pairOutside j k).map (A.point i p - ·)).prod / A.denom i p) ↔ _
    rw [negative_div _ _ (val_list_prod _ (p0 p)).1 (sep i p)]
    rw [negative_list_prod _ (p0 p), List.map_map]
    rfl
  let nx := A.X_nonzero disjoint sep i
  have L := order_affine (nx 0) (nx 1) (nx 2) (geo i).1
  have R := order_affine (nx 1) (nx 2) (nx 3) (geo i).2
  rw [vFull 0,vFull 1,vFull 2, uFull 0,uFull 2] at L
  rw [vFull 1,vFull 2,vFull 3, uFull 1,uFull 3] at R
  change (V 0 + V 2 = 2*V 1 ∧ (U 0 ↔ U 2)) ∧ (V 1 + V 3 = 2*V 2 ∧ (U 1 ↔ U 3))
  cases useRoot
  · let I (p : Fin 4) := ((A.pairOutside j k).map fun q => val (A.point i p-q)).sum
    let J (p : Fin 4) := xorProduct ((A.pairOutside j k).map fun q => Negative (A.point i p-q))
    let D (p : Fin 4) := A.denom i p
    have conV (p : Fin 4) : val (D p) = val (D 0) := by
      cases h : A.root with
      | none => simp [D, denom, h]
      | some r =>
          have farp := (far rfl r (by simp [h]) i p).1
          have far0 := (far rfl r (by simp [h]) i 0).1
          simpa only [D, denom, h, Option.elim] using farp.trans far0.symm
    have conU (p : Fin 4) : Negative (D p) ↔ Negative (D 0) := by
      cases h : A.root with
      | none => simp [D, denom, h]
      | some r =>
          have farp := (far rfl r (by simp [h]) i p).2
          have far0 := (far rfl r (by simp [h]) i 0).2
          simpa only [D, denom, h, Option.elim] using farp.trans far0.symm
    change ((I 0-val (D 0))+(I 2-val (D 2)) = 2*(I 1-val (D 1)) ∧
      ((¬(J 0 ↔ Negative (D 0))) ↔ (¬(J 2 ↔ Negative (D 2))))) at L
    change ((I 1-val (D 1))+(I 3-val (D 3)) = 2*(I 2-val (D 2)) ∧
      ((¬(J 1 ↔ Negative (D 1))) ↔ (¬(J 3 ↔ Negative (D 3))))) at R
    rw [conV 2, conV 1, conU 2] at L
    rw [conV 1, conV 2, conV 3, conU 1, conU 3] at R
    have values₁ := affine_offset_cancel (I 0) (I 1) (I 2) (val (D 0)) L.1
    have values₂ := affine_offset_cancel (I 1) (I 2) (I 3) (val (D 0)) R.1
    have signs₁ := affine_bit_cancel (J 0) (J 2) (Negative (D 0)) L.2
    have signs₂ := affine_bit_cancel (J 1) (J 3) (Negative (D 0)) R.2
    have vone : val (1 : K) = 0 := Padic.valuation_one
    have uone : ¬Negative (1 : K) := by
      rw [negative_iff _ one_ne_zero, minusLead, lead_one]
      decide +kernel
    simpa only [V, U, I, J, effectiveDenom, Bool.false_eq_true, ite_false, vone,
      sub_zero, show Negative (1 : K) = False from propext ⟨uone, False.elim⟩, iff_false, not_not]
      using And.intro (And.intro values₁ signs₁) (And.intro values₂ signs₂)
  · simpa only [V, U, effectiveDenom, Bool.true_eq, ite_true, Denom, denom] using And.intro L R

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open scoped Classical
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

private theorem centered_slots (A : APState) (i : Fin 3) :
    A.point i 1 - A.step i = A.point i 0 ∧
    A.point i 1 + A.step i = A.point i 2 ∧
    A.point i 1 + 2*A.step i = A.point i 3 := by
  refine ⟨?_,?_,?_⟩ <;> simp [point] <;> ring

set_option maxHeartbeats 3000000 in
theorem nearest_pairOutside (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) {i j k : Fin 3}
    (ij : i ≠ j) (ik : i ≠ k) (jk : j ≠ k)
    (useRoot : Bool)
    (far : useRoot = false → ∀ r ∈ A.root, val (A.point i 1-r) < 0)
    (m : ℤ) (hm : 0 ≤ m) (small : m < val (A.step i))
    (near : ∀ q ∈ A.pairOutside j k, val (A.point i 1-q) ≤ m)
    (nearRoot : useRoot → ∀ r ∈ A.root, val (A.point i 1-r) ≤ m) :
    let x := A.point i 1
    let count : K → ℤ := fun z => if val z = m then 1 else 0
    let unit : K → ℤ := fun z => if val z = m then (if Negative z then -1 else 1) else 0
    let roof := if useRoot then A.root.map (x-·) else none
    ((((A.pairOutside j k).map fun y => count (x-y)).sum - roof.elim 0 count) % 3 = 0) ∧
      ((((A.pairOutside j k).map fun y => unit (x-y)).sum - roof.elim 0 unit) % 3 = 0) := by
  let x := A.point i 1
  let d := A.step i
  let R := A.pairOutside j k
  let roof := if useRoot then A.root.map (x-·) else none
  obtain ⟨eq0,eq2,eq3⟩ := centered_slots A i
  have otherBlock (q : K) (h : q ∈ R) (p : Fin 4) : A.point i p-q ≠ 0 := by
    simp only [R,pairOutside,List.mem_append] at h
    rcases h with h | h
    · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp h
      exact A.point_sub_nonzero disjoint ij p t
    · obtain ⟨t,rfl⟩ := List.mem_ofFn.mp h
      exact A.point_sub_nonzero disjoint ik p t
  have rs (r : K) (h : r ∈ A.root) : val (x-r) ≤ m := by
    cases e : useRoot with
    | false => exact (far e r h).le.trans hm
    | true => exact nearRoot (by simp [e]) r h
  have q (p : Fin 4) : Quotient R A.root (A.point i p) = A.X i p :=
    A.quotient_of_pairOutside ij ik jk p
  have step1 : Quotient R A.root (x-d) * Quotient R A.root (x+d) = Quotient R A.root x ^ 2 := by
    change Quotient R A.root (A.point i 1-A.step i) *
      Quotient R A.root (A.point i 1+A.step i) = Quotient R A.root (A.point i 1) ^ 2
    rw [eq0,eq2,q,q,q]
    exact (geo i).1
  have step2 : Quotient R A.root x * Quotient R A.root (x+2*d) = Quotient R A.root (x+d) ^ 2 := by
    change Quotient R A.root (A.point i 1) *
      Quotient R A.root (A.point i 1+2*A.step i) = Quotient R A.root (A.point i 1+A.step i) ^ 2
    rw [eq2,eq3,q,q,q]
    exact (geo i).2
  have compare (q : K) (h : q ∈ R) :
      ∀ t ∈ [x-d,x,x+d,x+2*d], t-q ≠ 0 := by
    intro t hq
    change t ∈ [A.point i 1-A.step i,A.point i 1,A.point i 1+A.step i,A.point i 1+2*A.step i] at hq
    rw [eq0,eq2,eq3] at hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact otherBlock q h 0
    · exact otherBlock q h 1
    · exact otherBlock q h 2
    · exact otherBlock q h 3
  have denomnz : ∀ t ∈ [x-d,x,x+d,x+2*d], Denom A.root t ≠ 0 := by
    intro t ht
    change t ∈ [A.point i 1-A.step i,A.point i 1,A.point i 1+A.step i,A.point i 1+2*A.step i] at ht
    rw [eq0,eq2,eq3] at ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl
    · exact sep i 0
    · exact sep i 1
    · exact sep i 2
    · exact sep i 3
  have h := nearestResidue R A.root x d m (A.step_nonzero disjoint i) small compare denomnz near rs step1 step2
  dsimp only at h
  have root_eq :
      (if A.root.isSome then Impact m (Denom A.root x) else 0) = roof.elim 0 (Impact m) := by
    cases useRoot with
    | false =>
      cases e : A.root with
      | none => simp [roof,e]
      | some r =>
        have g := far rfl r (by simp [e])
        have ng : val (x-r) ≠ m := by change val (x-r) < 0 at g; omega
        have nz : x-r ≠ 0 := by simpa [Denom,e] using denomnz x (by simp)
        simp [roof,e,Denom,Impact,nz,ng]
    | true =>
      cases e : A.root <;> simp [roof,e,Denom]
  rw [root_eq] at h
  have hRoot : ∀ z ∈ roof, z ≠ 0 := by
    intro z hz
    cases useRoot <;> cases e : A.root <;> simp [roof,e] at hz
    subst z
    simpa [Denom,e] using denomnz x (by simp)
  have others : ∀ z ∈ R.map (x-·), z ≠ 0 := by
    intro z hz
    obtain ⟨y,mem,rfl⟩ := List.mem_map.mp hz
    exact otherBlock y mem 1
  have square : (roof.elim 0 (Impact m))^2 = roof.elim 0 (fun z => (Impact m z)^2) := by
    cases roof <;> simp
  have H := impacts_modThree (R.map (x-·)) others roof hRoot m
    (by simpa only [List.map_map, Function.comp_def, square] using h.1)
    (by simpa [List.map_map,Function.comp_def] using h.2)
  simpa [List.map_map,Function.comp_def,R] using H

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

structure NormalizedTuple {ι : Type*} (x : ι → K) where
  order : ℤ
  entries : ι → O
  entries_cast : ∀ i, (entries i : K) = x i * (3 : K) ^ (-order)
  has_unit : ∃ i, PadicInt.toZMod (entries i) ≠ 0

theorem normalized_tuple {ι : Type*} [Fintype ι] (x : ι → K) (nonzero : ∃ i, x i ≠ 0) :
    Nonempty (NormalizedTuple x) := by
  classical
  let active := (Finset.univ : Finset ι).filter fun i => x i ≠ 0
  have activeNonempty : active.Nonempty := by
    obtain ⟨i, hi⟩ := nonzero
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let orders := active.image fun i => val (x i)
  have ordersNonempty : orders.Nonempty := activeNonempty.image _
  let n := orders.min' ordersNonempty
  have lower (i : ι) (hi : x i ≠ 0) : n ≤ val (x i) := by
    apply Finset.min'_le
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩)
  let y (i : ι) : O := if hi : x i ≠ 0 then scaled (x i) hi n (lower i hi) else 0
  have yCast (i : ι) : (y i : K) = x i * (3 : K) ^ (-n) := by
    by_cases hi : x i ≠ 0
    · simp only [y, dif_pos hi]
      rfl
    · have zero : x i = 0 := not_ne_iff.mp hi
      simp [y, zero]
  have nIn : n ∈ orders := Finset.min'_mem _ _
  obtain ⟨i, hi, hv⟩ := Finset.mem_image.1 nIn
  have hi' : x i ≠ 0 := (Finset.mem_filter.1 hi).2
  refine ⟨⟨n, y, yCast, i, ?_⟩⟩
  rw [show y i = scaled (x i) hi' n (lower i hi') by simp [y, hi']]
  rw [scaled_residue, if_pos hv.symm]
  exact lead_ne_zero _ _

namespace NormalizedTuple

variable {ι : Type*} [Fintype ι] {x : ι → K} (T : NormalizedTuple x)

def digit (i : ι) : F := PadicInt.toZMod (T.entries i)

def linear (c : ι → ℤ) : O := ∑ i, (c i : O) * T.entries i

theorem cast_linear (c : ι → ℤ) :
    (T.linear c : K) = (∑ i, (c i : K) * x i) * (3 : K) ^ (-T.order) := by
  rw [Finset.sum_mul]
  simp only [linear, PadicInt.coe_sum, PadicInt.coe_mul, PadicInt.coe_intCast]
  exact Finset.sum_congr rfl (fun i _ => by rw [T.entries_cast, mul_assoc])

end NormalizedTuple

theorem valuation_scale_pow (x : K) (hx : x ≠ 0) (n : ℤ) :
    val (x * (3 : K) ^ (-n)) = val x - n := scaled_val x hx n

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem sub_pole_dominates (x r : K) (hr : r ≠ 0)
    (dom : x ≠ 0 → val r < val x) :
    ∃ hx : x - r ≠ 0, val (x-r) = val r ∧ lead (x-r) hx = -lead r hr := by
  classical
  let n := val r
  let X : O := if h : x ≠ 0 then scaled x h n (dom h).le else 0
  let R := scaled r hr n le_rfl
  have castX : (X : K) = x * (3 : K)^(-n) := by
    by_cases h : x ≠ 0
    · simp only [X, dite_eq_left h]
      rfl
    · have z : x = 0 := not_ne_iff.mp h
      simp [X, z]
  have redX : PadicInt.toZMod X = 0 := by
    by_cases h : x ≠ 0
    · have ne : n ≠ val x := (dom h).ne
      simp only [X, dite_eq_left h, scaled_residue, ite_eq_right ne]
    · simp only [X, dite_eq_right h, map_zero]
  have redR : PadicInt.toZMod R = lead r hr := rfl
  have castSub : ((X-R : O) : K) = (x-r) * (3 : K)^(-n) := by
    rw [PadicInt.coe_sub, castX, sub_mul]
    rfl
  have redSub : PadicInt.toZMod (X-R) = -lead r hr := by
    rw [map_sub, redX, redR, zero_sub]
  have hn : PadicInt.toZMod (X-R) ≠ 0 := by
    rw [redSub, neg_ne_zero]
    exact lead_ne_zero _ _
  have nx : x-r ≠ 0 := by
    intro zero
    have subZero : X-R = 0 := by
      apply Subtype.ext
      rw [castSub, zero, zero_mul]
      rfl
    exact hn (by rw [subZero, map_zero])
  have norm : ‖((X-R : O) : K)‖ ≤ 1 := (X-R).property
  rw [castSub] at norm
  have scaledNonneg := (Padic.norm_le_one_iff_val_nonneg _).mp norm
  change 0 ≤ val ((x-r) * (3 : K)^(-n)) at scaledNonneg
  rw [valuation_scale_pow _ nx n] at scaledNonneg
  have lower : n ≤ val (x-r) := by omega
  have same : X-R = scaled (x-r) nx n lower := by
    apply Subtype.ext
    exact castSub
  rw [same, scaled_residue] at redSub hn
  have eq : n = val (x-r) := by
    by_contra ne
    exact hn (ite_eq_right ne)
  rw [ite_eq_left eq] at redSub
  exact ⟨nx, eq.symm, redSub⟩

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

def CanonicalAPResidues (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool) : Prop :=
  s 0 = 0 ∧
    ((a 0 = true ∧ a 1 = true ∧ a 2 = true ∧
        ((s 1, s 2) = (0,0) ∨ (s 1, s 2) = (0,1) ∨ (s 1, s 2) = (1,2))) ∨
     (a 0 = true ∧ a 1 = true ∧ a 2 = false ∧
        ((s 1,s 2) = (0,0) ∨ (s 1,s 2) = (0,1) ∨ (s 1,s 2) = (1,0) ∨
          (s 1,s 2) = (1,2))) ∨
     (a 0 = true ∧ a 1 = false ∧ a 2 = false ∧
        ((s 1,s 2) = (0,0) ∨ (s 1,s 2) = (0,1) ∨ (s 1,s 2) = (1,1) ∨
          (s 1,s 2) = (1,2))) ∨
     (a 0 = false ∧ a 1 = false ∧ a 2 = false ∧
        ((s 1,s 2) = (0,1) ∨ (s 1,s 2) = (1,2))))

instance (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool) : Decidable (CanonicalAPResidues s a) := by
  unfold CanonicalAPResidues
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem ap_residue_canonical_fun : ∀ (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool),
    ((∃ i, a i = true) ∨ ∃ i, s i ≠ s 0) →
    ∃ (p : Fin 3 → Fin 3) (ε : ZMod 3),
      (p 0 ≠ p 1 ∧ p 0 ≠ p 2 ∧ p 1 ≠ p 2) ∧ (ε = 1 ∨ ε = -1) ∧
        CanonicalAPResidues (fun i => ε * (s (p i) - s (p 0))) (fun i => a (p i)) := by
  decide +kernel

theorem ap_residue_canonical (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool)
    (nontrivial : (∃ i, a i = true) ∨ ∃ i, s i ≠ s 0) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : ZMod 3),
      (ε = 1 ∨ ε = -1) ∧
        CanonicalAPResidues (fun i => ε * (s (π i) - s (π 0))) (fun i => a (π i)) := by
  obtain ⟨p, ε, ⟨p01, p02, p12⟩, sign, canon⟩ := ap_residue_canonical_fun s a nontrivial
  have inj : Function.Injective p := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  let π := Equiv.ofBijective p (Finite.injective_iff_bijective.mp inj)
  exact ⟨π, ε, sign, canon⟩

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

private theorem neg_valuation (x : K) (hx : x ≠ 0) : val (-x) = val x := by
  have n : ‖-x‖ = ‖x‖ := norm_neg _
  rw [Padic.norm_eq_zpow_neg_valuation (neg_ne_zero.mpr hx),
    Padic.norm_eq_zpow_neg_valuation hx] at n
  exact neg_injective ((zpow_right_injective₀ (by norm_num : (0 : ℝ) < 3)
    (by norm_num : (3 : ℝ) ≠ 1)) n)

private theorem lead_negated (x : K) (hx : x ≠ 0) :
    lead (-x) (neg_ne_zero.mpr hx) = -lead x hx := by
  unfold lead
  rw [← map_neg]
  congr 1
  apply Subtype.ext
  change -x * (3 : K)^(-val (-x)) = -(x * (3 : K)^(-val x))
  rw [neg_valuation x hx, neg_mul]

namespace APState

structure PrimitiveCoordinates (A : APState) where
  starts : Fin 3 → O
  steps : Fin 3 → O
  starts_eq : ∀ i, (starts i : K) = A.start i
  steps_eq : ∀ i, (steps i : K) = A.step i
  start_zero : A.start 0 = 0
  canonical : CanonicalAPResidues (fun i => PadicInt.toZMod (starts i))
    (fun i => decide (PadicInt.toZMod (steps i) ≠ 0))
  oriented : ∀ i (h : A.step i ≠ 0), lead (A.step i) h = 1

theorem primitive_state (A : APState) (disjoint : A.Disjoint) (sep : A.Separate) (g : A.Geometric) :
    ∃ B : APState, B.Disjoint ∧ B.Separate ∧ B.Geometric ∧ Nonempty (PrimitiveCoordinates B) := by
  classical
  let data : Fin 3 ⊕ Fin 3 → K := Sum.elim (fun i => A.start i - A.start 0) A.step
  obtain ⟨T⟩ := normalized_tuple data ⟨Sum.inr 0, A.step_nonzero disjoint 0⟩
  let t : K := (3 : K)^(-T.order)
  have tne : t ≠ 0 := zpow_ne_zero _ (by norm_num)
  let B := A.transform t (-t * A.start 0) (Equiv.refl _) (fun _ => false)
  have bd : B.Disjoint := A.disjoint_transform _ _ tne _ _ disjoint
  have bs : B.Separate := A.separate_transform _ _ tne _ _ sep
  have bg : B.Geometric := A.geometric_transform _ _ _ _ g
  let W (i : Fin 3) : O := T.entries (.inl i)
  let D (i : Fin 3) : O := T.entries (.inr i)
  have W_cast (i : Fin 3) : (W i : K) = B.start i := by
    show (T.entries (.inl i) : K) = B.start i
    rw [T.entries_cast]
    dsimp [data, B, transform, t]
    ring
  have D_cast (i : Fin 3) : (D i : K) = B.step i := by
    show (T.entries (.inr i) : K) = B.step i
    rw [T.entries_cast]
    simp [data, B, transform, t, mul_comm]
  have w0 : W 0 = 0 := by
    apply Subtype.ext
    change (W 0 : K) = 0
    rw [W_cast]
    simp [B, transform]
  let s (i : Fin 3) : F := PadicInt.toZMod (W i)
  let a (i : Fin 3) : Bool := decide (PadicInt.toZMod (D i) ≠ 0)
  have nontrivial : (∃ i, a i = true) ∨ ∃ i, s i ≠ s 0 := by
    obtain ⟨i, hi⟩ := T.has_unit
    cases i with
    | inl j =>
        right
        refine ⟨j, ?_⟩
        simpa only [s, w0, map_zero] using (show s j ≠ 0 from hi)
    | inr j => exact Or.inl ⟨j, decide_eq_true (show PadicInt.toZMod (D j) ≠ 0 from hi)⟩
  obtain ⟨π, ε, εCase, order⟩ := ap_residue_canonical s a nontrivial
  let u : O := if ε = 1 then 1 else -1
  have red_u : PadicInt.toZMod u = ε := by
    rcases εCase with h | h
    · simp [u, h]
    · simp [u, h, show (-1 : F) ≠ 1 by decide]
  have epsNonzero : ε ≠ 0 := by
    rcases εCase with h | h <;> simp [h]
  have uNonzero : (u : K) ≠ 0 := by
    intro h
    have uz : u = 0 := by apply Subtype.ext; exact h
    exact epsNonzero (by rw [← red_u, uz, map_zero])
  let y (i : Fin 3) := (u : K) * B.step (π i)
  have yNonzero (i : Fin 3) : y i ≠ 0 := mul_ne_zero uNonzero (B.step_nonzero bd (π i))
  let flip (i : Fin 3) := decide (lead (y i) (yNonzero i) = -1)
  let firstShift : K := if flip 0 then 3 * B.step (π 0) else 0
  let C := B.transform u (-(u : K)*(B.start (π 0) + firstShift)) π flip
  have cd : C.Disjoint := B.disjoint_transform _ _ uNonzero _ _ bd
  have cs : C.Separate := B.separate_transform _ _ uNonzero _ _ bs
  have cg : C.Geometric := B.geometric_transform _ _ _ _ bg
  let st (i : Fin 3) : O := u * (W (π i)-W (π 0) +
    (if flip i then 3*D (π i) else 0) - (if flip 0 then 3*D (π 0) else 0))
  let dt (i : Fin 3) : O := u * (if flip i then -D (π i) else D (π i))
  have st_cast (i : Fin 3) : (st i : K) = C.start i := by
    have castThree : ((3 : O) : K) = 3 := rfl
    cases f : flip i <;> cases f0 : flip 0 <;>
      simp [st, C, firstShift, transform, f, f0, W_cast, D_cast, castThree] <;> ring
  have dt_cast (i : Fin 3) : (dt i : K) = C.step i := by
    cases f : flip i <;> simp [dt, C, transform, f, D_cast]
  have st_red (i : Fin 3) : PadicInt.toZMod (st i) = ε * (s (π i) - s (π 0)) := by
    have three : (3 : F) = 0 := by decide
    have redThree : PadicInt.toZMod (3 : O) = 0 := by
      calc
        _ = (3 : F) := map_natCast (PadicInt.toZMod : O →+* F) 3
        _ = _ := three
    cases f : flip i <;> cases f0 : flip 0 <;> simp [st, f, f0, red_u, s, redThree]
  have dt_active (i : Fin 3) : decide (PadicInt.toZMod (dt i) ≠ 0) = a (π i) := by
    cases f : flip i <;> simp [dt, f, red_u, epsNonzero, a]
  have oriented (i : Fin 3) (h : C.step i ≠ 0) : lead (C.step i) h = 1 := by
    rcases lead_one_or_neg_one (y i) (yNonzero i) with plus | minus
    · have f : flip i = false := by simp [flip, plus, show (1 : F) ≠ -1 by decide]
      have eq : C.step i = y i := by simp [C, transform, f, y]
      simpa only [eq] using plus
    · have f : flip i = true := by simp [flip, minus]
      have eq : C.step i = -y i := by simp [C, transform, f, y]
      have negated := lead_negated (y i) (yNonzero i)
      rw [minus, neg_neg] at negated
      simpa only [← eq] using negated
  have startsZero : C.start 0 = 0 := by
    simp [C, transform, firstShift]
  refine ⟨C, cd, cs, cg, ⟨st, dt, st_cast, dt_cast, startsZero, ?_, oriented⟩⟩
  simpa only [st_red, dt_active] using order

end APState

end

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

abbrev Form := Fin 7 → ℤ

def formEval {R : Type*} [CommRing R] (x : Fin 7 → R) (f : Form) : R :=
  ∑ i, (f i : R) * x i

theorem formEval_sub {R : Type*} [CommRing R] (x : Fin 7 → R) (f g : Form) :
    formEval x (fun i => f i - g i) = formEval x f - formEval x g := by
  simp [formEval, sub_mul, Finset.sum_sub_distrib]

theorem formEval_mul_const {R : Type*} [CommRing R] (x : Fin 7 → R) (g : Form) (n : ℤ) :
    formEval x (fun i => n * g i) = (n : R) * formEval x g := by
  simp [formEval, mul_assoc, Finset.mul_sum]

theorem formEval_ringHom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (x : Fin 7 → R) (f : Form) : φ (formEval x f) = formEval (φ ∘ x) f := by
  simp [formEval]

def fieldVars (A : APState) (r : K) : Fin 7 → K :=
  ![A.start 0, A.start 1, A.start 2, A.step 0, A.step 1, A.step 2, r]

def pointForm (i : Fin 3) (j : Fin 4) : Form := fun k =>
  if k.val = i.val then 1 else if k.val = 3+i.val then (j.val : ℤ) else 0

def poleForm : Form := ![0,0,0,0,0,0,1]

theorem eval_pointForm (A : APState) (r : K) (i : Fin 3) (j : Fin 4) :
    formEval (A.fieldVars r) (pointForm i j) = A.point i j := by
  fin_cases i <;> simp [formEval, Fin.sum_univ_succ, pointForm, fieldVars, point]

theorem eval_poleForm (A : APState) (r : K) : formEval (A.fieldVars r) poleForm = r := by
  simp [formEval, Fin.sum_univ_succ, fieldVars, poleForm]

def location (A : APState) (r : K) (idx : Option Slot) : K := idx.elim r fun k => A.point k.1 k.2

def locationForm (idx : Option Slot) : Form := idx.elim poleForm fun k => pointForm k.1 k.2

theorem eval_locationForm (A : APState) (r : K) (idx : Option Slot) :
    formEval (A.fieldVars r) (locationForm idx) = A.location r idx := by
  cases idx with
  | none => exact eval_poleForm A r
  | some k => exact eval_pointForm A r k.1 k.2

theorem location_injective (A : APState) (r : K) (noCollisions : A.Disjoint) (outside : A.Separate)
    (root_eq : A.root = some r) : Function.Injective (A.location r) := by
  intro a b equal
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j =>
          have forbidden : A.point j.1 j.2 - r ≠ 0 := by
            simpa [denom, root_eq] using outside j.1 j.2
          exact (forbidden (sub_eq_zero.mpr equal.symm)).elim
  | some i =>
      cases b with
      | none =>
          have forbidden : A.point i.1 i.2 - r ≠ 0 := by
            simpa [denom, root_eq] using outside i.1 i.2
          exact (forbidden (sub_eq_zero.mpr equal)).elim
      | some j => exact congrArg some (noCollisions equal)

def PrimitiveCoordinates.vars {A : APState} (D : PrimitiveCoordinates A) (r : O) : Fin 7 → O :=
  ![D.starts 0, D.starts 1, D.starts 2, D.steps 0, D.steps 1, D.steps 2, r]

theorem PrimitiveCoordinates.vars_cast {A : APState} (D : PrimitiveCoordinates A) (r : O) :
    (PadicInt.Coe.ringHom ∘ D.vars r) = A.fieldVars r := by
  funext i
  fin_cases i <;> simp [PrimitiveCoordinates.vars, fieldVars, D.starts_eq, D.steps_eq]

theorem PrimitiveCoordinates.form_residue {A : APState} (D : PrimitiveCoordinates A) (r : O) (f : Form)
    (hne : formEval (A.fieldVars r) f ≠ 0) :
    let x := formEval (A.fieldVars r) f
    0 ≤ val x ∧ formEval (PadicInt.toZMod ∘ D.vars r) f = if val x = 0 then lead x hne else 0 := by
  let x := formEval (A.fieldVars r) f
  let U := formEval (D.vars r) f
  have Ucast : (U : K) = x := by
    change PadicInt.Coe.ringHom U = x
    simp only [U, formEval_ringHom, D.vars_cast, x]
  have nonneg : 0 ≤ val x := by
    rw [← Ucast]
    exact PadicInt.valuation_coe_nonneg
  have same : U = scaled x hne 0 nonneg := by
    apply Subtype.ext
    change (U : K) = x * (3 : K)^(-(0 : ℤ))
    simp [Ucast]
  refine ⟨nonneg, ?_⟩
  rw [← formEval_ringHom PadicInt.toZMod, show formEval (D.vars r) f = U from rfl, same, scaled_residue]
  simp [x, eq_comm]

def solverForm (idx : Option Slot) : Form := fun k => if k = 0 then 0 else locationForm idx k

theorem eval_solverForm (A : APState) (r : K) (startZero : A.start 0 = 0) (idx : Option Slot) :
    formEval (A.fieldVars r) (solverForm idx) = A.location r idx := by
  rw [← eval_locationForm A r idx]
  unfold formEval
  apply Finset.sum_congr rfl
  intro k _
  by_cases eq : k = 0
  · subst k
    simp [solverForm, fieldVars, startZero]
  · simp [solverForm, eq]

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private theorem int_unit_val (a : ℤ) (hr : (a : F) ≠ 0) : val (a : K) = 0 := by
  change Padic.valuation (a : K) = 0
  rw [Padic.valuation_intCast]
  have hn : ¬(3 : ℤ) ∣ a := fun hd => hr ((ZMod.intCast_zmod_eq_zero_iff_dvd a 3).2 hd)
  simp [padicValInt.eq_zero_of_not_dvd hn]

private theorem int_unit_lead (a : ℤ) (ha : (a : K) ≠ 0) (hr : (a : F) ≠ 0) :
    lead (a : K) ha = (a : F) := by
  unfold lead
  have eq : scaled (a : K) ha (val (a : K)) le_rfl = (a : O) := by
    apply Subtype.ext
    change (a : K) * (3 : K)^(-val (a : K)) = (a : K)
    rw [int_unit_val a hr]
    simp
  rw [eq, map_intCast]

private theorem pow_three_lead (k : ℕ) :
    lead ((3 : K)^k) (pow_ne_zero k (by norm_num)) = 1 := by
  unfold lead
  have vp : val ((3 : K)^k) = (k : ℤ) := by
    rw [show ((3 : K)^k) = (3 : K)^(k : ℤ) by simp]
    change Padic.valuation ((3 : K)^(k : ℤ)) = _
    rw [Padic.valuation_zpow]
    change (k : ℤ) * val (3 : K) = _
    rw [val_three, mul_one]
  have eq : scaled ((3 : K)^k) (pow_ne_zero k (by norm_num))
      (val ((3 : K)^k)) le_rfl = 1 := by
    apply Subtype.ext
    change (3 : K)^k * (3 : K)^(-val ((3 : K)^k)) = 1
    rw [vp, zpow_neg]
    rw [zpow_natCast, mul_inv_cancel₀ (pow_ne_zero k (by norm_num))]
  rw [eq, map_one]

theorem int_factor_val_lead (a b : ℤ) (k : ℕ) (hfactor : a = (3 : ℤ)^k * b)
    (ha : (a : K) ≠ 0) (hr : (b : F) ≠ 0) :
    val (a : K) = (k : ℤ) ∧ lead (a : K) ha = (b : F) := by
  subst a
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat] at ha ⊢
  have hk : (3 : K)^k ≠ 0 := pow_ne_zero k (by norm_num)
  have hb : (b : K) ≠ 0 := right_ne_zero_of_mul ha
  constructor
  · rw [val_mul hk hb, int_unit_val b hr]
    rw [show ((3 : K)^k) = (3 : K)^(k : ℤ) by simp]
    change Padic.valuation ((3 : K)^(k : ℤ)) + 0 = _
    rw [Padic.valuation_zpow]
    change (k : ℤ) * val (3 : K) + 0 = _
    rw [val_three, mul_one, add_zero]
  · rw [lead_mul _ _ hk hb, pow_three_lead k, int_unit_lead b hb hr, one_mul]

private theorem signed_unit_mul (s a b : F) (hs : s ≠ 0) (ha : a ≠ 0)
    (hb : b = 1 ∨ b = -1) :
    (s * (b * a) = -1 ↔ if b = -1 then ¬(s*a = -1) else s*a = -1) := by
  revert s a b
  decide +kernel

theorem int_factor_scaled_mul (a b : ℤ) (k : ℕ) (x : K) (s : F)
    (hfactor : a = (3 : ℤ)^k * b) (ha : (a : K) ≠ 0) (hx : x ≠ 0) (hs : s ≠ 0)
    (hr : (b : F) = 1 ∨ (b : F) = -1) :
    val ((a : K)*x) = val x + (k : ℤ) ∧
      (s * lead ((a : K)*x) (mul_ne_zero ha hx) = -1 ↔
        if (b : F) = -1 then ¬(s * lead x hx = -1) else s * lead x hx = -1) := by
  have hbn : (b : F) ≠ 0 := by rcases hr with h|h <;> rw [h] <;> decide
  obtain ⟨hv, hl⟩ := int_factor_val_lead a b k hfactor ha hbn
  constructor
  · rw [val_mul ha hx, hv, add_comm]
  · rw [lead_mul _ _ ha hx, hl]
    exact signed_unit_mul s _ _ hs (lead_ne_zero _ hx) hr

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

abbrev ResidueRow := Int × Int × Int × Int
def rowDot (x y : ResidueRow) : Int :=
  x.1*y.1 + x.2.1*y.2.1 + x.2.2.1*y.2.2.1 + x.2.2.2*y.2.2.2

def residueFacts (v : Int) (u : Prop) (r : Int) : Prop :=
  if r = 0 then 0 < v else v = 0 ∧ (if r = 1 then ¬u else u)

abbrev PackedTerm := Nat × Int × Bool
abbrev PackedTriad := PackedTerm × PackedTerm × PackedTerm

def packedVal (v : Nat → Int) (f : PackedTerm) : Int := v f.1 + f.2.1

def packedUnit (u : Nat → Prop) (f : PackedTerm) : Prop :=
  if f.2.2 then ¬u f.1 else u f.1

def packedTriad (v : Nat → Int) (u : Nat → Prop) (triad : PackedTriad) : Prop :=
  let (a, b, c) := triad
  let va := packedVal v a
  let vb := packedVal v b
  let vc := packedVal v c
  let ua := packedUnit u a
  let ub := packedUnit u b
  let uc := packedUnit u c
  (va = vb ∧ va < vc ∧ ¬(ua ↔ ub)) ∨
    (va = vc ∧ va < vb ∧ ¬(ua ↔ uc)) ∨
    (vb = vc ∧ vb < va ∧ ¬(ub ↔ uc)) ∨
    (va = vb ∧ va = vc ∧ (ua ↔ ub) ∧ (ua ↔ uc))
def normalizedOverlapResidues : Array ResidueRow :=
  #[(1,0,0,0), (1,0,0,1), (1,0,0,2), (1,0,1,0), (1,0,1,1), (1,0,1,2), (1,0,2,0), (1,0,2,1), (1,0,2,2), (1,1,0,0), (1,1,0,1), (1,1,0,2), (1,1,1,0), (1,1,1,1), (1,1,1,2), (1,1,2,0), (1,1,2,1), (1,1,2,2), (1,2,0,0), (1,2,0,1), (1,2,0,2), (1,2,1,0), (1,2,1,1), (1,2,1,2), (1,2,2,0), (1,2,2,1), (1,2,2,2), (0,1,0,0), (0,1,0,1), (0,1,0,2), (0,1,1,0), (0,1,1,1), (0,1,1,2), (0,1,2,0), (0,1,2,1), (0,1,2,2), (0,0,1,0), (0,0,1,1), (0,0,1,2), (0,0,0,1)]

def overlapForms00 : Array ResidueRow :=
  #[(0,0,0,1), (0,0,1,0), (0,0,1,1), (0,0,2,1), (0,0,3,1), (0,1, -3, -1), (0,1, -2, -1), (0,1, -1, -1), (0,1,0, -1), (0,1,0,0), (0,2, -3, -1), (0,2, -2, -1), (0,2, -1, -1), (0,2,0, -1), (0,3, -3, -1), (0,3, -2, -1), (0,3, -1, -1), (0,3,0, -1), (1, -3,0,0), (1, -2,0,0), (1, -1,0,0), (1,0, -3, -1), (1,0, -2, -1), (1,0, -1, -1), (1,0,0, -1), (1,0,0,0), (2, -3,0,0), (2, -1,0,0), (2,0, -3, -1), (2,0, -2, -1), (2,0, -1, -1), (2,0,0, -1), (3, -2,0,0), (3, -1,0,0), (3,0, -3, -1), (3,0, -2, -1), (3,0, -1, -1), (3,0,0, -1)]

def overlapResidue00 (a k : Nat) : Int :=
  rowDot overlapForms00[k]! normalizedOverlapResidues[a]! % 3

@[simp] def overlapLane (word position : Nat) : Nat := word / 2048^position % 2048
@[simp] def overlapIndex (lane : Nat) : Nat := lane % 64
@[simp] def overlapMultiplier (lane : Nat) : Int := ((lane / 64 : Nat) : Int) - 10
@[simp] def overlapOffset (multiplier : Int) : Nat :=
  if multiplier % 9 = 0 then 2 else if multiplier % 3 = 0 then 1 else 0
@[simp] def overlapUnitPart (multiplier : Int) : Int :=
  multiplier / (3 : Int)^(overlapOffset multiplier)
@[simp] def overlapNegative (multiplier : Int) : Bool :=
  decide (overlapUnitPart multiplier % 3 = 2)
@[simp] def overlapDecodedTerm (lane : Nat) : PackedTerm :=
  (overlapIndex lane, overlapOffset (overlapMultiplier lane), overlapNegative (overlapMultiplier lane))
@[simp] def overlapDecodedTriad (word : Nat) : PackedTriad :=
  (overlapDecodedTerm (overlapLane word 0), overlapDecodedTerm (overlapLane word 1),
    overlapDecodedTerm (overlapLane word 2))

def overlapEncodedTriads00 : Array Nat := #[2434404864,2430079552,2165971520,2472036928,2488945216,2547567168,2572864064,2425752256,2430077632,2434403008,2966426304,3238927040,
  2463644352,2455126720,2472035008,3025029824,3008383680,2207931072,2220518080,2539174592,2522268352,2547565248,3108948672,3083913920,
  2291854016,2304441024,2970489600,2476358400,2488943360,2560277248,2572862208,2429948609,2434144961,2442537665,2446734017,2450930369,
  2463519425,2467715777,2471912129,2480304833,2484501185,2488697537,2509679297,2513875649,2518072001,2539053761,2543250113,2547446465,
  2564231873,2568428225,2572624577,2434142977,2446732033,2450928385,2467713793,2471910145,2484499201,2488695553,2513873665,2518070017,
  2543248129,2547444481,2568426241,2572622593,2450926401,2471908161,2488693569,2518068033,2547442497,2572620609,2434275906,2467842626,
  2484750914,2543372866,2568669762,2970622658,2459448002,2455124674,2467838658,3020835522,3004189378,2216321730,2534978242,2522266306,
  2543368898,3104754370,3079719618,2300244674,2484747010,2568665858,2463648323,2480556611,2539178563,2564475459,2455122627,2463642307,
  2472032963,3016641219,2999995075,2212125379,2522264259,2539172547,2547563203,3100560067,3075525315,2296048323,2480550659,2564469507,
  2459454020,2476362308,2534984260,2560281156,2455120580,2459445956,2467836612,3012446916,2995800772,2207929028,2220516036,2522262212,
  2534976196,2543366852,3096365764,3071331012,2291851972,2304438980,2476354308,2488939268,2560273156,2572858116,2451190277,2446864965,
  2182756933,2476233285,2484623941,2983211717,3255712453,2459323077,2476231365,3012580037,3020970693,2505482949,2534857413,2560035525,
  2987275013,2451061318,2480429638,2488820294,2987408070,2463517382,2480425670,3016776390,3025167046,2509677254,2539051718,2564229830,
  2476235335,2484625991,2467711687,2484619975,3012582087,3020972743,2513871559,2543246023,2568424135,2480431688,2488822344,2471905992,
  2488814280,3016778440,3025169096,2518065864,2547440328,2572618440,2526595529,2551892489,2526585417,2530789961,2556086857,2283461193,
  2476102345,2480298697,2484495049,2488691401,2497090249,2501286601,2526583497,3062932169,2522260169,2530779849,2551882441,3092171465,
  3067136713,3356416713,2287655625,2555839177,2501284617,2522258185,2556076809,3087977225,2530661129,2522256201,2526581577,2530777929,
  3062942537,2551880585,2530776009,2556074953,2283459529,2551878729,2287653961,2556073097,2472172042,2467846730,2203738698,3004193482,
  3276694218,2505480906,2534974154,2560033482,3008256778,2472043083,3008389835,2509675211,2539168459,2564227787,2513869516,2543362764,
  2568422092,2518063821,2547557069,2572616397,2488957454,2484632142,2220524110,3020978894,3293479630,2505478862,2560271054,2534855374,
  3025042190,2488828495,3025175247,2509673167,2564465359,2539049679,2513867472,2568659664,2543243984,2518061777,2572853969,2547438289,
  2522520082,2501417554,2526714450,2254086738,3062799058,3037764306,3355878098,3335168722,3092030162,3327042258,2258281170,2526464722,
  1994312402,2019871442,3058604818,2015546130,3066731346,2530922899,2522391123,2530910803,3087835859,3066995411,3058737875,2526454483,
  2551761619,2262485715,2287913683,3628784339,2015156947,3091899155,2258029395,3092828372,3088503124,3067531668,3063335380,2555970004,
  2555959892,2530659028,2555955924,3092306644,2551634644,2551630612,2526202708,3092317012,2518331925,2514006613,2249898581,2560156245,
  2568546901,3050353365,3322854101,2534853333,2560150229,3096502997,3104893653,3054416661,2518202966,2564352598,2572743254,3054549718,
  2539047638,2564344534,3100699350,3109090006,2560158295,2568548951,2543241943,2568538839,3096505047,3104895703,2564354648,2572745304,
  2547436248,2572733144,3100701400,3109092056,2551765593,3088112345,2555828953,2560025305,2564221657,2568418009,2572614361,2287403865,
  1993790361,2014893017,2018956377,3092709851,2555577179,2547706396,2543381084,2279273052,3079727836,3352228572,3083791132,2547577437,
  3083924189,2572884514,2568559202,2304451170,3104905954,3377406690,3108969250,2572755555,3109102307]

def overlapTriads00 (k : Nat) : PackedTriad := overlapDecodedTriad overlapEncodedTriads00[k]!

def overlapRules00 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop) : Nat → Prop
  | 0 => ((v 0) ≥ 0)
  | 1 => ((v 1) ≥ 0)
  | 2 => ((v 2) ≥ 0)
  | 3 => ((v 3) ≥ 0)
  | 4 => ((v 4) ≥ 0)
  | 5 => ((v 5) ≥ 0)
  | 6 => ((v 6) ≥ 0)
  | 7 => ((v 7) ≥ 0)
  | 8 => ((v 8) ≥ 0)
  | 9 => ((v 9) ≥ 0)
  | 10 => ((v 10) ≥ 0)
  | 11 => ((v 11) ≥ 0)
  | 12 => ((v 12) ≥ 0)
  | 13 => ((v 13) ≥ 0)
  | 14 => ((v 14) ≥ 0)
  | 15 => ((v 15) ≥ 0)
  | 16 => ((v 16) ≥ 0)
  | 17 => ((v 17) ≥ 0)
  | 18 => ((v 18) ≥ 0)
  | 19 => ((v 19) ≥ 0)
  | 20 => ((v 20) ≥ 0)
  | 21 => ((v 21) ≥ 0)
  | 22 => ((v 22) ≥ 0)
  | 23 => ((v 23) ≥ 0)
  | 24 => ((v 24) ≥ 0)
  | 25 => ((v 25) ≥ 0)
  | 26 => ((v 26) ≥ 0)
  | 27 => ((v 27) ≥ 0)
  | 28 => ((v 28) ≥ 0)
  | 29 => ((v 29) ≥ 0)
  | 30 => ((v 30) ≥ 0)
  | 31 => ((v 31) ≥ 0)
  | 32 => ((v 32) ≥ 0)
  | 33 => ((v 33) ≥ 0)
  | 34 => ((v 34) ≥ 0)
  | 35 => ((v 35) ≥ 0)
  | 36 => ((v 36) ≥ 0)
  | 37 => ((v 37) ≥ 0)
  | 38 => (((v 25) = 0) ∨ ((v 9) = 0) ∨ ((v 1) = 0) ∨ ((v 0) = 0))
  | 39 => (((t0 < 0) ∧ (t0 = t1) ∧ ¬(k0 ↔ k1)) ∨ ((t0 = 0) ∧ (t1 > 0) ∧ (¬k0)) ∨ ((t0 > 0) ∧ (t1 = 0) ∧ (¬k1)) ∨ ((t0 = 0) ∧ (t1 = 0) ∧ k0 ∧ k1))
  | 40 => ((((((v 0) + 0) + ((v 3) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 4) + 0) + ((v 2) + 0) + ((v 9) + 1)) - t0) + (((v 31) + 0) + ((v 29) + 0) + ((v 27) + 0) + ((v 20) + 0) + ((v 28) + 0) + ((v 30) + 0) + ((v 26) + 0))) = (2 * (((v 24) + 0) + ((v 22) + 0) + ((v 20) + 0) + ((v 19) + 0) + ((v 21) + 0) + ((v 23) + 0) + ((v 18) + 0))))
  | 41 => ((¬((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 0)))) ↔ (¬(u 3)))) ↔ (¬(u 9)))) ↔ (u 9))) ↔ (¬(u 4)))) ↔ (¬(u 2)))) ↔ (¬(u 9)))) ↔ k0)) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 31))) ↔ (u 29))) ↔ (u 27))) ↔ (¬(u 20)))) ↔ (u 28))) ↔ (u 30))) ↔ (u 26))))
  | 42 => (((((v 24) + 0) + ((v 22) + 0) + ((v 20) + 0) + ((v 19) + 0) + ((v 21) + 0) + ((v 23) + 0) + ((v 18) + 0)) + (((v 37) + 0) + ((v 35) + 0) + ((v 33) + 0) + ((v 32) + 0) + ((v 34) + 0) + ((v 36) + 0) + ((v 20) + 1))) = (2 * (((v 31) + 0) + ((v 29) + 0) + ((v 27) + 0) + ((v 20) + 0) + ((v 28) + 0) + ((v 30) + 0) + ((v 26) + 0))))
  | 43 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 24))) ↔ (u 22))) ↔ (u 20))) ↔ (u 19))) ↔ (u 21))) ↔ (u 23))) ↔ (u 18))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 37))) ↔ (u 35))) ↔ (u 33))) ↔ (u 32))) ↔ (u 34))) ↔ (u 36))) ↔ (u 20))))
  | 44 => ((((((v 0) + 0) + ((v 3) + 0) + ((v 25) + 0) + ((v 25) + 1) + ((v 4) + 0) + ((v 25) + 0) + ((v 2) + 0)) - t1) + (((v 13) + 0) + ((v 11) + 0) + ((v 20) + 0) + ((v 32) + 0) + ((v 10) + 0) + ((v 19) + 0) + ((v 12) + 0))) = (2 * (((v 8) + 0) + ((v 6) + 0) + ((v 27) + 0) + ((v 33) + 0) + ((v 5) + 0) + ((v 20) + 0) + ((v 7) + 0))))
  | 45 => ((¬((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 0)))) ↔ (¬(u 3)))) ↔ (u 25))) ↔ (¬(u 25)))) ↔ (¬(u 4)))) ↔ (¬(u 25)))) ↔ (¬(u 2)))) ↔ k1)) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 13))) ↔ (u 11))) ↔ (u 20))) ↔ (¬(u 32)))) ↔ (u 10))) ↔ (¬(u 19)))) ↔ (u 12))))
  | 46 => (((((v 8) + 0) + ((v 6) + 0) + ((v 27) + 0) + ((v 33) + 0) + ((v 5) + 0) + ((v 20) + 0) + ((v 7) + 0)) + (((v 17) + 0) + ((v 15) + 0) + ((v 26) + 0) + ((v 20) + 1) + ((v 14) + 0) + ((v 18) + 0) + ((v 16) + 0))) = (2 * (((v 13) + 0) + ((v 11) + 0) + ((v 20) + 0) + ((v 32) + 0) + ((v 10) + 0) + ((v 19) + 0) + ((v 12) + 0))))
  | 47 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 8))) ↔ (u 6))) ↔ (¬(u 27)))) ↔ (¬(u 33)))) ↔ (u 5))) ↔ (¬(u 20)))) ↔ (u 7))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 17))) ↔ (u 15))) ↔ (¬(u 26)))) ↔ (¬(u 20)))) ↔ (u 14))) ↔ (¬(u 18)))) ↔ (u 16))))
  | 48 => (((((v 8) + 0) + ((v 0) + 0) + ((v 31) + 0) + ((v 13) + 0) + ((v 37) + 0) + ((v 24) + 0) + ((v 17) + 0)) + (((v 6) + 0) + ((v 3) + 0) + ((v 29) + 0) + ((v 11) + 0) + ((v 35) + 0) + ((v 22) + 0) + ((v 15) + 0))) = (2 * (((v 7) + 0) + ((v 2) + 0) + ((v 30) + 0) + ((v 12) + 0) + ((v 36) + 0) + ((v 23) + 0) + ((v 16) + 0))))
  | 49 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 8)))) ↔ (u 0))) ↔ (¬(u 31)))) ↔ (¬(u 13)))) ↔ (¬(u 37)))) ↔ (¬(u 24)))) ↔ (¬(u 17)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 6)))) ↔ (u 3))) ↔ (¬(u 29)))) ↔ (¬(u 11)))) ↔ (¬(u 35)))) ↔ (¬(u 22)))) ↔ (¬(u 15)))))
  | 50 => (((((v 7) + 0) + ((v 2) + 0) + ((v 30) + 0) + ((v 12) + 0) + ((v 36) + 0) + ((v 23) + 0) + ((v 16) + 0)) + (((v 5) + 0) + ((v 4) + 0) + ((v 28) + 0) + ((v 10) + 0) + ((v 34) + 0) + ((v 21) + 0) + ((v 14) + 0))) = (2 * (((v 6) + 0) + ((v 3) + 0) + ((v 29) + 0) + ((v 11) + 0) + ((v 35) + 0) + ((v 22) + 0) + ((v 15) + 0))))
  | 51 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 7)))) ↔ (u 2))) ↔ (¬(u 30)))) ↔ (¬(u 12)))) ↔ (¬(u 36)))) ↔ (¬(u 23)))) ↔ (¬(u 16)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 5)))) ↔ (u 4))) ↔ (¬(u 28)))) ↔ (¬(u 10)))) ↔ (¬(u 34)))) ↔ (¬(u 21)))) ↔ (¬(u 14)))))
  | k => if k < 409 then packedTriad v u (overlapTriads00 (k-52)) else True

private def overlapCores00 : Array (List Nat × List Nat × List Nat × List Nat) :=
  #[([],[18,19,20,21,22,23,24],[26,27,28,29,30,31],[42,310,312,351,352,361,362]),
   ([],[18,19,20,28,29,30,31],[5,6,7,8,26,27,34,35,36,37],[42,193,205,214,223,310,312]),
   ([32],[5,6,7,8,14,15,16,17,18,19,20,25,34,35,36,37],[0,2,21,22,23,24,26,27],[42,43,47,57,71,125,134,339]),
   ([],[1,2,6,11,15,18,19,20,21,24,30,35],[3,7,12,16,22,26,27,28,31,36],[42,48,71,87,90,93,102,310,312,372]),
   ([],[0,1,4,7,12,16,18,19,20,22,28,31,36],[2,5,8,10,13,14,17,23,26,27,29,34,37],[42,48,50,53,64,85,91,100,310,312,374]),
   ([],[1,3,5,8,10,13,14,17,18,19,20,23,25,29,34,37],[0,4,6,11,15,21,24,26,27,30,35],[42,46,48,50,59,86,89,92,101,162,339]),
   ([5],[3,7,12,16,18,19,20,21,24,29,36],[2,6,11,15,23,26,27,28,31,35],[42,50,128,173,208,310,312,351,362]),
   ([],[0,4,6,11,15,18,19,20,23,28,31,35],[1,3,5,8,10,13,14,17,22,26,27,30,34,37],[42,48,50,59,86,89,92,101,310,312,352]),
   ([],[2,5,8,10,13,14,17,18,19,20,22,25,30,34,37],[0,1,4,7,12,16,21,24,26,27,29,36],[42,46,48,50,53,57,64,85,91,100,339]),
   ([],[5,6,7,8,18,21,22,23,24,27,32],[19,26,28,29,30,31,33],[42,195,207,216,225]),
   ([],[10,11,12,13,18,27,28,29,30,31,32],[19,26,33,34,35,36,37],[42,269,275,278,281]),
   ([],[18,27,32,34,35,36,37],[19,21,22,23,24,26,33],[42]),
   ([],[1,2,5,8,9,12,15,18,21,24,25,27,30,32,35],[3,6,10,13,16,19,22,26,28,31,33,36],[42,46,48,50,58,71,93,161,177,195,208]),
   ([5],[0,1,4,6,10,13,16,18,22,27,28,31,32,36],[2,7,11,14,17,19,23,26,29,33,34,37],[42,46,48,50,91,100,217,269,374]),
   ([],[1,3,7,11,14,17,18,23,25,27,29,32,34,37],[0,4,5,8,12,15,19,21,24,26,30,33,35],[42,46,48,50,57,59,85,92,162]),
   ([],[3,5,8,9,11,16,18,21,24,27,29,32,36],[1,2,7,10,13,15,19,23,26,28,31,33,35],[42,46,48,50,54,56,76,102,173,185,199]),
   ([],[0,4,7,10,13,15,18,23,27,28,31,32,35],[1,3,6,12,14,17,19,22,26,30,33,34,37],[42,46,48,50,87,92,96,101,186,352]),
   ([],[2,6,9,12,14,17,18,22,25,27,30,32,34,37],[0,4,5,8,11,16,19,21,24,26,29,33,36],[42,46,48,50,53,55,57,128,134]),
   ([],[10,11,12,13,18,21,22,23,24,33],[5,6,7,8,20,26,28,29,30,31,32],[42,46,185,186,195,198,199,207,216,225,331]),
   ([],[0,2,3,4,5,6,7,8,18,25,28,29,30,31,33],[9,14,15,16,17,20,26,32,34,35,36,37],[39,40,42,44,46,55,64,123,128,236]),
   ([],[14,15,16,17,18,25,33,34,35,36,37],[0,2,3,4,9,10,11,12,13,20,21,22,23,24,26,32],[39,40,43,44,45,46,57,71,125,134,229]),
   ([4],[1,2,7,10,13,15,18,21,24,30,33,35],[3,5,8,9,11,16,20,22,26,28,31,32,36],[42,46,48,50,56,71,121,185,199,206,302,321]),
   ([],[0,1,4,5,8,11,16,18,22,25,28,31,33,36],[2,6,9,12,14,17,20,23,26,29,32,34,37],[39,40,42,44,46,48,50,53,91,215,255,269,281,350]),
   ([2],[1,3,6,12,14,17,18,23,25,29,33,34,37],[0,4,7,9,10,13,15,20,21,24,26,30,32,35],[39,40,42,44,46,48,116,120,126,134,194,255,275]),
   ([14],[3,6,10,13,16,18,21,24,25,29,33,36],[2,5,8,12,15,20,23,26,28,31,32,35],[42,46,48,50,74,170,173,174,208,215,290,331,403]),
   ([],[0,4,5,8,12,15,18,23,25,28,31,33,35],[1,3,7,9,11,14,17,20,22,26,30,32,34,37],[39,40,42,44,46,48,50,55,59,119,206,236,269,352]),
   ([],[2,7,11,14,17,18,22,25,30,33,34,37],[0,1,4,6,9,10,13,16,20,21,24,26,29,32,36],[39,40,42,44,46,48,50,53,100,194,224,278,331,395]),
   ([18],[5,6,7,8,9,19,32],[10,11,12,13,20,27,33],[46,185,186,198,199,228]),
   ([5,6,7,8,18],[9,10,11,12,13,19,32],[14,15,16,17,20,27,33],[46,228]),
   ([],[9,14,15,16,17,19,21,22,23,24,32,34,35,36,37],[0,2,5,6,7,8,20,27,33],[43,46,47,55,64,123,128,254]),
   ([18],[1,2,5,8,9,12,15,19,22,29,32,35],[3,6,10,13,16,20,23,27,30,33,36],[46,48,64,93,96,99,102,208,228]),
   ([5,18],[0,1,4,6,9,10,13,16,19,23,30,32,36],[2,7,11,14,17,20,21,24,27,28,31,33,34,37],[46,48,50,91,221,228]),
   ([],[1,3,7,9,11,14,17,19,21,24,28,31,32,34,37],[0,4,5,8,12,15,20,22,27,29,33,35],[42,46,48,50,59,92,95,98,101,160,306]),
   ([18],[3,5,8,9,11,16,19,23,30,32,36],[2,7,10,13,15,20,22,27,29,33,35],[46,50,134,166,185,193,195,199,228]),
   ([18],[0,4,7,9,10,13,15,19,22,29,32,35],[1,3,6,12,14,17,20,21,24,27,28,31,33,34,37],[42,46,48,50,59,92,98,186,228]),
   ([],[2,6,9,12,14,17,19,21,24,28,31,32,34,37],[0,1,4,5,8,11,16,20,23,27,30,33,36],[42,46,48,50,53,55,71,91,94,100,306]),
   ([0],[1,2,6,11,15,22,29,35],[3,7,12,16,23,30,36],[48,87,90,93,96,99,102]),
   ([],[4,7,12,16,23,30,36],[2,5,10,14,21,28,34],[51]),
   ([],[3,8,13,17,24,31,37],[0,6,11,15,22,29,35],[49]),
   ([],[],[5,6,7,8,10,11,12,13,14,15,16,17,21,22,23,24,28,29,30,31,34,35,36,37],[42,43,46,308,309,322,325,330,392])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapResidueData00 :
    (List.range 40).all (fun a =>
      let c := overlapCores00[a]!
      c.1.all (fun k => decide (k < 38 ∧ overlapResidue00 a k = 0)) &&
      c.2.1.all (fun k => decide (k < 38 ∧ overlapResidue00 a k = 1)) &&
      c.2.2.1.all (fun k => decide (k < 38 ∧ overlapResidue00 a k = 2))) = true := by
  decide

private theorem classifyResidues00 (v : Nat → Int) (u : Nat → Prop) (a : Nat) (ha : a < 40)
    (hres : ∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) :
    let c := overlapCores00[a]!
    (∀ k ∈ c.1,0 < v k) ∧ (∀ k ∈ c.2.1, v k = 0 ∧ ¬u k) ∧
    (∀ k ∈ c.2.2.1, v k = 0 ∧ u k) := by
  let c := overlapCores00[a]!
  have h := List.all_eq_true.mp overlapResidueData00 a (List.mem_range.mpr ha)
  obtain ⟨hzo, ht⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hz, ho⟩ := Bool.and_eq_true_iff.mp hzo
  have ds0 : ∀ k ∈ c.1,0 < v k := by
    intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp hz k hk)
    simpa [residueFacts, hval] using hres k bound
  have ds1 : ∀ k ∈ c.2.1, v k = 0 ∧ ¬u k := by
    intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ho k hk)
    simpa [residueFacts, hval] using hres k bound
  have ds2 : ∀ k ∈ c.2.2.1, v k = 0 ∧ u k := by
    intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ht k hk)
    simpa [residueFacts, hval] using hres k bound
  exact ⟨ds0, ds1, ds2⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible00Group0 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules00 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 0 ≤ a) (ghi : a < 10)
    (hres : ∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) : False := by
  let c := overlapCores00[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues00 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules00 v u t0 t1 k0 k1 k := fun k _ => rules k
  clear hres rules
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores00, c, List.forall_mem_cons] at ds0 ds1 ds2 rv
    all_goals
      simp [overlapEncodedTriads00, overlapRules00, overlapTriads00, packedTriad, packedVal, packedUnit] at rv
      all_goals
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (splits:=30) (liaSteps:=20000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible00Group1 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules00 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 10 ≤ a) (ghi : a < 18)
    (hres : ∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) : False := by
  let c := overlapCores00[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues00 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules00 v u t0 t1 k0 k1 k := fun k _ => rules k
  clear hres rules
  rcases (show a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores00, c, List.forall_mem_cons] at ds0 ds1 ds2 rv
    all_goals
      simp [overlapEncodedTriads00, overlapRules00, overlapTriads00, packedTriad, packedVal, packedUnit] at rv
      all_goals
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (splits:=30) (liaSteps:=20000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible00Group2 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules00 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 18 ≤ a) (ghi : a < 27)
    (hres : ∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) : False := by
  let c := overlapCores00[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues00 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules00 v u t0 t1 k0 k1 k := fun k _ => rules k
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬ u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  clear hres rules
  rcases (show a = 18 ∨ a = 19 ∨ a = 20 ∨ a = 21 ∨ a = 22 ∨ a = 23 ∨ a = 24 ∨ a = 25 ∨ a = 26 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores00, c] at ds0 rv
    all_goals
      simp [overlapEncodedTriads00, overlapRules00, overlapTriads00, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        clear v1 b1 v2 b2 ds1 ds2
        try clear c ha
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (ring := false) (ematch := 0) (splits:=30) (liaSteps:=30000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible00Group3 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules00 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 27 ≤ a) (ghi : a < 40)
    (hres : ∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) : False := by
  let c := overlapCores00[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues00 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules00 v u t0 t1 k0 k1 k := fun k _ => rules k
  clear hres rules
  rcases (show a = 27 ∨ a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 ∨ a = 32 ∨ a = 33 ∨ a = 34 ∨ a = 35 ∨ a = 36 ∨ a = 37 ∨ a = 38 ∨ a = 39 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores00, c, List.forall_mem_cons] at ds0 ds1 ds2 rv
    all_goals
      simp [overlapEncodedTriads00, overlapRules00, overlapTriads00, packedTriad, packedVal, packedUnit] at rv
      all_goals
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (splits:=30) (liaSteps:=20000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem overlapImpossible00 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules00 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40)
    (hres : ∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) : False := by
  by_cases h0 : a < 10
  · exact overlapImpossible00Group0 v u t0 t1 k0 k1 rules a ha (by omega) h0 hres
  by_cases h1 : a < 18
  · exact overlapImpossible00Group1 v u t0 t1 k0 k1 rules a ha (by omega) h1 hres
  by_cases h2 : a < 27
  · exact overlapImpossible00Group2 v u t0 t1 k0 k1 rules a ha (by omega) h2 hres
  exact overlapImpossible00Group3 v u t0 t1 k0 k1 rules a ha (by omega) ha hres

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

def overlapForms01 : Array ResidueRow :=
  #[(0,0,0,1), (0,0,1,0), (0,0,1,1), (0,0,2,1), (0,0,3,1), (0,1, -3, -1), (0,1, -2, -1), (0,1, -1, -1), (0,1,0, -1), (0,1,0,0), (0,1,0,1), (0,1,1,1), (0,1,2,1), (0,1,3,1), (0,2, -3, -1), (0,2, -2, -1), (0,2, -1, -1), (0,2,0, -1), (1, -2,0,0), (1, -1,0,0), (1,0, -3, -1), (1,0, -2, -1), (1,0, -1, -1), (1,0,0, -1), (1,0,0,0), (1,1,0,0), (2, -1,0,0), (2,0, -3, -1), (2,0, -2, -1), (2,0, -1, -1), (2,0,0, -1), (2,1,0,0), (3, -2,0,0), (3, -1,0,0), (3,0, -3, -1), (3,0, -2, -1), (3,0, -1, -1), (3,0,0, -1), (3,1,0,0)]

def overlapResidue01 (a k : Nat) : Int :=
  rowDot overlapForms01[k]! normalizedOverlapResidues[a]! % 3

def overlapEncodedTriads01 : Array Nat := #[2488816064,2434404864,2430079552,2165971520,2488814144,2543370816,2572862016,2425752256,2430077632,2434403008,2966426304,3238927040,
  2480421568,2455126720,2488812224,3025160896,2459323072,2534978240,2518072000,2543368896,3108946624,3079717568,2291851968,2304438976,
  2970489600,2459321088,2560275200,2572860160,3025163072,2429948609,2434144961,2442537665,2446734017,2450930369,2463519425,2467715777,
  2471912129,2480304833,2484501185,2488697537,2505482945,2509679297,2513875649,2534857409,2539053761,2543250113,2564231873,2568428225,
  2572624577,2434142977,2446732033,2450928385,2467713793,2471910145,2484499201,2488695553,2509677313,2513873665,2539051777,2543248129,
  2568426241,2572622593,2450926401,2471908161,2488693569,2513871681,2543246145,2572620609,2476233154,2484623810,2434275906,2484619842,
  2539176514,2568667714,2970622658,2476225218,2455124674,2484615874,3020966594,2463517378,2530781890,2518069954,2539172546,3104752322,
  3075523266,2300242626,2459316994,2463513346,2467709698,2568663810,3012580162,3020970818,2480431555,2488822211,2480425539,2534982211,
  2564473411,2455122627,2480419523,2488810179,3016772291,2467711683,2518067907,2534976195,2543366851,3100558019,3071328963,2296046275,
  2463509251,2467705603,2471901955,2564467459,3016778563,3025169219,2476239300,2476231236,2530787908,2560279108,2455120580,2476223172,
  2484613828,3012577988,2471905988,2518065860,2530779844,2539170500,3096363716,3067134660,2291849924,2304436932,2471897860,2560271108,
  2572856068,3012586308,2451190277,2446864965,2182756933,2472036933,2983211717,3255712453,3008383685,2476100293,2501286597,2530661061,
  2560035525,2987275013,2207673157,2451061318,2467842630,2987408070,3004189382,2480294598,2505480902,2534855366,2564229830,2207667014,
  2211865414,2463648327,2999995079,2484488903,2509675207,2539049671,2568424135,2216057671,2220256071,2459454024,2995800776,2488683208,
  2513869512,2543243976,2572618440,2220249928,2283469001,2551892297,2287663433,2556086665,3025555913,3021363657,3017171401,3012979145,
  2526595529,2551890441,2577058313,2526593609,2556084809,2547567177,2283459145,2308635209,2497090249,2518063817,2526583497,2551880393,
  3092169417,3062940361,2522268361,2547565257,2577056457,3083913929,3356414665,2287653577,3381590729,2555839177,2518061833,2522258185,
  2556074761,3087975177,3113143049,2547438345,2576812809,2488423241,2484230985,2480038729,2475846473,2522256201,2526581577,2547555145,
  3062942537,2576810825,2551878537,2577046409,2547553225,2556072905,2308625353,2577044553,2472172042,2467846730,2203738698,3004193482,
  3276694218,2522266314,2547446474,2576820938,3008256778,2472043083,3008389835,2522264267,2547444427,2576818891,2522262220,2547442380,
  2576816844,2522260173,2547440333,2576814797,2488957454,2484632142,2220524110,3020978894,3293479630,2501284558,2530777806,2560033486,
  3025042190,2488828495,3025175247,2505478863,2534972111,2564227791,2509673168,2539166416,2568422096,2513867473,2543360721,2572616401,
  2522520082,2518194770,2526714450,2254094930,3087833810,3062799058,3054541522,3381052114,3351954130,3327050450,2551759570,2258289362,
  2287911634,2526464722,2011089618,3628782290,2015154898,2555837138,3091897106,3058604818,2040711954,3083508562,2547700115,2555970003,
  2576943571,2522399315,2547696211,2555957843,3113009875,3083780819,3058746067,2526462675,2555953875,2576927443,2279262931,3092304595,
  2551632595,2040330963,2551628563,2555824915,2258029395,3092317011,3113290579,2283195347,2019097555,2014772307,2514135572,2509810260,
  2245702228,2560154196,2568544852,3046157012,3318657748,2530656980,2560148180,3096500948,3104891604,3050220308,2514006613,2564350549,
  2572741205,3050353365,2534851285,2564342485,3100697301,3109087957,2560156246,2568546902,2539045590,2568536790,3096502998,3104893654,
  2564352599,2572743255,2543239895,2572731095,3100699351,3109090007,3382116440,3088644312,3113683224,3088632152,3113668952,3092707672,
  3092695448,3084308888,3063335384,2551763544,2547436248,3088110296,2555826904,2560023256,2564219608,2568415960,2572612312,2576808664,
  2576796440,2526202712,2287403864,2576939609,3624587993,2019349209,3113286361,2308377433,2010567577,2040058841,3092709850,2555577178,
  2543510043,2539184731,2275076699,3075531483,3348032219,3079594779,2543381084,3079727836,2577074720,3113159456,2572884514,2568559202,
  2304451170,3104905954,3377406690,3108969250,2572755555,3109102307]

def overlapTriads01 (k : Nat) : PackedTriad := overlapDecodedTriad overlapEncodedTriads01[k]!

def overlapRules01 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop) : Nat → Prop
  | 0 => ((v 0) ≥ 0)
  | 1 => ((v 1) ≥ 0)
  | 2 => ((v 2) ≥ 0)
  | 3 => ((v 3) ≥ 0)
  | 4 => ((v 4) ≥ 0)
  | 5 => ((v 5) ≥ 0)
  | 6 => ((v 6) ≥ 0)
  | 7 => ((v 7) ≥ 0)
  | 8 => ((v 8) ≥ 0)
  | 9 => ((v 9) ≥ 0)
  | 10 => ((v 10) ≥ 0)
  | 11 => ((v 11) ≥ 0)
  | 12 => ((v 12) ≥ 0)
  | 13 => ((v 13) ≥ 0)
  | 14 => ((v 14) ≥ 0)
  | 15 => ((v 15) ≥ 0)
  | 16 => ((v 16) ≥ 0)
  | 17 => ((v 17) ≥ 0)
  | 18 => ((v 18) ≥ 0)
  | 19 => ((v 19) ≥ 0)
  | 20 => ((v 20) ≥ 0)
  | 21 => ((v 21) ≥ 0)
  | 22 => ((v 22) ≥ 0)
  | 23 => ((v 23) ≥ 0)
  | 24 => ((v 24) ≥ 0)
  | 25 => ((v 25) ≥ 0)
  | 26 => ((v 26) ≥ 0)
  | 27 => ((v 27) ≥ 0)
  | 28 => ((v 28) ≥ 0)
  | 29 => ((v 29) ≥ 0)
  | 30 => ((v 30) ≥ 0)
  | 31 => ((v 31) ≥ 0)
  | 32 => ((v 32) ≥ 0)
  | 33 => ((v 33) ≥ 0)
  | 34 => ((v 34) ≥ 0)
  | 35 => ((v 35) ≥ 0)
  | 36 => ((v 36) ≥ 0)
  | 37 => ((v 37) ≥ 0)
  | 38 => ((v 38) ≥ 0)
  | 39 => (((v 24) = 0) ∨ ((v 9) = 0) ∨ ((v 1) = 0) ∨ ((v 0) = 0))
  | 40 => (((t0 < 0) ∧ (t0 = t1) ∧ ¬(k0 ↔ k1)) ∨ ((t0 = 0) ∧ (t1 > 0) ∧ (¬k0)) ∨ ((t0 > 0) ∧ (t1 = 0) ∧ (¬k1)) ∨ ((t0 = 0) ∧ (t1 = 0) ∧ k0 ∧ k1))
  | 41 => ((((((v 0) + 0) + ((v 3) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 4) + 0) + ((v 2) + 0)) - t0) + (((v 30) + 0) + ((v 28) + 0) + ((v 31) + 0) + ((v 26) + 0) + ((v 19) + 0) + ((v 27) + 0) + ((v 29) + 0))) = (2 * (((v 23) + 0) + ((v 21) + 0) + ((v 25) + 0) + ((v 19) + 0) + ((v 18) + 0) + ((v 20) + 0) + ((v 22) + 0))))
  | 42 => ((¬((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 0)))) ↔ (¬(u 3)))) ↔ (u 9))) ↔ (¬(u 9)))) ↔ (u 9))) ↔ (¬(u 4)))) ↔ (¬(u 2)))) ↔ k0)) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 30))) ↔ (u 28))) ↔ (u 31))) ↔ (u 26))) ↔ (¬(u 19)))) ↔ (u 27))) ↔ (u 29))))
  | 43 => (((((v 23) + 0) + ((v 21) + 0) + ((v 25) + 0) + ((v 19) + 0) + ((v 18) + 0) + ((v 20) + 0) + ((v 22) + 0)) + (((v 37) + 0) + ((v 35) + 0) + ((v 38) + 0) + ((v 33) + 0) + ((v 32) + 0) + ((v 34) + 0) + ((v 36) + 0))) = (2 * (((v 30) + 0) + ((v 28) + 0) + ((v 31) + 0) + ((v 26) + 0) + ((v 19) + 0) + ((v 27) + 0) + ((v 29) + 0))))
  | 44 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 23))) ↔ (u 21))) ↔ (u 25))) ↔ (u 19))) ↔ (u 18))) ↔ (u 20))) ↔ (u 22))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 37))) ↔ (u 35))) ↔ (u 38))) ↔ (u 33))) ↔ (u 32))) ↔ (u 34))) ↔ (u 36))))
  | 45 => (((((v 10) + 0) + ((v 12) + 0) + ((v 31) + 0) + ((v 38) + 0) + ((v 13) + 0) + ((v 25) + 0) + ((v 11) + 0)) + (((v 8) + 0) + ((v 6) + 0) + ((v 26) + 0) + ((v 33) + 0) + ((v 5) + 0) + ((v 19) + 0) + ((v 7) + 0))) = (2 * ((((v 0) + 0) + ((v 3) + 0) + ((v 24) + 0) + ((v 24) + 1) + ((v 4) + 0) + ((v 24) + 0) + ((v 2) + 0)) - t1)))
  | 46 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 10)))) ↔ (¬(u 12)))) ↔ (¬(u 31)))) ↔ (¬(u 38)))) ↔ (¬(u 13)))) ↔ (¬(u 25)))) ↔ (¬(u 11)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 8))) ↔ (u 6))) ↔ (¬(u 26)))) ↔ (¬(u 33)))) ↔ (u 5))) ↔ (¬(u 19)))) ↔ (u 7))))
  | 47 => ((((((v 0) + 0) + ((v 3) + 0) + ((v 24) + 0) + ((v 24) + 1) + ((v 4) + 0) + ((v 24) + 0) + ((v 2) + 0)) - t1) + (((v 17) + 0) + ((v 15) + 0) + ((v 19) + 0) + ((v 32) + 0) + ((v 14) + 0) + ((v 18) + 0) + ((v 16) + 0))) = (2 * (((v 8) + 0) + ((v 6) + 0) + ((v 26) + 0) + ((v 33) + 0) + ((v 5) + 0) + ((v 19) + 0) + ((v 7) + 0))))
  | 48 => ((¬((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 0)))) ↔ (¬(u 3)))) ↔ (u 24))) ↔ (¬(u 24)))) ↔ (¬(u 4)))) ↔ (¬(u 24)))) ↔ (¬(u 2)))) ↔ k1)) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 17))) ↔ (u 15))) ↔ (u 19))) ↔ (¬(u 32)))) ↔ (u 14))) ↔ (¬(u 18)))) ↔ (u 16))))
  | 49 => (((((v 10) + 0) + ((v 8) + 0) + ((v 30) + 0) + ((v 0) + 0) + ((v 17) + 0) + ((v 37) + 0) + ((v 23) + 0)) + (((v 12) + 0) + ((v 6) + 0) + ((v 28) + 0) + ((v 3) + 0) + ((v 15) + 0) + ((v 35) + 0) + ((v 21) + 0))) = (2 * (((v 11) + 0) + ((v 7) + 0) + ((v 29) + 0) + ((v 2) + 0) + ((v 16) + 0) + ((v 36) + 0) + ((v 22) + 0))))
  | 50 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 10))) ↔ (¬(u 8)))) ↔ (¬(u 30)))) ↔ (u 0))) ↔ (¬(u 17)))) ↔ (¬(u 37)))) ↔ (¬(u 23)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 12))) ↔ (¬(u 6)))) ↔ (¬(u 28)))) ↔ (u 3))) ↔ (¬(u 15)))) ↔ (¬(u 35)))) ↔ (¬(u 21)))))
  | 51 => (((((v 11) + 0) + ((v 7) + 0) + ((v 29) + 0) + ((v 2) + 0) + ((v 16) + 0) + ((v 36) + 0) + ((v 22) + 0)) + (((v 13) + 0) + ((v 5) + 0) + ((v 27) + 0) + ((v 4) + 0) + ((v 14) + 0) + ((v 34) + 0) + ((v 20) + 0))) = (2 * (((v 12) + 0) + ((v 6) + 0) + ((v 28) + 0) + ((v 3) + 0) + ((v 15) + 0) + ((v 35) + 0) + ((v 21) + 0))))
  | 52 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 11))) ↔ (¬(u 7)))) ↔ (¬(u 29)))) ↔ (u 2))) ↔ (¬(u 16)))) ↔ (¬(u 36)))) ↔ (¬(u 22)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 13))) ↔ (¬(u 5)))) ↔ (¬(u 27)))) ↔ (u 4))) ↔ (¬(u 14)))) ↔ (¬(u 34)))) ↔ (¬(u 20)))))
  | k => if k < 443 then packedTriad v u (overlapTriads01 (k-53)) else True

private def overlapCores01 : Array (List Nat × List Nat × List Nat × List Nat) :=
  #[([32,33,34,35,36,37,38],[18,19,20,21,22,23,24,25],[26,27,28,29,30,31],[43,321,324,329,366,367,376,377]),
   ([20,21,22,23,32,33,38],[10,18,19,24,25,27,28,29,30],[5,6,7,8,26,31,34,35,36,37],[43,195,205,213,221,284,321,329]),
   ([27,28,29,30,32,33,38],[5,6,7,8,14,15,16,17,18,19,24,25,34,35,36,37],[0,2,3,4,10,11,12,13,20,21,22,23,26,31],[43,45,47,58,70,125,133,340]),
   ([0,8,10,17,22,28,32,33,34,37,38],[1,2,6,11,15,18,19,20,23,24,25,29,35],[3,7,12,16,21,26,27,30,31,36],[43,49,70,86,92,101,139,290,321,329,387]),
   ([3,6,12,15,20,23,29,32,33,35,38],[0,1,4,7,10,13,16,18,19,21,24,25,27,30,36],[2,5,8,11,14,17,22,26,28,31,34,37],[43,49,51,55,65,84,88,95,284,321,329,393]),
   ([2,7,9,11,16,21,27,30,32,33,36,38],[3,5,8,12,14,17,18,19,22,24,25,28,34,37],[0,4,6,10,13,15,20,23,26,29,31,35],[40,41,43,47,49,51,133,210,212,215,290,358,395,427]),
   ([4,5,13,14,21,29,32,33,34,37,38],[3,7,12,16,18,19,20,23,24,25,28,36],[1,2,6,11,15,22,26,27,30,31,35],[43,51,89,128,178,290,321,329,366,377]),
   ([2,7,11,16,20,23,28,32,33,36,38],[0,4,6,10,13,15,18,19,22,24,25,27,30,35],[1,3,5,8,12,14,17,21,26,29,31,34,37],[43,49,51,60,85,87,91,100,284,321,329,367]),
   ([3,6,9,12,15,22,27,30,32,33,35,38],[2,5,8,11,14,17,18,19,21,24,25,29,34,37],[0,1,4,7,10,13,16,20,23,26,28,31,36],[40,41,43,45,47,49,51,55,58,65,66,84,88,99,340,341]),
   ([0,2,3,4,19,31,34,35,36,37],[5,6,7,8,10,11,12,13,20,21,22,23,24,26,32,38],[14,15,16,17,18,25,27,28,29,30,33],[43,45,47,197,207,215,223,354]),
   ([5,6,7,8,19,20,21,22,23,31],[0,2,3,4,9,14,15,16,17,24,26,27,28,29,30,32,38],[10,11,12,13,18,25,33,34,35,36,37],[40,41,43,45,47,241]),
   ([19,27,28,29,30,31],[9,24,26,32,34,35,36,37,38],[0,2,18,20,21,22,23,25,33],[43,58,70,125,133,238,241]),
   ([0,4,7,12,15,19,22,28,31,34,37],[1,2,5,8,10,13,16,20,23,24,26,29,32,35,38],[3,6,11,14,17,18,21,25,27,30,33,36],[43,45,46,47,49,51,54,59,65,96,120,145,213,354]),
   ([3,5,8,11,16,19,20,23,29,31,35],[0,1,4,6,9,12,14,17,21,24,26,27,30,32,36,38],[2,7,10,13,15,18,22,25,28,33,34,37],[40,41,45,47,49,51,95,99,144,158,161,195,221,338,389]),
   ([2,6,10,13,14,17,19,21,27,30,31,36],[1,3,7,9,11,15,22,24,26,28,32,34,37,38],[0,4,5,8,12,16,18,20,23,25,29,33,35],[40,41,43,47,49,51,53,119,126,133,146,167,168,205,295,339]),
   ([0,4,6,11,16,19,21,29,31,34,37],[3,5,8,9,10,13,15,20,23,24,26,28,32,36,38],[1,2,7,12,14,17,18,22,25,27,30,33,35],[43,45,47,49,51,75,84,144,170,173,178,205,268,377]),
   ([2,5,8,12,15,19,20,23,28,31,36],[0,4,7,9,11,14,17,22,24,26,27,30,32,35,38],[1,3,6,10,13,16,18,21,25,29,33,34,37],[40,41,43,45,47,49,51,60,70,86,88,100,241]),
   ([3,7,10,13,14,17,19,22,27,30,31,35],[2,6,9,12,16,21,24,26,29,32,34,37,38],[0,1,4,5,8,11,15,18,20,23,25,28,33,36],[40,41,43,45,47,49,51,58,116,117,133,149,163,167,213,283]),
   ([0,2,3,4,18,25,26,34,35,36,37],[14,15,16,17,20,21,22,23,24,31,33],[5,6,7,8,10,11,12,13,19,27,28,29,30,32,38],[43,45,47,197,207,215,223,330]),
   ([10,11,12,13,14,15,16,17,18,20,21,22,23,25,26],[0,2,3,4,5,6,7,8,24,27,28,29,30,31,33],[9,19,32,34,35,36,37,38],[40,41,43,45,47,57,65,69,124,128,132,141,163,247]),
   ([5,6,7,8,18,25,26,27,28,29,30],[10,11,12,13,24,31,33,34,35,36,37],[0,2,3,4,9,14,15,16,17,19,20,21,22,23,32,38],[40,41,43,45,47,58,70,125,133,236]),
   ([0,4,6,11,16,18,22,25,26,28,34,37],[1,2,7,12,14,17,20,23,24,29,31,33,35],[3,5,8,9,10,13,15,19,21,27,30,32,36,38],[43,45,47,49,51,56,87,94,120,170,173,206,233,267]),
   ([3,7,10,13,14,17,18,20,23,25,26,29,35],[0,1,4,5,8,11,15,21,24,27,30,31,33,36],[2,6,9,12,16,19,22,28,32,34,37,38],[40,41,43,45,49,51,117,118,121,163,167,214,233,266,302,389]),
   ([2,5,8,12,15,18,21,25,26,27,30,36],[1,3,6,10,13,16,22,24,28,31,33,34,37],[0,4,7,9,11,14,17,19,20,23,29,32,35,38],[40,41,43,45,47,49,51,58,60,65,86,88,93,236,247]),
   ([0,4,7,12,15,18,21,25,26,29,34,37],[3,6,11,14,17,20,23,24,28,31,33,36],[2,5,8,9,10,13,16,19,22,27,30,32,35,38],[40,41,43,45,47,49,51,56,59,65,75,145,247,267,377]),
   ([2,6,10,13,14,17,18,20,23,25,26,28,36],[0,4,5,8,12,16,22,24,27,30,31,33,35],[1,3,7,9,11,15,19,21,29,32,34,37,38],[40,41,43,47,49,51,57,89,116,126,139,167,206,267,269,365,367]),
   ([3,5,8,11,16,18,22,25,26,27,30,35],[2,7,10,13,15,21,24,29,31,33,34,37],[0,1,4,6,9,12,14,17,19,20,23,28,32,36,38],[40,41,43,45,47,49,51,55,58,87,91,94,133,236,247]),
   ([],[5,6,7,8,10,11,12,13,25,31,38],[19,26,33],[46]),
   ([5,6,7,8,24],[0,2,3,4,14,15,16,17,18,25,31,32,38],[10,11,12,13,19,26,33],[45,47]),
   ([10,11,12,13,14,15,16,17,24],[9,18,25,31,32,38],[0,2,3,4,5,6,7,8,19,26,33],[45,47,57,65,69,124,128,132,141,163]),
   ([0,4,7,12,15,23,24,30,37],[1,2,5,8,10,13,16,18,21,25,28,31,32,35,38],[3,6,11,14,17,19,22,26,29,33,36],[45,47,49,65,88,95,98,101]),
   ([3,5,8,11,16,21,24,28,35],[0,1,4,6,12,14,17,18,22,25,29,31,32,36,38],[2,7,10,13,15,19,20,23,26,27,30,33,34,37],[45,47,49,51,86,87]),
   ([2,6,10,13,14,17,22,24,29,36],[1,3,7,11,15,18,20,23,25,27,30,31,32,34,37,38],[0,4,5,8,12,16,19,21,26,28,33,35],[45,47,49,51,94,97,100,128,146,208]),
   ([0,4,6,11,16,20,24,27,34],[3,5,8,10,13,15,18,22,25,29,31,32,36,38],[1,2,7,12,14,17,19,21,26,28,33,35],[45,47,51,83,87,133,173,195,197]),
   ([2,5,8,12,15,22,24,29,36],[0,4,7,11,14,17,18,21,25,28,31,32,35,38],[1,3,6,10,13,16,19,20,23,26,27,30,33,34,37],[45,47,49,51,60,88,94,97,100]),
   ([3,7,10,13,14,17,21,24,28,35],[2,6,9,12,16,18,20,23,25,27,30,31,32,34,37,38],[0,4,5,8,11,15,19,22,26,29,33,36],[43,45,47,49,51,69,143,152,163]),
   ([0,8,10,17,23,30,37],[1,2,6,11,15,21,28,35],[3,7,12,16,22,29,36],[49,86,92,95,98,101,139]),
   ([],[4,7,13,16,22,29,36],[2,5,11,14,20,27,34],[52]),
   ([],[3,8,12,17,23,30,37],[0,6,10,15,21,28,35],[50]),
   ([18,19,24,25,26,31,32,33,38],[10,11,12,13],[5,6,7,8,20,21,22,23,27,28,29,30,34,35,36,37],[43,46,328,335,350,360,412,419,421])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapResidueData01 :
    (List.range 40).all (fun a =>
      let c := overlapCores01[a]!
      c.1.all (fun k => decide (k < 39 ∧ overlapResidue01 a k = 0)) &&
      c.2.1.all (fun k => decide (k < 39 ∧ overlapResidue01 a k = 1)) &&
      c.2.2.1.all (fun k => decide (k < 39 ∧ overlapResidue01 a k = 2))) = true := by
  decide

private theorem classifyResidues01 (v : Nat → Int) (u : Nat → Prop) (a : Nat) (ha : a < 40)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) :
    let c := overlapCores01[a]!
    (∀ k ∈ c.1,0 < v k) ∧ (∀ k ∈ c.2.1, v k = 0 ∧ ¬u k) ∧
    (∀ k ∈ c.2.2.1, v k = 0 ∧ u k) := by
  let c := overlapCores01[a]!
  have h := List.all_eq_true.mp overlapResidueData01 a (List.mem_range.mpr ha)
  obtain ⟨hzo, ht⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hz, ho⟩ := Bool.and_eq_true_iff.mp hzo
  have ds0 : ∀ k ∈ c.1,0 < v k := by
    intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp hz k hk)
    simpa [residueFacts, hval] using hres k bound
  have ds1 : ∀ k ∈ c.2.1, v k = 0 ∧ ¬u k := by
    intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ho k hk)
    simpa [residueFacts, hval] using hres k bound
  have ds2 : ∀ k ∈ c.2.2.1, v k = 0 ∧ u k := by
    intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ht k hk)
    simpa [residueFacts, hval] using hres k bound
  exact ⟨ds0, ds1, ds2⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible01Group0 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules01 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 0 ≤ a) (ghi : a < 10)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) : False := by
  let c := overlapCores01[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues01 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules01 v u t0 t1 k0 k1 k := fun k _ => rules k
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬ u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  clear hres rules
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores01, c] at ds0 rv
    all_goals
      simp [overlapEncodedTriads01, overlapRules01, overlapTriads01, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        clear v1 b1 v2 b2 ds1 ds2
        try clear c ha
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (ring := false) (ematch := 0) (splits:=30) (liaSteps:=30000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible01Group1Except (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules01 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 10 ≤ a) (ghi : a < 18)
    (hex : a ≠ 13)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) : False := by
  let c := overlapCores01[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues01 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules01 v u t0 t1 k0 k1 k := fun k _ => rules k
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬ u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  clear hres rules
  rcases (show a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores01, c] at ds0 rv
    all_goals
      simp [overlapEncodedTriads01, overlapRules01, overlapTriads01, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        clear v1 b1 v2 b2 ds1 ds2
        try clear c ha
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (ring := false) (ematch := 0) (splits:=30) (liaSteps:=30000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible01Group2 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules01 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 18 ≤ a) (ghi : a < 27)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) : False := by
  let c := overlapCores01[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues01 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules01 v u t0 t1 k0 k1 k := fun k _ => rules k
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬ u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  clear hres rules
  rcases (show a = 18 ∨ a = 19 ∨ a = 20 ∨ a = 21 ∨ a = 22 ∨ a = 23 ∨ a = 24 ∨ a = 25 ∨ a = 26 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores01, c] at ds0 rv
    all_goals
      simp [overlapEncodedTriads01, overlapRules01, overlapTriads01, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        clear v1 b1 v2 b2 ds1 ds2
        try clear c ha
        first
        | omega (splitDisjunctions := false)
        | grind (qlia := true) (ring := false) (ematch := 0) (splits:=30) (liaSteps:=30000)
        | omega
        | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible01Group3 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules01 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (glo : 27 ≤ a) (ghi : a < 40)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) : False := by
  let c := overlapCores01[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues01 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules01 v u t0 t1 k0 k1 k := fun k _ => rules k
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬ u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  clear hres rules
  rcases (show a = 27 ∨ a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 ∨ a = 32 ∨ a = 33 ∨ a = 34 ∨ a = 35 ∨ a = 36 ∨ a = 37 ∨ a = 38 ∨ a = 39 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores01, c] at ds0 rv
    all_goals
      simp [overlapEncodedTriads01, overlapRules01, overlapTriads01, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c ha
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits:=30) (liaSteps:=30000)
          | omega
          | grind (splits:=45) (liaSteps:=200000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible01Special1111 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules01 v u t0 t1 k0 k1 k)
    (a : Nat) (ha : a < 40) (targetCase : a=13)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) : False := by
  let c := overlapCores01[a]!
  obtain ⟨ds0, ds1, ds2⟩ := classifyResidues01 v u a ha hres
  have rv : ∀ k ∈ c.2.2.2, overlapRules01 v u t0 t1 k0 k1 k := fun k _ => rules k
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬ u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  clear hres rules
  subst a
  all_goals
    simp [overlapCores01, c] at ds0 rv
    all_goals
      simp [overlapEncodedTriads01, overlapRules01, overlapTriads01, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        clear v1 b1 v2 b2 ds1 ds2
        try clear c ha
        rcases rv with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14⟩
        generalize v 11 = v11, v 16 = v16, v 19 = v19, v 20 = v20, v 23 = v23, v 29 = v29, v 3 = v3, v 31 = v31, v 35 = v35, v 5 = v5, v 8 = v8 at *
        rcases ds0 with ⟨pos3,pos5,pos8,pos11,pos16,pos19,pos20,pos23,pos29,pos31,pos35⟩
        have nv3 : ¬ v3 < 1 := by omega (splitDisjunctions := false)
        have nv11 : ¬ v11 < 1 := by omega (splitDisjunctions := false)
        have nv19 : ¬ v19 < 1 := by omega (splitDisjunctions := false)
        by_cases bu19 : (u 19)
        · clear h6 h7 h8 h9 h10 h11 h12 h14
          simp [bu19] at h0 h1 h2 h3 h4 h5 h13 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
        · by_cases bu23 : (u 23)
          · clear h6 h7
            simp [bu19, bu23, nv3, nv11, nv19] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14
            rcases h13 with ⟨e,l⟩ | ⟨e,l,s⟩
            · subst v19
              all_goals (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 30000))
            · subst v31
              all_goals (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 30000))
          · by_cases bu5 : (u 5)
            · by_cases bk0 : k0
              · by_cases bk1 : k1
                · by_cases bu35 : (u 35)
                  · clear h6 h7 h8 h11 h12 h13 h14
                    simp [bu19, bu23, bu5, bk0, bk1, bu35] at h0 h1 h2 h3 h4 h5 h9 h10 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                  · clear h6 h7 h8 h9 h11 h12 h13
                    simp [bu19, bu23, bu5, bk0, bk1, bu35] at h0 h1 h2 h3 h4 h5 h10 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                · by_cases bu11 : (u 11)
                  · by_cases bu16 : (u 16)
                    · by_cases bu35 : (u 35)
                      · clear h6 h7 h12
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu35] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                      · clear h6 h7
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu35, nv3, nv11, nv19] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14
                        obtain ⟨h8a,h8b⟩ := h8
                        subst v11 v16
                        first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits:=25) (liaSteps:=30000)
                    · by_cases bu3 : (u 3)
                      · clear h6 h7 h12
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu3, nv3, nv11, nv19] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h13 h14
                        obtain ⟨h8a,h8b⟩ := h8
                        subst v16
                        first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits:=25) (liaSteps:=30000)
                      · clear h6 h7
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu3] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                  · by_cases bu3 : (u 3)
                    · clear h0 h1 h4 h6 h7 h8 h11 h12 h14
                      simp [bu19, bu23, bu5, bk0, bk1, bu11, bu3] at h2 h3 h5 h9 h10 h13 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                    · clear h6 h7
                      simp [bu19, bu23, bu5, bk0, bk1, bu11, bu3] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
              · by_cases bk1 : k1
                · by_cases bu11 : (u 11)
                  · by_cases bu16 : (u 16)
                    · by_cases bu35 : (u 35)
                      · clear h6 h7 h12
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu35] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                      · clear h6 h7 h9
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu35] at h0 h1 h2 h3 h4 h5 h8 h10 h11 h12 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                    · by_cases bu3 : (u 3)
                      · clear h6 h7 h12
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu3] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                      · clear h6 h7 h12
                        simp [bu19, bu23, bu5, bk0, bk1, bu11, bu16, bu3, nv3, nv11, nv19] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h13 h14
                        obtain ⟨e, _⟩ := h8
                        subst v16
                        rcases h9 with ⟨a9, b9⟩ | ⟨a9, b9, c9⟩
                        all_goals rcases h10 with ⟨a10, b10⟩ | ⟨a10, b10⟩
                        all_goals rcases h0 with ⟨a0, b0⟩ | ⟨a0, b0⟩
                        all_goals first | omega | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000)
                  · by_cases bu3 : (u 3)
                    · clear h0 h1 h6 h7 h8 h11
                      simp [bu19, bu23, bu5, bk0, bk1, bu11, bu3] at h2 h3 h4 h5 h9 h10 h12 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                    · clear h6 h7
                      simp [bu19, bu23, bu5, bk0, bk1, bu11, bu3] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                · by_cases bu35 : (u 35)
                  · clear h1 h3 h4 h5 h6 h7 h8 h10 h11 h12 h13 h14
                    simp [bu19, bu23, bu5, bk0, bk1, bu35] at h0 h2 h9 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
                  · clear h6 h7 h8 h9 h10 h12 h13
                    simp [bu19, bu23, bu5, bk0, bk1, bu35] at h0 h1 h2 h3 h4 h5 h11 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))
            · clear h6 h7
              simp [bu19, bu23, bu5] at h0 h1 h2 h3 h4 h5 h8 h9 h10 h11 h12 h13 h14 <;> (first | omega (splitDisjunctions := false) | grind (qlia := true) (ring := false) (splits := 25) (liaSteps := 20000))

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem overlapImpossible01 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules01 v u t0 t1 k0 k1 k) (a : Nat) (ha : a < 40)
    (hres : ∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) : False := by
  by_cases h0 : a < 10
  · exact overlapImpossible01Group0 v u t0 t1 k0 k1 rules a ha (Nat.zero_le _) h0 hres
  by_cases h1 : a < 18
  · by_cases h13 : a = 13
    · exact overlapImpossible01Special1111 v u t0 t1 k0 k1 rules a ha h13 hres
    exact overlapImpossible01Group1Except v u t0 t1 k0 k1 rules a ha (by omega) h1 h13 hres
  by_cases h2 : a < 27
  · exact overlapImpossible01Group2 v u t0 t1 k0 k1 rules a ha (by omega) h2 hres
  exact overlapImpossible01Group3 v u t0 t1 k0 k1 rules a ha (by omega) ha hres

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

def overlapForms11 : Array ResidueRow :=
  #[(0,0,0,1), (0,0,1,0), (0,0,1,1), (0,0,2,1), (0,0,3,1), (0,1, -3, -1), (0,1, -2, -1), (0,1, -1, -1), (0,1,0, -1), (0,1,0,0), (0,1,0,1), (0,1,1,1), (0,1,2,1), (0,1,3,1), (0,2, -3, -1), (0,2, -2, -1), (0,2, -1, -1), (0,2,0, -1), (1, -2,0,0), (1, -1,0,0), (1,0, -3, -1), (1,0, -2, -1), (1,0, -1, -1), (1,0,0, -1), (1,0,0,0), (1,0,0,1), (1,0,1,1), (1,0,2,1), (1,0,3,1), (1,1,0,0), (1,2,0,0), (2, -1,0,0), (2,0, -3, -1), (2,0, -2, -1), (2,0, -1, -1), (2,0,0, -1), (2,1,0,0)]

def overlapResidue11 (a k : Nat) : Int :=
  rowDot overlapForms11[k]! normalizedOverlapResidues[a]! % 3

def overlapEncodedTriads11 : Array ℕ := #[2488816064,2564344256,2434404864,2430079552,2165971520,2488814144,2564342336,2425752256,2430077632,2434403008,2966426304,3238927040,
  2480421568,2455126720,2488812224,3025160896,2459323072,2555949760,2518072000,2564340416,3100689088,2522268352,2970489600,2459321088,
  2522266368,3025163072,3100691264,2429948609,2434144961,2442537665,2446734017,2450930369,2463519425,2467715777,2471912129,2480304833,
  2484501185,2488697537,2505482945,2509679297,2513875649,2526464705,2530661057,2534857409,2555839169,2560035521,2564231873,2434142977,
  2446732033,2450928385,2467713793,2471910145,2484499201,2488695553,2509677313,2513873665,2530659073,2534855425,2560033537,2564229889,
  2450926401,2471908161,2488693569,2513871681,2534853441,2564227905,2476233154,2484623810,2551761346,2560152002,2434275906,2484619842,
  2560148034,2970622658,2476225218,2455124674,2484615874,3020966594,2463517378,2551753410,2518069954,2560144066,3096494786,2526462658,
  2459316994,2463513346,2467709698,2522262274,2526458626,2530654978,3012580162,3020970818,3088108354,3096499010,2480431555,2488822211,
  2555959747,2564350403,2480425539,2555953731,2455122627,2480419523,2488810179,3016772291,2467711683,2518067907,2555947715,2564338371,
  3092300483,2530656963,2463509251,2467705603,2471901955,2526454531,2530650883,2534847235,3016778563,3025169219,3092306755,3100697411,
  2476239300,2551767492,2476231236,2551759428,2455120580,2476223172,2484613828,3012577988,2471905988,2518065860,2551751364,2560142020,
  3088106180,2534851268,2471897860,2534843140,3012586308,3088114500,2451190277,2446864965,2182756933,2472036933,2983211717,3255712453,
  3008383685,2476100293,2501286597,2539053765,2551642821,2987275013,2207673157,2451061318,2467842630,2987408070,3004189382,2480294598,
  2505480902,2539051718,2555837126,2207667014,2211865414,2463648327,2999995079,2484488903,2509675207,2539049671,2560031431,2216057671,
  2220256071,2459454024,2995800776,2488683208,2513869512,2539047624,2564225736,2220249928,2547577161,3025555913,3021363657,3017171401,
  3012979145,2547575241,2568548809,2547565129,2568546889,2497090249,2518063817,2547555017,3083911881,2539045577,2568536777,3104893641,
  2543250121,2518061833,2539035401,2543239945,2568420105,2488423241,2484230985,2480038729,2475846473,2539033417,2547553097,2543229769,
  2568526665,3083922249,3104895817,2543227785,2568524745,2472172042,2467846730,2203738698,3004193482,3276694218,2522258122,2539043530,
  2568428234,3008256778,2472043083,3008389835,2526452427,2539041483,2568426187,2530646732,2539039436,2568424140,2534841037,2539037389,
  2568422093,2488957454,2484632142,2220524110,3020978894,3293479630,2501284558,2551749326,2543248078,3025042190,2488828495,3025175247,
  2505478863,2555943631,2543246031,2509673168,2560137936,2543243984,2513867473,2564332241,2543241937,2539297298,2518194770,2547685970,
  2543370834,2270872146,3083770578,3054541522,3372925650,3343827666,3079717586,2279260882,3616336594,2547444434,2032069330,3075382034,
  3104480082,3079445330,2568681875,2543501843,2539176531,2568667731,2275076691,3104752339,3075523283,2547434195,3348032211,2300242643,
  2568418003,3079586579,2279009107,2010575827,2514135572,2509810260,2245702228,2534982228,3046157012,3318657748,3071328980,2551628500,
  3050220308,2283201364,2514006613,2530787925,3050353365,3067134677,2555822805,2283195221,2287393621,2526593622,3062940374,2560017110,
  2291585878,2295784278,2522399319,3058746071,2564211415,2295778135,3352752472,3105290648,3101084120,3096891864,3092699608,3088507352,
  3084315096,2543381080,3079727832,2568415960,2563951448,2559759192,2555566936,2551374680,2547182424,2299982680,2535117337,2530792025,
  2266683993,3067138777,3339639513,3071202073,2534988378,3071335130,3084579165,3105288669,2568155997,2031549341,2564491808,2560166496,
  2296058464,3096513248,3369013984,3100576544,2564362849,3100709601]

def overlapTriads11 (k : ℕ) : PackedTriad := overlapDecodedTriad overlapEncodedTriads11[k]!

def overlapRules11 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop) : Nat → Prop
  | 0 => ((v 0) ≥ 0)
  | 1 => ((v 1) ≥ 0)
  | 2 => ((v 2) ≥ 0)
  | 3 => ((v 3) ≥ 0)
  | 4 => ((v 4) ≥ 0)
  | 5 => ((v 5) ≥ 0)
  | 6 => ((v 6) ≥ 0)
  | 7 => ((v 7) ≥ 0)
  | 8 => ((v 8) ≥ 0)
  | 9 => ((v 9) ≥ 0)
  | 10 => ((v 10) ≥ 0)
  | 11 => ((v 11) ≥ 0)
  | 12 => ((v 12) ≥ 0)
  | 13 => ((v 13) ≥ 0)
  | 14 => ((v 14) ≥ 0)
  | 15 => ((v 15) ≥ 0)
  | 16 => ((v 16) ≥ 0)
  | 17 => ((v 17) ≥ 0)
  | 18 => ((v 18) ≥ 0)
  | 19 => ((v 19) ≥ 0)
  | 20 => ((v 20) ≥ 0)
  | 21 => ((v 21) ≥ 0)
  | 22 => ((v 22) ≥ 0)
  | 23 => ((v 23) ≥ 0)
  | 24 => ((v 24) ≥ 0)
  | 25 => ((v 25) ≥ 0)
  | 26 => ((v 26) ≥ 0)
  | 27 => ((v 27) ≥ 0)
  | 28 => ((v 28) ≥ 0)
  | 29 => ((v 29) ≥ 0)
  | 30 => ((v 30) ≥ 0)
  | 31 => ((v 31) ≥ 0)
  | 32 => ((v 32) ≥ 0)
  | 33 => ((v 33) ≥ 0)
  | 34 => ((v 34) ≥ 0)
  | 35 => ((v 35) ≥ 0)
  | 36 => ((v 36) ≥ 0)
  | 37 => (((v 24) = 0) ∨ ((v 9) = 0) ∨ ((v 1) = 0) ∨ ((v 0) = 0))
  | 38 => (((t0 < 0) ∧ (t0 = t1) ∧ ¬(k0 ↔ k1)) ∨ ((t0 = 0) ∧ (t1 > 0) ∧ (¬k0)) ∨ ((t0 > 0) ∧ (t1 = 0) ∧ (¬k1)) ∨ ((t0 = 0) ∧ (t1 = 0) ∧ k0 ∧ k1))
  | 39 => (((((v 25) + 0) + ((v 27) + 0) + ((v 19) + 0) + ((v 29) + 0) + ((v 30) + 0) + ((v 28) + 0) + ((v 26) + 0)) + (((v 23) + 0) + ((v 21) + 0) + ((v 29) + 0) + ((v 19) + 0) + ((v 18) + 0) + ((v 20) + 0) + ((v 22) + 0))) = (2 * ((((v 0) + 0) + ((v 3) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 4) + 0) + ((v 2) + 0)) - t0)))
  | 40 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 25)))) ↔ (¬(u 27)))) ↔ (¬(u 19)))) ↔ (¬(u 29)))) ↔ (¬(u 30)))) ↔ (¬(u 28)))) ↔ (¬(u 26)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 23))) ↔ (u 21))) ↔ (u 29))) ↔ (u 19))) ↔ (u 18))) ↔ (u 20))) ↔ (u 22))))
  | 41 => ((((((v 0) + 0) + ((v 3) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 9) + 0) + ((v 4) + 0) + ((v 2) + 0)) - t0) + (((v 35) + 0) + ((v 33) + 0) + ((v 36) + 0) + ((v 31) + 0) + ((v 19) + 0) + ((v 32) + 0) + ((v 34) + 0))) = (2 * (((v 23) + 0) + ((v 21) + 0) + ((v 29) + 0) + ((v 19) + 0) + ((v 18) + 0) + ((v 20) + 0) + ((v 22) + 0))))
  | 42 => ((¬((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 0)))) ↔ (¬(u 3)))) ↔ (u 9))) ↔ (¬(u 9)))) ↔ (u 9))) ↔ (¬(u 4)))) ↔ (¬(u 2)))) ↔ k0)) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 35))) ↔ (u 33))) ↔ (u 36))) ↔ (u 31))) ↔ (¬(u 19)))) ↔ (u 32))) ↔ (u 34))))
  | 43 => (((((v 10) + 0) + ((v 12) + 0) + ((v 36) + 0) + ((v 19) + 0) + ((v 13) + 0) + ((v 29) + 0) + ((v 11) + 0)) + (((v 8) + 0) + ((v 6) + 0) + ((v 31) + 0) + ((v 29) + 0) + ((v 5) + 0) + ((v 19) + 0) + ((v 7) + 0))) = (2 * ((((v 0) + 0) + ((v 3) + 0) + ((v 24) + 0) + ((v 24) + 0) + ((v 4) + 0) + ((v 24) + 0) + ((v 2) + 0)) - t1)))
  | 44 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 10)))) ↔ (¬(u 12)))) ↔ (¬(u 36)))) ↔ (u 19))) ↔ (¬(u 13)))) ↔ (¬(u 29)))) ↔ (¬(u 11)))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 8))) ↔ (u 6))) ↔ (¬(u 31)))) ↔ (u 29))) ↔ (u 5))) ↔ (¬(u 19)))) ↔ (u 7))))
  | 45 => ((((((v 0) + 0) + ((v 3) + 0) + ((v 24) + 0) + ((v 24) + 0) + ((v 4) + 0) + ((v 24) + 0) + ((v 2) + 0)) - t1) + (((v 17) + 0) + ((v 15) + 0) + ((v 19) + 0) + ((v 30) + 0) + ((v 14) + 0) + ((v 18) + 0) + ((v 16) + 0))) = (2 * (((v 8) + 0) + ((v 6) + 0) + ((v 31) + 0) + ((v 29) + 0) + ((v 5) + 0) + ((v 19) + 0) + ((v 7) + 0))))
  | 46 => ((¬((¬((¬((¬((¬((¬((¬((¬(False ↔ (¬(u 0)))) ↔ (¬(u 3)))) ↔ (u 24))) ↔ (u 24))) ↔ (¬(u 4)))) ↔ (¬(u 24)))) ↔ (¬(u 2)))) ↔ k1)) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 17))) ↔ (u 15))) ↔ (u 19))) ↔ (u 30))) ↔ (u 14))) ↔ (¬(u 18)))) ↔ (u 16))))
  | 47 => (((((v 10) + 0) + ((v 8) + 0) + ((v 35) + 0) + ((v 0) + 0) + ((v 17) + 0) + ((v 23) + 0) + ((v 25) + 0)) + (((v 12) + 0) + ((v 6) + 0) + ((v 33) + 0) + ((v 3) + 0) + ((v 15) + 0) + ((v 21) + 0) + ((v 27) + 0))) = (2 * (((v 11) + 0) + ((v 7) + 0) + ((v 34) + 0) + ((v 2) + 0) + ((v 16) + 0) + ((v 22) + 0) + ((v 26) + 0))))
  | 48 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 10))) ↔ (¬(u 8)))) ↔ (¬(u 35)))) ↔ (u 0))) ↔ (¬(u 17)))) ↔ (¬(u 23)))) ↔ (u 25))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 12))) ↔ (¬(u 6)))) ↔ (¬(u 33)))) ↔ (u 3))) ↔ (¬(u 15)))) ↔ (¬(u 21)))) ↔ (u 27))))
  | 49 => (((((v 11) + 0) + ((v 7) + 0) + ((v 34) + 0) + ((v 2) + 0) + ((v 16) + 0) + ((v 22) + 0) + ((v 26) + 0)) + (((v 13) + 0) + ((v 5) + 0) + ((v 32) + 0) + ((v 4) + 0) + ((v 14) + 0) + ((v 20) + 0) + ((v 28) + 0))) = (2 * (((v 12) + 0) + ((v 6) + 0) + ((v 33) + 0) + ((v 3) + 0) + ((v 15) + 0) + ((v 21) + 0) + ((v 27) + 0))))
  | 50 => ((¬((¬((¬((¬((¬((¬((¬(False ↔ (u 11))) ↔ (¬(u 7)))) ↔ (¬(u 34)))) ↔ (u 2))) ↔ (¬(u 16)))) ↔ (¬(u 22)))) ↔ (u 26))) ↔ (¬((¬((¬((¬((¬((¬((¬(False ↔ (u 13))) ↔ (¬(u 5)))) ↔ (¬(u 32)))) ↔ (u 4))) ↔ (¬(u 14)))) ↔ (¬(u 20)))) ↔ (u 28))))
  | k => if k < 393 then packedTriad v u (overlapTriads11 (k-51)) else True

private def overlapCores11 : Array (List Nat × List Nat × List Nat × List Nat) :=
  #[([],[18,19,20,21,22,23,25,26,27,28,29,30],[],[40]),
   ([9,20,21,22,23],[0,2,3,4,18,19,29,30,32,33,34,35],[5,6,7,8,25,26,27,28,31,36],[39,41,197,207,215,223]),
   ([9,25,26,27,28,32,33,34,35],[18,19,24,29,30],[0,2,3,4,20,21,22,23,31,36],[39,41,57,68,72,123,130,134,140,166]),
   ([0,4,8,9,10,17,22,27,33],[1,2,6,11,15,18,19,20,23,25,28,29,30,34],[3,7,12,16,21,26,31,32,35,36],[39,41,47,68,82,88,93,135]),
   ([3,6,9,12,15,20,23,26,34],[0,1,4,7,10,13,16,18,19,21,27,29,30,32,35],[2,5,8,11,14,17,22,25,28,31,33,36],[39,41,47,49,91,92,197]),
   ([2,7,9,11,16,21,25,28,32,35],[1,3,5,8,12,14,17,18,19,22,24,26,29,30,33],[0,4,6,10,13,15,20,23,27,31,34,36],[39,41,43,45,47,49,81,83,130,148,346]),
   ([0,4,5,9,13,14,21,26,34],[3,7,12,16,18,19,20,23,25,28,29,30,33],[1,2,6,11,15,22,27,31,32,35,36],[39,41,49,79,85,92,125,182]),
   ([2,7,9,11,16,20,23,27,33],[0,4,6,10,13,15,18,19,22,26,29,30,32,35],[1,3,5,8,12,14,17,21,25,28,31,34,36],[39,41,47,49,58,81,83,87,93,197]),
   ([3,6,9,12,15,22,25,28,32,35],[2,5,8,11,14,17,18,19,21,24,27,29,30,34],[0,1,4,7,10,13,16,20,23,26,31,33,36],[39,41,43,45,47,49,80,84,119,158,352]),
   ([0,2,3,4,19,30,36],[9,20,21,22,23,25,26,27,28,31],[18,29,32,33,34,35],[39,41,235,243]),
   ([5,6,7,8,19,20,21,22,23,30,36],[0,2,3,4,9,14,15,16,17,24,31,32,33,34,35],[10,11,12,13,18,25,26,27,28,29],[38,39,41,43,45,236,257,285,291,294,297]),
   ([19,25,26,27,28,30,32,33,34,35,36],[9,24,31],[0,2,3,4,18,20,21,22,23,29],[39,41,57,68,72,123,130,134,140,166,235,243]),
   ([0,4,7,12,15,19,22,27,30,33,36],[2,5,8,9,10,13,16,20,23,24,25,28,31,34],[3,6,11,14,17,18,21,26,29,32,35],[39,41,43,45,47,49,55,63,68,145,147,235,243]),
   ([3,5,8,11,16,19,20,23,26,30,34,36],[0,1,4,6,9,12,14,17,21,24,27,31,32,35],[2,7,10,13,15,18,22,25,28,29,33],[39,41,43,45,47,49,96,111,118,161,164,197,223,255,296]),
   ([2,6,10,13,14,17,19,21,25,28,30,32,35,36],[1,3,7,9,11,15,22,24,26,31,33],[0,4,5,8,12,16,18,20,23,27,29,34],[39,41,43,45,47,49,56,57,72,112,130,135,172,173,235,243]),
   ([0,4,6,11,16,19,21,26,30,34,36],[3,5,8,9,10,13,15,20,23,24,25,28,31,33],[2,7,12,14,17,18,22,27,29,32,35],[39,41,43,45,47,49,55,118,120,177,182,235,243]),
   ([2,5,8,12,15,19,20,23,27,30,33,36],[0,4,7,9,11,14,17,22,24,26,31,32,35],[1,3,6,10,13,16,18,21,25,28,29,34],[38,39,41,43,45,47,49,68,111,140,223,233,293,330,333]),
   ([3,7,10,13,14,17,19,22,25,28,30,32,35,36],[2,6,9,12,16,21,24,27,31,34],[0,1,4,5,8,11,15,18,20,23,26,29,33],[39,41,43,45,47,49,52,56,72,85,94,125,130,158,243,267]),
   ([0,2,3,4,18,29,31],[14,15,16,17,20,21,22,23,24,25,26,27,28,36],[5,6,7,8,9,10,11,12,13,19,30,32,33,34,35],[39,41,43,45,198]),
   ([10,11,12,13,18,20,21,22,23,29,31],[0,2,3,4,5,6,7,8,24,32,33,34,35,36],[9,19,25,26,27,28,30],[38,39,41,43,67,129,137,163,197,198,207,215,223]),
   ([5,6,7,8,18,25,26,27,28,29,31],[10,11,12,13,24,36],[0,2,3,4,9,14,15,16,17,19,20,21,22,23,30],[38,39,43,45,72,134,140,166,227,240]),
   ([0,4,6,11,16,18,22,27,29,31,33],[1,2,7,12,14,17,20,23,24,25,28,34,36],[3,5,8,9,10,13,15,19,21,26,30,32,35],[38,39,41,43,45,47,49,80,83,90,93,198,227]),
   ([3,7,10,13,14,17,18,20,23,26,29,31,34],[0,1,4,5,8,11,15,21,24,27,32,35,36],[2,6,9,12,16,19,22,25,28,30,33],[39,40,41,43,45,47,49,56,67,81,85,91,92,114,120,125,144,164,197,198,216,217,232,252,253,266,285]),
   ([2,5,8,12,15,18,21,25,28,29,31,32,35],[1,3,6,10,13,16,22,24,26,33,36],[0,4,7,9,11,14,17,19,20,23,27,30,34],[38,39,40,41,43,44,45,46,47,49,50,52,57,72,82,84,89,94,111,116,130,137,138,145,148,172,174,198,208,224,225,227,253,275,300,302,384,385]),
   ([0,4,7,12,15,18,21,26,29,31,34],[3,6,11,14,17,20,23,24,25,28,33,36],[1,2,5,8,9,10,13,16,19,22,27,30,32,35],[38,39,41,43,45,47,49,81,84,89,92,198,227]),
   ([2,6,10,13,14,17,18,20,23,27,29,31,33],[0,4,5,8,12,16,22,24,26,32,35,36],[3,7,9,11,15,19,21,25,28,30,34],[39,41,43,45,47,49,125,135,140,147,187,197,209,232,297,302]),
   ([3,5,8,11,16,18,22,25,28,29,31,32,35],[2,7,10,13,15,21,24,27,34,36],[0,1,4,6,9,12,14,17,19,20,23,26,30,33],[38,39,41,42,43,44,45,47,48,49,50,52,57,72,82,83,87,90,94,111,116,118,119,130,158,161,166,172,198,199,208,224,227,252,272,294,300,302,312,373,384,385]),
   ([],[5,6,7,8,10,11,12,13,29,36],[19,31],[44]),
   ([5,6,7,8,24],[0,2,3,4,14,15,16,17,18,29,36],[10,11,12,13,19,30,31],[43,45]),
   ([10,11,12,13,14,15,16,17,24],[9,18,29,36],[0,2,3,4,5,6,7,8,19,30,31],[43,45,56,63,67,122,125,129,137,163]),
   ([0,4,7,12,15,23,24,25,35],[1,2,5,8,10,13,16,18,21,26,29,33,36],[3,6,11,14,17,19,22,27,30,31,34],[43,45,47,63,84,91,97,138]),
   ([3,5,8,11,16,21,24,27,33],[0,1,4,6,12,14,17,18,22,25,28,29,34,36],[2,7,10,13,15,19,20,23,26,30,31,32,35],[43,45,47,49,82,83]),
   ([2,6,10,13,14,17,22,24,26,34],[3,7,9,11,15,18,20,23,27,29,32,35,36],[0,4,5,8,12,16,19,21,25,28,30,31,33],[39,41,43,45,47,49,125,135,146,348,350]),
   ([0,4,6,11,16,20,24,28,32],[3,5,8,10,13,15,18,22,27,29,34,36],[1,2,7,12,14,17,19,21,26,30,31,33],[43,45,49,79,83,94,130,177,197]),
   ([2,5,8,12,15,22,24,26,34],[0,4,7,11,14,17,18,21,25,28,29,33,36],[1,3,6,10,13,16,19,20,23,27,30,31,32,35],[43,45,47,49,58,84,90,92,96]),
   ([3,7,10,13,14,17,21,24,27,33],[2,6,9,12,16,18,20,23,26,29,32,35,36],[0,4,5,8,11,15,19,22,25,28,30,31,34],[39,41,43,45,47,49,54,117,146,153,165]),
   ([0,8,10,17,23,25,35],[1,2,6,11,15,21,26,33],[3,7,12,16,22,27,34],[47,82,88,91,97,135,138]),
   ([],[4,7,13,16,22,28,34],[2,5,11,14,20,26,32],[50]),
   ([],[3,8,12,17,23,27,35],[0,6,10,15,21,25,33],[48]),
   ([9,18,19,29,30,31,36],[0,2,3,4,10,11,12,13,25,26,27,28],[5,6,7,8,20,21,22,23],[39,40,44,305,316,327])]

private theorem overlapGroupResidues11 :
    (List.range 40).all (fun a =>
      let c := overlapCores11[a]!
      c.1.all (fun k => decide (k < 37 ∧ overlapResidue11 a k = 0)) &&
      c.2.1.all (fun k => decide (k < 37 ∧ overlapResidue11 a k = 1)) &&
      c.2.2.1.all (fun k => decide (k < 37 ∧ overlapResidue11 a k = 2))) = true := by
  decide +kernel

private def overlapGroupFacts11 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop) (a : Nat) : Prop :=
  let c := overlapCores11[a]!
  (∀ k ∈ c.1,0 < v k) ∧ (∀ k ∈ c.2.1, v k = 0 ∧ ¬u k) ∧
  (∀ k ∈ c.2.2.1, v k = 0 ∧ u k) ∧ (∀ k ∈ c.2.2.2, overlapRules11 v u t0 t1 k0 k1 k)

private theorem overlapGroupPrepare11 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules11 v u t0 t1 k0 k1 k) (a : Nat) (ha : a < 40)
    (hres : ∀ k, k < 37 → residueFacts (v k) (u k) (overlapResidue11 a k)) : overlapGroupFacts11 v u t0 t1 k0 k1 a := by
  have h := List.all_eq_true.mp overlapGroupResidues11 a (List.mem_range.mpr ha)
  obtain ⟨hzo, ht⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hz, ho⟩ := Bool.and_eq_true_iff.mp hzo
  refine ⟨?_, ?_, ?_, fun k _ => rules k⟩
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp hz k hk)
    simpa [residueFacts, hval] using hres k bound
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ho k hk)
    simpa [residueFacts, hval] using hres k bound
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ht k hk)
    simpa [residueFacts, hval] using hres k bound

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11Group0 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 0 ≤ a) (ghi : a < 12)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 40000)
          | grind (splits := 46) (liaSteps := 200000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11Group1 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 12 ≤ a) (ghi : a < 18)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 40000)
          | grind (splits := 46) (liaSteps := 200000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11Group2 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 18 ≤ a) (ghi : a < 27)
    (neq22 : a ≠ 22) (neq23 : a ≠ 23) (neq26 : a ≠ 26)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 18 ∨ a = 19 ∨ a = 20 ∨ a = 21 ∨ a = 24 ∨ a = 25 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals clear neq22 neq23 neq26
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 40000)
          | grind (splits := 46) (liaSteps := 200000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11Group3 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 27 ≤ a) (ghi : a < 40)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 27 ∨ a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 ∨ a = 32 ∨ a = 33 ∨ a = 34 ∨ a = 35 ∨ a = 36 ∨ a = 37 ∨ a = 38 ∨ a = 39 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 40000)
          | grind (splits := 46) (liaSteps := 200000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11At22 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 22 ≤ a) (ghi : a < 23)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  have ea : a = 22 := by omega
  subst a
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          by_cases hc : 1 ≤ v 10 <;> try omega (splitDisjunctions := false)
          all_goals first
          | grind (splits := 36) (liaSteps := 120000)
          | grind (qlia := true) (ring := false) (mbtc := false) (ematch := 0) (splits := 35) (liaSteps := 50000)
          | grind (splits := 48) (liaSteps := 250000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11At23 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 23 ≤ a) (ghi : a < 24)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  have ea : a = 23 := by omega
  subst a
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          skip
          first
          | grind (splits := 36) (liaSteps := 120000)
          | grind (qlia := true) (ring := false) (mbtc := false) (ematch := 0) (splits := 35) (liaSteps := 50000)
          | grind (splits := 48) (liaSteps := 250000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem overlapImpossible11At26 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (a : Nat) (glo : 26 ≤ a) (ghi : a < 27)
    (facts : overlapGroupFacts11 v u t0 t1 k0 k1 a) : False := by
  let c := overlapCores11[a]!
  rcases facts with ⟨ds0, ds1, ds2, rv⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  have ea : a = 26 := by omega
  subst a
  all_goals
    simp [overlapCores11, c, List.forall_mem_cons] at ds0 rv
    all_goals
      simp [overlapEncodedTriads11, overlapRules11, overlapTriads11, packedTriad, packedVal, packedUnit] at rv
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at rv
        try simp at rv
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          skip
          first
          | grind (splits := 36) (liaSteps := 120000)
          | grind (qlia := true) (ring := false) (mbtc := false) (ematch := 0) (splits := 35) (liaSteps := 50000)
          | grind (splits := 48) (liaSteps := 250000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem overlapImpossible11 (v : Nat → Int) (u : Nat → Prop) (t0 t1 : Int) (k0 k1 : Prop)
    (rules : ∀ k : Nat, overlapRules11 v u t0 t1 k0 k1 k) (a : Nat) (ha : a < 40)
    (hres : ∀ k, k < 37 → residueFacts (v k) (u k) (overlapResidue11 a k)) : False := by
  have h := overlapGroupPrepare11 v u t0 t1 k0 k1 rules a ha hres
  by_cases h0 : a < 12
  · exact overlapImpossible11Group0 v u t0 t1 k0 k1 a (by omega) h0 h
  by_cases h1 : a < 18
  · exact overlapImpossible11Group1 v u t0 t1 k0 k1 a (by omega) h1 h
  by_cases eq22 : a = 22
  · exact overlapImpossible11At22 v u t0 t1 k0 k1 a (by omega) (by omega) h
  by_cases eq23 : a = 23
  · exact overlapImpossible11At23 v u t0 t1 k0 k1 a (by omega) (by omega) h
  by_cases eq26 : a = 26
  · exact overlapImpossible11At26 v u t0 t1 k0 k1 a (by omega) (by omega) h
  by_cases h2 : a < 27
  · exact overlapImpossible11Group2 v u t0 t1 k0 k1 a (by omega) h2 eq22 eq23 eq26 h
  exact overlapImpossible11Group3 v u t0 t1 k0 k1 a (by omega) ha h

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.OverlapBridge

open PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable local instance : DecidableEq K := Classical.decEq K

abbrev Node := Fin 3 × Fin 4

def rowSub (a b : ResidueRow) : ResidueRow :=
  (a.1-b.1, a.2.1-b.2.1, a.2.2.1-b.2.2.1, a.2.2.2-b.2.2.2)

def rowMul (k : ℤ) (a : ResidueRow) : ResidueRow :=
  (k*a.1, k*a.2.1, k*a.2.2.1, k*a.2.2.2)

def rowAdd (a b : ResidueRow) : ResidueRow :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2+b.2.2.2)

noncomputable def rowEval {R : Type*} [CommRing R] (x : Fin 4 → R) (a : ResidueRow) : R :=
  (a.1 : R)*x 0 + (a.2.1 : R)*x 1 + (a.2.2.1 : R)*x 2 + (a.2.2.2 : R)*x 3

private theorem rowEval_sub (x : Fin 4 → K) (a b : ResidueRow) :
    rowEval x (rowSub a b) = rowEval x a - rowEval x b := by simp [rowEval,rowSub]; ring

private theorem rowEval_add (x : Fin 4 → K) (a b : ResidueRow) :
    rowEval x (rowAdd a b) = rowEval x a + rowEval x b := by simp [rowEval,rowAdd]; ring

private theorem rowEval_mul (x : Fin 4 → K) (k : ℤ) (a : ResidueRow) :
    rowEval x (rowMul k a) = (k : K)*rowEval x a := by simp [rowEval,rowMul]; ring

def chartRow (p q : Fin 4) (j : Node) : ResidueRow :=
  if j.1 = 0 then ((j.2.val : ℤ)-(p.val : ℤ),0,0,0)
  else if j.1 = 1 then (0,(j.2.val : ℤ)-(q.val : ℤ),0,0)
  else (0,0,j.2.val,1)

def axisRow (i : Fin 4) : ResidueRow :=
  ((if i=0 then 1 else 0), (if i=1 then 1 else 0), (if i=2 then 1 else 0), (if i=3 then 1 else 0))

theorem rowEval_axis (x : Fin 4 → K) (i : Fin 4) : rowEval x (axisRow i) = x i := by
  fin_cases i <;> simp [rowEval,axisRow]

private theorem rowEval_nonnegative (x : Fin 4 → O) (a : ResidueRow) :
    0 ≤ val (rowEval (fun i => (x i : K)) a) := by
  have h : ((rowEval x a : O) : K) = rowEval (fun i => (x i : K)) a := by
    simp [rowEval]
  rw [← h]
  exact PadicInt.valuation_coe_nonneg

noncomputable def chartPoint (p q : Fin 4) (x : Fin 4 → O) (i : Node) : K :=
  rowEval (fun j => (x j : K)) (chartRow p q i)

def Collision (p q : Fin 4) (x : Fin 4 → O) : Prop :=
  ∀ a b : Node, chartPoint p q x a = chartPoint p q x b →
    a=b ∨ (a=(0,p) ∧ b=(1,q)) ∨ (a=(1,q) ∧ b=(0,p))

def outsideSlots (p q : Fin 4) (i : Fin 3) : Finset Node :=
  Finset.univ.filter (fun k => k.1 ≠ i ∧ k ≠ (1,q) ∧ (i=2 ∨ k ≠ (0,p)))

theorem outside_ne_row (p q : Fin 4) (x : Fin 4 → O) (h : Collision p q x)
    (i : Fin 3) (j : Fin 4) (k : Node) (hk : k ∈ outsideSlots p q i) :
    chartPoint p q x (i,j) ≠ chartPoint p q x k := by
  have ⟨first, gone1, gone0⟩ := (Finset.mem_filter.mp hk).2
  intro equal
  rcases h (i,j) k equal with same|⟨same,hk⟩|⟨same,hk⟩
  · exact first (congrArg Prod.fst same).symm
  · exact gone1 hk
  · have hi : i=1 := congrArg Prod.fst same
    rcases gone0 with hi'|hneq
    · exact (by decide : (1 : Fin 3) ≠ 2) (hi.symm.trans hi')
    · exact hneq hk

noncomputable def overlapCross (p q : Fin 4) (x : Fin 4 → O) (i : Fin 3) (j : Fin 4) : K :=
  ∏ k ∈ outsideSlots p q i, (chartPoint p q x (i,j) - chartPoint p q x k)

noncomputable def share (p q : Fin 4) (θ₀ θ₁ : K) (k : Node) : K :=
  if k=(0,p) then θ₀ else if k=(1,q) then θ₁ else 1

private theorem share_ne (p q : Fin 4) (θ₀ θ₁ : K) (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0)
    (k : Node) : share p q θ₀ θ₁ k ≠ 0 := by
  unfold share
  split_ifs <;> first | assumption | exact one_ne_zero

def negBit (x : K) : Prop := ∃ h : x ≠ 0, minusLead x h

theorem negBit_iff (x : K) (h : x ≠ 0) : negBit x ↔ minusLead x h := by
  exact ⟨fun ⟨_,p⟩ => p, fun p => ⟨h,p⟩⟩

def xorProp (a b : Prop) : Prop := ¬(a ↔ b)

theorem negBit_mul (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    negBit (x*y) ↔ xorProp (negBit x) (negBit y) := by
  rw [negBit_iff _ (mul_ne_zero hx hy), xorProp, negBit_iff x hx, negBit_iff y hy]
  exact minusLead_mul x y hx hy

private theorem negBit_inv (x : K) (hx : x ≠ 0) : negBit x⁻¹ ↔ negBit x := by
  rw [negBit_iff _ (inv_ne_zero hx), negBit_iff _ hx]
  unfold minusLead
  rw [lead_inv]
  have cases : ∀ v : F, v⁻¹ = -1 ↔ v = -1 := by decide +kernel
  exact cases _

theorem negBit_div (x y : K) (hx : x ≠ 0) (hy : y ≠ 0) :
    negBit (x/y) ↔ xorProp (negBit x) (negBit y) := by
  rw [div_eq_mul_inv, negBit_mul _ _ hx (inv_ne_zero hy), negBit_inv _ hy]

theorem negBit_one : ¬ negBit (1 : K) := by
  rw [negBit_iff _ one_ne_zero]
  unfold minusLead
  rw [lead_one]
  decide

private theorem prod_ne (l : List K) (h : ∀ x ∈ l, x ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => exact one_ne_zero
  | cons a l ih =>
    exact mul_ne_zero (h _ (List.mem_cons_self ..)) (ih (fun x hx => h _ (List.mem_cons_of_mem _ hx)))

theorem val_list_prod (l : List K) (h : ∀ x ∈ l, x ≠ 0) :
    val l.prod = (l.map val).sum := by
  induction l with
  | nil => exact Padic.valuation_one
  | cons a l ih =>
    have ht : ∀ x ∈ l, x ≠ 0 := fun x hx => h _ (List.mem_cons_of_mem _ hx)
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    rw [val_mul (h _ (List.mem_cons_self ..)) (prod_ne l ht), ih ht]

private theorem prod_negBit_acc (a : K) (ha : a ≠ 0) (l : List K) (h : ∀ x ∈ l, x ≠ 0) :
    negBit (a*l.prod) ↔ l.foldl (fun s x => xorProp s (negBit x)) (negBit a) := by
  induction l generalizing a with
  | nil => simp
  | cons b l ih =>
    have hb := h b (List.mem_cons_self ..)
    have ht : ∀ x ∈ l, x ≠ 0 := fun x hx => h _ (List.mem_cons_of_mem _ hx)
    simp only [List.prod_cons, List.foldl_cons, ← mul_assoc]
    rw [ih (a*b) (mul_ne_zero ha hb) ht, negBit_mul a b ha hb]

theorem negBit_list_prod (l : List K) (h : ∀ x ∈ l, x ≠ 0) :
    negBit l.prod ↔ l.foldl (fun s x => xorProp s (negBit x)) False := by
  have f : negBit (1 : K) = False := propext ⟨negBit_one, False.elim⟩
  simpa only [one_mul, f] using prod_negBit_acc 1 one_ne_zero l h

theorem progression_rules (a b c : K) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (eq : a*c=b^2) : (val a+val c=2*val b) ∧ (negBit a ↔ negBit c) := by
  have eq' : a*c=b*b := by simpa [pow_two] using eq
  constructor
  · have v := congrArg val eq'
    rw [val_mul ha hc, val_mul hb hb] at v
    omega
  · have h := negBit_mul a c ha hc
    rw [eq', negBit_mul b b hb hb, xorProp] at h
    unfold xorProp at h
    tauto

private theorem chart_share_point (p q : Fin 4) (x : Fin 4 → O) :
    chartPoint p q x (0,p) = chartPoint p q x (1,q) := by
  simp [chartPoint, chartRow, rowEval]

theorem overlapCross_eq_image_difference (p q : Fin 4) (x : Fin 4 → O)
    (h : Collision p q x) (i : Fin 3) (j : Fin 4) :
    overlapCross p q x i j =
      ∏ y ∈ (Finset.univ.image (chartPoint p q x)) \
        (Finset.univ.image fun k : Fin 4 => chartPoint p q x (i,k)),
        (chartPoint p q x (i,j) - y) := by
  classical
  let E := chartPoint p q x
  let U := Finset.univ.image E
  let B := Finset.univ.image fun k : Fin 4 => E (i,k)
  have inj : Set.InjOn E (outsideSlots p q i : Set Node) := by
    intro a ha b hb eq
    rcases h a b eq with same|⟨_,hb'⟩|⟨ha',_⟩
    · exact same
    · exact ((Finset.mem_filter.mp hb).2.2.1 hb').elim
    · exact ((Finset.mem_filter.mp ha).2.2.1 ha').elim
  have image : (outsideSlots p q i).image E = U \ B := by
    ext y
    constructor
    · intro hy
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hy
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩, ?_⟩
      intro hy
      obtain ⟨r,_,eq⟩ := Finset.mem_image.mp hy
      exact outside_ne_row p q x h i r k hk eq
    · intro hy
      obtain ⟨hu,hb⟩ := Finset.mem_sdiff.mp hy
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
      have none : ∀ r : Fin 4, E (i,r) ≠ E k :=
        fun r eq => hb (Finset.mem_image.mpr ⟨r,Finset.mem_univ _,eq⟩)
      have nk : k.1 ≠ i := by
        obtain ⟨l,r⟩ := k
        intro eq
        change l=i at eq
        subst l
        exact none r rfl
      have onlyThird (hk : k = (0,p) ∨ k = (1,q)) : i=2 := by
        fin_cases i
        · exfalso
          apply none p
          rcases hk with h0|h1
          · rw [h0]; rfl
          · rw [h1]; exact chart_share_point p q x
        · exfalso
          apply none q
          rcases hk with h0|h1
          · rw [h0]; exact (chart_share_point p q x).symm
          · rw [h1]; rfl
        · rfl
      by_cases k1 : k=(1,q)
      · refine Finset.mem_image.mpr ⟨(0,p), ?_, ?_⟩
        have i2 := onlyThird (Or.inr k1)
        · simp [outsideSlots, i2]
        · rw [k1]; exact chart_share_point p q x
      · refine Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,nk,k1,?_⟩,rfl⟩
        by_cases k0 : k=(0,p)
        · exact Or.inl (onlyThird (Or.inl k0))
        · exact Or.inr k0
  unfold overlapCross
  rw [← Finset.prod_image inj, image]

structure Factor where
  node : Node
  index : ℕ
  multiplier : ℤ
  order : ℕ
  unitPart : ℤ
  negative : Bool
  deriving DecidableEq

def Factor.code (a : Factor) : PackedTerm := (a.index,a.order,a.negative)

def Factor.valid (forms : Array ResidueRow) (source target : ResidueRow) (a : Factor) : Prop :=
  a.index < forms.size ∧
  rowSub source target = rowMul a.multiplier forms[a.index]! ∧
  a.multiplier = (3 : ℤ)^a.order*a.unitPart ∧
  (a.unitPart : F) = if a.negative then -1 else 1

instance (forms : Array ResidueRow) (u v : ResidueRow) (a : Factor) :
    Decidable (a.valid forms u v) := by unfold Factor.valid; infer_instance

noncomputable def formVal (x : Fin 4 → O) (forms : Array ResidueRow) (k : ℕ) : ℤ :=
  val (rowEval (fun i => (x i : K)) forms[k]!)

def formBit (x : Fin 4 → O) (forms : Array ResidueRow) (k : ℕ) : Prop :=
  negBit (rowEval (fun i => (x i : K)) forms[k]!)

private theorem factor_of_cast (x : Fin 4 → O) (forms : Array ResidueRow) (a : Factor)
    (factor : a.multiplier = (3 : ℤ)^a.order*a.unitPart)
    (unit : (a.unitPart : F) = if a.negative then -1 else 1)
    (hne : rowEval (fun i => (x i : K)) forms[a.index]! ≠ 0) :
    let y := (a.multiplier : K)*rowEval (fun i => (x i : K)) forms[a.index]!
    val y = packedVal (formVal x forms) a.code ∧
      (negBit y ↔ packedUnit (formBit x forms) a.code) := by
  have onePart : (a.unitPart : F) = 1 ∨ (a.unitPart : F) = -1 := by
    cases hb : a.negative <;> simp [unit, hb]
  have nPart : a.unitPart ≠ 0 := by
    intro zz
    rcases onePart with u|u <;> rw [zz, Int.cast_zero] at u <;> exact (by decide : (0 : F) ≠ _) u
  have nm : (a.multiplier : K) ≠ 0 := by
    exact_mod_cast (show a.multiplier ≠ 0 by rw [factor]; exact mul_ne_zero (pow_ne_zero _ (by decide)) nPart)
  obtain ⟨hval,hunit⟩ := int_factor_scaled_mul a.multiplier a.unitPart a.order _ (1 : F)
    factor nm hne (by decide) onePart
  constructor
  · exact hval
  · rw [negBit_iff _ (mul_ne_zero nm hne)]
    unfold minusLead
    have base := negBit_iff _ hne
    unfold minusLead at base
    cases h : a.negative <;>
      simpa [Factor.code, packedUnit, formBit, h, unit, base, show (1 : F) ≠ -1 by decide] using hunit

private theorem factor_difference (p q : Fin 4) (x : Fin 4 → O) (forms : Array ResidueRow)
    (i : Node) (a : Factor) (h : a.valid forms (chartRow p q i) (chartRow p q a.node))
    (hd : chartPoint p q x i ≠ chartPoint p q x a.node) :
    val (chartPoint p q x i-chartPoint p q x a.node) = packedVal (formVal x forms) a.code ∧
      (negBit (chartPoint p q x i-chartPoint p q x a.node) ↔ packedUnit (formBit x forms) a.code) := by
  have eq : chartPoint p q x i - chartPoint p q x a.node =
    (a.multiplier : K)*rowEval (fun i => (x i : K)) forms[a.index]! := by
    unfold chartPoint
    rw [← rowEval_sub, h.2.1, rowEval_mul]
  have hn : rowEval (fun i => (x i : K)) forms[a.index]! ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at eq
    exact hd (sub_eq_zero.mp eq)
  rw [eq]
  apply factor_of_cast x forms a h.2.2.1 h.2.2.2 hn

private theorem val_zero_of_digit_nonzero (x : O) (h : PadicInt.toZMod x ≠ 0) : val (x : K) = 0 := by
  have hz : (x : K) ≠ 0 := by
    intro z
    have z' : x=0 := Subtype.ext z
    exact h (by simp [z'])
  have hv : 0 ≤ val (x : K) := PadicInt.valuation_coe_nonneg
  have eq : scaled (x : K) hz 0 hv = x := by
    apply Subtype.ext
    change (x : K) * (3 : K)^(-(0 : ℤ)) = (x : K)
    simp
  have r := scaled_residue (x : K) hz 0 hv
  rw [eq] at r
  by_contra h'
  have ne : 0 ≠ val (x : K) := Ne.symm h'
  rw [ite_eq_right ne] at r
  exact h r

def ProductValid (p q : Fin 4) (forms : Array ResidueRow) (i : Fin 3) (j : Fin 4)
    (l : List Factor) : Prop :=
  (l.map Factor.node).Nodup ∧ (l.map Factor.node).toFinset = outsideSlots p q i ∧
  l.all (fun a => decide (a.valid forms (chartRow p q (i,j)) (chartRow p q a.node))) = true

instance (p q : Fin 4) (forms : Array ResidueRow) (i : Fin 3) (j : Fin 4) (l : List Factor) :
    Decidable (ProductValid p q forms i j l) := by unfold ProductValid; infer_instance

def productVal (v : Nat → Int) (l : List Factor) : ℤ :=
  (l.map fun a => packedVal v a.code).sum

def productBit (u : Nat → Prop) (l : List Factor) : Prop :=
  l.foldl (fun s a => xorProp s (packedUnit u a.code)) False

private theorem cross_rules (p q : Fin 4) (x : Fin 4 → O) (collision : Collision p q x)
    (forms : Array ResidueRow) (i : Fin 3) (j : Fin 4) (l : List Factor)
    (hl : ProductValid p q forms i j l) :
    val (overlapCross p q x i j) = productVal (formVal x forms) l ∧
    (negBit (overlapCross p q x i j) ↔ productBit (formBit x forms) l) := by
  let f (k : Node) := chartPoint p q x (i,j)-chartPoint p q x k
  have eq : overlapCross p q x i j = (l.map fun a => f a.node).prod := by
    change (∏ k ∈ outsideSlots p q i, f k) = _
    rw [← hl.2.1, List.prod_toFinset f hl.1, List.map_map]
    rfl
  have valid (a) (ha : a ∈ l) : a.valid forms (chartRow p q (i,j)) (chartRow p q a.node) :=
    of_decide_eq_true (List.all_eq_true.mp hl.2.2 a ha)
  have extension (a) (ha : a ∈ l) : a.node ∈ outsideSlots p q i := by
    rw [← hl.2.1, List.mem_toFinset]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have diff (a) (ha : a ∈ l) : chartPoint p q x (i,j) ≠ chartPoint p q x a.node :=
    outside_ne_row p q x collision i j a.node (extension a ha)
  have nz : ∀ y ∈ (l.map fun a => f a.node), y ≠ 0 := by
    intro y hy
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hy
    exact sub_ne_zero.mpr (diff a ha)
  have params (a) (ha : a ∈ l) := factor_difference p q x forms (i,j) a (valid a ha) (diff a ha)
  constructor
  · rw [eq, val_list_prod _ nz, List.map_map]
    change (l.map fun a => val (f a.node)).sum = _
    congr 1
    exact List.map_congr_left (fun a ha => (params a ha).1)
  · rw [eq, negBit_list_prod _ nz]
    unfold productBit
    have hmap : l.map (fun a => negBit (f a.node)) =
        l.map (fun a => packedUnit (formBit x forms) a.code) :=
      List.map_congr_left (fun a ha => propext (params a ha).2)
    calc
      _ ↔ (l.map fun a => negBit (f a.node)).foldl xorProp False := by
        simp only [List.foldl_map]
      _ ↔ _ := by
        rw [hmap, List.foldl_map]

def effectVal (v : Nat → Int) (l : List Factor) (p q : Fin 4)
    (t0 t1 : ℤ) (i : Fin 3) (j : Fin 4) : ℤ :=
  if (i,j)=(0,p) then productVal v l-t0
  else if (i,j)=(1,q) then productVal v l-t1
  else productVal v l

def effectBit (u : Nat → Prop) (l : List Factor) (p q : Fin 4)
    (k0 k1 : Prop) (i : Fin 3) (j : Fin 4) : Prop :=
  if (i,j)=(0,p) then xorProp (productBit u l) k0
  else if (i,j)=(1,q) then xorProp (productBit u l) k1
  else productBit u l

noncomputable def overlapX (p q : Fin 4) (x : Fin 4 → O) (θ₀ θ₁ : K) (i : Fin 3) (j : Fin 4) : K :=
  overlapCross p q x i j / share p q θ₀ θ₁ (i,j)

def Geometric (p q : Fin 4) (x : Fin 4 → O) (θ₀ θ₁ : K) : Prop := ∀ i : Fin 3,
  overlapX p q x θ₀ θ₁ i 0 * overlapX p q x θ₀ θ₁ i 2 = (overlapX p q x θ₀ θ₁ i 1)^2 ∧
  overlapX p q x θ₀ θ₁ i 1 * overlapX p q x θ₀ θ₁ i 3 = (overlapX p q x θ₀ θ₁ i 2)^2

private theorem overlapCross_ne (p q : Fin 4) (x : Fin 4 → O) (collision : Collision p q x)
    (i : Fin 3) (j : Fin 4) : overlapCross p q x i j ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  exact sub_ne_zero.mpr (outside_ne_row p q x collision i j k hk)

private theorem effect_rules (p q : Fin 4) (x : Fin 4 → O) (collision : Collision p q x)
    (forms : Array ResidueRow) (θ₀ θ₁ : K) (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0)
    (i : Fin 3) (j : Fin 4) (l : List Factor) (hl : ProductValid p q forms i j l) :
    val (overlapX p q x θ₀ θ₁ i j) = effectVal (formVal x forms) l p q (val θ₀) (val θ₁) i j ∧
    (negBit (overlapX p q x θ₀ θ₁ i j) ↔
      effectBit (formBit x forms) l p q (negBit θ₀) (negBit θ₁) i j) := by
  obtain ⟨v,u⟩ := cross_rules p q x collision forms i j l hl
  have cross := overlapCross_ne p q x collision i j
  unfold overlapX
  rw [val_div _ _ cross (share_ne p q θ₀ θ₁ h₀ h₁ _), v,
    negBit_div _ _ cross (share_ne p q θ₀ θ₁ h₀ h₁ _), u]
  unfold effectVal effectBit share
  split_ifs <;> simp [xorProp, Padic.valuation_one, negBit_one]

theorem geometry_of_products (p q : Fin 4) (x : Fin 4 → O) (collision : Collision p q x)
    (forms : Array ResidueRow) (θ₀ θ₁ : K) (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0)
    (l : Fin 3 → Fin 4 → List Factor) (hl : ∀ i j, ProductValid p q forms i j (l i j))
    (geom : Geometric p q x θ₀ θ₁) :
    let v := fun i j => effectVal (formVal x forms) (l i j) p q (val θ₀) (val θ₁) i j
    let u := fun i j => effectBit (formBit x forms) (l i j) p q (negBit θ₀) (negBit θ₁) i j
    ∀ i : Fin 3, (v i 0+v i 2=2*v i 1) ∧ (u i 0 ↔ u i 2) ∧
      (v i 1+v i 3=2*v i 2) ∧ (u i 1 ↔ u i 3) := by
  dsimp
  intro i
  have ne (j) : overlapX p q x θ₀ θ₁ i j ≠ 0 :=
    div_ne_zero (overlapCross_ne p q x collision i j) (share_ne p q θ₀ θ₁ h₀ h₁ _)
  have eff (j) := effect_rules p q x collision forms θ₀ θ₁ h₀ h₁ i j (l i j) (hl i j)
  obtain ⟨v1,u1⟩ := progression_rules _ _ _ (ne 0) (ne 1) (ne 2) (geom i).1
  obtain ⟨v2,u2⟩ := progression_rules _ _ _ (ne 1) (ne 2) (ne 3) (geom i).2
  rw [(eff 0).1,(eff 1).1,(eff 2).1] at v1
  rw [(eff 1).1,(eff 2).1,(eff 3).1] at v2
  rw [(eff 0).2,(eff 2).2] at u1
  rw [(eff 1).2,(eff 3).2] at u2
  exact ⟨v1,u1,v2,u2⟩

structure FormWitness where
  left : Node
  right : Node
  multiplier : ℤ
  deriving Inhabited

def FormWitness.valid (p q : Fin 4) (row : ResidueRow) (W : FormWitness) : Prop :=
  W.left ≠ W.right ∧ ¬(W.left=(0,p) ∧ W.right=(1,q)) ∧ ¬(W.left=(1,q) ∧ W.right=(0,p)) ∧
  rowSub (chartRow p q W.left) (chartRow p q W.right) = rowMul W.multiplier row

instance (p q : Fin 4) (row : ResidueRow) (W : FormWitness) :
    Decidable (W.valid p q row) := by unfold FormWitness.valid; infer_instance

theorem form_nonzero_of_witness (p q : Fin 4) (x : Fin 4 → O) (collision : Collision p q x)
    (row : ResidueRow) (W : FormWitness) (h : W.valid p q row) :
    rowEval (fun i => (x i : K)) row ≠ 0 := by
  have ne : chartPoint p q x W.left ≠ chartPoint p q x W.right := by
    intro same
    rcases collision W.left W.right same with e|e|e
    · exact h.1 e
    · exact h.2.1 e
    · exact h.2.2.1 e
  intro z
  apply ne
  apply sub_eq_zero.mp
  unfold chartPoint
  rw [← rowEval_sub, h.2.2.2, rowEval_mul, z, mul_zero]

structure TriadRow where
  left : Factor
  mid : Factor
  right : Factor

def TriadRow.code (T : TriadRow) : PackedTriad := (T.left.code,T.mid.code,T.right.code)

def TriadRow.valid (forms : Array ResidueRow) (Tr : TriadRow) : Prop :=
  ([Tr.left,Tr.mid,Tr.right].all (fun a => decide
    (a.index < forms.size ∧ a.multiplier = (3 : ℤ)^a.order*a.unitPart ∧
      (a.unitPart : F) = if a.negative then -1 else 1))) = true ∧
  rowAdd (rowAdd (rowMul Tr.left.multiplier forms[Tr.left.index]!)
    (rowMul Tr.mid.multiplier forms[Tr.mid.index]!)) (rowMul Tr.right.multiplier forms[Tr.right.index]!) =
    (0,0,0,0)

instance (forms : Array ResidueRow) (Tr : TriadRow) : Decidable (Tr.valid forms) := by
  unfold TriadRow.valid
  infer_instance

private theorem factor_int_ne (a : Factor) (factor : a.multiplier = (3 : ℤ)^a.order*a.unitPart)
    (unit : (a.unitPart : F) = if a.negative then -1 else 1) : (a.multiplier : K) ≠ 0 := by
  have nu : a.unitPart ≠ 0 := by
    intro z
    rw [z, Int.cast_zero] at unit
    cases hb : a.negative
    · exact (show (0 : F) ≠ 1 by decide) (by simpa [hb] using unit)
    · exact (show (0 : F) ≠ -1 by decide) (by simpa [hb] using unit)
  exact_mod_cast (show a.multiplier ≠ 0 by rw [factor]; exact mul_ne_zero (pow_ne_zero _ (by decide)) nu)

theorem packed_triad_of_row (x : Fin 4 → O) (forms : Array ResidueRow) (Tr : TriadRow)
    (h : Tr.valid forms) (nonzero : ∀ k, k < forms.size → rowEval (fun i => (x i : K)) forms[k]! ≠ 0) :
    packedTriad (formVal x forms) (formBit x forms) Tr.code := by
  let p (a : Factor) := (a.multiplier : K)*rowEval (fun i => (x i : K)) forms[a.index]!
  have facts (a) (ha : a ∈ [Tr.left,Tr.mid,Tr.right]) :
      a.index < forms.size ∧ a.multiplier = (3 : ℤ)^a.order*a.unitPart ∧
        (a.unitPart : F) = if a.negative then -1 else 1 :=
    of_decide_eq_true (List.all_eq_true.mp h.1 a ha)
  have ne (a) (ha : a ∈ [Tr.left,Tr.mid,Tr.right]) : p a ≠ 0 := by
    obtain ⟨bound, mul, unit⟩ := facts a ha
    exact mul_ne_zero (factor_int_ne a mul unit) (nonzero a.index bound)
  have va (a) (ha : a ∈ [Tr.left,Tr.mid,Tr.right]) := by
    obtain ⟨bound,mul,unit⟩ := facts a ha
    exact factor_of_cast x forms a mul unit (nonzero a.index bound)
  have eq : p Tr.left+p Tr.mid+p Tr.right = 0 := by
    have row := congrArg (rowEval (fun i => (x i : K))) h.2
    rw [rowEval_add,rowEval_add,rowEval_mul,rowEval_mul,rowEval_mul] at row
    have n : rowEval (fun i => (x i : K)) (0,0,0,0) = 0 := by simp [rowEval]
    rw [n] at row
    exact row
  have hL : Tr.left ∈ [Tr.left,Tr.mid,Tr.right] := by simp
  have hM : Tr.mid ∈ [Tr.left,Tr.mid,Tr.right] := by simp
  have hR : Tr.right ∈ [Tr.left,Tr.mid,Tr.right] := by simp
  have tri := triad_val _ _ _ (ne _ hL) (ne _ hM) (ne _ hR) eq
  have vL := va _ hL
  have vM := va _ hM
  have vR := va _ hR
  dsimp only at vL vM vR
  change val (p Tr.left) = _ ∧ (negBit (p Tr.left) ↔ _) at vL
  change val (p Tr.mid) = _ ∧ (negBit (p Tr.mid) ↔ _) at vM
  change val (p Tr.right) = _ ∧ (negBit (p Tr.right) ↔ _) at vR
  unfold Triad at tri
  rw [← negBit_iff _ (ne _ hL), ← negBit_iff _ (ne _ hM), ← negBit_iff _ (ne _ hR),
    vL.1,vM.1,vR.1,vL.2,vM.2,vR.2] at tri
  exact tri

@[simp] private def factorFromLane (lane : ℕ) : Factor :=
  let m := overlapMultiplier lane
  ⟨(0,0), overlapIndex lane, m, overlapOffset m, overlapUnitPart m, overlapNegative m⟩

@[simp] private def overlapNode (k : ℕ) : Node :=
  (⟨(k/4)%3, Nat.mod_lt _ (by decide)⟩, ⟨k % 4, Nat.mod_lt _ (by decide)⟩)

@[simp] private def factorAtWord (word : ℕ) : Factor :=
  let a := factorFromLane (word/16)
  { a with node := overlapNode (word % 16) }

private def witnessAtWord (word : ℕ) : FormWitness :=
  ⟨overlapNode (word % 16), overlapNode ((word/16)%16), ((word/256 : ℕ) : ℤ)-10⟩

def factors00 (i : Fin 3) (j : Fin 4) : List Factor :=
  (#[[9224,9274,9365,8342,9291,9257,7319],[11656,11626,11589,11574,11611,11641,11559],[11768,11738,11701,12614,11723,11753,11687],[11864,11834,11797,11782,11819,11849,13639],[9224,9274,8594,7571,9291,9617,9257],[11400,11370,9650,9747,11355,9537,11385],[11480,11450,8514,9731,11435,9521,11465],[11544,11514,9634,7491,11499,9505,11529],[9349,11264,9714,9430,9811,9601,9495],[9333,11296,9698,9414,9795,9585,9479],[9317,11312,9682,9398,9779,9569,9463],[9301,11328,9666,9382,9763,9553,9447]] : Array (List ℕ))[i.val*4+j.val]!.map factorAtWord

def witnesses00 : Array FormWitness :=
  (
  #[2432,2490,2448,2464,2480,2395,2394,2393,2392,2422,2411,2410,2409,2408,2427,2426,2425,2424,2327,2326,1847,2331,2330,2329,2328,2354,2343,2341,2347,2346,2345,2344,2358,2357,2363,2362,2361,2360] : Array ℕ).map witnessAtWord

private def triadRow00 (k : ℕ) : TriadRow :=
  let word := overlapEncodedTriads00[k]!
  ⟨factorFromLane (overlapLane word 0), factorFromLane (overlapLane word 1),
    factorFromLane (overlapLane word 2)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem witness_valid00 : ∀ k : Fin 38,
    witnesses00[k.val]!.valid 0 0 overlapForms00[k.val]! := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem products_valid00 : ∀ i j,
    ProductValid 0 0 overlapForms00 i j (factors00 i j) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem triads_valid00 : ∀ k : Fin 357,
    (triadRow00 k.val).valid overlapForms00 := by
  decide +kernel

theorem form_ne00 (x : Fin 4 → O) (collision : Collision 0 0 x)
    (k : ℕ) (hk : k < 38) :
    rowEval (fun i => (x i : K)) overlapForms00[k]! ≠ 0 :=
  form_nonzero_of_witness 0 0 x collision _ witnesses00[k]! (witness_valid00 ⟨k,hk⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem rules00 (x : Fin 4 → O) (primitive : ∃ i, PadicInt.toZMod (x i) ≠ 0)
    (collision : Collision 0 0 x) (θ₀ θ₁ : K)
    (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0) (total : θ₀+θ₁=1)
    (geom : Geometric 0 0 x θ₀ θ₁) :
    ∀ k, overlapRules00 (formVal x overlapForms00) (formBit x overlapForms00)
      (val θ₀) (val θ₁) (negBit θ₀) (negBit θ₁) k := by
  let v := formVal x overlapForms00
  let u := formBit x overlapForms00
  let t0 := val θ₀
  let t1 := val θ₁
  let k0 := negBit θ₀
  let k1 := negBit θ₁
  have vnonneg (k) : 0 ≤ v k := rowEval_nonnegative x _
  have hprimitive : v 25 = 0 ∨ v 9 = 0 ∨ v 1 = 0 ∨ v 0 = 0 := by
    obtain ⟨i,hi⟩ := primitive
    have h0 := val_zero_of_digit_nonzero (x i) hi
    fin_cases i
    · exact Or.inl ((show v 25=0 by change val (rowEval _ (axisRow 0)) = 0; rw [rowEval_axis]; exact h0))
    · exact Or.inr (Or.inl ((show v 9=0 by change val (rowEval _ (axisRow 1)) = 0; rw [rowEval_axis]; exact h0)))
    · exact Or.inr (Or.inr (Or.inl ((show v 1=0 by change val (rowEval _ (axisRow 2)) = 0; rw [rowEval_axis]; exact h0))))
    · exact Or.inr (Or.inr (Or.inr ((show v 0=0 by change val (rowEval _ (axisRow 3)) = 0; rw [rowEval_axis]; exact h0))))
  have hfrac := split_fractions θ₀ θ₁ h₀ h₁ total
  rw [← negBit_iff θ₀ h₀, ← negBit_iff θ₁ h₁] at hfrac
  have hgeo := geometry_of_products 0 0 x collision overlapForms00 θ₀ θ₁ h₀ h₁
    factors00 products_valid00 geom
  intro k
  change overlapRules00 v u t0 t1 k0 k1 k
  by_cases less : k < 38
  · have shape : overlapRules00 v u t0 t1 k0 k1 k ↔ 0 ≤ v k := by
      interval_cases k <;> rfl
    exact shape.mpr (vnonneg k)
  by_cases intermediate : k < 52
  · interval_cases k
    · exact hprimitive
    · exact hfrac
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.2.1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.2.2
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.2.1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.2.2
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.2.1
    · simpa [overlapRules00, effectVal, effectBit, factors00, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.2.2
  have shape : overlapRules00 v u t0 t1 k0 k1 k ↔
      (if k < 409 then packedTriad v u (overlapTriads00 (k-52)) else True) := by
    rw [show k=(k-52)+52 by omega]
    rfl
  rw [shape]
  split_ifs with h
  · have hbound : k-52 < 357 := by omega
    have hvalid := triads_valid00 ⟨k-52,hbound⟩
    change (triadRow00 (k-52)).valid _ at hvalid
    change packedTriad v u (triadRow00 (k-52)).code
    apply packed_triad_of_row _ _ _ hvalid
    intro j hj
    exact form_ne00 x collision j (by simpa [overlapForms00] using hj)

def factors01 (i : Fin 3) (j : Fin 4) : List Factor :=
  (#[[9224,9274,11412,9366,8343,9291,9257],[11640,11610,11668,11574,11559,11595,11625],[11752,11722,11764,11686,12599,11707,11737],[11864,11834,11876,11798,11783,11819,11849],[9384,9418,9714,9827,9435,9617,9401],[9224,9274,8578,7555,9291,9601,9257],[11400,11370,9634,9747,11355,9521,11385],[11544,11514,8498,9731,11499,9505,11529],[11428,9350,9698,11264,9495,9811,9585],[11444,9334,9682,11296,9479,9795,9569],[11460,9318,9666,11312,9463,9779,9553],[11476,9302,9650,11328,9447,9763,9537]] : Array (List ℕ))[i.val*4+j.val]!.map factorAtWord

def witnesses01 : Array FormWitness :=
  (
  #[2432,2490,2448,2464,2480,2411,2410,2409,2408,2422,2436,2452,2468,2484,2427,2426,2425,2424,2327,2087,2331,2330,2329,2328,2354,2324,2342,2347,2346,2345,2344,2340,2359,2358,2363,2362,2361,2360,2356] : Array ℕ).map witnessAtWord

private def triadRow01 (k : ℕ) : TriadRow :=
  let word := overlapEncodedTriads01[k]!
  ⟨factorFromLane (overlapLane word 0), factorFromLane (overlapLane word 1),
    factorFromLane (overlapLane word 2)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem witness_valid01 : ∀ k : Fin 39,
    witnesses01[k.val]!.valid 0 1 overlapForms01[k.val]! := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem products_valid01 : ∀ i j,
    ProductValid 0 1 overlapForms01 i j (factors01 i j) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem triads_valid01 : ∀ k : Fin 390,
    (triadRow01 k.val).valid overlapForms01 := by
  decide +kernel

theorem form_ne01 (x : Fin 4 → O) (collision : Collision 0 1 x)
    (k : ℕ) (hk : k < 39) :
    rowEval (fun i => (x i : K)) overlapForms01[k]! ≠ 0 :=
  form_nonzero_of_witness 0 1 x collision _ witnesses01[k]! (witness_valid01 ⟨k,hk⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem rules01 (x : Fin 4 → O) (primitive : ∃ i, PadicInt.toZMod (x i) ≠ 0)
    (collision : Collision 0 1 x) (θ₀ θ₁ : K)
    (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0) (total : θ₀+θ₁=1)
    (geom : Geometric 0 1 x θ₀ θ₁) :
    ∀ k, overlapRules01 (formVal x overlapForms01) (formBit x overlapForms01)
      (val θ₀) (val θ₁) (negBit θ₀) (negBit θ₁) k := by
  let v := formVal x overlapForms01
  let u := formBit x overlapForms01
  let t0 := val θ₀
  let t1 := val θ₁
  let k0 := negBit θ₀
  let k1 := negBit θ₁
  have vnonneg (k) : 0 ≤ v k := rowEval_nonnegative x _
  have hprimitive : v 24 = 0 ∨ v 9 = 0 ∨ v 1 = 0 ∨ v 0 = 0 := by
    obtain ⟨i,hi⟩ := primitive
    have h0 := val_zero_of_digit_nonzero (x i) hi
    fin_cases i
    · exact Or.inl ((show v 24=0 by change val (rowEval _ (axisRow 0)) = 0; rw [rowEval_axis]; exact h0))
    · exact Or.inr (Or.inl ((show v 9=0 by change val (rowEval _ (axisRow 1)) = 0; rw [rowEval_axis]; exact h0)))
    · exact Or.inr (Or.inr (Or.inl ((show v 1=0 by change val (rowEval _ (axisRow 2)) = 0; rw [rowEval_axis]; exact h0))))
    · exact Or.inr (Or.inr (Or.inr ((show v 0=0 by change val (rowEval _ (axisRow 3)) = 0; rw [rowEval_axis]; exact h0))))
  have hfrac := split_fractions θ₀ θ₁ h₀ h₁ total
  rw [← negBit_iff θ₀ h₀, ← negBit_iff θ₁ h₁] at hfrac
  have hgeo := geometry_of_products 0 1 x collision overlapForms01 θ₀ θ₁ h₀ h₁
    factors01 products_valid01 geom
  intro k
  change overlapRules01 v u t0 t1 k0 k1 k
  by_cases less : k < 39
  · have shape : overlapRules01 v u t0 t1 k0 k1 k ↔ 0 ≤ v k := by
      interval_cases k <;> rfl
    exact shape.mpr (vnonneg k)
  by_cases intermediate : k < 53
  · interval_cases k
    · exact hprimitive
    · exact hfrac
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.2.1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.2.2
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.2.1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.2.2
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.2.1
    · simpa [overlapRules01, effectVal, effectBit, factors01, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.2.2
  have shape : overlapRules01 v u t0 t1 k0 k1 k ↔
      (if k < 443 then packedTriad v u (overlapTriads01 (k-53)) else True) := by
    rw [show k=(k-53)+53 by omega]
    rfl
  rw [shape]
  split_ifs with h
  · have hbound : k-53 < 390 := by omega
    have hvalid := triads_valid01 ⟨k-53,hbound⟩
    change (triadRow01 (k-53)).valid _ at hvalid
    change packedTriad v u (triadRow01 (k-53)).code
    apply packed_triad_of_row _ _ _ hvalid
    intro j hj
    exact form_ne01 x collision j (by simpa [overlapForms01] using hj)

def factors11 (i : Fin 3) (j : Fin 4) : List Factor :=
  (#[[9624,9658,9524,9686,9703,9675,9641],[9224,9274,11412,9366,8343,9291,9257],[11640,11610,11732,11574,11559,11595,11625],[11832,11802,11844,11766,12599,11787,11817],[9384,9418,9795,11568,9435,9682,9401],[9224,9274,8579,11648,9291,9602,9257],[11400,11370,9715,11728,11355,9522,11385],[11544,11514,8499,11744,11499,9506,11529],[11428,9350,9779,11265,9495,9586,11664],[11444,9334,9763,11297,9479,9570,11680],[11460,9318,9747,11313,9463,9554,11696],[11476,9302,9731,11329,9447,9538,11712]] : Array (List ℕ))[i.val*4+j.val]!.map factorAtWord

def witnesses11 : Array FormWitness :=
  (
  #[2433,2490,2449,2465,2481,2411,2410,2409,2408,2422,2436,2452,2468,2484,2427,2426,2425,2424,2343,2103,2347,2346,2345,2344,2354,2432,2448,2464,2480,2340,2416,2358,2363,2362,2361,2360,2356] : Array ℕ).map witnessAtWord

private def triadRow11 (k : ℕ) : TriadRow :=
  let word := overlapEncodedTriads11[k]!
  ⟨factorFromLane (overlapLane word 0), factorFromLane (overlapLane word 1),
    factorFromLane (overlapLane word 2)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem witness_valid11 : ∀ k : Fin 37,
    witnesses11[k.val]!.valid 1 1 overlapForms11[k.val]! := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem products_valid11 : ∀ i j,
    ProductValid 1 1 overlapForms11 i j (factors11 i j) := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem triads_valid11 : ∀ k : Fin 342,
    (triadRow11 k.val).valid overlapForms11 := by
  decide +kernel

theorem form_ne11 (x : Fin 4 → O) (collision : Collision 1 1 x)
    (k : ℕ) (hk : k < 37) :
    rowEval (fun i => (x i : K)) overlapForms11[k]! ≠ 0 :=
  form_nonzero_of_witness 1 1 x collision _ witnesses11[k]! (witness_valid11 ⟨k,hk⟩)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem rules11 (x : Fin 4 → O) (primitive : ∃ i, PadicInt.toZMod (x i) ≠ 0)
    (collision : Collision 1 1 x) (θ₀ θ₁ : K)
    (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0) (total : θ₀+θ₁=1)
    (geom : Geometric 1 1 x θ₀ θ₁) :
    ∀ k, overlapRules11 (formVal x overlapForms11) (formBit x overlapForms11)
      (val θ₀) (val θ₁) (negBit θ₀) (negBit θ₁) k := by
  let v := formVal x overlapForms11
  let u := formBit x overlapForms11
  let t0 := val θ₀
  let t1 := val θ₁
  let k0 := negBit θ₀
  let k1 := negBit θ₁
  have vnonneg (k) : 0 ≤ v k := rowEval_nonnegative x _
  have hprimitive : v 24 = 0 ∨ v 9 = 0 ∨ v 1 = 0 ∨ v 0 = 0 := by
    obtain ⟨i,hi⟩ := primitive
    have h0 := val_zero_of_digit_nonzero (x i) hi
    fin_cases i
    · exact Or.inl ((show v 24=0 by change val (rowEval _ (axisRow 0)) = 0; rw [rowEval_axis]; exact h0))
    · exact Or.inr (Or.inl ((show v 9=0 by change val (rowEval _ (axisRow 1)) = 0; rw [rowEval_axis]; exact h0)))
    · exact Or.inr (Or.inr (Or.inl ((show v 1=0 by change val (rowEval _ (axisRow 2)) = 0; rw [rowEval_axis]; exact h0))))
    · exact Or.inr (Or.inr (Or.inr ((show v 0=0 by change val (rowEval _ (axisRow 3)) = 0; rw [rowEval_axis]; exact h0))))
  have hfrac := split_fractions θ₀ θ₁ h₀ h₁ total
  rw [← negBit_iff θ₀ h₀, ← negBit_iff θ₁ h₁] at hfrac
  have hgeo := geometry_of_products 1 1 x collision overlapForms11 θ₀ θ₁ h₀ h₁
    factors11 products_valid11 geom
  intro k
  change overlapRules11 v u t0 t1 k0 k1 k
  by_cases less : k < 37
  · have shape : overlapRules11 v u t0 t1 k0 k1 k ↔ 0 ≤ v k := by
      interval_cases k <;> rfl
    exact shape.mpr (vnonneg k)
  by_cases intermediate : k < 51
  · interval_cases k
    · exact hprimitive
    · exact hfrac
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.2.1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 0).2.2.2
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.2.1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 1).2.2.2
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.2.1
    · simpa [overlapRules11, effectVal, effectBit, factors11, productVal, productBit,
        Factor.code, packedVal, packedUnit, xorProp, add_assoc] using (hgeo 2).2.2.2
  have shape : overlapRules11 v u t0 t1 k0 k1 k ↔
      (if k < 393 then packedTriad v u (overlapTriads11 (k-51)) else True) := by
    rw [show k=(k-51)+51 by omega]
    rfl
  rw [shape]
  split_ifs with h
  · have hbound : k-51 < 342 := by omega
    have hvalid := triads_valid11 ⟨k-51,hbound⟩
    change (triadRow11 (k-51)).valid _ at hvalid
    change packedTriad v u (triadRow11 (k-51)).code
    apply packed_triad_of_row _ _ _ hvalid
    intro j hj
    exact form_ne11 x collision j (by simpa [overlapForms11] using hj)

end PEqualNP.Outside.L_gct_234.OverlapBridge

namespace PEqualNP.Outside.L_gct_234

abbrev FieldRow := ZMod 3 × ZMod 3 × ZMod 3 × ZMod 3

def castResidueRow (x : ResidueRow) : FieldRow :=
  (x.1, x.2.1, x.2.2.1, x.2.2.2)

def scaleResidueRow (s : ZMod 3) (x : FieldRow) : FieldRow :=
  (s*x.1, s*x.2.1, s*x.2.2.1, s*x.2.2.2)

def CanonicalResidueRow (x : FieldRow) : Prop :=
  x.1 = 1 ∨ (x.1 = 0 ∧ (x.2.1 = 1 ∨
    (x.2.1 = 0 ∧ (x.2.2.1 = 1 ∨ (x.2.2.1 = 0 ∧ x.2.2.2 = 1)))))

instance (x : FieldRow) : Decidable (CanonicalResidueRow x) := by
  unfold CanonicalResidueRow
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem normalizedOverlapResidues_cover :
    ∀ x : FieldRow, CanonicalResidueRow x →
      ∃ a : Fin 40, castResidueRow normalizedOverlapResidues[a.val]! = x := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sign_normalizes_overlap_residue :
    ∀ x : FieldRow, x ≠ (0,0,0,0) →
      ∃ s : ZMod 3, (s = 1 ∨ s = -1) ∧ CanonicalResidueRow (scaleResidueRow s x) := by
  decide +kernel

def rowDotMod (c : ResidueRow) (x : FieldRow) : ZMod 3 :=
  (c.1 : ZMod 3)*x.1 + (c.2.1 : ZMod 3)*x.2.1 +
    (c.2.2.1 : ZMod 3)*x.2.2.1 + (c.2.2.2 : ZMod 3)*x.2.2.2

theorem rowDot_cast (c x : ResidueRow) :
    (rowDot c x : ZMod 3) = rowDotMod c (castResidueRow x) := by
  simp [rowDot, rowDotMod, castResidueRow]

theorem residueFacts_of_digit (v r : ℤ) (angular : ZMod 3) (nonneg : 0 ≤ v)
    (angularNonzero : angular ≠ 0) (lower : 0 ≤ r) (upper : r < 3)
    (digit : (r : ZMod 3) = if v = 0 then angular else 0) :
    residueFacts v (angular = -1) r := by
  interval_cases r
  · have ne : v ≠ 0 := by
      intro hz
      simp [hz] at digit
      exact angularNonzero digit.symm
    simpa [residueFacts] using show 0 < v by omega
  · have hz : v = 0 := by
      by_contra hn
      simp [hn] at digit
    have eq : angular = 1 := by simpa [hz] using digit.symm
    simp [residueFacts, hz, eq, show (1 : ZMod 3) ≠ -1 by decide]
  · have hz : v = 0 := by
      by_contra hn
      have impossible : (2 : ZMod 3) = 0 := by simpa [hn] using digit
      exact (show (2 : ZMod 3) ≠ 0 by decide) impossible
    have eq : angular = -1 := by
      calc
        angular = (2 : ZMod 3) := by simpa [hz] using digit.symm
        _ = -1 := by decide
    simp [residueFacts, hz, eq]

theorem residueFacts_of_rowDigit (v : ℤ) (angular : ZMod 3) (c x : ResidueRow)
    (nonneg : 0 ≤ v) (angularNonzero : angular ≠ 0)
    (digit : rowDotMod c (castResidueRow x) = if v = 0 then angular else 0) :
    residueFacts v (angular = -1) (rowDot c x % 3) := by
  apply residueFacts_of_digit v _ angular nonneg angularNonzero (Int.emod_nonneg _ (by decide))
    (Int.emod_lt_of_pos _ (by decide))
  rw [show ((rowDot c x % 3 : ℤ) : ZMod 3) = (rowDot c x : ZMod 3) from ZMod.intCast_mod _ 3,
    rowDot_cast]
  exact digit

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.OverlapBridge

open PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable def coordinateDigits (x : Fin 4 → O) : FieldRow :=
  (PadicInt.toZMod (x 0),PadicInt.toZMod (x 1),PadicInt.toZMod (x 2),PadicInt.toZMod (x 3))

theorem residue_from_coordinates (x : Fin 4 → O) (c r : ResidueRow)
    (digit : castResidueRow r = coordinateDigits x)
    (ne : rowEval (fun i => (x i : K)) c ≠ 0) :
    residueFacts (val (rowEval (fun i => (x i : K)) c))
      (negBit (rowEval (fun i => (x i : K)) c)) (rowDot c r % 3) := by
  let z := rowEval (fun i => (x i : K)) c
  have v : 0 ≤ val z := rowEval_nonnegative x c
  have u : scaled z ne 0 v = rowEval x c := by
    apply Subtype.ext
    change z*(3 : K)^(-(0 : ℤ)) = ((rowEval x c : O) : K)
    simp [z,rowEval]
  have h := scaled_residue z ne 0 v
  rw [u] at h
  change residueFacts (val z) (negBit z) _
  rw [negBit_iff z ne]
  unfold minusLead
  apply residueFacts_of_rowDigit (val z) (lead z ne) c r v (lead_ne_zero z ne)
  rw [digit, show rowDotMod c (coordinateDigits x) = PadicInt.toZMod (rowEval x c) by
    simp [coordinateDigits,rowDotMod,rowEval]]
  simpa only [eq_comm] using h

end PEqualNP.Outside.L_gct_234.OverlapBridge

namespace PEqualNP.Outside.L_gct_234.OverlapBridge

open PEqualNP.Outside.L_gct_234.Triadic
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem impossible00_from_solver
    (solver : ∀ (v : ℕ → ℤ) (u : ℕ → Prop) (t0 t1 : ℤ) (k0 k1 : Prop),
      (∀ k, overlapRules00 v u t0 t1 k0 k1 k) →
      ∀ a : ℕ, a < 40 → (∀ k, k < 38 → residueFacts (v k) (u k) (overlapResidue00 a k)) → False)
    (x : Fin 4 → O) (primitive : ∃ i, PadicInt.toZMod (x i) ≠ 0)
    (digit : CanonicalResidueRow (coordinateDigits x)) (collision : Collision 0 0 x)
    (θ₀ θ₁ : K) (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0) (total : θ₀+θ₁=1)
    (geom : Geometric 0 0 x θ₀ θ₁) : False := by
  obtain ⟨i,hi⟩ := normalizedOverlapResidues_cover (coordinateDigits x) digit
  refine solver _ _ _ _ _ _ (rules00 x primitive collision θ₀ θ₁ h₀ h₁ total geom) i i.isLt ?_
  intro k hk
  exact residue_from_coordinates x overlapForms00[k]! normalizedOverlapResidues[i.val]!
    hi (form_ne00 x collision k hk)

theorem impossible01_from_solver
    (solver : ∀ (v : ℕ → ℤ) (u : ℕ → Prop) (t0 t1 : ℤ) (k0 k1 : Prop),
      (∀ k, overlapRules01 v u t0 t1 k0 k1 k) →
      ∀ a : ℕ, a < 40 → (∀ k, k < 39 → residueFacts (v k) (u k) (overlapResidue01 a k)) → False)
    (x : Fin 4 → O) (primitive : ∃ i, PadicInt.toZMod (x i) ≠ 0)
    (digit : CanonicalResidueRow (coordinateDigits x)) (collision : Collision 0 1 x)
    (θ₀ θ₁ : K) (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0) (total : θ₀+θ₁=1)
    (geom : Geometric 0 1 x θ₀ θ₁) : False := by
  obtain ⟨i,hi⟩ := normalizedOverlapResidues_cover (coordinateDigits x) digit
  refine solver _ _ _ _ _ _ (rules01 x primitive collision θ₀ θ₁ h₀ h₁ total geom) i i.isLt ?_
  intro k hk
  exact residue_from_coordinates x overlapForms01[k]! normalizedOverlapResidues[i.val]!
    hi (form_ne01 x collision k hk)

theorem impossible11_from_solver
    (solver : ∀ (v : ℕ → ℤ) (u : ℕ → Prop) (t0 t1 : ℤ) (k0 k1 : Prop),
      (∀ k, overlapRules11 v u t0 t1 k0 k1 k) →
      ∀ a : ℕ, a < 40 → (∀ k, k < 37 → residueFacts (v k) (u k) (overlapResidue11 a k)) → False)
    (x : Fin 4 → O) (primitive : ∃ i, PadicInt.toZMod (x i) ≠ 0)
    (digit : CanonicalResidueRow (coordinateDigits x)) (collision : Collision 1 1 x)
    (θ₀ θ₁ : K) (h₀ : θ₀ ≠ 0) (h₁ : θ₁ ≠ 0) (total : θ₀+θ₁=1)
    (geom : Geometric 1 1 x θ₀ θ₁) : False := by
  obtain ⟨i,hi⟩ := normalizedOverlapResidues_cover (coordinateDigits x) digit
  refine solver _ _ _ _ _ _ (rules11 x primitive collision θ₀ θ₁ h₀ h₁ total geom) i i.isLt ?_
  intro k hk
  exact residue_from_coordinates x overlapForms11[k]! normalizedOverlapResidues[i.val]!
    hi (form_ne11 x collision k hk)

end PEqualNP.Outside.L_gct_234.OverlapBridge

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

open PEqualNP.Outside.L_gct_234.Triadic
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable def tupleDigits {x : Fin 4 → K} (T : NormalizedTuple x) : FieldRow :=
  (T.digit 0, T.digit 1, T.digit 2, T.digit 3)

theorem tupleDigits_nonzero {x : Fin 4 → K} (T : NormalizedTuple x) :
    tupleDigits T ≠ (0,0,0,0) := by
  obtain ⟨i, hi⟩ := T.has_unit
  intro allZero
  have h := Prod.mk.inj allZero
  have h' := Prod.mk.inj h.2
  have h'' := Prod.mk.inj h'.2
  have hz : T.digit i = 0 := by
    fin_cases i
    · exact h.1
    · exact h'.1
    · exact h''.1
    · exact h''.2
  exact hi hz

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

local instance : DecidableEq K := Classical.decEq K

def atSlot (A : APState) (j : Slot) : K := A.point j.1 j.2

def support (A : APState) : Finset K := by
  classical
  exact Finset.univ.image A.atSlot

def blockSupport (A : APState) (i : Fin 3) : Finset K := by
  classical
  exact Finset.univ.image (A.point i)

def distinctOutside (A : APState) (i : Fin 3) : Finset K := by
  classical
  exact A.support \ A.blockSupport i

def outerCross (A : APState) (i : Fin 3) (j : Fin 4) : K :=
  ∏ u ∈ A.distinctOutside i, (A.point i j - u)

def overlapX (A : APState) (share : Slot → K) (i : Fin 3) (j : Fin 4) : K :=
  A.outerCross i j / share (i,j)

def OverlapGeometric (A : APState) (share : Slot → K) : Prop := ∀ i,
  A.overlapX share i 0 * A.overlapX share i 2 = A.overlapX share i 1 ^ 2 ∧
    A.overlapX share i 1 * A.overlapX share i 3 = A.overlapX share i 2 ^ 2

theorem support_transform (A : APState) (t b : K) (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) :
    (A.transform t b π flip).support = A.support.image (fun x => b+t*x) := by
  classical
  ext x
  simp only [support, Finset.mem_image, Finset.mem_univ, true_and, atSlot, point_transform]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨slotMap π flip j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    obtain ⟨k, eq⟩ := (slotMap π flip).surjective j
    exact ⟨k, by rw [← eq]; rfl⟩

theorem blockSupport_transform (A : APState) (t b : K) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (i : Fin 3) :
    (A.transform t b π flip).blockSupport i = (A.blockSupport (π i)).image (fun x => b+t*x) := by
  classical
  ext x
  simp only [blockSupport, Finset.mem_image, Finset.mem_univ, true_and, point_transform]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨orient (flip i) j, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    obtain ⟨k, rfl⟩ := (orient (flip i)).surjective j
    exact ⟨k, rfl⟩

theorem affine_injective (t b : K) (ht : t ≠ 0) : Function.Injective fun x : K => b+t*x := by
  intro x y eq
  exact mul_left_cancel₀ ht (add_left_cancel eq)

theorem distinctOutside_transform (A : APState) (t b : K) (ht : t ≠ 0)
    (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (i : Fin 3) :
    (A.transform t b π flip).distinctOutside i = (A.distinctOutside (π i)).image (fun x => b+t*x) := by
  classical
  unfold distinctOutside
  rw [support_transform, blockSupport_transform, Finset.image_sdiff _ _ (affine_injective t b ht)]

theorem outerCross_transform (A : APState) (t b : K) (ht : t ≠ 0) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) (i : Fin 3) (j : Fin 4) :
    (A.transform t b π flip).outerCross i j =
      t^(A.distinctOutside (π i)).card * A.outerCross (π i) (orient (flip i) j) := by
  classical
  unfold outerCross
  rw [distinctOutside_transform A t b ht, point_transform, Finset.prod_image (affine_injective t b ht).injOn]
  simp_rw [show ∀ x y : K, b+t*x-(b+t*y)=t*(x-y) by intro x y; ring]
  rw [Finset.prod_mul_distrib, Finset.prod_const]

theorem overlapX_transform (A : APState) (share : Slot → K) (t b : K) (ht : t ≠ 0)
    (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (i : Fin 3) (j : Fin 4) :
    (A.transform t b π flip).overlapX (share ∘ slotMap π flip) i j =
      t^(A.distinctOutside (π i)).card * A.overlapX share (π i) (orient (flip i) j) := by
  unfold overlapX
  rw [outerCross_transform A t b ht, mul_div_assoc]
  rfl

theorem overlapGeometric_transform (A : APState) (share : Slot → K) (t b : K) (ht : t ≠ 0)
    (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (g : A.OverlapGeometric share) :
    (A.transform t b π flip).OverlapGeometric (share ∘ slotMap π flip) := by
  intro i
  simp only [overlapX_transform A share t b ht]
  let a := t^(A.distinctOutside (π i)).card
  have G := g (π i)
  cases flip i
  · simp only [orient, Bool.false_eq_true, ite_false, Equiv.refl_apply]
    constructor
    · linear_combination a^2 * G.1
    · linear_combination a^2 * G.2
  · simp only [orient, ite_true]
    have r0 : Fin.revPerm (0 : Fin 4) = 3 := by decide
    have r1 : Fin.revPerm (1 : Fin 4) = 2 := by decide
    have r2 : Fin.revPerm (2 : Fin 4) = 1 := by decide
    have r3 : Fin.revPerm (3 : Fin 4) = 0 := by decide
    rw [r0, r1, r2, r3]
    constructor
    · linear_combination a^2 * G.2
    · linear_combination a^2 * G.1

def SoleCollision (A : APState) (l r : Slot) : Prop :=
  l.1 ≠ r.1 ∧ A.atSlot l = A.atSlot r ∧
    ∀ a b : Slot, A.atSlot a = A.atSlot b → a = b ∨ (a = l ∧ b = r) ∨ (a = r ∧ b = l)

theorem soleCollision_comm (A : APState) (l r : Slot) (h : A.SoleCollision l r) : A.SoleCollision r l := by
  exact ⟨h.1.symm, h.2.1.symm, fun a b he => by
    rcases h.2.2 a b he with same | lr | rl
    · exact Or.inl same
    · exact Or.inr (Or.inr lr)
    · exact Or.inr (Or.inl rl)⟩

theorem soleCollision_transform (A : APState) (t b : K) (ht : t ≠ 0) (π : Equiv.Perm (Fin 3))
    (flip : Fin 3 → Bool) {a c : Slot} (h : A.SoleCollision (slotMap π flip a) (slotMap π flip c)) :
    (A.transform t b π flip).SoleCollision a c := by
  have pointEq (i : Slot) : (A.transform t b π flip).atSlot i = b+t*A.atSlot (slotMap π flip i) :=
    point_transform A t b π flip i.1 i.2
  refine ⟨?_, by rw [pointEq, pointEq, h.2.1], ?_⟩
  · intro eq
    exact h.1 (congrArg π eq)
  · intro j k equal
    rw [pointEq, pointEq] at equal
    have imageEqual := affine_injective t b ht equal
    rcases h.2.2 _ _ imageEqual with same | lr | rl
    · exact Or.inl ((slotMap π flip).injective same)
    · exact Or.inr (Or.inl ⟨(slotMap π flip).injective lr.1, (slotMap π flip).injective lr.2⟩)
    · exact Or.inr (Or.inr ⟨(slotMap π flip).injective rl.1, (slotMap π flip).injective rl.2⟩)

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def CanonicalCollisionSlots (p q : Fin 4) : Prop :=
  (p,q) = (0,0) ∨ (p,q) = (0,1) ∨ (p,q) = (1,1)

structure OverlapNormalized (A : APState) where
  p : Fin 4
  q : Fin 4
  canonical : CanonicalCollisionSlots p q
  coords : Fin 4 → O
  chart0 : ∀ j : Fin 4, A.point 0 j = ((j.val : K) - (p.val : K)) * (coords 0 : K)
  chart1 : ∀ j : Fin 4, A.point 1 j = ((j.val : K) - (q.val : K)) * (coords 1 : K)
  chart2 : ∀ j : Fin 4, A.point 2 j = (coords 3 : K) + (j.val : K) * (coords 2 : K)
  has_unit : ∃ i, PadicInt.toZMod (coords i) ≠ 0
  canonicalDigit : CanonicalResidueRow
    (PadicInt.toZMod (coords 0), PadicInt.toZMod (coords 1), PadicInt.toZMod (coords 2),
     PadicInt.toZMod (coords 3))
  steps_ne : ∀ i, A.step i ≠ 0
  root_none : A.root = none
  collisions : A.SoleCollision (0,p) (1,q)
  shares : Slot → K
  shares_ne : ∀ k, shares k ≠ 0
  shares_unit : ∀ k, k ≠ (0,p) → k ≠ (1,q) → shares k = 1
  shares_sum : shares (0,p) + shares (1,q) = 1
  geom : A.OverlapGeometric shares

private def lowSlot (j : Fin 4) : Fin 4 := if j.val ≤ 1 then j else j.rev

private def flipSlot (j : Fin 4) : Bool := decide (1 < j.val)

private theorem lowSlot_cases : ∀ j : Fin 4, lowSlot j = 0 ∨ lowSlot j = 1 := by decide +kernel

private theorem orient_lowSlot : ∀ j : Fin 4, orient (flipSlot j) (lowSlot j) = j := by decide +kernel

private theorem pair_permutation_fun : ∀ a b : Fin 3, a ≠ b →
    ∃ f : Fin 3 → Fin 3, f 0 = a ∧ f 1 = b ∧ f 0 ≠ f 1 ∧ f 0 ≠ f 2 ∧ f 1 ≠ f 2 := by
  decide +kernel

private theorem pair_permutation (a b : Fin 3) (ne : a ≠ b) :
    ∃ π : Equiv.Perm (Fin 3), π 0 = a ∧ π 1 = b := by
  obtain ⟨f, h0, h1, n01, n02, n12⟩ := pair_permutation_fun a b ne
  have fi : Function.Injective f := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi), h0, h1⟩

private theorem arrange_overlap (l r : Slot) (diff : l.1 ≠ r.1) :
    ∃ (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (p q : Fin 4),
      CanonicalCollisionSlots p q ∧
      ((slotMap π flip (0,p) = l ∧ slotMap π flip (1,q) = r) ∨
       (slotMap π flip (0,p) = r ∧ slotMap π flip (1,q) = l)) := by
  have ordered (a b : Slot) (h : a.1 ≠ b.1) (canonical : CanonicalCollisionSlots (lowSlot a.2) (lowSlot b.2)) :
      ∃ (π : Equiv.Perm (Fin 3)) (flip : Fin 3 → Bool) (p q : Fin 4), CanonicalCollisionSlots p q ∧
        (slotMap π flip (0,p) = a ∧ slotMap π flip (1,q) = b) := by
    obtain ⟨π, p0, p1⟩ := pair_permutation a.1 b.1 h
    let flip : Fin 3 → Bool := ![flipSlot a.2, flipSlot b.2, false]
    exact ⟨π, flip, lowSlot a.2, lowSlot b.2, canonical, by
      simp [slotMap, flip, p0, p1, orient_lowSlot]⟩
  rcases lowSlot_cases l.2 with l0 | l1 <;> rcases lowSlot_cases r.2 with r0 | r1
  · obtain ⟨π, flip, p, q, c, e⟩ := ordered l r diff (Or.inl (Prod.ext l0 r0))
    exact ⟨π, flip, p, q, c, Or.inl e⟩
  · obtain ⟨π, flip, p, q, c, e⟩ := ordered l r diff (Or.inr (Or.inl (Prod.ext l0 r1)))
    exact ⟨π, flip, p, q, c, Or.inl e⟩
  · obtain ⟨π, flip, p, q, c, e⟩ := ordered r l diff.symm (Or.inr (Or.inl (Prod.ext r0 l1)))
    exact ⟨π, flip, p, q, c, Or.inr e⟩
  · obtain ⟨π, flip, p, q, c, e⟩ := ordered l r diff (Or.inr (Or.inr (Prod.ext l1 r1)))
    exact ⟨π, flip, p, q, c, Or.inl e⟩

theorem normalized_overlap (A : APState) (l r : Slot) (coll : A.SoleCollision l r)
    (steps : ∀ i, A.step i ≠ 0) (noRoot : A.root = none)
    (share : Slot → K) (shareNe : ∀ k, share k ≠ 0)
    (shareUnit : ∀ k, k ≠ l → k ≠ r → share k = 1)
    (shareSum : share l + share r = 1) (g : A.OverlapGeometric share) :
    ∃ B : APState, Nonempty (OverlapNormalized B) := by
  classical
  obtain ⟨π, flip, p, q, canonical, maps⟩ := arrange_overlap l r coll.1
  let U := A.transform 1 0 π flip
  let S := share ∘ slotMap π flip
  have Ucoll : U.SoleCollision (0,p) (1,q) := by
    apply A.soleCollision_transform 1 0 one_ne_zero π flip
    rcases maps with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · simpa only [h0,h1] using coll
    · simpa only [h0,h1] using A.soleCollision_comm l r coll
  have Usteps (i : Fin 3) : U.step i ≠ 0 := by
    cases h : flip i <;> simp [U, transform, h, steps]
  have Une (k : Slot) : S k ≠ 0 := shareNe _
  have Uunit (k : Slot) (k0 : k ≠ (0,p)) (k1 : k ≠ (1,q)) : S k = 1 := by
    have i0 : slotMap π flip k ≠ slotMap π flip (0,p) := fun eq => k0 ((slotMap π flip).injective eq)
    have i1 : slotMap π flip k ≠ slotMap π flip (1,q) := fun eq => k1 ((slotMap π flip).injective eq)
    rcases maps with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact shareUnit _ (h0 ▸ i0) (h1 ▸ i1)
    · exact shareUnit _ (h1 ▸ i1) (h0 ▸ i0)
  have Usum : S (0,p) + S (1,q) = 1 := by
    rcases maps with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · simpa [S, h0, h1] using shareSum
    · simpa [S, h0, h1, add_comm] using shareSum
  have Ug : U.OverlapGeometric S := A.overlapGeometric_transform share 1 0 one_ne_zero π flip g
  let anchor := U.point 0 p
  have anchor1 : U.point 1 q = anchor := Ucoll.2.1.symm
  let data : Fin 4 → K := ![U.step 0, U.step 1, U.step 2, U.start 2 - anchor]
  obtain ⟨T⟩ := normalized_tuple data ⟨0, Usteps 0⟩
  obtain ⟨s, sign, digitCanon⟩ := sign_normalizes_overlap_residue (tupleDigits T) (tupleDigits_nonzero T)
  let w : O := if s = 1 then 1 else -1
  have redw : PadicInt.toZMod w = s := by
    rcases sign with h | h
    · simp [w,h]
    · simp [w,h,show (-1 : F) ≠ 1 by decide]
  have sne : s ≠ 0 := by rcases sign with h | h <;> simp [h]
  have wne : (w : K) ≠ 0 := by
    intro h
    have zero : w = 0 := by apply Subtype.ext; exact h
    exact sne (by rw [← redw, zero, map_zero])
  let t : K := (w : K) * (3 : K)^(-T.order)
  have tne : t ≠ 0 := mul_ne_zero wne (zpow_ne_zero _ (by norm_num))
  let B := U.transform t (-t * anchor) (Equiv.refl _) (fun _ => false)
  let coords (i : Fin 4) := w * T.entries i
  have coordCast (i : Fin 4) : (coords i : K) = t * data i := by
    simp only [coords, PadicInt.coe_mul, T.entries_cast, t]
    ring
  have coordRed (i : Fin 4) : PadicInt.toZMod (coords i) = s * T.digit i := by
    simp [coords, redw, NormalizedTuple.digit]
  have unitDigit : ∃ i, PadicInt.toZMod (coords i) ≠ 0 := by
    obtain ⟨i, hi⟩ := T.has_unit
    exact ⟨i, by rw [coordRed]; exact mul_ne_zero sne hi⟩
  have digitCanonical : CanonicalResidueRow
      (PadicInt.toZMod (coords 0), PadicInt.toZMod (coords 1), PadicInt.toZMod (coords 2),
       PadicInt.toZMod (coords 3)) := by
    simpa only [scaleResidueRow, tupleDigits, coordRed] using digitCanon
  have pointB (i : Fin 3) (j : Fin 4) : B.point i j = t * (U.point i j - anchor) := by
    unfold B
    rw [point_transform U]
    simp [orient]
    ring
  have B0 (j : Fin 4) : B.point 0 j = ((j.val : K) - (p.val : K)) * (coords 0 : K) := by
    rw [pointB, coordCast]
    dsimp [anchor, data, point]
    ring
  have B1 (j : Fin 4) : B.point 1 j = ((j.val : K) - (q.val : K)) * (coords 1 : K) := by
    rw [pointB, coordCast, ← anchor1]
    dsimp [data, point]
    ring
  have B2 (j : Fin 4) : B.point 2 j = (coords 3 : K) + (j.val : K) * (coords 2 : K) := by
    rw [pointB, coordCast, coordCast]
    dsimp [data, point]
    ring
  have slotId (k : Slot) : slotMap (Equiv.refl (Fin 3)) (fun _ => false) k = k := by
    obtain ⟨i,j⟩ := k
    simp [slotMap, orient]
  have Bcoll : B.SoleCollision (0,p) (1,q) := by
    apply U.soleCollision_transform _ _ tne
    simpa only [slotId] using Ucoll
  have Bg : B.OverlapGeometric S := by
    have hg := U.overlapGeometric_transform S t (-t*anchor) tne (Equiv.refl _) (fun _ => false) Ug
    have eq : S ∘ slotMap (Equiv.refl (Fin 3)) (fun _ => false) = S := by
      funext k
      simp [slotId]
    rwa [eq] at hg
  have Bsteps (i : Fin 3) : B.step i ≠ 0 := by simp [B, transform, tne, Usteps]
  have Bnone : B.root = none := by simp [B, U, transform, noRoot]
  exact ⟨B, ⟨p,q,canonical,coords,B0,B1,B2,unitDigit,digitCanonical,Bsteps,Bnone,Bcoll,
    S,Une,Uunit,Usum,Bg⟩⟩

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

theorem OverlapNormalized.chartPoint_eq {A : APState} (D : OverlapNormalized A) (k : Slot) :
    OverlapBridge.chartPoint D.p D.q D.coords k = A.atSlot k := by
  obtain ⟨i,j⟩ := k
  fin_cases i
  · simp [OverlapBridge.chartPoint, OverlapBridge.chartRow, OverlapBridge.rowEval, atSlot, D.chart0]
  · simp [OverlapBridge.chartPoint, OverlapBridge.chartRow, OverlapBridge.rowEval, atSlot, D.chart1]
  · simp [OverlapBridge.chartPoint, OverlapBridge.chartRow, OverlapBridge.rowEval, atSlot, D.chart2, add_comm]

theorem OverlapNormalized.bridgeCollision {A : APState} (D : OverlapNormalized A) :
    OverlapBridge.Collision D.p D.q D.coords := by
  intro a b e
  rw [D.chartPoint_eq, D.chartPoint_eq] at e
  exact D.collisions.2.2 a b e

theorem OverlapNormalized.bridgeCross {A : APState} (D : OverlapNormalized A) (i : Fin 3) (j : Fin 4) :
    OverlapBridge.overlapCross D.p D.q D.coords i j = A.outerCross i j := by
  classical
  rw [OverlapBridge.overlapCross_eq_image_difference _ _ _ D.bridgeCollision]
  have points : OverlapBridge.chartPoint D.p D.q D.coords = A.atSlot := funext D.chartPoint_eq
  simp only [points, outerCross, distinctOutside, support, blockSupport, atSlot]

theorem OverlapNormalized.bridgeShare {A : APState} (D : OverlapNormalized A) (k : Slot) :
    OverlapBridge.share D.p D.q (D.shares (0,D.p)) (D.shares (1,D.q)) k = D.shares k := by
  by_cases h0 : k = (0,D.p)
  · simp [OverlapBridge.share, h0]
  by_cases h1 : k = (1,D.q)
  · simp [OverlapBridge.share, h0, h1]
  · simp [OverlapBridge.share, h0,h1,D.shares_unit k h0 h1]

theorem OverlapNormalized.bridgeGeom {A : APState} (D : OverlapNormalized A) :
    OverlapBridge.Geometric D.p D.q D.coords (D.shares (0,D.p)) (D.shares (1,D.q)) := by
  have Xeq (i : Fin 3) (j : Fin 4) :
      OverlapBridge.overlapX D.p D.q D.coords (D.shares (0,D.p)) (D.shares (1,D.q)) i j =
        A.overlapX D.shares i j := by
    unfold OverlapBridge.overlapX overlapX
    rw [D.bridgeCross, D.bridgeShare]
  intro i
  simpa only [Xeq] using D.geom i

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem OverlapNormalized.impossible {A : APState} (D : OverlapNormalized A) : False := by
  let θ₀ := D.shares (0,D.p)
  let θ₁ := D.shares (1,D.q)
  have h₀ : θ₀ ≠ 0 := D.shares_ne _
  have h₁ : θ₁ ≠ 0 := D.shares_ne _
  have total : θ₀ + θ₁ = 1 := D.shares_sum
  have geom : OverlapBridge.Geometric D.p D.q D.coords θ₀ θ₁ := D.bridgeGeom
  have collision := D.bridgeCollision
  have digit : CanonicalResidueRow (OverlapBridge.coordinateDigits D.coords) := D.canonicalDigit
  have canonical := D.canonical
  unfold CanonicalCollisionSlots at canonical
  rcases canonical with h | h | h
  · have p : D.p = 0 := congrArg Prod.fst h
    have q : D.q = 0 := congrArg Prod.snd h
    exact OverlapBridge.impossible00_from_solver overlapImpossible00 D.coords D.has_unit digit
      (by simpa only [p,q] using collision) θ₀ θ₁ h₀ h₁ total (by simpa only [p,q] using geom)
  · have p : D.p = 0 := congrArg Prod.fst h
    have q : D.q = 1 := congrArg Prod.snd h
    exact OverlapBridge.impossible01_from_solver overlapImpossible01 D.coords D.has_unit digit
      (by simpa only [p,q] using collision) θ₀ θ₁ h₀ h₁ total (by simpa only [p,q] using geom)
  · have p : D.p = 1 := congrArg Prod.fst h
    have q : D.q = 1 := congrArg Prod.snd h
    exact OverlapBridge.impossible11_from_solver overlapImpossible11 D.coords D.has_unit digit
      (by simpa only [p,q] using collision) θ₀ θ₁ h₀ h₁ total (by simpa only [p,q] using geom)

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.TableGeometry

open PEqualNP.Outside.L_gct_234.Triadic CubeAP LocalFactor

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable def initialState {m d : Fin 3 → ℕ} (T : RationalTable m d) : APState :=
  ⟨fun i => (3 : K)*(m i : K), fun i => (d i : K), T.root.map fun z => (z : K)⟩

private theorem initial_point {m d : Fin 3 → ℕ} (T : RationalTable m d) (i : Fin 3) (j : Fin 4) :
    (initialState T).point i j = (exp (m i) (d i) j : K) := by
  simp [initialState,APState.point,exp]

private theorem initial_cast {m d : Fin 3 → ℕ} (T : RationalTable m d) (k : APState.Slot) :
    (initialState T).atSlot k = (exponents m d k : K) := initial_point T k.1 k.2

private theorem initial_denom {m d : Fin 3 → ℕ} (T : RationalTable m d) (i : Fin 3) (j : Fin 4) :
    (initialState T).denom i j = linearValue T.root (exp (m i) (d i) j) := by
  cases h : T.root <;> simp [APState.denom, initialState, h, linearValue, APState.point, exp]

private theorem initial_outer {m d : Fin 3 → ℕ} (T : RationalTable m d) (i : Fin 3) (j : Fin 4) :
    (initialState T).outerCross i j = (outerProduct m d i j : K) := by
  classical
  let castNat : ℕ → K := fun n => (n : K)
  let U := Finset.univ.image (exponents m d)
  let B := Finset.univ.image (exp (m i) (d i))
  have us : (initialState T).support = U.image castNat := by
    unfold APState.support U
    rw [Finset.image_image]
    congr 1
    funext k
    exact initial_cast T k
  have bs : (initialState T).blockSupport i = B.image castNat := by
    unfold APState.blockSupport B
    rw [Finset.image_image]
    congr 1
    funext k
    exact initial_point T i k
  unfold APState.outerCross APState.distinctOutside
  have cast_inj : Function.Injective castNat := Nat.cast_injective
  rw [us,bs,← Finset.image_sdiff _ _ cast_inj,
    Finset.prod_image cast_inj.injOn,initial_point T]
  unfold outerProduct
  push_cast
  rfl

private theorem outer_eq_cross (A : APState) (inj : A.Disjoint) (i : Fin 3) (j : Fin 4) :
    A.outerCross i j = A.cross i j := by
  classical
  have eq : A.distinctOutside i = (APState.otherBlockIndices i).image A.atSlot := by
    ext y
    unfold APState.distinctOutside APState.support APState.blockSupport APState.otherBlockIndices
    constructor
    · intro h
      obtain ⟨hU,hB⟩ := Finset.mem_sdiff.mp h
      obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hU
      refine Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
      intro same
      exact hB (Finset.mem_image.mpr ⟨k.2, Finset.mem_univ _,by simp [APState.atSlot,same]⟩)
    · intro h
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp h
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,?_⟩
      intro hb
      obtain ⟨t,_,h⟩ := Finset.mem_image.mp hb
      have eq : ((i,t) : APState.Slot) = k := inj h
      exact (Finset.mem_filter.mp hk).2 (congrArg Prod.fst eq).symm
  unfold APState.outerCross APState.cross
  have inj' : Function.Injective A.atSlot := inj
  rw [eq,Finset.prod_image (inj'.injOn)]
  rfl

private theorem quotient_geometry (l r : Fin 4 → K) (c t : K)
    (hl : ∀ j, l j ≠ 0)
    (h : ∀ j : Fin 4, l j = c*t^j.val*r j) :
    (r 0/l 0)*(r 2/l 2) = (r 1/l 1)^2 ∧
      (r 1/l 1)*(r 3/l 3) = (r 2/l 2)^2 := by
  have hr (j) : r j ≠ 0 := by
    intro z
    exact hl j (by rw [h,z,mul_zero])
  have hc : c ≠ 0 := by
    intro z
    exact hl 0 (by rw [h,z,zero_mul,zero_mul])
  have ht : t ≠ 0 := by
    intro z
    exact hl 1 (by rw [h,z]; simp)
  have inv (j : Fin 4) : r j/l j = c⁻¹*(t⁻¹)^j.val := by
    rw [h,inv_pow]
    field_simp [hc, pow_ne_zero j.val ht, hr j]
  simp_rw [inv]
  constructor
  · change (c⁻¹*(t⁻¹)^0)*(c⁻¹*(t⁻¹)^2)=(c⁻¹*(t⁻¹)^1)^2
    ring
  · change (c⁻¹*(t⁻¹)^1)*(c⁻¹*(t⁻¹)^3)=(c⁻¹*(t⁻¹)^2)^2
    ring

theorem initial_disjoint_data {m d : Fin 3 → ℕ} (T : RationalTable m d)
    (no_collision : Function.Injective (exponents m d)) :
    (initialState T).Disjoint ∧ (initialState T).Separate ∧ (initialState T).Geometric := by
  let A := initialState T
  have inj : A.Disjoint := by
    intro k l h
    apply no_collision
    apply (Nat.cast_injective (R := K))
    change (initialState T).atSlot k = (initialState T).atSlot l at h
    simpa only [initial_cast T] using h
  have separate : A.Separate := by
    intro i j h
    have ht := T.linear_ne (exp (m i) (d i) j)
      (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩)
    rw [initial_denom T] at h
    apply ht
    cases hr : T.root
    · simp [linearValue,hr]
      simpa [linearValue,hr] using h
    · simp only [linearValue,hr] at h ⊢
      exact_mod_cast h
  refine ⟨inj, separate, ?_⟩
  intro i
  have hg (j : Fin 4) : A.denom i j = (T.scale i : K)*(T.ratio i : K)^j.val*A.cross i j := by
    have geo := T.geometry_cast (K:=K) i j
    rw [T.share_eq_one_of_unique (i,j) (fun k eq => no_collision eq), Rat.cast_one, one_mul,
      ← initial_denom T, ← initial_outer T, outer_eq_cross A inj] at geo
    exact geo
  exact quotient_geometry (A.denom i) (A.cross i) _ _ (separate i) hg

theorem initial_overlap_data {m d : Fin 3 → ℕ} (T : RationalTable m d)
    (large : 11 ≤ (Finset.univ.image (exponents m d)).card)
    (nd : ∀ i,0 < d i)
    (h : ¬Function.Injective (exponents m d)) :
    ∃ l r : APState.Slot,
      (initialState T).SoleCollision l r ∧ (initialState T).root = none ∧
      (∀ k : APState.Slot, (T.share k : K) ≠ 0) ∧
      (∀ k : APState.Slot, k ≠ l → k ≠ r → (T.share k : K) = 1) ∧
      (T.share l : K) + (T.share r : K) = 1 ∧
      (initialState T).OverlapGeometric (fun k => (T.share k : K)) := by
  classical
  let e := exponents m d
  let A := initialState T
  unfold Function.Injective at h
  push Not at h
  obtain ⟨l,r,same,ne⟩ := h
  have eleven : (Finset.univ.image e).card = 11 := by
    have upper : (Finset.univ.image e).card ≤ 12 := Finset.card_image_le.trans (by simp)
    have not_twelve : (Finset.univ.image e).card ≠ 12 := by
      intro eq
      have hi := Finset.card_image_iff.mp (by simpa using eq :
        (Finset.univ.image e).card = (Finset.univ : Finset (Fin 3 × Fin 4)).card)
      exact ne (hi (Finset.mem_univ _) (Finset.mem_univ _) same)
    change 11 ≤ (Finset.univ.image e).card at large
    omega
  have apart : l.1 ≠ r.1 := by
    obtain ⟨l,i⟩ := l
    obtain ⟨r,j⟩ := r
    intro eq
    change l=r at eq
    subst r
    have ji : i=j := exp_injective (m l) (d l) (nd l) same
    exact ne (Prod.ext rfl ji)
  have rem := injective_except_collision m d large l r ne same
  have exactPair (k j : APState.Slot) (h : e k=e j) :
      k=j ∨ (k=l ∧ j=r) ∨ (k=r ∧ j=l) := by
    by_cases hk : k=r
    · subst k
      by_cases hj : j=r
      · exact Or.inl hj.symm
      have jl : j=l := rem hj ne (h.symm.trans same.symm)
      exact Or.inr (Or.inr ⟨rfl,jl⟩)
    by_cases hj : j=r
    · subst j
      exact Or.inr (Or.inl ⟨rem hk ne (h.trans same.symm),rfl⟩)
    · exact Or.inl (rem hk hj h)
  have hn : T.root = none := T.constant_if_overlap eleven
  have hs (k) : (T.share k : K) ≠ 0 := by exact_mod_cast T.share_ne k
  refine ⟨l,r,⟨apart,?_ ,?_⟩,by simp [A,initialState,hn], hs, ?_, ?_, ?_⟩
  · rw [initial_cast T, initial_cast T, same]
  · intro k j eq
    apply exactPair k j
    apply (Nat.cast_injective (R := K))
    simpa only [initial_cast T] using eq
  · intro k hkl hkr
    rw [T.share_eq_one_of_unique k (by
      intro j hj
      rcases exactPair j k hj with h|⟨h,h'⟩|⟨h,h'⟩
      · exact h
      · exact (hkr h').elim
      · exact (hkl h').elim), Rat.cast_one]
  · have total := T.shares_sum_one_of_exact_pair l r ne same (by
      intro k h
      rcases exactPair k l h with h|⟨h,_⟩|⟨h,_⟩
      · exact Or.inl h
      · exact Or.inl h
      · exact Or.inr h)
    exact_mod_cast total
  · intro i
    have hg (j : Fin 4) : (T.share (i,j) : K) =
        (T.scale i : K)*(T.ratio i : K)^j.val*A.outerCross i j := by
      have g := T.geometry_cast (K:=K) i j
      rw [hn,linearValue,mul_one,←initial_outer T] at g
      exact g
    exact quotient_geometry (fun j => (T.share (i,j) : K)) (A.outerCross i) _ _ (fun j => hs (i,j)) hg

end PEqualNP.Outside.L_gct_234.TableGeometry

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

abbrev DisjointRow := Int × Int × Int × Int × Int × Int × Int

def disjointDot (x y : DisjointRow) : Int :=
  x.1*y.1 + x.2.1*y.2.1 + x.2.2.1*y.2.2.1 + x.2.2.2.1*y.2.2.2.1 +
  x.2.2.2.2.1*y.2.2.2.2.1 + x.2.2.2.2.2.1*y.2.2.2.2.2.1 +
  x.2.2.2.2.2.2*y.2.2.2.2.2.2

abbrev CoeffTerm := Nat × Int
abbrev CoeffTriad := CoeffTerm × CoeffTerm × CoeffTerm

def coeffOrder (a : Int) : Nat := if a % 9 = 0 then 2 else if a % 3 = 0 then 1 else 0

def coeffUnit (a : Int) : Int := a / ((3 : Int) ^ coeffOrder a)

def packCoeffTerm (t : CoeffTerm) : PackedTerm :=
  (t.1, coeffOrder t.2, decide (coeffUnit t.2 % 3 = 2))

def packCoeffTriad (tr : CoeffTriad) : PackedTriad :=
  (packCoeffTerm tr.1, packCoeffTerm tr.2.1, packCoeffTerm tr.2.2)

def disjointTriadIndicesConst : List Nat := [55,56,57,59,60,61,62,63,64,65,66,68,69,72,73,75,77,78,83,85,86,87,88,92,93,96,99,101,102,104,106,107,108,110,111,114,115,116,117,119,122,123,124,127,128,130,133,137,138,145,147,150,152,156,158,159,168,170,184,185,191,194,195,197,200,205,210,212,213,222,223,228,233,234,236,237,241,251,253,256,257,259,260,264,265,267,270,283,287,288,297,300,326,333,348,349,352,358,360,363,378,381,385,395]

def disjointEncodedCoeffTriadsConst : Array Nat := #[
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,58112320,96032102,60473669,0,97046947,
  96819559,53645634,58373441,57060161,56797505,63628097,63626562,0,59945796,60474691,0,0,54429634,54960448,0,58896769,0,87365963,62041934,0,
  0,0,0,52595010,0,87627078,59682115,57583489,62836610,0,0,0,113039718,56272832,0,0,57324352,0,0,61778253,
  0,59425600,87890249,0,59681604,0,62042956,60994376,60475329,0,60475777,63627201,0,0,62307148,61258568,52070784,62834626,0,88677706,
  0,0,52332354,61000002,54433602,0,0,61785986,63099266,0,91566419,0,0,62043467,0,0,0,60209988,63619409,0,
  0,0,0,0,0,53120322,0,63618898,0,0,62042445,0,54696258,0,0,0,96261030,0,95769445,88415049,
  0,0,0,0,0,0,0,0,60473158,0,62052161,0,0,0,0,0,0,0,0,0,
  0,0,0,0,113826659,90517847,0,0,0,0,0,59681093,0,0,87628620,51808576,0,54954946,0,0,
  90747287,0,0,0,0,55748416,0,0,0,0,92092761,0,86839621,92848543,0,0,0,0,0,0,
  0,0,95244645,55217602,0,0,0,0,53380994,0,0,0,0,87102278,95506788,0,55222208,57322817,0,0,
  0,54171584,0,0,0,0,0,0,0,0,0,56273728,0,57848129,0,0,95507302,93899171,0,105421635,
  93669731,0,0,0,92058518,97051055,0,59424704,0,0,56534849,0,0,0,0,0,0,0,0,0,
  0,0,0,62826833,0,0,0,63622594,53908290,0,0,0,0,0,0,0,0,107524951,0,0,
  92355418,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,96295273,0,0,0,0,0,0,59420097,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,63620431,59680582,0,0,58894785,0,0,0,0,0,87595403,0,
  52857666,0,0,91304790,0,0,0,0,0,0,0,0,0,0,0,0,0,0,57323456,0,
  0,58632129,0,0,0,109624147,0,0,0,0,0,0,0,0,0,90780504]

@[simp] def disjointDecodeCoeffTerm (lane : Nat) : CoeffTerm :=
  (lane % 64, ((lane / 64 : Nat) : Int) - 4)

@[simp] def disjointDecodeCoeffTriad (word : Nat) : CoeffTriad :=
  (disjointDecodeCoeffTerm (word % 512),
   disjointDecodeCoeffTerm (word / 512 % 512),
   disjointDecodeCoeffTerm (word / 512 ^ 2 % 512))

def disjointCoeffTriadAtConst (k : Nat) : CoeffTriad :=
  if disjointEncodedCoeffTriadsConst[k]! = 0 then default else disjointDecodeCoeffTriad disjointEncodedCoeffTriadsConst[k]!

def disjointTriadAtConst (k : Nat) : PackedTriad := packCoeffTriad (disjointCoeffTriadAtConst k)

def disjointFormsConst : Array DisjointRow :=
  #[(0,0,0,0,0,1,0), (0,0,0,0,1,0,0), (0,0,0,1,0,0,0), (0,0,1, -3,0,0,0), (0,0,1, -3,0,1,0), (0,0,1, -3,0,2,0), (0,0,1, -3,0,3,0), (0,0,1, -2,0,0,0), (0,0,1, -2,0,1,0), (0,0,1, -2,0,2,0), (0,0,1, -2,0,3,0), (0,0,1, -1,0,0,0), (0,0,1, -1,0,1,0), (0,0,1, -1,0,2,0), (0,0,1, -1,0,3,0), (0,0,1,0,0,0,0), (0,0,1,0,0,1,0), (0,0,1,0,0,2,0), (0,0,1,0,0,3,0), (0,1, -1,0,0, -3,0), (0,1, -1,0,0, -2,0), (0,1, -1,0,0, -1,0), (0,1, -1,0,0,0,0), (0,1, -1,0,1, -3,0), (0,1, -1,0,1, -2,0), (0,1, -1,0,1, -1,0), (0,1, -1,0,1,0,0), (0,1, -1,0,2, -3,0), (0,1, -1,0,2, -2,0), (0,1, -1,0,2, -1,0), (0,1, -1,0,2,0,0), (0,1, -1,0,3, -3,0), (0,1, -1,0,3, -2,0), (0,1, -1,0,3, -1,0), (0,1, -1,0,3,0,0), (0,1,0, -3,0,0,0), (0,1,0, -3,1,0,0), (0,1,0, -3,2,0,0), (0,1,0, -3,3,0,0), (0,1,0, -2,0,0,0), (0,1,0, -2,1,0,0), (0,1,0, -2,2,0,0), (0,1,0, -2,3,0,0), (0,1,0, -1,0,0,0), (0,1,0, -1,1,0,0), (0,1,0, -1,2,0,0), (0,1,0, -1,3,0,0), (0,1,0,0,0,0,0), (0,1,0,0,1,0,0), (0,1,0,0,2,0,0), (0,1,0,0,3,0,0)]

def disjointResiduesConst : Array DisjointRow :=
  #[(0,0,0,1,0,0,0), (0,0,0,1,1,0,0), (0,0,0,1,1,1,0), (0,0,1,0,0,0,0), (0,0,1,1,0,0,0), (0,0,1,1,1,0,0), (0,0,1,1,1,1,0), (0,1,0,1,1,0,0), (0,1,1,1,0,0,0), (0,1,2,0,0,0,0), (0,1,2,1,0,0,0), (0,1,2,1,1,0,0), (0,1,2,1,1,1,0)]

def disjointResidueConst (a k : Nat) : Int :=
  disjointDot disjointFormsConst[k]! disjointResiduesConst[a]! % 3

noncomputable def disjointNonTriadRulesConst (v m : Nat → Int) (u : Nat → Prop) : Nat → Prop
  | 401 => (((v 48) + (v 47) + (v 17) + (v 50) + (v 15) + (v 16) + (v 49) + (v 18) + (v 40) + (v 39) + (v 9) + (v 42) + (v 7) + (v 8) + (v 41) + (v 10)) = ((2 * (v 44)) + (2 * (v 43)) + (2 * (v 13)) + (2 * (v 46)) + (2 * (v 11)) + (2 * (v 12)) + (2 * (v 45)) + (2 * (v 14))))
  | 403 => (((v 44) + (v 43) + (v 13) + (v 46) + (v 11) + (v 12) + (v 45) + (v 14) + (v 36) + (v 35) + (v 5) + (v 38) + (v 3) + (v 4) + (v 37) + (v 6)) = ((2 * (v 40)) + (2 * (v 39)) + (2 * (v 9)) + (2 * (v 42)) + (2 * (v 7)) + (2 * (v 8)) + (2 * (v 41)) + (2 * (v 10))))
  | 405 => (((v 35) + (v 39) + (v 43) + (v 20) + (v 22) + (v 21) + (v 47) + (v 19) + (v 37) + (v 41) + (v 45) + (v 28) + (v 30) + (v 29) + (v 49) + (v 27)) = ((2 * (v 36)) + (2 * (v 40)) + (2 * (v 44)) + (2 * (v 24)) + (2 * (v 26)) + (2 * (v 25)) + (2 * (v 48)) + (2 * (v 23))))
  | 406 => (((((((((u 35) ↔ (u 39)) ↔ (u 43)) ↔ (u 20)) ↔ (u 22)) ↔ (u 21)) ↔ (u 47)) ↔ (u 19)) ↔ ((((((((u 37) ↔ (u 41)) ↔ (u 45)) ↔ (u 28)) ↔ (u 30)) ↔ (u 29)) ↔ (u 49)) ↔ (u 27)))
  | 407 => (((v 36) + (v 40) + (v 44) + (v 24) + (v 26) + (v 25) + (v 48) + (v 23) + (v 38) + (v 42) + (v 46) + (v 32) + (v 34) + (v 33) + (v 50) + (v 31)) = ((2 * (v 37)) + (2 * (v 41)) + (2 * (v 45)) + (2 * (v 28)) + (2 * (v 30)) + (2 * (v 29)) + (2 * (v 49)) + (2 * (v 27))))
  | 409 => (((v 26) + (v 3) + (v 22) + (v 7) + (v 11) + (v 30) + (v 15) + (v 34) + (v 24) + (v 5) + (v 20) + (v 9) + (v 13) + (v 28) + (v 17) + (v 32)) = ((2 * (v 25)) + (2 * (v 4)) + (2 * (v 21)) + (2 * (v 8)) + (2 * (v 12)) + (2 * (v 29)) + (2 * (v 16)) + (2 * (v 33))))
  | 410 => (((u 34) ↔ (((((((u 26) ↔ (u 3)) ↔ (u 22)) ↔ (u 7)) ↔ (u 11)) ↔ (u 30)) ↔ (u 15))) ↔ ((u 32) ↔ (((((((u 24) ↔ (u 5)) ↔ (u 20)) ↔ (u 9)) ↔ (u 13)) ↔ (u 28)) ↔ (u 17))))
  | 411 => (((v 25) + (v 4) + (v 21) + (v 8) + (v 12) + (v 29) + (v 16) + (v 33) + (v 23) + (v 6) + (v 19) + (v 10) + (v 14) + (v 27) + (v 18) + (v 31)) = ((2 * (v 24)) + (2 * (v 5)) + (2 * (v 20)) + (2 * (v 9)) + (2 * (v 13)) + (2 * (v 28)) + (2 * (v 17)) + (2 * (v 32))))
  | 413 => (((m 0) = (v 11)) ∨ ((m 0) = (v 46)) ∨ ((m 0) = (v 12)) ∨ ((m 0) = (v 44)) ∨ ((m 0) = (v 45)) ∨ ((m 0) = (v 14)) ∨ ((m 0) = (v 13)) ∨ ((m 0) = (v 43)))
  | 422 => (((v 2) ≤ (m 0)) ∨ (((((if ((v 44) = (m 0)) then 1 else 0) + (if ((v 43) = (m 0)) then 1 else 0) + (if ((v 13) = (m 0)) then 1 else 0) + (if ((v 46) = (m 0)) then 1 else 0) + (if ((v 11) = (m 0)) then 1 else 0) + (if ((v 12) = (m 0)) then 1 else 0) + (if ((v 45) = (m 0)) then 1 else 0) + (if ((v 14) = (m 0)) then 1 else 0)) % 3) = 0) ∧ ((((if ((v 44) = (m 0)) then (if (u 44) then 1 else (-1 : Int)) else 0) + (if ((v 43) = (m 0)) then (if (u 43) then 1 else (-1 : Int)) else 0) + (if ((v 13) = (m 0)) then (if (u 13) then 1 else (-1 : Int)) else 0) + (if ((v 46) = (m 0)) then (if (u 46) then 1 else (-1 : Int)) else 0) + (if ((v 11) = (m 0)) then (if (u 11) then 1 else (-1 : Int)) else 0) + (if ((v 12) = (m 0)) then (if (u 12) then 1 else (-1 : Int)) else 0) + (if ((v 45) = (m 0)) then (if (u 45) then 1 else (-1 : Int)) else 0) + (if ((v 14) = (m 0)) then (if (u 14) then 1 else (-1 : Int)) else 0)) % 3) = 0)))
  | 433 => (((m 2) = (v 16)) ∨ ((m 2) = (v 4)) ∨ ((m 2) = (v 8)) ∨ ((m 2) = (v 29)) ∨ ((m 2) = (v 25)) ∨ ((m 2) = (v 33)) ∨ ((m 2) = (v 12)) ∨ ((m 2) = (v 21)))
  | 442 => (((v 0) ≤ (m 2)) ∨ (((((if ((v 25) = (m 2)) then 1 else 0) + (if ((v 4) = (m 2)) then 1 else 0) + (if ((v 21) = (m 2)) then 1 else 0) + (if ((v 8) = (m 2)) then 1 else 0) + (if ((v 12) = (m 2)) then 1 else 0) + (if ((v 29) = (m 2)) then 1 else 0) + (if ((v 16) = (m 2)) then 1 else 0) + (if ((v 33) = (m 2)) then 1 else 0)) % 3) = 0) ∧ ((((if ((v 25) = (m 2)) then (if (u 25) then 1 else (-1 : Int)) else 0) + (if ((v 4) = (m 2)) then (if (u 4) then (-1 : Int) else 1) else 0) + (if ((v 21) = (m 2)) then (if (u 21) then 1 else (-1 : Int)) else 0) + (if ((v 8) = (m 2)) then (if (u 8) then (-1 : Int) else 1) else 0) + (if ((v 12) = (m 2)) then (if (u 12) then (-1 : Int) else 1) else 0) + (if ((v 29) = (m 2)) then (if (u 29) then 1 else (-1 : Int)) else 0) + (if ((v 16) = (m 2)) then (if (u 16) then (-1 : Int) else 1) else 0) + (if ((v 33) = (m 2)) then (if (u 33) then 1 else (-1 : Int)) else 0)) % 3) = 0)))
  | _ => True

noncomputable def disjointRulesConst (v m : Nat → Int) (u : Nat → Prop) (k : Nat) : Prop :=
  if k ∈ disjointTriadIndicesConst then packedTriad v u (disjointTriadAtConst k) else disjointNonTriadRulesConst v m u k

private def disjointCoresConst : Array (List Nat × List Nat × List Nat × List Nat) :=
  #[([0,1,3,4,5,6,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,47,48,49,50],[2,7,8,9,10,39,40,41,42],[11,12,13,14,43,44,45,46],[401]),
   ([0,3,4,5,6,15,16,17,18,19,20,21,22,31,32,33,34,35,38,41,44,47,50],[1,2,7,8,9,10,23,24,25,26,36,39,42,45,48],[11,12,13,14,27,28,29,30,37,40,43,46,49],[256,326,401,407]),
   ([3,6,9,12,15,18,19,22,25,28,31,34,35,38,41,44,47,50],[0,1,2,4,7,10,13,16,20,23,26,29,32,36,39,42,45,48],[5,8,11,14,17,21,24,27,30,33,37,40,43,46,49],[86,111,117,210,223,233,259,326,333,349,381,401,403,405,407,409,411]),
   ([0,1,2,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50],[3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18],[19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],[433,442]),
   ([0,1,11,12,13,14,35,36,37,38,47,48,49,50],[2,3,4,5,6,15,16,17,18,39,40,41,42],[7,8,9,10,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,43,44,45,46],[403]),
   ([0,11,12,13,14,23,24,25,26,35,38,41,44,47,50],[1,2,3,4,5,6,15,16,17,18,27,28,29,30,36,39,42,45,48],[7,8,9,10,19,20,21,22,31,32,33,34,37,40,43,46,49],[111,117,256,326,401,403,405,407]),
   ([5,8,11,14,17,20,23,26,29,32,35,38,41,44,47,50],[0,1,2,3,6,9,12,15,18,21,24,27,30,33,36,39,42,45,48],[4,7,10,13,16,19,22,25,28,31,34,37,40,43,46,49],[108,111,117,133,191,197,212,241,300,326,378,401,403,405,407,409,411]),
   ([0,3,4,5,6,15,16,17,18,27,28,29,30,37,40,43,46,49],[1,2,7,8,9,10,19,20,21,22,31,32,33,34,35,38,41,44,47,50],[11,12,13,14,23,24,25,26,36,39,42,45,48],[222,403,405,407]),
   ([0,1,11,12,13,14,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,43,44,45,46],[2,3,4,5,6,15,16,17,18,35,36,37,38,47,48,49,50],[7,8,9,10,39,40,41,42],[401]),
   ([0,1,2],[35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50],[3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34],[413,422]),
   ([0,1,7,8,9,10,43,44,45,46],[2,11,12,13,14,35,36,37,38,47,48,49,50],[3,4,5,6,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,39,40,41,42],[401,403]),
   ([0,7,8,9,10,23,24,25,26,37,40,43,46,49],[1,2,11,12,13,14,27,28,29,30,35,38,41,44,47,50],[3,4,5,6,15,16,17,18,19,20,21,22,31,32,33,34,36,39,42,45,48],[401,403,405,407]),
   ([4,7,10,13,16,20,23,26,29,32,37,40,43,46,49],[0,1,2,5,8,11,14,17,21,24,27,30,33,35,38,41,44,47,50],[3,6,9,12,15,18,19,22,25,28,31,34,36,39,42,45,48],[401,403,405,407,409,411])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem disjointResidueDataConst :
    (List.range 13).all (fun a =>
      let c := disjointCoresConst[a]!
      c.1.all (fun k => decide (k < 51 ∧ disjointResidueConst a k = 0)) &&
      c.2.1.all (fun k => decide (k < 51 ∧ disjointResidueConst a k = 1)) &&
      c.2.2.1.all (fun k => decide (k < 51 ∧ disjointResidueConst a k = 2))) = true := by
  decide +kernel

private def disjointFirstFactsConst (v m : Nat → Int) (u : Nat → Prop) (a : Nat) : Prop :=
  let c := disjointCoresConst[a]!
  (∀ k ∈ c.1,0 < v k) ∧ (∀ k ∈ c.2.1, v k = 0 ∧ ¬u k) ∧
  (∀ k ∈ c.2.2.1, v k = 0 ∧ u k) ∧ (∀ k ∈ c.2.2.2, disjointRulesConst v m u k)

private theorem disjointFirstPrepareConst (v m : Nat → Int) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesConst v m u k) (a : Nat) (ha : a < 13)
    (hres : ∀ k, k < 51 → residueFacts (v k) (u k) (disjointResidueConst a k)) : disjointFirstFactsConst v m u a := by
  have h := List.all_eq_true.mp disjointResidueDataConst a (List.mem_range.mpr ha)
  obtain ⟨hzo, ht⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hz, ho⟩ := Bool.and_eq_true_iff.mp hzo
  refine ⟨?_, ?_, ?_, fun k _ => rules k⟩
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp hz k hk)
    simpa [residueFacts, hval] using hres k bound
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ho k hk)
    simpa [residueFacts, hval] using hres k bound
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ht k hk)
    simpa [residueFacts, hval] using hres k bound

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem disjointImpossibleConstGroup0 (v m : Nat → Int) (u : Nat → Prop)
    (a : Nat) (glo : 0 ≤ a) (ghi : a < 13) (except2 : a ≠ 2) (except6 : a ≠ 6)
    (facts : disjointFirstFactsConst v m u a) : False := by
  let c := disjointCoresConst[a]!
  rcases facts with ⟨ds0, ds1, ds2, hr⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  have hne2 : a ≠ 2 := except2
  have hne6 : a ≠ 6 := except6
  rcases (show a = 0 ∨ a = 1 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 7 ∨ a = 8 ∨ a = 9 ∨ a = 10 ∨ a = 11 ∨ a = 12 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals clear hne2 hne6 except2 except6
  all_goals
    simp [disjointCoresConst,c,List.forall_mem_cons] at ds0 hr
    all_goals
      simp [disjointRulesConst, disjointNonTriadRulesConst, disjointTriadIndicesConst, disjointTriadAtConst,
        disjointCoeffTriadAtConst, disjointEncodedCoeffTriadsConst, packCoeffTriad, packCoeffTerm,
        coeffOrder, coeffUnit, packedTriad, packedVal, packedUnit] at hr
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at hr
        try simp at hr
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 35000)
          | grind (splits := 50) (liaSteps := 220000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem disjointImpossibleConstGroup6 (v m : Nat → Int) (u : Nat → Prop)
    (a : Nat) (glo : 6 ≤ a) (ghi : a < 7)
    (facts : disjointFirstFactsConst v m u a) : False := by
  let c := disjointCoresConst[a]!
  rcases facts with ⟨ds0, ds1, ds2, hr⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  have ea : a = 6 := by omega
  subst a
  all_goals
    simp [disjointCoresConst,c,List.forall_mem_cons] at ds0 hr
    all_goals
      simp [disjointRulesConst, disjointNonTriadRulesConst, disjointTriadIndicesConst, disjointTriadAtConst,
        disjointCoeffTriadAtConst, disjointEncodedCoeffTriadsConst, packCoeffTriad, packCoeffTerm,
        coeffOrder, coeffUnit, packedTriad, packedVal, packedUnit] at hr
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at hr
        try simp at hr
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          by_cases h11 : u 11
          all_goals
            try simp [h11] at hr
            try
              (have h : ¬u 11 := h11
               clear h
               by_cases h14 : u 14 <;> simp [h14] at hr)
          all_goals first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 35000)
          | grind (splits := 50) (liaSteps := 220000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem disjointImpossibleConst (v m : Nat → Int) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesConst v m u k) (a : Nat) (ha : a < 13)
    (hres : ∀ k, k < 51 → residueFacts (v k) (u k) (disjointResidueConst a k))
    (exception : a = 2 → False) : False := by
  have h := disjointFirstPrepareConst v m u rules a ha hres
  by_cases b2 : a = 2
  · exact exception b2
  by_cases b6 : a = 6
  · exact disjointImpossibleConstGroup6 v m u a (by omega) (by omega) h
  exact disjointImpossibleConstGroup0 v m u a (by omega) ha b2 b6 h

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

def disjointTriadIndicesLinear : List Nat := [67,68,69,70,72,74,75,76,77,78,79,80,81,82,83,84,85,86,88,89,90,91,92,93,94,95,96,97,98,102,103,105,106,107,108,109,110,112,114,115,116,117,118,119,121,122,123,125,126,127,128,130,131,132,134,135,136,138,139,140,142,143,144,145,146,147,150,152,153,154,155,158,159,160,161,162,163,165,166,168,169,170,171,173,174,175,179,181,184,185,187,188,189,190,191,192,193,194,196,197,198,204,205,206,207,209,212,216,218,219,224,225,226,227,228,229,231,234,235,236,237,239,242,243,244,248,249,250,251,252,253,256,257,258,259,262,269,271,272,273,274,275,276,277,279,280,281,282,283,285,286,290,291,293,294,295,298,299,301,302,303,306,307,308,313,315,316,317,318,320,321,322,323,324,325,329,330,333,336,339,342,343,344,350,353,354,356,357,359,360,361,362,365,368,369,370,371,372,373,376,377,381,382,386,387,391,395,397,399,401,402,405,409,410,411,412,415,416,422,424,425,426,427,429,430,431,433,434,435,436,439,440,441,442,443,444,445,446,447,448,450,455,458,463,464,465,466,470,471,473,475,476,477,480,483,485,488,489]

def disjointEncodedCoeffTriadsLinear : Array Nat := #[
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
  0,0,0,0,0,0,0,60213569,98133358,89992019,62574921,0,56534913,0,52103491,99707247,54696260,66512197,60474690,66507095,
  59161410,58898754,66779458,66776388,90741127,62047048,62575943,0,64928597,59950913,55742404,56798529,61260674,60998018,57059265,87365963,88416591,64143186,63094606,0,
  0,0,65460550,53645636,0,91568475,88677706,61783367,59684738,65200004,58112321,0,105423695,0,115403118,65204032,58374081,60476225,66242904,59425601,
  0,90483603,61263745,63879505,0,61526849,89203021,65991490,57324352,0,56273728,61782856,65462597,0,64144208,63095628,62576578,0,62577026,66777538,
  99673005,0,65455443,64408400,63359820,53121409,57060225,65198020,0,0,90776910,0,114879347,53382980,63101252,55746372,0,0,63887236,65724804,
  116980088,93667675,57056581,115402603,0,64144719,63096139,0,65722820,62311240,66769240,94981474,0,66508115,63359309,51840832,0,0,0,54170948,
  0,66768730,0,0,52135808,64143697,0,56271172,65190742,90742154,94983016,98624430,93899171,97870701,90252109,0,98101683,60475329,64929107,0,
  0,0,0,0,62574410,110938462,64153410,55748416,0,56799040,0,0,112778091,0,0,0,60213121,0,56009027,107261779,
  0,0,0,0,116976491,92619103,98623403,53120961,89692552,100235642,0,61782345,0,0,56004934,88679248,64927577,52859201,0,56792004,
  0,0,65985350,99972985,92848543,0,0,0,64928087,60475777,66514243,57849665,90746260,61264193,0,0,94194017,65981779,65454933,87890249,
  0,0,65981269,0,0,0,0,0,0,60737346,0,64939843,97345901,99939255,57316804,65189722,61526401,86577992,0,55480134,
  55482181,66254656,54431620,65980249,0,56531781,96033644,0,0,0,88152906,97608044,0,99710328,57321921,59424066,0,0,99447671,62310729,
  0,55222209,85494080,54171585,0,0,56797569,56267204,52596545,0,0,0,0,58374977,0,59949378,90779990,65454423,66506585,0,
  97608558,96000427,62575432,56006981,107520839,95770987,0,0,0,94159774,100201912,0,0,61525953,0,0,58636098,0,0,62052162,
  0,0,110676835,62310218,65191252,0,0,0,0,0,65190232,0,0,86544775,57054534,0,66772420,54958916,0,64935750,
  107524436,56529734,89167751,0,0,111727463,0,0,93932388,109626207,106996553,94945691,94456674,57323841,0,0,89727822,66243414,0,0,
  0,66769750,89168778,0,0,0,65466178,103322439,0,0,0,66514882,0,0,0,111200604,0,53121857,0,105947466,
  0,90517333,98658673,0,0,94720359,0,0,0,61521346,57061185,66779968,61001537,0,0,65453913,116977006,0,0,0,
  0,0,52858753,0,56535873,58111873,51545920,64677826,0,66510150,66770260,61781834,0,61258690,60996034,62311751,66243924,0,0,87595403,
  88646031,86315335,53908292,57322881,65987397,91831132,56010561,93406046,64672081,0,65464643,0,0,0,0,111725918,0,0,66247620,0,
  0,0,0,59424705,93669731,58374529,60733378,0,0,0,111725403,90254676,0,91797915,0,65980759,56273217,105946951,0,0,
  55484227,0,0,92881760,0,56533827,0,0,90217353,57058627]

def disjointCoeffTriadAtLinear (k : Nat) : CoeffTriad :=
  if disjointEncodedCoeffTriadsLinear[k]! = 0 then default else disjointDecodeCoeffTriad disjointEncodedCoeffTriadsLinear[k]!

def disjointTriadAtLinear (k : Nat) : PackedTriad := packCoeffTriad (disjointCoeffTriadAtLinear k)

def disjointFormsLinear : Array DisjointRow :=
  #[(0,0,0,0,0,0,1), (0,0,0,0,0,1,0), (0,0,0,0,1,0,0), (0,0,0,1,0,0, -1), (0,0,0,1,0,0,0), (0,0,0,2,0,0, -1), (0,0,0,3,0,0, -1), (0,0,1, -3,0,0,0), (0,0,1, -3,0,1,0), (0,0,1, -3,0,2,0), (0,0,1, -3,0,3,0), (0,0,1, -2,0,0,0), (0,0,1, -2,0,1,0), (0,0,1, -2,0,2,0), (0,0,1, -2,0,3,0), (0,0,1, -1,0,0,0), (0,0,1, -1,0,1,0), (0,0,1, -1,0,2,0), (0,0,1, -1,0,3,0), (0,0,1,0,0,0, -1), (0,0,1,0,0,0,0), (0,0,1,0,0,1, -1), (0,0,1,0,0,1,0), (0,0,1,0,0,2, -1), (0,0,1,0,0,2,0), (0,0,1,0,0,3, -1), (0,0,1,0,0,3,0), (0,1, -1,0,0, -3,0), (0,1, -1,0,0, -2,0), (0,1, -1,0,0, -1,0), (0,1, -1,0,0,0,0), (0,1, -1,0,1, -3,0), (0,1, -1,0,1, -2,0), (0,1, -1,0,1, -1,0), (0,1, -1,0,1,0,0), (0,1, -1,0,2, -3,0), (0,1, -1,0,2, -2,0), (0,1, -1,0,2, -1,0), (0,1, -1,0,2,0,0), (0,1, -1,0,3, -3,0), (0,1, -1,0,3, -2,0), (0,1, -1,0,3, -1,0), (0,1, -1,0,3,0,0), (0,1,0, -3,0,0,0), (0,1,0, -3,1,0,0), (0,1,0, -3,2,0,0), (0,1,0, -3,3,0,0), (0,1,0, -2,0,0,0), (0,1,0, -2,1,0,0), (0,1,0, -2,2,0,0), (0,1,0, -2,3,0,0), (0,1,0, -1,0,0,0), (0,1,0, -1,1,0,0), (0,1,0, -1,2,0,0), (0,1,0, -1,3,0,0), (0,1,0,0,0,0, -1), (0,1,0,0,0,0,0), (0,1,0,0,1,0, -1), (0,1,0,0,1,0,0), (0,1,0,0,2,0, -1), (0,1,0,0,2,0,0), (0,1,0,0,3,0, -1), (0,1,0,0,3,0,0)]

def disjointResiduesLinear : Array DisjointRow :=
  #[(0,0,0,1,0,0,0), (0,0,0,1,0,0,1), (0,0,0,1,0,0,2), (0,0,0,1,1,0,0), (0,0,0,1,1,0,1), (0,0,0,1,1,0,2), (0,0,0,1,1,1,0), (0,0,0,1,1,1,1), (0,0,0,1,1,1,2), (0,0,1,0,0,0,0), (0,0,1,0,0,0,1), (0,0,1,0,0,0,2), (0,0,1,1,0,0,0), (0,0,1,1,0,0,1), (0,0,1,1,0,0,2), (0,0,1,1,1,0,0), (0,0,1,1,1,0,1), (0,0,1,1,1,0,2), (0,0,1,1,1,1,0), (0,0,1,1,1,1,1), (0,0,1,1,1,1,2), (0,1,0,1,1,0,0), (0,1,0,1,1,0,1), (0,1,0,1,1,0,2), (0,1,1,1,0,0,0), (0,1,1,1,0,0,1), (0,1,1,1,0,0,2), (0,1,2,0,0,0,0), (0,1,2,0,0,0,1), (0,1,2,0,0,0,2), (0,1,2,1,0,0,0), (0,1,2,1,0,0,1), (0,1,2,1,0,0,2), (0,1,2,1,1,0,0), (0,1,2,1,1,0,1), (0,1,2,1,1,0,2), (0,1,2,1,1,1,0), (0,1,2,1,1,1,1), (0,1,2,1,1,1,2)]

def disjointResidueLinear (a k : Nat) : Int :=
  disjointDot disjointFormsLinear[k]! disjointResiduesLinear[a]! % 3

noncomputable def disjointNonTriadRulesLinear (v m : Nat → Int) (u : Nat → Prop) : Nat → Prop
  | 65 => (¬(u 2))
  | 66 => (¬(u 1))
  | 491 => (((v 58) + (v 56) + (v 24) + (v 62) + (v 20) + (v 22) + (v 60) + (v 26) + ((-1 : Int) * (v 0)) + (v 48) + (v 47) + (v 13) + (v 50) + (v 11) + (v 12) + (v 49) + (v 14) + ((-1 : Int) * (v 5))) = ((2 * (v 52)) + (2 * (v 51)) + (2 * (v 17)) + (2 * (v 54)) + (2 * (v 15)) + (2 * (v 16)) + (2 * (v 53)) + (2 * (v 18)) + ((-2 : Int) * (v 3))))
  | 492 => (¬(((u 0) ↔ ((u 26) ↔ ((u 60) ↔ ((u 22) ↔ ((u 20) ↔ ((u 62) ↔ ((u 24) ↔ ((u 56) ↔ (u 58))))))))) ↔ (((u 14) ↔ ((u 49) ↔ ((u 12) ↔ ((u 11) ↔ ((u 50) ↔ ((u 13) ↔ ((u 47) ↔ (u 48)))))))) ↔ (u 5))))
  | 493 => (((v 52) + (v 51) + (v 17) + (v 54) + (v 15) + (v 16) + (v 53) + (v 18) + ((-1 : Int) * (v 3)) + (v 44) + (v 43) + (v 9) + (v 46) + (v 7) + (v 8) + (v 45) + (v 10) + ((-1 : Int) * (v 6))) = ((2 * (v 48)) + (2 * (v 47)) + (2 * (v 13)) + (2 * (v 50)) + (2 * (v 11)) + (2 * (v 12)) + (2 * (v 49)) + (2 * (v 14)) + ((-2 : Int) * (v 5))))
  | 494 => ((((u 18) ↔ ((u 53) ↔ ((u 16) ↔ ((u 15) ↔ ((u 54) ↔ ((u 17) ↔ ((u 51) ↔ (u 52)))))))) ↔ (u 3)) ↔ (((u 10) ↔ ((u 45) ↔ ((u 8) ↔ ((u 7) ↔ ((u 46) ↔ ((u 9) ↔ ((u 43) ↔ (u 44)))))))) ↔ (u 6)))
  | 495 => (((v 43) + (v 47) + (v 51) + (v 28) + (v 30) + (v 29) + (v 56) + (v 27) + ((-1 : Int) * (v 55)) + (v 45) + (v 49) + (v 53) + (v 36) + (v 38) + (v 37) + (v 60) + (v 35) + ((-1 : Int) * (v 59))) = ((2 * (v 44)) + (2 * (v 48)) + (2 * (v 52)) + (2 * (v 32)) + (2 * (v 34)) + (2 * (v 33)) + (2 * (v 58)) + (2 * (v 31)) + ((-2 : Int) * (v 57))))
  | 496 => ((((((((((u 43) ↔ (u 47)) ↔ (u 51)) ↔ (u 28)) ↔ (u 30)) ↔ (u 29)) ↔ (u 56)) ↔ (u 27)) ↔ (u 55)) ↔ (((((((((u 45) ↔ (u 49)) ↔ (u 53)) ↔ (u 36)) ↔ (u 38)) ↔ (u 37)) ↔ (u 60)) ↔ (u 35)) ↔ (u 59)))
  | 497 => (((v 44) + (v 48) + (v 52) + (v 32) + (v 34) + (v 33) + (v 58) + (v 31) + ((-1 : Int) * (v 57)) + (v 46) + (v 50) + (v 54) + (v 40) + (v 42) + (v 41) + (v 62) + (v 39) + ((-1 : Int) * (v 61))) = ((2 * (v 45)) + (2 * (v 49)) + (2 * (v 53)) + (2 * (v 36)) + (2 * (v 38)) + (2 * (v 37)) + (2 * (v 60)) + (2 * (v 35)) + ((-2 : Int) * (v 59))))
  | 498 => ((((((((((u 44) ↔ (u 48)) ↔ (u 52)) ↔ (u 32)) ↔ (u 34)) ↔ (u 33)) ↔ (u 58)) ↔ (u 31)) ↔ (u 57)) ↔ (((((((((u 46) ↔ (u 50)) ↔ (u 54)) ↔ (u 40)) ↔ (u 42)) ↔ (u 41)) ↔ (u 62)) ↔ (u 39)) ↔ (u 61)))
  | 499 => (((v 34) + (v 7) + (v 30) + (v 11) + (v 15) + (v 38) + (v 20) + (v 42) + ((-1 : Int) * (v 19)) + (v 32) + (v 9) + (v 28) + (v 13) + (v 17) + (v 36) + (v 24) + (v 40) + ((-1 : Int) * (v 23))) = ((2 * (v 33)) + (2 * (v 8)) + (2 * (v 29)) + (2 * (v 12)) + (2 * (v 16)) + (2 * (v 37)) + (2 * (v 22)) + (2 * (v 41)) + ((-2 : Int) * (v 21))))
  | 500 => ((((u 42) ↔ (((((((u 34) ↔ (u 7)) ↔ (u 30)) ↔ (u 11)) ↔ (u 15)) ↔ (u 38)) ↔ (u 20))) ↔ (u 19)) ↔ (((u 40) ↔ (((((((u 32) ↔ (u 9)) ↔ (u 28)) ↔ (u 13)) ↔ (u 17)) ↔ (u 36)) ↔ (u 24))) ↔ (u 23)))
  | 501 => (((v 33) + (v 8) + (v 29) + (v 12) + (v 16) + (v 37) + (v 22) + (v 41) + ((-1 : Int) * (v 21)) + (v 31) + (v 10) + (v 27) + (v 14) + (v 18) + (v 35) + (v 26) + (v 39) + ((-1 : Int) * (v 25))) = ((2 * (v 32)) + (2 * (v 9)) + (2 * (v 28)) + (2 * (v 13)) + (2 * (v 17)) + (2 * (v 36)) + (2 * (v 24)) + (2 * (v 40)) + ((-2 : Int) * (v 23))))
  | 502 => ((((u 41) ↔ (((((((u 33) ↔ (u 8)) ↔ (u 29)) ↔ (u 12)) ↔ (u 16)) ↔ (u 37)) ↔ (u 22))) ↔ (u 21)) ↔ (((u 39) ↔ (((((((u 31) ↔ (u 10)) ↔ (u 27)) ↔ (u 14)) ↔ (u 18)) ↔ (u 35)) ↔ (u 26))) ↔ (u 25)))
  | 503 => (((m 0) = (v 17)) ∨ ((m 0) = (v 54)) ∨ ((m 0) = (v 15)) ∨ ((m 0) = (v 18)) ∨ ((m 0) = (v 3)) ∨ ((m 0) = (v 51)) ∨ ((m 0) = (v 53)) ∨ ((m 0) = (v 52)) ∨ ((m 0) = (v 16)))
  | 513 => (((v 4) ≤ (m 0)) ∨ (((((if ((v 52) = (m 0)) then 1 else 0) + (if ((v 51) = (m 0)) then 1 else 0) + (if ((v 17) = (m 0)) then 1 else 0) + (if ((v 54) = (m 0)) then 1 else 0) + (if ((v 15) = (m 0)) then 1 else 0) + (if ((v 16) = (m 0)) then 1 else 0) + (if ((v 53) = (m 0)) then 1 else 0) + (if ((v 18) = (m 0)) then 1 else 0) + (if ((v 3) = (m 0)) then (-1 : Int) else 0)) % 3) = 0) ∧ ((((if ((v 52) = (m 0)) then (if (u 52) then 1 else (-1 : Int)) else 0) + (if ((v 51) = (m 0)) then (if (u 51) then 1 else (-1 : Int)) else 0) + (if ((v 17) = (m 0)) then (if (u 17) then 1 else (-1 : Int)) else 0) + (if ((v 54) = (m 0)) then (if (u 54) then 1 else (-1 : Int)) else 0) + (if ((v 15) = (m 0)) then (if (u 15) then 1 else (-1 : Int)) else 0) + (if ((v 16) = (m 0)) then (if (u 16) then 1 else (-1 : Int)) else 0) + (if ((v 53) = (m 0)) then (if (u 53) then 1 else (-1 : Int)) else 0) + (if ((v 18) = (m 0)) then (if (u 18) then 1 else (-1 : Int)) else 0) + (if ((v 3) = (m 0)) then (if (u 3) then 1 else (-1 : Int)) else 0)) % 3) = 0)))
  | 514 => (((m 1) = (v 34)) ∨ ((m 1) = (v 48)) ∨ ((m 1) = (v 58)) ∨ ((m 1) = (v 57)) ∨ ((m 1) = (v 52)) ∨ ((m 1) = (v 31)) ∨ ((m 1) = (v 32)) ∨ ((m 1) = (v 33)) ∨ ((m 1) = (v 44)))
  | 524 => (((v 2) ≤ (m 1)) ∨ (((((if ((v 44) = (m 1)) then 1 else 0) + (if ((v 48) = (m 1)) then 1 else 0) + (if ((v 52) = (m 1)) then 1 else 0) + (if ((v 32) = (m 1)) then 1 else 0) + (if ((v 34) = (m 1)) then 1 else 0) + (if ((v 33) = (m 1)) then 1 else 0) + (if ((v 58) = (m 1)) then 1 else 0) + (if ((v 31) = (m 1)) then 1 else 0) + (if ((v 57) = (m 1)) then (-1 : Int) else 0)) % 3) = 0) ∧ ((((if ((v 44) = (m 1)) then (if (u 44) then (-1 : Int) else 1) else 0) + (if ((v 48) = (m 1)) then (if (u 48) then (-1 : Int) else 1) else 0) + (if ((v 52) = (m 1)) then (if (u 52) then (-1 : Int) else 1) else 0) + (if ((v 32) = (m 1)) then (if (u 32) then (-1 : Int) else 1) else 0) + (if ((v 34) = (m 1)) then (if (u 34) then (-1 : Int) else 1) else 0) + (if ((v 33) = (m 1)) then (if (u 33) then (-1 : Int) else 1) else 0) + (if ((v 58) = (m 1)) then (if (u 58) then (-1 : Int) else 1) else 0) + (if ((v 31) = (m 1)) then (if (u 31) then (-1 : Int) else 1) else 0) + (if ((v 57) = (m 1)) then (if (u 57) then 1 else (-1 : Int)) else 0)) % 3) = 0)))
  | 525 => (((m 2) = (v 8)) ∨ ((m 2) = (v 33)) ∨ ((m 2) = (v 29)) ∨ ((m 2) = (v 12)) ∨ ((m 2) = (v 16)) ∨ ((m 2) = (v 37)) ∨ ((m 2) = (v 22)) ∨ ((m 2) = (v 41)) ∨ ((m 2) = (v 21)))
  | 535 => (((v 1) ≤ (m 2)) ∨ (((((if ((v 33) = (m 2)) then 1 else 0) + (if ((v 8) = (m 2)) then 1 else 0) + (if ((v 29) = (m 2)) then 1 else 0) + (if ((v 12) = (m 2)) then 1 else 0) + (if ((v 16) = (m 2)) then 1 else 0) + (if ((v 37) = (m 2)) then 1 else 0) + (if ((v 22) = (m 2)) then 1 else 0) + (if ((v 41) = (m 2)) then 1 else 0) + (if ((v 21) = (m 2)) then (-1 : Int) else 0)) % 3) = 0) ∧ ((((if ((v 33) = (m 2)) then (if (u 33) then 1 else (-1 : Int)) else 0) + (if ((v 8) = (m 2)) then (if (u 8) then (-1 : Int) else 1) else 0) + (if ((v 29) = (m 2)) then (if (u 29) then 1 else (-1 : Int)) else 0) + (if ((v 12) = (m 2)) then (if (u 12) then (-1 : Int) else 1) else 0) + (if ((v 16) = (m 2)) then (if (u 16) then (-1 : Int) else 1) else 0) + (if ((v 37) = (m 2)) then (if (u 37) then 1 else (-1 : Int)) else 0) + (if ((v 22) = (m 2)) then (if (u 22) then (-1 : Int) else 1) else 0) + (if ((v 41) = (m 2)) then (if (u 41) then 1 else (-1 : Int)) else 0) + (if ((v 21) = (m 2)) then (if (u 21) then 1 else (-1 : Int)) else 0)) % 3) = 0)))
  | _ => True

noncomputable def disjointRulesLinear (v m : Nat → Int) (u : Nat → Prop) (k : Nat) : Prop :=
  if k ∈ disjointTriadIndicesLinear then packedTriad v u (disjointTriadAtLinear k) else disjointNonTriadRulesLinear v m u k

def disjointSkippedLinear : List Nat := [3,6,7,8,15,16,18,19,20,21,36,37,38]

private def disjointCoresLinear : Array (List Nat × List Nat × List Nat × List Nat) :=
  #[([0,6,7,8,9,10,20,22,24,26,43,44,45,46,56,58,60,62],[3,4,11,12,13,14,47,48,49,50],[5,15,16,17,18,51,52,53,54],[75,83,109,126,150,159,187,194,302,491,493]),
   ([3,20,22,24,26,56,58,60,62],[0,4,5,11,12,13,14,47,48,49,50],[15,16,17,18,21,25,51,52,53,54],[75,83,109,126,128,130,159,194,491]),
   ([5,7,8,9,10,43,44,45,46],[6,11,12,13,14,47,48,49,50],[0,3,15,16,17,18,51,52,53,54],[175,493]),
   ([],[],[],[]),
   ([3,7,8,9,10,20,22,24,26,43,46,49,52,56,62],[0,2,5,11,12,13,14,44,47,50,53,58],[6,15,16,17,18,21,25,45,48,51,54,60],[82,126,128,130,191,194,402,491,493]),
   ([5,7,8,9,10,20,22,24,26,43,46,49,52,56,62],[2,6,11,12,13,14,21,25,44,47,50,53,58],[0,3,15,16,17,18,45,48,51,54,60],[82,126,128,130,175,194,320,402,491,493]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([1],[8,12,16,21,22],[29,33,37,41],[525,535]),
   ([1,19,21,23,25],[7,8,9,10,11,12,13,14,15,16,17,18,20,22,24,26],[3,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42],[146,218,219,499,501,502,525,535]),
   ([1],[8,12,16,22],[21,29,33,37,41],[525,535]),
   ([0,6,15,16,17,18,43,44,45,46,55,56,57,58,59,60,61,62],[3,4,7,8,9,10,19,20,21,22,23,24,25,26,47,48,49,50],[5,11,12,13,14,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,51,52,53,54],[70,76,85,102,112,169,184,242,359,429,491,493,495,497,499,501]),
   ([3,15,16,17,18,43,44,45,46,56,58,60,62],[0,4,5,7,8,9,10,20,22,24,26,47,48,49,50],[6,11,12,13,14,30,33,37,40,51,52,53,54],[70,75,83,85,107,109,159,169,491,493]),
   ([5,15,16,17,18,43,44,45,46],[4,6,7,8,9,10,47,48,49,50],[0,3,11,12,13,14,30,33,37,40,51,52,53,54],[70,76,85,106,107,169,175,259,357,493]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([5,15,16,17,18,31,32,33,34,43,46,49,52,56,59,62],[2,4,6,7,8,9,10,20,22,24,26,35,36,37,38,44,47,50,53,55,58,61],[0,3,11,12,13,14,19,21,23,27,28,29,30,39,40,41,42,45,48,51,54,57,60],[70,76,80,82,97,114,175,191,224,336,444,491,493,495,497,499]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([3,7,8,9,10,35,36,37,38,45,48,51,54,55,60,61],[2,5,11,12,13,14,27,28,29,30,39,40,41,42,43,46,49,52,56,57,62],[6,15,16,17,18,21,31,32,33,34,44,47,50,53,58,59],[75,78,88,108,161,250,272,315,325,493,495,497]),
   ([5,7,8,9,10,35,36,37,38,45,48,51,54,57,60],[2,6,11,12,13,14,27,28,29,30,39,40,41,42,43,46,49,52,56,59,62],[0,3,15,16,17,18,31,32,33,34,44,47,50,53,55,58,61],[75,78,108,132,161,175,272,315,325,493,495,497]),
   ([0,15,16,17,18,51,52,53,54],[3,4,9,10,20,22,24,26,43,44,45,46,56,58,60,62],[5,11,12,13,14,47,48,49,50],[68,76,106,158,193,259,291,357,491]),
   ([],[0,5,20,22,24,26,56,58,60,62],[11,12,13,14,47,48,49,50],[492]),
   ([5,15,16,17,18,51,52,53,54],[4,9,10,20,22,24,26,43,44,45,46,56,58,60,62],[0,3,11,12,13,14,47,48,49,50],[68,76,106,158,175,193,259,291,357,491]),
   ([1],[],[8,12,16,21,22,29,33,37,41],[525,535]),
   ([4],[0,51,52,53,54],[3,15,16,17,18],[426,503,513]),
   ([2],[44,48,52,58],[31,32,33,34,57],[514,524]),
   ([0,6,11,12,13,14,51,52,53,54],[3,4,15,16,17,18,43,44,45,46,56,58,60,62],[5,7,8,9,10,20,22,24,26,28,31,37,47,48,49,50],[68,74,97,123,143,491,493]),
   ([3,11,12,13,14,51,52,53,54],[0,4,5,15,16,17,18,43,44,45,46,56,58,60,62],[6,7,8,9,10,20,22,24,26,47,48,49,50],[103,153,179,442,491,493]),
   ([5,11,12,13,14,51,52,53,54],[6,15,16,17,18,43,44,45,46,56,58,60,62],[0,3,7,8,9,10,20,22,24,26,28,31,37,47,48,49,50],[68,97,123,143,491,493]),
   ([0,6,11,12,13,14,31,32,33,34,45,48,51,54,59,60],[2,3,4,15,16,17,18,35,36,37,38,43,46,49,52,55,56,61,62],[5,7,8,9,10,20,22,24,26,27,28,29,30,39,40,41,42,44,47,50,53,57,58],[68,74,80,81,154,242,281,295,336,491,493,495,497]),
   ([3,11,12,13,14,31,32,33,34,45,48,51,54,55,60,61],[0,4,5,15,16,17,18,21,35,36,37,38,43,46,49,52,56,57,62],[6,7,8,9,10,20,22,24,26,27,28,29,30,39,40,41,42,44,47,50,53,58,59],[75,77,88,103,153,154,179,250,271,442,491,493,495,497]),
   ([5,11,12,13,14,31,32,33,34,45,48,51,54,57,60],[6,15,16,17,18,35,36,37,38,43,46,49,52,56,59,62],[0,3,7,8,9,10,20,22,24,26,27,28,29,30,39,40,41,42,44,47,50,53,55,58,61],[68,123,169,491,493,495,497]),
   ([],[],[],[]),
   ([],[],[],[]),
   ([],[],[],[])]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem disjointResidueDataLinear :
    (List.range 39).all (fun a =>
      let c := disjointCoresLinear[a]!
      c.1.all (fun k => decide (k < 63 ∧ disjointResidueLinear a k = 0)) &&
      c.2.1.all (fun k => decide (k < 63 ∧ disjointResidueLinear a k = 1)) &&
      c.2.2.1.all (fun k => decide (k < 63 ∧ disjointResidueLinear a k = 2))) = true := by
  decide +kernel

private def disjointFirstFactsLinear (v m : Nat → Int) (u : Nat → Prop) (a : Nat) : Prop :=
  let c := disjointCoresLinear[a]!
  (∀ k ∈ c.1,0 < v k) ∧ (∀ k ∈ c.2.1, v k = 0 ∧ ¬u k) ∧
  (∀ k ∈ c.2.2.1, v k = 0 ∧ u k) ∧ (∀ k ∈ c.2.2.2, disjointRulesLinear v m u k)

private theorem disjointFirstPrepareLinear (v m : Nat → Int) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k) (a : Nat) (ha : a < 39)
    (hres : ∀ k, k < 63 → residueFacts (v k) (u k) (disjointResidueLinear a k)) : disjointFirstFactsLinear v m u a := by
  have h := List.all_eq_true.mp disjointResidueDataLinear a (List.mem_range.mpr ha)
  obtain ⟨hzo, ht⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hz, ho⟩ := Bool.and_eq_true_iff.mp hzo
  refine ⟨?_, ?_, ?_, fun k _ => rules k⟩
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp hz k hk)
    simpa [residueFacts, hval] using hres k bound
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ho k hk)
    simpa [residueFacts, hval] using hres k bound
  · intro k hk
    have ⟨bound, hval⟩ := of_decide_eq_true (List.all_eq_true.mp ht k hk)
    simpa [residueFacts, hval] using hres k bound

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem disjointImpossibleLinearGroup0 (v m : Nat → Int) (u : Nat → Prop)
    (a : Nat) (glo : 0 ≤ a) (ghi : a < 10) (hs : a ∉ disjointSkippedLinear)
    (facts : disjointFirstFactsLinear v m u a) : False := by
  let c := disjointCoresLinear[a]!
  rcases facts with ⟨ds0, ds1, ds2, hr⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 ∨ a = 7 ∨ a = 8 ∨ a = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    try exact (hs (by decide)).elim
  all_goals
    clear hs
    simp [disjointCoresLinear,c,List.forall_mem_cons] at ds0 hr
    all_goals
      simp [disjointRulesLinear, disjointNonTriadRulesLinear, disjointTriadIndicesLinear, disjointTriadAtLinear,
        disjointCoeffTriadAtLinear, disjointEncodedCoeffTriadsLinear, packCoeffTriad, packCoeffTerm,
        coeffOrder, coeffUnit, packedTriad, packedVal, packedUnit] at hr
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at hr
        try simp at hr
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 35000)
          | grind (splits := 50) (liaSteps := 220000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem disjointImpossibleLinearGroup1 (v m : Nat → Int) (u : Nat → Prop)
    (a : Nat) (glo : 10 ≤ a) (ghi : a < 20) (hs : a ∉ disjointSkippedLinear)
    (facts : disjointFirstFactsLinear v m u a) : False := by
  let c := disjointCoresLinear[a]!
  rcases facts with ⟨ds0, ds1, ds2, hr⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 10 ∨ a = 11 ∨ a = 12 ∨ a = 13 ∨ a = 14 ∨ a = 15 ∨ a = 16 ∨ a = 17 ∨ a = 18 ∨ a = 19 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    try exact (hs (by decide)).elim
  all_goals
    clear hs
    simp [disjointCoresLinear,c,List.forall_mem_cons] at ds0 hr
    all_goals
      simp [disjointRulesLinear, disjointNonTriadRulesLinear, disjointTriadIndicesLinear, disjointTriadAtLinear,
        disjointCoeffTriadAtLinear, disjointEncodedCoeffTriadsLinear, packCoeffTriad, packCoeffTerm,
        coeffOrder, coeffUnit, packedTriad, packedVal, packedUnit] at hr
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at hr
        try simp at hr
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 35000)
          | grind (splits := 50) (liaSteps := 220000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem disjointImpossibleLinearGroup2 (v m : Nat → Int) (u : Nat → Prop)
    (a : Nat) (glo : 20 ≤ a) (ghi : a < 30) (hs : a ∉ disjointSkippedLinear)
    (facts : disjointFirstFactsLinear v m u a) : False := by
  let c := disjointCoresLinear[a]!
  rcases facts with ⟨ds0, ds1, ds2, hr⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 20 ∨ a = 21 ∨ a = 22 ∨ a = 23 ∨ a = 24 ∨ a = 25 ∨ a = 26 ∨ a = 27 ∨ a = 28 ∨ a = 29 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    try exact (hs (by decide)).elim
  all_goals
    clear hs
    simp [disjointCoresLinear,c,List.forall_mem_cons] at ds0 hr
    all_goals
      simp [disjointRulesLinear, disjointNonTriadRulesLinear, disjointTriadIndicesLinear, disjointTriadAtLinear,
        disjointCoeffTriadAtLinear, disjointEncodedCoeffTriadsLinear, packCoeffTriad, packCoeffTerm,
        coeffOrder, coeffUnit, packedTriad, packedVal, packedUnit] at hr
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at hr
        try simp at hr
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 35000)
          | grind (splits := 50) (liaSteps := 220000)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem disjointImpossibleLinearGroup3 (v m : Nat → Int) (u : Nat → Prop)
    (a : Nat) (glo : 30 ≤ a) (ghi : a < 39) (hs : a ∉ disjointSkippedLinear)
    (facts : disjointFirstFactsLinear v m u a) : False := by
  let c := disjointCoresLinear[a]!
  rcases facts with ⟨ds0, ds1, ds2, hr⟩
  have v1 (k) (h : k ∈ c.2.1) : v k = 0 := (ds1 k h).1
  have b1 (k) (h : k ∈ c.2.1) : ¬u k := (ds1 k h).2
  have v2 (k) (h : k ∈ c.2.2.1) : v k = 0 := (ds2 k h).1
  have b2 (k) (h : k ∈ c.2.2.1) : u k := (ds2 k h).2
  rcases (show a = 30 ∨ a = 31 ∨ a = 32 ∨ a = 33 ∨ a = 34 ∨ a = 35 ∨ a = 36 ∨ a = 37 ∨ a = 38 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    try exact (hs (by decide)).elim
  all_goals
    clear hs
    simp [disjointCoresLinear,c,List.forall_mem_cons] at ds0 hr
    all_goals
      simp [disjointRulesLinear, disjointNonTriadRulesLinear, disjointTriadIndicesLinear, disjointTriadAtLinear,
        disjointCoeffTriadAtLinear, disjointEncodedCoeffTriadsLinear, packCoeffTriad, packCoeffTerm,
        coeffOrder, coeffUnit, packedTriad, packedVal, packedUnit] at hr
      all_goals
        try simp (disch := decide) only [v1,b1,v2,b2] at hr
        try simp at hr
        all_goals
          clear v1 b1 v2 b2 ds1 ds2
          try clear c glo ghi
          first
          | omega (splitDisjunctions := false)
          | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 35000)
          | grind (splits := 50) (liaSteps := 220000)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem disjointImpossibleLinear (v m : Nat → Int) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k) (a : Nat) (ha : a < 39)
    (hres : ∀ k, k < 63 → residueFacts (v k) (u k) (disjointResidueLinear a k))
    (exception : a ∈ disjointSkippedLinear → False) : False := by
  by_cases hs : a ∈ disjointSkippedLinear
  · exact exception hs
  have h := disjointFirstPrepareLinear v m u rules a ha hres
  by_cases b : a < 10
  · exact disjointImpossibleLinearGroup0 v m u a (by omega) b hs h
  by_cases b : a < 20
  · exact disjointImpossibleLinearGroup1 v m u a (by omega) b hs h
  by_cases b : a < 30
  · exact disjointImpossibleLinearGroup2 v m u a (by omega) b hs h
  exact disjointImpossibleLinearGroup3 v m u a (by omega) ha hs h

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

def certifiedExtreme (upper : Bool) (a : ℤ) (xs : List ℤ) : ℤ :=
  xs.foldl (if upper then max else min) a

theorem certifiedExtreme_present (upper : Bool) (a : ℤ) (xs : List ℤ) :
    certifiedExtreme upper a xs ∈ a :: xs := by
  induction xs generalizing a with
  | nil => simp [certifiedExtreme]
  | cons x xs ih =>
    cases upper
    · change certifiedExtreme false (min a x) xs ∈ a :: x :: xs
      rcases min_choice a x with h|h
      · rw [h]
        rcases List.mem_cons.mp (ih a) with e|e
        · simp [e]
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e)
      · rw [h]
        exact List.mem_cons_of_mem _ (ih x)
    · change certifiedExtreme true (max a x) xs ∈ a :: x :: xs
      rcases max_choice a x with h|h
      · rw [h]
        rcases List.mem_cons.mp (ih a) with e|e
        · simp [e]
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ e)
      · rw [h]
        exact List.mem_cons_of_mem _ (ih x)

theorem certifiedExtreme_upper (a : ℤ) (xs : List ℤ) :
    ∀ y ∈ a :: xs, y ≤ certifiedExtreme true a xs := by
  induction xs generalizing a with
  | nil => simp [certifiedExtreme]
  | cons x xs ih =>
    intro y h
    change y ≤ certifiedExtreme true (max a x) xs
    have high := ih (max a x) (max a x) (by simp)
    obtain rfl|rfl|r := (by simpa using (List.mem_cons.mp h) : y=a ∨ y=x ∨ y∈xs)
    · exact (le_max_left ..).trans high
    · exact (le_max_right ..).trans high
    · exact ih _ _ (List.mem_cons_of_mem _ r)

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.Triadic

open scoped Classical

noncomputable def parityBit (p : Prop) : ZMod 2 := if p then 1 else 0

theorem parityBit_not (p : Prop) : parityBit (¬p) = 1 + parityBit p := by
  by_cases h : p <;> simp [parityBit,h] <;> decide

theorem parityBit_iff (p q : Prop) :
    parityBit (p ↔ q) = 1 + parityBit p + parityBit q := by
  by_cases h : p <;> by_cases h' : q <;> simp [parityBit,h,h'] <;> decide

theorem parityBit_inj (p q : Prop) : parityBit p = parityBit q ↔ (p ↔ q) := by
  by_cases h : p <;> by_cases h' : q <;> simp [parityBit,h,h']

theorem parityBit_opp (p q : Prop) : parityBit (¬p) = parityBit q ↔ ¬(p ↔ q) := by
  rw [parityBit_inj]
  tauto

end PEqualNP.Outside.L_gct_234.Triadic

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def rowForm (f : DisjointRow) : Form :=
  ![f.1,f.2.1,f.2.2.1,f.2.2.2.1,f.2.2.2.2.1,f.2.2.2.2.2.1,f.2.2.2.2.2.2]

def formValue (forms : Array DisjointRow) (x : Fin 7 → K) (i : Nat) : K :=
  formEval x (rowForm forms[i]!)

def coeffValidity (size : Nat) (term : CoeffTerm) : Prop :=
  term.1 < size ∧ term.2 ≠ 0 ∧
  term.2 = (3 : ℤ)^coeffOrder term.2 * coeffUnit term.2 ∧
  ((coeffUnit term.2 : ℤ) : ZMod 3) = if coeffUnit term.2 % 3 = 2 then -1 else 1

instance (size : Nat) (t : CoeffTerm) : Decidable (coeffValidity size t) := by
  unfold coeffValidity
  infer_instance

def triadValidity (forms : Array DisjointRow) (tr : CoeffTriad) : Prop :=
  coeffValidity forms.size tr.1 ∧ coeffValidity forms.size tr.2.1 ∧ coeffValidity forms.size tr.2.2 ∧
    ∀ i : Fin 7, tr.1.2 * rowForm forms[tr.1.1]! i +
      tr.2.1.2 * rowForm forms[tr.2.1.1]! i + tr.2.2.2 * rowForm forms[tr.2.2.1]! i = 0

instance (forms : Array DisjointRow) (tr : CoeffTriad) : Decidable (triadValidity forms tr) := by
  unfold triadValidity
  infer_instance

theorem term_zero_ne (forms : Array DisjointRow) (x : Fin 7 → K)
    (nz : ∀ i, i < forms.size → formValue forms x i ≠ 0)
    (t : CoeffTerm) (valid : coeffValidity forms.size t) :
    (t.2 : K)*formValue forms x t.1 ≠ 0 :=
  mul_ne_zero (Int.cast_ne_zero.mpr valid.2.1) (nz _ valid.1)

theorem termInterpretation (forms : Array DisjointRow) (x : Fin 7 → K)
    (nz : ∀ i, i < forms.size → formValue forms x i ≠ 0)
    (t : CoeffTerm) (valid : coeffValidity forms.size t) :
    val ((t.2 : K)*formValue forms x t.1) = packedVal (val ∘ formValue forms x) (packCoeffTerm t) ∧
      (Negative ((t.2 : K)*formValue forms x t.1) ↔
        packedUnit (Negative ∘ formValue forms x) (packCoeffTerm t)) := by
  let z := formValue forms x t.1
  have zz : z ≠ 0 := nz _ valid.1
  have ta : (t.2 : K) ≠ 0 := Int.cast_ne_zero.mpr valid.2.1
  have unitSign : ((coeffUnit t.2 : ℤ) : F) = 1 ∨ ((coeffUnit t.2 : ℤ) : F) = -1 := by
    rw [valid.2.2.2]
    split_ifs <;> simp
  have q := int_factor_scaled_mul t.2 (coeffUnit t.2) (coeffOrder t.2) z 1 valid.2.2.1 ta zz one_ne_zero unitSign
  constructor
  · exact q.1
  · rw [negative_iff _ (mul_ne_zero ta zz)]
    change lead ((t.2 : K)*z) (mul_ne_zero ta zz) = -1 ↔ _
    simp only [one_mul] at q
    rw [q.2, valid.2.2.2]
    by_cases H : coeffUnit t.2 % 3 = 2 <;>
      simp [packCoeffTerm, packedUnit, H, z, negative_iff _ zz, minusLead,
        show (1 : F) ≠ -1 by decide]

theorem eval_triad (forms : Array DisjointRow) (x : Fin 7 → K) (tr : CoeffTriad)
    (valid : triadValidity forms tr) :
    (tr.1.2 : K)*formValue forms x tr.1.1 + (tr.2.1.2 : K)*formValue forms x tr.2.1.1 +
      (tr.2.2.2 : K)*formValue forms x tr.2.2.1 = 0 := by
  unfold formValue
  simp only [formEval, Finset.mul_sum, ← mul_assoc, ← Finset.sum_add_distrib, ← add_mul, ← Int.cast_mul,
    ← Int.cast_add]
  have h := valid.2.2.2
  exact Finset.sum_eq_zero (fun i _ => by rw [h i, Int.cast_zero, zero_mul])

theorem packedTriad_of_valid (forms : Array DisjointRow) (x : Fin 7 → K)
    (nz : ∀ i, i < forms.size → formValue forms x i ≠ 0)
    (tr : CoeffTriad) (valid : triadValidity forms tr) :
    packedTriad (val ∘ formValue forms x) (Negative ∘ formValue forms x) (packCoeffTriad tr) := by
  let z := fun w : CoeffTerm => (w.2 : K)*formValue forms x w.1
  have a := term_zero_ne forms x nz tr.1 valid.1
  have b := term_zero_ne forms x nz tr.2.1 valid.2.1
  have c := term_zero_ne forms x nz tr.2.2 valid.2.2.1
  have h := triad_val (z tr.1) (z tr.2.1) (z tr.2.2) a b c (eval_triad forms x tr valid)
  have eqA := termInterpretation forms x nz tr.1 valid.1
  have eqB := termInterpretation forms x nz tr.2.1 valid.2.1
  have eqC := termInterpretation forms x nz tr.2.2 valid.2.2.1
  change Triad (val (z tr.1)) (val (z tr.2.1)) (val (z tr.2.2))
    (minusLead (z tr.1) a) (minusLead (z tr.2.1) b) (minusLead (z tr.2.2) c) at h
  rw [← negative_iff _ a, ← negative_iff _ b, ← negative_iff _ c,
    eqA.1, eqB.1, eqC.1, eqA.2, eqB.2, eqC.2] at h
  exact h

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def slotCode (p : ℕ) : Option Slot :=
  if p < 12 then some (Fin.ofNat 3 (p/4), Fin.ofNat 4 p) else none

def selectedDistance (terms : Array (Array CoeffTerm)) (a b : ℕ) : CoeffTerm :=
  (terms[a]!)[b]!

def validDistance (forms : Array DisjointRow) (a b : ℕ) (term : CoeffTerm) : Prop :=
  coeffValidity forms.size term ∧
    ∀ k, solverForm (slotCode a) k - solverForm (slotCode b) k =
      term.2 * rowForm forms[term.1]! k

instance (forms : Array DisjointRow) (a b : ℕ) (term : CoeffTerm) :
    Decidable (validDistance forms a b term) := by
  unfold validDistance
  infer_instance

theorem distanceValue (forms : Array DisjointRow) (A : APState) (r : K)
    (startZero : A.start 0 = 0) (a b : ℕ) (term : CoeffTerm) (valid : validDistance forms a b term) :
    A.location r (slotCode a) - A.location r (slotCode b) =
      (term.2 : K) * formValue forms (A.fieldVars r) term.1 := by
  rw [← A.eval_solverForm r startZero (slotCode a), ← A.eval_solverForm r startZero (slotCode b),
    ← formEval_sub]
  have eq := funext valid.2
  rw [eq, formEval_mul_const]
  rfl

theorem distanceInterpretation (forms : Array DisjointRow) (A : APState) (r : K)
    (startZero : A.start 0 = 0) (a b : ℕ) (term : CoeffTerm) (valid : validDistance forms a b term)
    (nz : ∀ i, i < forms.size → formValue forms (A.fieldVars r) i ≠ 0) :
    let v := val ∘ formValue forms (A.fieldVars r)
    let u := Negative ∘ formValue forms (A.fieldVars r)
    let z := A.location r (slotCode a) - A.location r (slotCode b)
    val z = packedVal v (packCoeffTerm term) ∧ (Negative z ↔ packedUnit u (packCoeffTerm term)) := by
  dsimp only
  rw [distanceValue forms A r startZero a b term valid]
  exact termInterpretation forms (A.fieldVars r) nz term valid.1

theorem slotCode_inj (i j : Fin 13) : slotCode i.val = slotCode j.val → i=j := by
  have eq : ∀ a b : Fin 13, slotCode a.val = slotCode b.val → a=b := by decide +kernel
  exact eq i j

theorem coveredFormNonzero (forms : Array DisjointRow) (terms : Array (Array CoeffTerm))
    (A : APState) (r : K) (startZero : A.start 0 = 0) (n : ℕ)
    (apart : ∀ a b : Fin n, a ≠ b → A.location r (slotCode a.val) ≠ A.location r (slotCode b.val))
    (law : ∀ a b : Fin n, a ≠ b → validDistance forms a.val b.val (selectedDistance terms a.val b.val))
    (covered : ∀ q : Fin forms.size, ∃ a b : Fin n, a ≠ b ∧ (selectedDistance terms a.val b.val).1 = q.val) :
    ∀ q, q < forms.size → formValue forms (A.fieldVars r) q ≠ 0 := by
  intro q hq zero
  obtain ⟨a,b,ne,same⟩ := covered ⟨q,hq⟩
  have v := distanceValue forms A r startZero a.val b.val _ (law a b ne)
  rw [same,zero,mul_zero] at v
  exact apart a b ne (sub_eq_zero.mp v)

theorem apart_linear (A : APState) (r : K) (disjoint : A.Disjoint)
    (sep : A.Separate) (rEq : A.root = some r) :
    ∀ a b : Fin 13, a ≠ b → A.location r (slotCode a.val) ≠ A.location r (slotCode b.val) := by
  intro a b ne eq
  exact ne (slotCode_inj a b (A.location_injective r disjoint sep rEq eq))

theorem apart_constant (A : APState) (disjoint : A.Disjoint) :
    ∀ a b : Fin 12, a ≠ b → A.location 0 (slotCode a.val) ≠ A.location 0 (slotCode b.val) := by
  intro a b ne eq
  have slots : slotCode a.val = slotCode b.val := by
    simp only [slotCode, ite_eq_left a.isLt, ite_eq_left b.isLt, location, Option.elim] at eq ⊢
    exact congrArg some (disjoint eq)
  have eq13 := slotCode_inj (a.castLE (by decide)) (b.castLE (by decide)) slots
  exact ne (Fin.ext (congrArg (fun x : Fin 13 => x.val) eq13))

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def PrimitiveCoordinates.pointO {A : APState} (D : PrimitiveCoordinates A) (i : Fin 3) (j : Fin 4) : O :=
  D.starts i + (j.val : O)*D.steps i

theorem PrimitiveCoordinates.pointO_coe {A : APState} (D : PrimitiveCoordinates A) (i : Fin 3) (j : Fin 4) :
    (D.pointO i j : K) = A.point i j := by
  simp [PrimitiveCoordinates.pointO, point, D.starts_eq, D.steps_eq]

theorem PrimitiveCoordinates.point_val_nonneg {A : APState} (D : PrimitiveCoordinates A) (i : Fin 3) (j : Fin 4) :
    0 ≤ val (A.point i j) := by
  rw [← D.pointO_coe]
  exact PadicInt.valuation_coe_nonneg

theorem PrimitiveCoordinates.point_diff_nonneg {A : APState} (D : PrimitiveCoordinates A)
    (i k : Fin 3) (j l : Fin 4) : 0 ≤ val (A.point i j - A.point k l) := by
  rw [← D.pointO_coe i j, ← D.pointO_coe k l, ← PadicInt.coe_sub]
  exact PadicInt.valuation_coe_nonneg

theorem PrimitiveCoordinates.far_root {A : APState} (D : PrimitiveCoordinates A) (r : K)
    (far : val r < 0) (i : Fin 3) (j : Fin 4) :
    val (A.point i j-r) = val r ∧ (Negative (A.point i j-r) ↔ ¬Negative r) := by
  have rne : r ≠ 0 := by
    intro h
    subst r
    simp [val] at far
  obtain ⟨q, h, p⟩ := sub_pole_dominates (A.point i j) r rne
    (fun _ => far.trans_le (D.point_val_nonneg i j))
  refine ⟨h, ?_⟩
  simp only [negative_iff _ q, negative_iff _ rne, minusLead, p]
  have code : ∀ u : F, u ≠ 0 → (-u = -1 ↔ u ≠ -1) := by decide +kernel
  exact code _ (lead_ne_zero r rne)

theorem slotCode_point (i : Fin 3) (j : Fin 4) :
    slotCode (4*i.val+j.val) = some (i,j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem slotCode_root : slotCode 12 = none := rfl

theorem step_difference (A : APState) (i : Fin 3) :
    A.point i 1 - A.point i 0 = A.step i := by simp [point]

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

theorem block_distance_transport (A : APState) (r : K) {n : Nat} (hn : 12 ≤ n)
    (v : Nat → Nat → ℤ) (u : Nat → Nat → Prop)
    (dist : ∀ a b : Fin n, a ≠ b →
      val (A.location r (slotCode a.val) - A.location r (slotCode b.val)) = v a.val b.val ∧
      (Negative (A.location r (slotCode a.val) - A.location r (slotCode b.val)) ↔ u a.val b.val))
    (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :
    val (A.point i p-A.point j q) = v (4*i.val+p.val) (4*j.val+q.val) ∧
      (Negative (A.point i p-A.point j q) ↔ u (4*i.val+p.val) (4*j.val+q.val)) := by
  let a : Fin n := ⟨4*i.val+p.val, by omega⟩
  let b : Fin n := ⟨4*j.val+q.val, by omega⟩
  have diff : a ≠ b := by
    intro eq
    have same := congrArg Fin.val eq
    change 4*i.val+p.val = 4*j.val+q.val at same
    have eqi : i = j := Fin.ext (by omega)
    have eqp : p = q := Fin.ext (by omega)
    exact ne.elim (fun h => h eqi) (fun h => h eqp)
  simpa only [a,b,slotCode_point,location,Option.elim] using dist a b diff

theorem root_distance_transport (A : APState) (r : K) (v : Nat → Nat → ℤ) (u : Nat → Nat → Prop)
    (dist : ∀ a b : Fin 13, a ≠ b →
      val (A.location r (slotCode a.val) - A.location r (slotCode b.val)) = v a.val b.val ∧
      (Negative (A.location r (slotCode a.val) - A.location r (slotCode b.val)) ↔ u a.val b.val))
    (i : Fin 3) (p : Fin 4) :
    val (A.point i p-r) = v (4*i.val+p.val) 12 ∧
      (Negative (A.point i p-r) ↔ u (4*i.val+p.val) 12) := by
  let a : Fin 13 := ⟨4*i.val+p.val, by omega⟩
  have diff : a ≠ (12 : Fin 13) := by
    intro eq
    have same := congrArg Fin.val eq
    change 4*i.val+p.val = 12 at same
    omega
  simpa only [a,show (12 : Fin 13).val = 12 from rfl,slotCode_point,slotCode_root,location,Option.elim] using
    dist a (12 : Fin 13) diff

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def disjointDistanceConst : Array (Array CoeffTerm) :=

  #[#[(0,0), (2, -1), (2, -2), (2, -3), (47, -1), (48, -1), (49, -1), (50, -1), (15, -1), (16, -1), (17, -1), (18, -1)],
   #[(2,1), (0,0), (2, -1), (2, -2), (43, -1), (44, -1), (45, -1), (46, -1), (11, -1), (12, -1), (13, -1), (14, -1)],
   #[(2,2), (2,1), (0,0), (2, -1), (39, -1), (40, -1), (41, -1), (42, -1), (7, -1), (8, -1), (9, -1), (10, -1)],
   #[(2,3), (2,2), (2,1), (0,0), (35, -1), (36, -1), (37, -1), (38, -1), (3, -1), (4, -1), (5, -1), (6, -1)],
   #[(47,1), (43,1), (39,1), (35,1), (0,0), (1, -1), (1, -2), (1, -3), (22,1), (21,1), (20,1), (19,1)],
   #[(48,1), (44,1), (40,1), (36,1), (1,1), (0,0), (1, -1), (1, -2), (26,1), (25,1), (24,1), (23,1)],
   #[(49,1), (45,1), (41,1), (37,1), (1,2), (1,1), (0,0), (1, -1), (30,1), (29,1), (28,1), (27,1)],
   #[(50,1), (46,1), (42,1), (38,1), (1,3), (1,2), (1,1), (0,0), (34,1), (33,1), (32,1), (31,1)],
   #[(15,1), (11,1), (7,1), (3,1), (22, -1), (26, -1), (30, -1), (34, -1), (0,0), (0, -1), (0, -2), (0, -3)],
   #[(16,1), (12,1), (8,1), (4,1), (21, -1), (25, -1), (29, -1), (33, -1), (0,1), (0,0), (0, -1), (0, -2)],
   #[(17,1), (13,1), (9,1), (5,1), (20, -1), (24, -1), (28, -1), (32, -1), (0,2), (0,1), (0,0), (0, -1)],
   #[(18,1), (14,1), (10,1), (6,1), (19, -1), (23, -1), (27, -1), (31, -1), (0,3), (0,2), (0,1), (0,0)]]

def disjointCoverConst : Array (Fin 12 × Fin 12) :=

  #[(8,9), (4,5), (0,1), (3,8), (3,9), (3,10), (3,11), (2,8), (2,9), (2,10), (2,11), (1,8), (1,9), (1,10), (1,11), (0,8), (0,9), (0,10), (0,11), (4,11), (4,10), (4,9), (4,8), (5,11), (5,10), (5,9), (5,8), (6,11), (6,10), (6,9), (6,8), (7,11), (7,10), (7,9), (7,8), (3,4), (3,5), (3,6), (3,7), (2,4), (2,5), (2,6), (2,7), (1,4), (1,5), (1,6), (1,7), (0,4), (0,5), (0,6), (0,7)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem disjointDistanceLawConst :
    ∀ a b : Fin 12, a ≠ b →
      validDistance disjointFormsConst a.val b.val (selectedDistance disjointDistanceConst a.val b.val) := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem disjointCoverLawConst :
    ∀ q : Fin disjointFormsConst.size,
      let (a,b) := disjointCoverConst[q.val]!
      a ≠ b ∧ (selectedDistance disjointDistanceConst a.val b.val).1 = q.val := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem disjointTriadLawConst :
    disjointTriadIndicesConst.all
      (fun k => decide (triadValidity disjointFormsConst (disjointCoeffTriadAtConst k))) = true := by
  decide +kernel

theorem disjointFieldNonzeroConst (A : APState) (r : K) (zero : A.start 0=0)
    (apart : ∀ a b : Fin 12, a ≠ b → A.location r (slotCode a.val) ≠ A.location r (slotCode b.val)) :
    ∀ q, q < disjointFormsConst.size → formValue disjointFormsConst (A.fieldVars r) q ≠ 0 := by
  apply coveredFormNonzero disjointFormsConst disjointDistanceConst A r zero 12 apart disjointDistanceLawConst
  intro q
  exact ⟨_, _, (disjointCoverLawConst q).1, (disjointCoverLawConst q).2⟩

theorem disjointTriadRealizedConst (A : APState) (r : K)
    (nz : ∀ k, k < disjointFormsConst.size → formValue disjointFormsConst (A.fieldVars r) k ≠ 0)
    (k : ℕ) (hk : k ∈ disjointTriadIndicesConst) :
    packedTriad (val ∘ formValue disjointFormsConst (A.fieldVars r))
      (Negative ∘ formValue disjointFormsConst (A.fieldVars r)) (disjointTriadAtConst k) :=
  packedTriad_of_valid disjointFormsConst (A.fieldVars r) nz (disjointCoeffTriadAtConst k)
    (of_decide_eq_true (List.all_eq_true.mp disjointTriadLawConst k hk))

def disjointAuxConst (v : Nat → Int) : Nat → Int

  | 0 => certifiedExtreme true (v 44) [(v 43), (v 13), (v 46), (v 11), (v 12), (v 45), (v 14)]

  | 1 => certifiedExtreme true (v 36) [(v 40), (v 44), (v 24), (v 26), (v 25), (v 48), (v 23)]

  | 2 => certifiedExtreme true (v 25) [(v 4), (v 21), (v 8), (v 12), (v 29), (v 16), (v 33)]

  | _ => 0

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def disjointDistanceLinear : Array (Array CoeffTerm) :=

  #[#[(0,0), (4, -1), (4, -2), (4, -3), (56, -1), (58, -1), (60, -1), (62, -1), (20, -1), (22, -1), (24, -1), (26, -1), (0, -1)],
   #[(4,1), (0,0), (4, -1), (4, -2), (51, -1), (52, -1), (53, -1), (54, -1), (15, -1), (16, -1), (17, -1), (18, -1), (3,1)],
   #[(4,2), (4,1), (0,0), (4, -1), (47, -1), (48, -1), (49, -1), (50, -1), (11, -1), (12, -1), (13, -1), (14, -1), (5,1)],
   #[(4,3), (4,2), (4,1), (0,0), (43, -1), (44, -1), (45, -1), (46, -1), (7, -1), (8, -1), (9, -1), (10, -1), (6,1)],
   #[(56,1), (51,1), (47,1), (43,1), (0,0), (2, -1), (2, -2), (2, -3), (30,1), (29,1), (28,1), (27,1), (55,1)],
   #[(58,1), (52,1), (48,1), (44,1), (2,1), (0,0), (2, -1), (2, -2), (34,1), (33,1), (32,1), (31,1), (57,1)],
   #[(60,1), (53,1), (49,1), (45,1), (2,2), (2,1), (0,0), (2, -1), (38,1), (37,1), (36,1), (35,1), (59,1)],
   #[(62,1), (54,1), (50,1), (46,1), (2,3), (2,2), (2,1), (0,0), (42,1), (41,1), (40,1), (39,1), (61,1)],
   #[(20,1), (15,1), (11,1), (7,1), (30, -1), (34, -1), (38, -1), (42, -1), (0,0), (1, -1), (1, -2), (1, -3), (19,1)],
   #[(22,1), (16,1), (12,1), (8,1), (29, -1), (33, -1), (37, -1), (41, -1), (1,1), (0,0), (1, -1), (1, -2), (21,1)],
   #[(24,1), (17,1), (13,1), (9,1), (28, -1), (32, -1), (36, -1), (40, -1), (1,2), (1,1), (0,0), (1, -1), (23,1)],
   #[(26,1), (18,1), (14,1), (10,1), (27, -1), (31, -1), (35, -1), (39, -1), (1,3), (1,2), (1,1), (0,0), (25,1)],
   #[(0,1), (3, -1), (5, -1), (6, -1), (55, -1), (57, -1), (59, -1), (61, -1), (19, -1), (21, -1), (23, -1), (25, -1), (0,0)]]

def disjointCoverLinear : Array (Fin 13 × Fin 13) :=

  #[(0,12), (8,9), (4,5), (1,12), (0,1), (2,12), (3,12), (3,8), (3,9), (3,10), (3,11), (2,8), (2,9), (2,10), (2,11), (1,8), (1,9), (1,10), (1,11), (8,12), (0,8), (9,12), (0,9), (10,12), (0,10), (11,12), (0,11), (4,11), (4,10), (4,9), (4,8), (5,11), (5,10), (5,9), (5,8), (6,11), (6,10), (6,9), (6,8), (7,11), (7,10), (7,9), (7,8), (3,4), (3,5), (3,6), (3,7), (2,4), (2,5), (2,6), (2,7), (1,4), (1,5), (1,6), (1,7), (4,12), (0,4), (5,12), (0,5), (6,12), (0,6), (7,12), (0,7)]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem disjointDistanceLawLinear :
    ∀ a b : Fin 13, a ≠ b →
      validDistance disjointFormsLinear a.val b.val (selectedDistance disjointDistanceLinear a.val b.val) := by
  decide +kernel

set_option maxRecDepth 32768 in
theorem disjointCoverLawLinear :
    ∀ q : Fin disjointFormsLinear.size,
      let (a,b) := disjointCoverLinear[q.val]!
      a ≠ b ∧ (selectedDistance disjointDistanceLinear a.val b.val).1 = q.val := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem disjointTriadLawLinear :
    disjointTriadIndicesLinear.all
      (fun k => decide (triadValidity disjointFormsLinear (disjointCoeffTriadAtLinear k))) = true := by
  decide +kernel

theorem disjointFieldNonzeroLinear (A : APState) (r : K) (zero : A.start 0=0)
    (apart : ∀ a b : Fin 13, a ≠ b → A.location r (slotCode a.val) ≠ A.location r (slotCode b.val)) :
    ∀ q, q < disjointFormsLinear.size → formValue disjointFormsLinear (A.fieldVars r) q ≠ 0 := by
  apply coveredFormNonzero disjointFormsLinear disjointDistanceLinear A r zero 13 apart disjointDistanceLawLinear
  intro q
  exact ⟨_, _, (disjointCoverLawLinear q).1, (disjointCoverLawLinear q).2⟩

theorem disjointTriadRealizedLinear (A : APState) (r : K)
    (nz : ∀ k, k < disjointFormsLinear.size → formValue disjointFormsLinear (A.fieldVars r) k ≠ 0)
    (k : ℕ) (hk : k ∈ disjointTriadIndicesLinear) :
    packedTriad (val ∘ formValue disjointFormsLinear (A.fieldVars r))
      (Negative ∘ formValue disjointFormsLinear (A.fieldVars r)) (disjointTriadAtLinear k) :=
  packedTriad_of_valid disjointFormsLinear (A.fieldVars r) nz (disjointCoeffTriadAtLinear k)
    (of_decide_eq_true (List.all_eq_true.mp disjointTriadLawLinear k hk))

def disjointAuxLinear (v : Nat → Int) : Nat → Int

  | 0 => certifiedExtreme true (v 52) [(v 51), (v 17), (v 54), (v 15), (v 16), (v 53), (v 18), (v 3)]

  | 1 => certifiedExtreme true (v 44) [(v 48), (v 52), (v 32), (v 34), (v 33), (v 58), (v 31), (v 57)]

  | 2 => certifiedExtreme true (v 33) [(v 8), (v 29), (v 12), (v 16), (v 37), (v 22), (v 41), (v 21)]

  | _ => 0

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234

open PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

def disjointCoefficients (row : DisjointRow) : APState.Form :=
  ![row.1, row.2.1, row.2.2.1, row.2.2.2.1, row.2.2.2.2.1, row.2.2.2.2.2.1, row.2.2.2.2.2.2]

def disjointDigits (row : DisjointRow) : Fin 7 → ZMod 3 := fun i => disjointCoefficients row i

def digitOfBool (a : Bool) : ZMod 3 := if a then 1 else 0

def residueVector (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool) (r : ZMod 3) : Fin 7 → ZMod 3 :=
  ![s 0, s 1, s 2, digitOfBool (a 0), digitOfBool (a 1), digitOfBool (a 2), r]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem disjointResiduesConst_cover : ∀ (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool),
    CanonicalAPResidues s a → ∃ i : Fin 13, disjointDigits disjointResiduesConst[i.val]! = residueVector s a 0 := by
  decide +kernel

def setDisjointRoot (row : DisjointRow) (r : ℤ) : DisjointRow :=
  (row.1, row.2.1, row.2.2.1, row.2.2.2.1, row.2.2.2.2.1, row.2.2.2.2.2.1, r)

def expectedDisjointResiduesLinear : Array DisjointRow := Id.run do
  let mut out := #[]
  for row in disjointResiduesConst do
    for r in #[0,1,2] do
      out := out.push (setDisjointRoot row r)
  return out

theorem disjointResiduesLinear_complete :
    disjointResiduesLinear = expectedDisjointResiduesLinear := by
  rfl

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem expectedDisjointResiduesLinear_cover :
    ∀ (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool) (r : ZMod 3), CanonicalAPResidues s a →
    ∃ i : Fin 39, disjointDigits expectedDisjointResiduesLinear[i.val]! = residueVector s a r := by
  decide +kernel

theorem disjointResiduesLinear_cover (complete : disjointResiduesLinear = expectedDisjointResiduesLinear)
    (s : Fin 3 → ZMod 3) (a : Fin 3 → Bool) (r : ZMod 3) (h : CanonicalAPResidues s a) :
    ∃ i : Fin 39, disjointDigits disjointResiduesLinear[i.val]! = residueVector s a r := by
  rw [complete]
  exact expectedDisjointResiduesLinear_cover s a r h

private theorem step_digit {A : APState} (D : APState.PrimitiveCoordinates A)
    (disjoint : A.Disjoint) (i : Fin 3) :
    PadicInt.toZMod (D.steps i) = digitOfBool (decide (PadicInt.toZMod (D.steps i) ≠ 0)) := by
  have nonzero := A.step_nonzero disjoint i
  have nonneg : 0 ≤ val (A.step i) := by
    rw [← D.steps_eq]
    exact PadicInt.valuation_coe_nonneg
  have same : D.steps i = scaled (A.step i) nonzero 0 nonneg := by
    apply Subtype.ext
    change (D.steps i : K) = A.step i * (3 : K)^(-(0 : ℤ))
    simp [D.steps_eq]
  rw [same, scaled_residue, D.oriented]
  by_cases h : (0 : ℤ) = val (A.step i) <;> simp [h, digitOfBool]

theorem primitive_residue_vector {A : APState} (D : APState.PrimitiveCoordinates A)
    (disjoint : A.Disjoint) (r : O) : (PadicInt.toZMod ∘ D.vars r) =
    residueVector (fun i => PadicInt.toZMod (D.starts i))
      (fun i => decide (PadicInt.toZMod (D.steps i) ≠ 0)) (PadicInt.toZMod r) := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact step_digit D disjoint 0
  · exact step_digit D disjoint 1
  · exact step_digit D disjoint 2
  · rfl

theorem dispatch_disjoint_const {A : APState} (D : APState.PrimitiveCoordinates A)
    (disjoint : A.Disjoint) : ∃ i : Fin 13,
    disjointDigits disjointResiduesConst[i.val]! = PadicInt.toZMod ∘ D.vars 0 := by
  rw [primitive_residue_vector D disjoint 0, map_zero]
  exact disjointResiduesConst_cover _ _ D.canonical

theorem dispatch_disjoint_linear {A : APState} (D : APState.PrimitiveCoordinates A)
    (disjoint : A.Disjoint) (r : O) :
    ∃ i : Fin 39, disjointDigits disjointResiduesLinear[i.val]! = PadicInt.toZMod ∘ D.vars r := by
  rw [primitive_residue_vector D disjoint r]
  exact disjointResiduesLinear_cover disjointResiduesLinear_complete _ _ _ D.canonical

theorem dispatch_disjoint_root {A : APState} (D : APState.PrimitiveCoordinates A) (disjoint : A.Disjoint) :
    ((A.root = none ∨ ∃ r : K, A.root = some r ∧ val r < 0) ∧
      ∃ i : Fin 13, disjointDigits disjointResiduesConst[i.val]! = PadicInt.toZMod ∘ D.vars 0) ∨
    ∃ r : O, A.root = some (r : K) ∧
      ∃ i : Fin 39, disjointDigits disjointResiduesLinear[i.val]! = PadicInt.toZMod ∘ D.vars r := by
  cases root : A.root with
  | none => exact Or.inl ⟨Or.inl rfl, dispatch_disjoint_const D disjoint⟩
  | some r =>
      by_cases integral : ‖r‖ ≤ 1
      · exact Or.inr ⟨⟨r,integral⟩, rfl, dispatch_disjoint_linear D disjoint ⟨r,integral⟩⟩
      · have negative : val r < 0 := by
          exact lt_of_not_ge (fun nonneg => integral ((Padic.norm_le_one_iff_val_nonneg r).mpr nonneg))
        exact Or.inl ⟨Or.inr ⟨r,rfl,negative⟩, dispatch_disjoint_const D disjoint⟩

end

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

open PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem disjointDot_cast (c row : DisjointRow) : (disjointDot c row : ZMod 3) =
    APState.formEval (disjointDigits row) (disjointCoefficients c) := by
  simp [disjointDot, APState.formEval, disjointDigits, disjointCoefficients,
    Fin.sum_univ_succ, add_assoc]

theorem disjoint_form_digit {A : APState} (D : APState.PrimitiveCoordinates A)
    (r : O) (c row : DisjointRow)
    (matchRow : disjointDigits row = PadicInt.toZMod ∘ D.vars r)
    (h : APState.formEval (A.fieldVars r) (disjointCoefficients c) ≠ 0) :
    let x := APState.formEval (A.fieldVars r) (disjointCoefficients c)
    residueFacts (val x) (lead x h = -1) (disjointDot c row % 3) := by
  let f := disjointCoefficients c
  let x := APState.formEval (A.fieldVars r) f
  obtain ⟨nonneg, digit⟩ := D.form_residue r f h
  apply residueFacts_of_digit _ _ _ nonneg (lead_ne_zero x h)
    (Int.emod_nonneg _ (by decide)) (Int.emod_lt_of_pos _ (by decide))
  rw [show ((disjointDot c row % 3 : ℤ) : ZMod 3) = (disjointDot c row : ZMod 3) from
    ZMod.intCast_mod _ 3, disjointDot_cast, matchRow]
  exact digit

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

open PEqualNP.Outside.L_gct_234.Triadic

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

theorem disjoint_model_residues {A : APState} (D : APState.PrimitiveCoordinates A)
    (r : O) (forms : Array DisjointRow) (model : ℕ → K) (row : DisjointRow)
    (matchRow : disjointDigits row = PadicInt.toZMod ∘ D.vars r)
    (value : ∀ k < forms.size, model k = APState.formEval (A.fieldVars r) (disjointCoefficients forms[k]!))
    (nonzero : ∀ k < forms.size, model k ≠ 0) :
    ∀ k < forms.size, residueFacts (val (model k)) (Negative (model k)) (disjointDot forms[k]! row % 3) := by
  intro k hk
  let x := APState.formEval (A.fieldVars r) (disjointCoefficients forms[k]!)
  have eq : model k = x := value k hk
  have h : x ≠ 0 := eq ▸ nonzero k hk
  have formspec := disjoint_form_digit D r forms[k]! row matchRow h
  rw [eq, negative_iff _ h, minusLead]
  exact formspec

theorem disjoint_const_residue_facts {A : APState} (D : APState.PrimitiveCoordinates A)
    (a : Fin 13) (model : ℕ → K)
    (matchRow : disjointDigits disjointResiduesConst[a.val]! = PadicInt.toZMod ∘ D.vars 0)
    (value : ∀ k < disjointFormsConst.size,
      model k = APState.formEval (A.fieldVars 0) (disjointCoefficients disjointFormsConst[k]!))
    (nonzero : ∀ k < disjointFormsConst.size, model k ≠ 0) :
    ∀ k < disjointFormsConst.size,
      residueFacts (val (model k)) (Negative (model k)) (disjointResidueConst a.val k) :=
  disjoint_model_residues D 0 disjointFormsConst model _ matchRow value nonzero

theorem disjoint_linear_residue_facts {A : APState} (D : APState.PrimitiveCoordinates A)
    (r : O) (a : Fin 39) (model : ℕ → K)
    (matchRow : disjointDigits disjointResiduesLinear[a.val]! = PadicInt.toZMod ∘ D.vars r)
    (value : ∀ k < disjointFormsLinear.size,
      model k = APState.formEval (A.fieldVars r) (disjointCoefficients disjointFormsLinear[k]!))
    (nonzero : ∀ k < disjointFormsLinear.size, model k ≠ 0) :
    ∀ k < disjointFormsLinear.size,
      residueFacts (val (model k)) (Negative (model k)) (disjointResidueLinear a.val k) :=
  disjoint_model_residues D r disjointFormsLinear model _ matchRow value nonzero

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234

private theorem occupiesExtreme {flag : Bool} {e a : ℤ} {xs : List ℤ}
    (eq : e = certifiedExtreme flag a xs) : e ∈ a :: xs :=
  eq.symm ▸ certifiedExtreme_present flag a xs

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical

structure NonExtremaConst (v : Nat → Int) (u : Nat → Prop) : Prop where
  r401 : disjointNonTriadRulesConst v (disjointAuxConst v) u 401
  r403 : disjointNonTriadRulesConst v (disjointAuxConst v) u 403
  r405 : disjointNonTriadRulesConst v (disjointAuxConst v) u 405
  r406 : disjointNonTriadRulesConst v (disjointAuxConst v) u 406
  r407 : disjointNonTriadRulesConst v (disjointAuxConst v) u 407
  r409 : disjointNonTriadRulesConst v (disjointAuxConst v) u 409
  r410 : disjointNonTriadRulesConst v (disjointAuxConst v) u 410
  r411 : disjointNonTriadRulesConst v (disjointAuxConst v) u 411
  r422 : disjointNonTriadRulesConst v (disjointAuxConst v) u 422
  r442 : disjointNonTriadRulesConst v (disjointAuxConst v) u 442

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 16000 in
theorem derivedNonTriadConst (v : Nat → Int) (u : Nat → Prop)
    (h : NonExtremaConst v u) (k : Nat) :
    disjointNonTriadRulesConst v (disjointAuxConst v) u k := by

  have hey0 : disjointAuxConst v 0 = certifiedExtreme true (v 44) [(v 43), (v 13), (v 46), (v 11), (v 12), (v 45), (v 14)] := rfl
  have hey2 : disjointAuxConst v 2 = certifiedExtreme true (v 25) [(v 4), (v 21), (v 8), (v 12), (v 29), (v 16), (v 33)] := rfl
  unfold disjointNonTriadRulesConst
  split
  · exact h.r401
  · exact h.r403
  · exact h.r405
  · exact h.r406
  · exact h.r407
  · exact h.r409
  · exact h.r410
  · exact h.r411
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using occupiesExtreme hey0
  · exact h.r422
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using occupiesExtreme hey2
  · exact h.r442
  · trivial

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical

structure NonExtremaLinear (v : Nat → Int) (u : Nat → Prop) : Prop where
  r65 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 65
  r66 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 66
  r491 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 491
  r492 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 492
  r493 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 493
  r494 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 494
  r495 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 495
  r496 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 496
  r497 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 497
  r498 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 498
  r499 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 499
  r500 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 500
  r501 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 501
  r502 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 502
  r513 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 513
  r524 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 524
  r535 : disjointNonTriadRulesLinear v (disjointAuxLinear v) u 535

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 16000 in
theorem derivedNonTriadLinear (v : Nat → Int) (u : Nat → Prop)
    (h : NonExtremaLinear v u) (k : Nat) :
    disjointNonTriadRulesLinear v (disjointAuxLinear v) u k := by

  have hey0 : disjointAuxLinear v 0 = certifiedExtreme true (v 52) [(v 51), (v 17), (v 54), (v 15), (v 16), (v 53), (v 18), (v 3)] := rfl
  have hey1 : disjointAuxLinear v 1 = certifiedExtreme true (v 44) [(v 48), (v 52), (v 32), (v 34), (v 33), (v 58), (v 31), (v 57)] := rfl
  have hey2 : disjointAuxLinear v 2 = certifiedExtreme true (v 33) [(v 8), (v 29), (v 12), (v 16), (v 37), (v 22), (v 41), (v 21)] := rfl
  unfold disjointNonTriadRulesLinear
  split
  · exact h.r65
  · exact h.r66
  · exact h.r491
  · exact h.r492
  · exact h.r493
  · exact h.r494
  · exact h.r495
  · exact h.r496
  · exact h.r497
  · exact h.r498
  · exact h.r499
  · exact h.r500
  · exact h.r501
  · exact h.r502
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using occupiesExtreme hey0
  · exact h.r513
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using occupiesExtreme hey1
  · exact h.r524
  · simpa only [List.mem_cons, List.not_mem_nil, or_false, false_or, or_assoc, or_comm, or_left_comm] using occupiesExtreme hey2
  · exact h.r535
  · trivial

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable section

set_option maxHeartbeats 5000000 in
theorem disjointGeometryConst (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) (D : PrimitiveCoordinates A) (far : ∀ q ∈ A.root, val q < 0)
    (dominance : ∀ q ∈ A.root, ∀ i p, val (A.point i p-q) = val q ∧
      (Negative (A.point i p-q) ↔ ¬Negative q)) :
    let x := formValue disjointFormsConst (A.fieldVars 0)
    let v := val ∘ x
    let u := Negative ∘ x
    disjointNonTriadRulesConst v (disjointAuxConst v) u 401 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 403 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 405 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 406 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 407 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 409 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 410 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 411 := by
  dsimp only
  let x := formValue disjointFormsConst (A.fieldVars 0)
  let v := val ∘ x
  let u := Negative ∘ x
  have nz := disjointFieldNonzeroConst A 0 D.start_zero (A.apart_constant disjoint)
  have dist (a b : Fin 12) (e : a ≠ b) :=
    distanceInterpretation disjointFormsConst A 0 D.start_zero a.val b.val (selectedDistance disjointDistanceConst a.val b.val)
      (disjointDistanceLawConst a b e) nz
  let vT := fun a b => packedVal v (packCoeffTerm (selectedDistance disjointDistanceConst a b))
  let uT := fun a b => packedUnit u (packCoeffTerm (selectedDistance disjointDistanceConst a b))
  have dv (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A 0 (by decide) vT uT dist i j p q ne).1
  have du (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A 0 (by decide) vT uT dist i j p q ne).2

  have g0 := A.affine_of_pairOutside disjoint sep geo (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) false (fun _ => dominance)
  have g1 := A.affine_of_pairOutside disjoint sep geo (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide) false (fun _ => dominance)
  have g2 := A.affine_of_pairOutside disjoint sep geo (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide) false (fun _ => dominance)
  dsimp only at g0 g1 g2
  simp only [pairOutside, List.ofFn_succ, List.ofFn_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, xorProduct, List.foldl_cons, List.foldl_nil, false_iff, not_false_eq_true, not_not, effectiveDenom, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false, Denom, Option.elim] at g0 g1 g2
  simp (disch := decide) only [dv, du] at g0 g1 g2
  norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit, negative_iff 1 one_ne_zero,minusLead,lead_one,show (1 : F) ≠ -1 by decide,show val (1 : K) = 0 from Padic.valuation_one] at g0 g1 g2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [disjointNonTriadRulesConst]
  · linear_combination g0.1.1
  · linear_combination g0.2.1
  · linear_combination g1.1.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g1.1.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g1.2.1
  · linear_combination g2.1.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g2.1.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g2.2.1
end
end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable section

set_option maxHeartbeats 5000000 in
theorem disjointGeometryLinear (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) (D : PrimitiveCoordinates A) (r : K) (rEq : A.root = some r) :
    let x := formValue disjointFormsLinear (A.fieldVars r)
    let v := val ∘ x
    let u := Negative ∘ x
    disjointNonTriadRulesLinear v (disjointAuxLinear v) u 491 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 492 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 493 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 494 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 495 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 496 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 497 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 498 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 499 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 500 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 501 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 502 := by
  dsimp only
  let x := formValue disjointFormsLinear (A.fieldVars r)
  let v := val ∘ x
  let u := Negative ∘ x
  have nz := disjointFieldNonzeroLinear A r D.start_zero (A.apart_linear r disjoint sep rEq)
  have dist (a b : Fin 13) (e : a ≠ b) :=
    distanceInterpretation disjointFormsLinear A r D.start_zero a.val b.val (selectedDistance disjointDistanceLinear a.val b.val)
      (disjointDistanceLawLinear a b e) nz
  let vT := fun a b => packedVal v (packCoeffTerm (selectedDistance disjointDistanceLinear a b))
  let uT := fun a b => packedUnit u (packCoeffTerm (selectedDistance disjointDistanceLinear a b))
  have dv (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A r (by decide) vT uT dist i j p q ne).1
  have du (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A r (by decide) vT uT dist i j p q ne).2
  have dp (i : Fin 3) (p : Fin 4) := (root_distance_transport A r vT uT dist i p).1
  have up (i : Fin 3) (p : Fin 4) := (root_distance_transport A r vT uT dist i p).2

  have g0 := A.affine_of_pairOutside disjoint sep geo (i := 0) (j := 1) (k := 2) (by decide) (by decide) (by decide) true (by simp)
  have g1 := A.affine_of_pairOutside disjoint sep geo (i := 1) (j := 0) (k := 2) (by decide) (by decide) (by decide) true (by simp)
  have g2 := A.affine_of_pairOutside disjoint sep geo (i := 2) (j := 0) (k := 1) (by decide) (by decide) (by decide) true (by simp)
  dsimp only at g0 g1 g2
  simp only [pairOutside, List.ofFn_succ, List.ofFn_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, xorProduct, List.foldl_cons, List.foldl_nil, false_iff, not_false_eq_true, not_not, effectiveDenom, Bool.true_eq_false, Bool.false_eq_true, ite_true, ite_false, Denom, rEq, Option.elim] at g0 g1 g2
  simp (disch := decide) only [dv, du, dp, up] at g0 g1 g2
  norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit, negative_iff 1 one_ne_zero,minusLead,lead_one,show (1 : F) ≠ -1 by decide,show val (1 : K) = 0 from Padic.valuation_one] at g0 g1 g2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [disjointNonTriadRulesLinear]
  · linear_combination g0.1.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g0.1.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g0.2.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g0.2.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g1.1.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g1.1.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g1.2.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g1.2.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g2.1.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g2.1.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
  · linear_combination g2.2.1
  ·
    first | apply (parityBit_inj _ _).mp | apply (parityBit_opp _ _).mp
    have eq := congrArg parityBit (propext (g2.2.2))
    simp only [parityBit_iff, parityBit_not] at eq ⊢
    linear_combination eq
end
end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable section

set_option maxHeartbeats 5000000 in
theorem disjointNearestConst (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) (D : PrimitiveCoordinates A) (far : ∀ q ∈ A.root, val q < 0) :
    let x := formValue disjointFormsConst (A.fieldVars 0)
    let v := val ∘ x
    let u := Negative ∘ x
    disjointNonTriadRulesConst v (disjointAuxConst v) u 422 ∧ disjointNonTriadRulesConst v (disjointAuxConst v) u 442 := by
  dsimp only
  let x := formValue disjointFormsConst (A.fieldVars 0)
  let v := val ∘ x
  let u := Negative ∘ x
  let aux := disjointAuxConst v
  have nz := disjointFieldNonzeroConst A 0 D.start_zero (A.apart_constant disjoint)
  have E (a b : Fin 12) (e : a ≠ b) :=
    distanceInterpretation disjointFormsConst A 0 D.start_zero a.val b.val (selectedDistance disjointDistanceConst a.val b.val)
      (disjointDistanceLawConst a b e) nz
  let vT := fun a b => packedVal v (packCoeffTerm (selectedDistance disjointDistanceConst a b))
  let uT := fun a b => packedUnit u (packCoeffTerm (selectedDistance disjointDistanceConst a b))
  have dv (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A 0 (by decide) vT uT E i j p q ne).1
  have du (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A 0 (by decide) vT uT E i j p q ne).2
  refine ⟨?_, ?_⟩
  · change disjointNonTriadRulesConst v aux u 422
    unfold disjointNonTriadRulesConst
    have step := E 1 0 (by decide)
    change val (A.point 0 1 - A.point 0 0) = vT 1 0 ∧
      (Negative (A.point 0 1 - A.point 0 0) ↔ uT 1 0) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    rcases le_or_gt (v 2) (aux 0) with order|order
    · exact Or.inl order
    · apply Or.inr
      have hSmall : aux 0 < val (A.step 0) := by rw [step.1]; exact order
      have hAux : aux 0 = certifiedExtreme true (v 44) [(v 43), (v 13), (v 46), (v 11), (v 12), (v 45), (v 14)] := rfl
      have upper (u : Int) (mem : u ∈ (v 44) :: [(v 43), (v 13), (v 46), (v 11), (v 12), (v 45), (v 14)]) : u ≤ aux 0 := by
        rw [hAux]
        exact certifiedExtreme_upper _ _ _ mem
      have close (y : K) (hy : y ∈ A.pairOutside 1 2) : val (A.point 0 1-y) ≤ aux 0 := by
        simp only [pairOutside,List.mem_append,List.mem_ofFn] at hy
        rcases hy with ⟨t,rfl⟩|⟨t,rfl⟩
        all_goals
          fin_cases t <;> simp (disch := decide) only [dv] <;> norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] <;>
            (apply upper; simp)
      have nonneg : 0 ≤ aux 0 :=
        (D.point_diff_nonneg 0 1 1 0).trans (close (A.point 1 0) (by
          simp only [pairOutside,List.mem_append,List.mem_ofFn]
          exact Or.inl ⟨0,rfl⟩))
      have closeRoot : false = true → ∀ r' ∈ A.root, val (A.point 0 1-r') ≤ aux 0 := by
        simp
      have p := A.nearest_pairOutside disjoint sep geo (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) (by decide) false (fun _ q rq => (D.far_root q (far q rq) 0 1).1 ▸ far q rq)
        (aux 0) nonneg hSmall close closeRoot
      dsimp only at p
      simp only [pairOutside,List.ofFn_succ,List.ofFn_zero,List.nil_append,List.cons_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
        Option.map,Option.elim] at p
      simp (disch := decide) only [dv,du] at p
      norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at p
      constructor
      · apply Nat.mod_eq_zero_of_dvd
        apply Int.natCast_dvd_natCast.mp
        simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        convert p.1 using 1 <;> (try simp only [sub_eq_add_neg, neg_ite, neg_zero, neg_neg]) <;> ring
      · apply Int.emod_eq_zero_of_dvd
        convert p.2 using 1 <;> (try simp only [sub_eq_add_neg, ite_not, neg_ite, neg_zero, neg_neg]) <;> ring
  · change disjointNonTriadRulesConst v aux u 442
    unfold disjointNonTriadRulesConst
    have step := E 9 8 (by decide)
    change val (A.point 2 1 - A.point 2 0) = vT 9 8 ∧
      (Negative (A.point 2 1 - A.point 2 0) ↔ uT 9 8) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    rcases le_or_gt (v 0) (aux 2) with order|order
    · exact Or.inl order
    · apply Or.inr
      have hSmall : aux 2 < val (A.step 2) := by rw [step.1]; exact order
      have hAux : aux 2 = certifiedExtreme true (v 25) [(v 4), (v 21), (v 8), (v 12), (v 29), (v 16), (v 33)] := rfl
      have upper (u : Int) (mem : u ∈ (v 25) :: [(v 4), (v 21), (v 8), (v 12), (v 29), (v 16), (v 33)]) : u ≤ aux 2 := by
        rw [hAux]
        exact certifiedExtreme_upper _ _ _ mem
      have close (y : K) (hy : y ∈ A.pairOutside 0 1) : val (A.point 2 1-y) ≤ aux 2 := by
        simp only [pairOutside,List.mem_append,List.mem_ofFn] at hy
        rcases hy with ⟨t,rfl⟩|⟨t,rfl⟩
        all_goals
          fin_cases t <;> simp (disch := decide) only [dv] <;> norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] <;>
            (apply upper; simp)
      have nonneg : 0 ≤ aux 2 :=
        (D.point_diff_nonneg 2 0 1 0).trans (close (A.point 0 0) (by
          simp only [pairOutside,List.mem_append,List.mem_ofFn]
          exact Or.inl ⟨0,rfl⟩))
      have closeRoot : false = true → ∀ r' ∈ A.root, val (A.point 2 1-r') ≤ aux 2 := by
        simp
      have p := A.nearest_pairOutside disjoint sep geo (i := 2) (j := 0) (k := 1)
        (by decide) (by decide) (by decide) false (fun _ q rq => (D.far_root q (far q rq) 2 1).1 ▸ far q rq)
        (aux 2) nonneg hSmall close closeRoot
      dsimp only at p
      simp only [pairOutside,List.ofFn_succ,List.ofFn_zero,List.nil_append,List.cons_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
        Option.map,Option.elim] at p
      simp (disch := decide) only [dv,du] at p
      norm_num [vT,uT,selectedDistance,disjointDistanceConst,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at p
      constructor
      · apply Nat.mod_eq_zero_of_dvd
        apply Int.natCast_dvd_natCast.mp
        simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
        convert p.1 using 1 <;> (try simp only [sub_eq_add_neg, neg_ite, neg_zero, neg_neg]) <;> ring
      · apply Int.emod_eq_zero_of_dvd
        convert p.2 using 1 <;> (try simp only [sub_eq_add_neg, ite_not, neg_ite, neg_zero, neg_neg]) <;> ring
end
end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
noncomputable section

set_option maxHeartbeats 5000000 in
theorem disjointNearestLinear (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) (D : PrimitiveCoordinates A) (r : K) (rEq : A.root = some r) :
    let x := formValue disjointFormsLinear (A.fieldVars r)
    let v := val ∘ x
    let u := Negative ∘ x
    disjointNonTriadRulesLinear v (disjointAuxLinear v) u 65 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 66 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 513 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 524 ∧ disjointNonTriadRulesLinear v (disjointAuxLinear v) u 535 := by
  dsimp only
  let x := formValue disjointFormsLinear (A.fieldVars r)
  let v := val ∘ x
  let u := Negative ∘ x
  let aux := disjointAuxLinear v
  have nz := disjointFieldNonzeroLinear A r D.start_zero (A.apart_linear r disjoint sep rEq)
  have E (a b : Fin 13) (e : a ≠ b) :=
    distanceInterpretation disjointFormsLinear A r D.start_zero a.val b.val (selectedDistance disjointDistanceLinear a.val b.val)
      (disjointDistanceLawLinear a b e) nz
  let vT := fun a b => packedVal v (packCoeffTerm (selectedDistance disjointDistanceLinear a b))
  let uT := fun a b => packedUnit u (packCoeffTerm (selectedDistance disjointDistanceLinear a b))
  have dv (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A r (by decide) vT uT E i j p q ne).1
  have du (i j : Fin 3) (p q : Fin 4) (ne : i ≠ j ∨ p ≠ q) :=
    (block_distance_transport A r (by decide) vT uT E i j p q ne).2
  have dp (i : Fin 3) (p : Fin 4) := (root_distance_transport A r vT uT E i p).1
  have up (i : Fin 3) (p : Fin 4) := (root_distance_transport A r vT uT E i p).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change disjointNonTriadRulesLinear v aux u 65
    unfold disjointNonTriadRulesLinear
    have step := E 5 4 (by decide)
    change val (A.point 1 1 - A.point 1 0) = vT 5 4 ∧
      (Negative (A.point 1 1 - A.point 1 0) ↔ uT 5 4) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    change ¬u 2
    rw [← step.2, negative_iff _ (A.step_nonzero disjoint 1), minusLead, D.oriented]
    decide
  · change disjointNonTriadRulesLinear v aux u 66
    unfold disjointNonTriadRulesLinear
    have step := E 9 8 (by decide)
    change val (A.point 2 1 - A.point 2 0) = vT 9 8 ∧
      (Negative (A.point 2 1 - A.point 2 0) ↔ uT 9 8) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    change ¬u 1
    rw [← step.2, negative_iff _ (A.step_nonzero disjoint 2), minusLead, D.oriented]
    decide
  · change disjointNonTriadRulesLinear v aux u 513
    unfold disjointNonTriadRulesLinear
    have step := E 1 0 (by decide)
    change val (A.point 0 1 - A.point 0 0) = vT 1 0 ∧
      (Negative (A.point 0 1 - A.point 0 0) ↔ uT 1 0) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    rcases le_or_gt (v 4) (aux 0) with order|order
    · exact Or.inl order
    · apply Or.inr
      have hSmall : aux 0 < val (A.step 0) := by rw [step.1]; exact order
      have hAux : aux 0 = certifiedExtreme true (v 52) [(v 51), (v 17), (v 54), (v 15), (v 16), (v 53), (v 18), (v 3)] := rfl
      have upper (u : Int) (mem : u ∈ (v 52) :: [(v 51), (v 17), (v 54), (v 15), (v 16), (v 53), (v 18), (v 3)]) : u ≤ aux 0 := by
        rw [hAux]
        exact certifiedExtreme_upper _ _ _ mem
      have close (y : K) (hy : y ∈ A.pairOutside 1 2) : val (A.point 0 1-y) ≤ aux 0 := by
        simp only [pairOutside,List.mem_append,List.mem_ofFn] at hy
        rcases hy with ⟨t,rfl⟩|⟨t,rfl⟩
        all_goals
          fin_cases t <;> simp (disch := decide) only [dv] <;> norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] <;>
            (apply upper; simp)
      have nonneg : 0 ≤ aux 0 :=
        (D.point_diff_nonneg 0 1 1 0).trans (close (A.point 1 0) (by
          simp only [pairOutside,List.mem_append,List.mem_ofFn]
          exact Or.inl ⟨0,rfl⟩))
      have closeRoot : true = true → ∀ r' ∈ A.root, val (A.point 0 1-r') ≤ aux 0 := by
        intro _ r' key
        simp [rEq] at key
        subst r'
        rw [dp]
        norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit]
        apply upper
        simp
      have p := A.nearest_pairOutside disjoint sep geo (i := 0) (j := 1) (k := 2)
        (by decide) (by decide) (by decide) true (by simp)
        (aux 0) nonneg hSmall close closeRoot
      dsimp only at p
      simp only [pairOutside,List.ofFn_succ,List.ofFn_zero,List.nil_append,List.cons_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
        Option.map,Option.elim,rEq] at p
      simp (disch := decide) only [dv,du,dp,up] at p
      norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at p
      constructor
      · apply Int.emod_eq_zero_of_dvd
        convert p.1 using 1 <;> (try simp only [sub_eq_add_neg, neg_ite, neg_zero, neg_neg]) <;> ring
      · apply Int.emod_eq_zero_of_dvd
        convert p.2 using 1 <;> (try simp only [sub_eq_add_neg, ite_not, neg_ite, neg_zero, neg_neg]) <;> ring
  · change disjointNonTriadRulesLinear v aux u 524
    unfold disjointNonTriadRulesLinear
    have step := E 5 4 (by decide)
    change val (A.point 1 1 - A.point 1 0) = vT 5 4 ∧
      (Negative (A.point 1 1 - A.point 1 0) ↔ uT 5 4) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    rcases le_or_gt (v 2) (aux 1) with order|order
    · exact Or.inl order
    · apply Or.inr
      have hSmall : aux 1 < val (A.step 1) := by rw [step.1]; exact order
      have hAux : aux 1 = certifiedExtreme true (v 44) [(v 48), (v 52), (v 32), (v 34), (v 33), (v 58), (v 31), (v 57)] := rfl
      have upper (u : Int) (mem : u ∈ (v 44) :: [(v 48), (v 52), (v 32), (v 34), (v 33), (v 58), (v 31), (v 57)]) : u ≤ aux 1 := by
        rw [hAux]
        exact certifiedExtreme_upper _ _ _ mem
      have close (y : K) (hy : y ∈ A.pairOutside 0 2) : val (A.point 1 1-y) ≤ aux 1 := by
        simp only [pairOutside,List.mem_append,List.mem_ofFn] at hy
        rcases hy with ⟨t,rfl⟩|⟨t,rfl⟩
        all_goals
          fin_cases t <;> simp (disch := decide) only [dv] <;> norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] <;>
            (apply upper; simp)
      have nonneg : 0 ≤ aux 1 :=
        (D.point_diff_nonneg 1 0 1 0).trans (close (A.point 0 0) (by
          simp only [pairOutside,List.mem_append,List.mem_ofFn]
          exact Or.inl ⟨0,rfl⟩))
      have closeRoot : true = true → ∀ r' ∈ A.root, val (A.point 1 1-r') ≤ aux 1 := by
        intro _ r' key
        simp [rEq] at key
        subst r'
        rw [dp]
        norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit]
        apply upper
        simp
      have p := A.nearest_pairOutside disjoint sep geo (i := 1) (j := 0) (k := 2)
        (by decide) (by decide) (by decide) true (by simp)
        (aux 1) nonneg hSmall close closeRoot
      dsimp only at p
      simp only [pairOutside,List.ofFn_succ,List.ofFn_zero,List.nil_append,List.cons_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
        Option.map,Option.elim,rEq] at p
      simp (disch := decide) only [dv,du,dp,up] at p
      norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at p
      constructor
      · apply Int.emod_eq_zero_of_dvd
        convert p.1 using 1 <;> (try simp only [sub_eq_add_neg, neg_ite, neg_zero, neg_neg]) <;> ring
      · apply Int.emod_eq_zero_of_dvd
        convert p.2 using 1 <;> (try simp only [sub_eq_add_neg, ite_not, neg_ite, neg_zero, neg_neg]) <;> ring
  · change disjointNonTriadRulesLinear v aux u 535
    unfold disjointNonTriadRulesLinear
    have step := E 9 8 (by decide)
    change val (A.point 2 1 - A.point 2 0) = vT 9 8 ∧
      (Negative (A.point 2 1 - A.point 2 0) ↔ uT 9 8) at step
    rw [step_difference] at step
    norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at step
    rcases le_or_gt (v 1) (aux 2) with order|order
    · exact Or.inl order
    · apply Or.inr
      have hSmall : aux 2 < val (A.step 2) := by rw [step.1]; exact order
      have hAux : aux 2 = certifiedExtreme true (v 33) [(v 8), (v 29), (v 12), (v 16), (v 37), (v 22), (v 41), (v 21)] := rfl
      have upper (u : Int) (mem : u ∈ (v 33) :: [(v 8), (v 29), (v 12), (v 16), (v 37), (v 22), (v 41), (v 21)]) : u ≤ aux 2 := by
        rw [hAux]
        exact certifiedExtreme_upper _ _ _ mem
      have close (y : K) (hy : y ∈ A.pairOutside 0 1) : val (A.point 2 1-y) ≤ aux 2 := by
        simp only [pairOutside,List.mem_append,List.mem_ofFn] at hy
        rcases hy with ⟨t,rfl⟩|⟨t,rfl⟩
        all_goals
          fin_cases t <;> simp (disch := decide) only [dv] <;> norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] <;>
            (apply upper; simp)
      have nonneg : 0 ≤ aux 2 :=
        (D.point_diff_nonneg 2 0 1 0).trans (close (A.point 0 0) (by
          simp only [pairOutside,List.mem_append,List.mem_ofFn]
          exact Or.inl ⟨0,rfl⟩))
      have closeRoot : true = true → ∀ r' ∈ A.root, val (A.point 2 1-r') ≤ aux 2 := by
        intro _ r' key
        simp [rEq] at key
        subst r'
        rw [dp]
        norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit]
        apply upper
        simp
      have p := A.nearest_pairOutside disjoint sep geo (i := 2) (j := 0) (k := 1)
        (by decide) (by decide) (by decide) true (by simp)
        (aux 2) nonneg hSmall close closeRoot
      dsimp only at p
      simp only [pairOutside,List.ofFn_succ,List.ofFn_zero,List.nil_append,List.cons_append,List.map_cons,
        List.map_nil,List.sum_cons,List.sum_nil,Bool.true_eq_false,Bool.false_eq_true,ite_true,ite_false,
        Option.map,Option.elim,rEq] at p
      simp (disch := decide) only [dv,du,dp,up] at p
      norm_num [vT,uT,selectedDistance,disjointDistanceLinear,packedVal,packedUnit,packCoeffTerm,coeffOrder,coeffUnit] at p
      constructor
      · apply Int.emod_eq_zero_of_dvd
        convert p.1 using 1 <;> (try simp only [sub_eq_add_neg, neg_ite, neg_zero, neg_neg]) <;> ring
      · apply Int.emod_eq_zero_of_dvd
        convert p.2 using 1 <;> (try simp only [sub_eq_add_neg, ite_not, neg_ite, neg_zero, neg_neg]) <;> ring
end
end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def secondResidueFacts (v : ℤ) (u : Prop) (d : F) : Prop :=
  if d = 0 then 1 < v else v = 1 ∧ (if d = 1 then ¬u else u)

def rowSecondDigit (f c : DisjointRow) (e : Fin 5 → F) : F :=
  ((disjointDot f c / 3 : ℤ) : F) +
    formEval (![0,e 0,e 1,0,e 2,e 3,e 4] : Fin 7 → F) (rowForm f)

def disjointSecondDigit (a k : Nat) (e : Fin 5 → F) : F :=
  rowSecondDigit disjointFormsLinear[k]! disjointResiduesLinear[a]! e

private theorem three_dvd_of_same_digit (x : O) (c : ℤ) (h : PadicInt.toZMod x = (c : F)) :
    ∃ y : O, x = c + 3*y := by
  have mem : x - (c : O) ∈ RingHom.ker (PadicInt.toZMod : O →+* F) := by
    rw [RingHom.mem_ker, map_sub, map_intCast, h, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at mem
  obtain ⟨y, e⟩ := mem
  change x - (c : O) = 3*y at e
  exact ⟨y, by rw [← e]; ring⟩

private theorem eval_shifted_digit (c f : Form) (y : Fin 7 → O) (q : ℤ)
    (carry : formEval c f = 3*q) :
    formEval (fun i => (c i : O) + 3*y i) f = 3*((q : O) + formEval y f) := by
  simp only [formEval, mul_add, Finset.sum_add_distrib, mul_left_comm _ (3 : O), ← Finset.mul_sum]
  have out := congrArg (fun x : ℤ => (x : O)) carry
  unfold formEval at out
  push_cast at out
  rw [out]

private theorem secondFacts_of_scaled (x : K) (nz : x ≠ 0) (z : O)
    (scaled_z : x = 3*(z : K)) :
    secondResidueFacts (val x) (Negative x) (PadicInt.toZMod z) := by
  have zn : (z : K) ≠ 0 := by
    intro h
    exact nz (by simp [scaled_z,h])
  have v3 : val (3 : K) = 1 := Padic.valuation_p (p := 3)
  have xval : val x = 1+val (z : K) := by
    have product : val (3*(z : K)) = val (3 : K) + val (z : K) :=
      Padic.valuation_mul (by norm_num : (3 : K) ≠ 0) zn
    rw [scaled_z, product, v3]
  have bound : 1 ≤ val x := by
    rw [xval]
    have : 0 ≤ val (z : K) := PadicInt.valuation_coe_nonneg
    omega
  have same : z = scaled x nz 1 bound := by
    apply Subtype.ext
    change (z : K) = x * (3 : K)^(-(1 : ℤ))
    rw [scaled_z, zpow_neg_one]
    ring_nf
  rw [same, scaled_residue]
  by_cases eq : 1 = val x
  · rw [ite_eq_left eq, secondResidueFacts, ite_eq_right (lead_ne_zero x nz)]
    refine ⟨eq.symm, ?_⟩
    rw [negative_iff _ nz]
    change (if lead x nz = 1 then ¬(lead x nz = -1) else lead x nz = -1)
    rcases lead_one_or_neg_one x nz with h | h
    · rw [ite_eq_left h, h]
      decide
    · rw [ite_eq_right (by rw [h]; decide), h]
  · rw [ite_eq_right eq, secondResidueFacts, ite_eq_left rfl]
    omega

private theorem second_residue_facts_for_row {A : APState} (D : PrimitiveCoordinates A)
    (r : O) (row : DisjointRow) (forms : Array DisjointRow)
    (matchRow : (fun i => (rowForm row i : F)) = PadicInt.toZMod ∘ D.vars r)
    (pivot : rowForm row 3 = 1) (c0 : rowForm row 0 = 0)
    (nz : ∀ k < forms.size, formValue forms (A.fieldVars r) k ≠ 0) :
    ∃ e : Fin 5 → F, ∀ k < forms.size, disjointDot forms[k]! row % 3 = 0 →
      secondResidueFacts (val (formValue forms (A.fieldVars r) k))
        (Negative (formValue forms (A.fieldVars r) k)) (rowSecondDigit forms[k]! row e) := by
  let c := rowForm row
  have c0' : c 0 = 0 := c0
  have c3 : c 3 = 1 := pivot
  have lifted (i : Fin 7) : ∃ y : O, D.vars r i = (c i : O) + 3*y :=
    three_dvd_of_same_digit _ _ (congrFun matchRow i).symm
  choose y hy using lifted
  let Y : Fin 7 → F := PadicInt.toZMod ∘ y
  let E (i : Fin 7) := Y i - Y 3 * (c i : F)
  have Y0 : Y 0 = 0 := by
    have x0 : D.vars r 0 = 0 := by
      apply Subtype.ext
      change (D.starts 0 : K) = 0
      rw [D.starts_eq, D.start_zero]
    have eq := hy 0
    rw [x0, c0'] at eq
    simp only [Int.cast_zero, zero_add] at eq
    have yy : y 0 = 0 := (mul_eq_zero.mp eq.symm).resolve_left (by norm_num)
    simp [Y,yy]
  refine ⟨![E 1,E 2,E 4,E 5,E 6], ?_⟩
  intro k hk zero
  let f := rowForm forms[k]!
  let q := disjointDot forms[k]! row / 3
  have dot : formEval c f = disjointDot forms[k]! row := by
    simp [c,f,rowForm,formEval,disjointDot,Fin.sum_univ_succ,add_assoc]
  have divisible : formEval c f % 3 = 0 := by simpa only [dot] using zero
  have carry : formEval c f = 3*q := by
    dsimp [q]
    rw [← dot]
    omega
  let z := (q : O) + formEval y f
  have scaled_z : formValue forms (A.fieldVars r) k = 3*(z : K) := by
    change formEval (A.fieldVars r) f = 3*(z : K)
    rw [← D.vars_cast, ← formEval_ringHom PadicInt.Coe.ringHom]
    have forward : D.vars r = fun i => (c i : O) + 3*y i := funext hy
    rw [forward, eval_shifted_digit _ _ _ _ carry]
    rfl
  have digit : PadicInt.toZMod z =
      rowSecondDigit forms[k]! row ![E 1,E 2,E 4,E 5,E 6] := by
    simp only [z, map_add, map_intCast, formEval_ringHom, rowSecondDigit]
    change (q : F) + formEval Y f = (q : F) + formEval _ f
    congr 1
    have rebase : (![0,E 1,E 2,0,E 4,E 5,E 6] : Fin 7 → F) = E := by
      funext i
      fin_cases i <;> simp [E,Y0,c0',c3]
    change formEval Y f = formEval (![0,E 1,E 2,0,E 4,E 5,E 6] : Fin 7 → F) f
    rw [rebase]
    have toF : ((formEval c f : ℤ) : F) = 0 := by
      rw [carry, Int.cast_mul]
      change (3 : F) * (q : F) = 0
      rw [show (3 : F) = 0 by decide, zero_mul]
    have dotZero : formEval (fun i => (c i : F)) f = 0 := by
      exact (formEval_ringHom (Int.castRingHom F) c f).symm.trans toF
    simp only [E, formEval, mul_sub, Finset.sum_sub_distrib, mul_left_comm _ (Y 3), ← Finset.mul_sum]
    change formEval Y f = formEval Y f - Y 3*formEval (fun i => (c i : F)) f
    rw [dotZero,mul_zero,sub_zero]
  rw [← digit]
  exact secondFacts_of_scaled _ (nz k hk) z scaled_z

theorem disjoint_second_residue_facts {A : APState} (D : PrimitiveCoordinates A)
    (r : O) (a : Fin 39)
    (matchRow : (fun i => (rowForm disjointResiduesLinear[a.val]! i : F)) = PadicInt.toZMod ∘ D.vars r)
    (pivot : rowForm disjointResiduesLinear[a.val]! 3 = 1)
    (c0 : rowForm disjointResiduesLinear[a.val]! 0 = 0)
    (nz : ∀ k < disjointFormsLinear.size, formValue disjointFormsLinear (A.fieldVars r) k ≠ 0) :
    ∃ e : Fin 5 → F, ∀ k < disjointFormsLinear.size, disjointResidueLinear a.val k = 0 →
      secondResidueFacts (val (formValue disjointFormsLinear (A.fieldVars r) k))
        (Negative (formValue disjointFormsLinear (A.fieldVars r) k)) (disjointSecondDigit a.val k e) :=
  second_residue_facts_for_row D r _ _ matchRow pivot c0 nz

def constSecondDigit (a k : Nat) (e : Fin 5 → F) : F :=
  rowSecondDigit disjointFormsConst[k]! disjointResiduesConst[a]! e

theorem const_second_residue_facts {A : APState} (D : PrimitiveCoordinates A)
    (a : Fin 13)
    (matchRow : (fun i => (rowForm disjointResiduesConst[a.val]! i : F)) = PadicInt.toZMod ∘ D.vars 0)
    (pivot : rowForm disjointResiduesConst[a.val]! 3 = 1)
    (c0 : rowForm disjointResiduesConst[a.val]! 0 = 0)
    (nz : ∀ k < disjointFormsConst.size, formValue disjointFormsConst (A.fieldVars 0) k ≠ 0) :
    ∃ e : Fin 5 → F, ∀ k < disjointFormsConst.size, disjointResidueConst a.val k = 0 →
      secondResidueFacts (val (formValue disjointFormsConst (A.fieldVars 0) k))
        (Negative (formValue disjointFormsConst (A.fieldVars 0) k)) (constSecondDigit a.val k e) :=
  second_residue_facts_for_row D 0 _ _ matchRow pivot c0 nz

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def second001100 (j : Fin 18) : Fin 5 → F :=
  ![0, (j.val / 6 : ℕ),0, (j.val / 3 % 2 : ℕ), (j.val % 3 : ℕ)]

private theorem second001100Cover :
    ∀ e : Fin 5 → F, disjointSecondDigit 3 49 e = 0 →
      disjointSecondDigit 3 52 e = 0 → disjointSecondDigit 3 1 e ≠ 2 →
      ∃ j : Fin 18, e = second001100 j := by decide +kernel

private def second001100Cores : Array (List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ × List ℕ) :=
  #[([3,11,12,13,14,44,47,50,53],[5,15,16,17,18,45,48,51,54],[],[6],[7,8,9,10,43],[320],[493,494]),
   ([11,12,13,14,31,32,33,34,44,47,53,57,58],[15,16,17,18,35,36,37,38,45,48,51,59,60],[29],[39,40,41,42],[7,8,9,10,19,21,23,25,43,55],[91,251,316,402,425,465,476],[495,496,499,501]),
   ([3,11,12,13,14,31,32,33,34,44,47,50,53,57,58],[5,15,16,17,18,35,36,37,38,45,48,51,54,59,60],[],[21,23,25,39,40,41,55,62],[0,6,7,8,9,10,43],[128,294,313,320,373,402,425,465],[491,493,495,501]),
   ([3,4,11,12,13,14,31,32,33,34,44,47,50,53,57,58],[5,15,16,17,18,35,36,37,38,45,48,51,54,59,60],[],[1,6,9,21,22,28,39,42,61,62],[7,10,23,24,29,40,43],[122,207,236,274,320,402],[491,493,495,497,499,501]),
   ([4,11,12,13,14,31,32,33,34],[15,16,17,18,35,36,37,38],[27],[0,1,9,22,23,28,39,42],[7,10,19,24,25,29,40],[90,128,313],[499,501]),
   ([12,13,14,31,32,33],[16,17,18,35,36,37],[27],[1,9,19,22,25,28,39],[0,7,10,21,24,29,40],[69,122,128,308],[501]),
   ([3,11,12,13,14,31,32,33,34,44,50,53,57,58],[15,16,17,18,35,36,37,38,45,48,51,54,59,60],[],[6,19,20,21,22,23,24,25,26,61,62],[27,28,29,30,43],[190,227,277,308,320,395,405],[494,497,499,501]),
   ([3,11,12,13,14,47,50,53,58],[5,15,16,17,18,48,51,54,60],[],[0,20,22,24,26,62],[],[402],[491,492]),
   ([2,3,11,12,13,14,31,32,33,34,44,47,50,53,57,58],[5,15,16,17,18,35,36,37,38,45,48,51,54,59,60],[7,9],[20,22,24,26,62],[0,6,21,23,25,27,28,29,30,43,61],[320,395,402,409],[491,493,497,501]),
   ([11,12,13,14,31,32,33,34],[15,16,17,18,35,36,37,38],[7],[1,8,19,20,25,26,29,40],[9,21,22,27,30,41],[125,145,329],[499,501]),
   ([3,11,12,13,14,31,32,33,34,44,47,50,53,57,58],[5,15,16,17,18,35,36,37,38,45,48,51,54,59,60],[7],[0,1,8,20,21,26,29,40,62],[9,22,23,27,30,41,43],[91,125,146,173,191,251,279,320],[491,493,497,499,501]),
   ([11,12,13,32,33,34],[15,16,17,36,37,38],[7],[1,8,20,23,29,40],[6,9,19,22,27,30,41],[91,125,234,251],[499]),
   ([3,11,12,13,14,44,47,50,53],[5,15,16,17,18,45,48,51,54],[],[6,7,8,9,10],[43],[320],[493,494]),
   ([3,11,12,13,14,47,50,53,58],[5,15,16,17,18,48,51,54,60],[],[0,62],[20,22,24,26],[402],[491,492]),
   ([3,11,12,13,14,44,47,50,53,58],[5,15,16,17,18,45,48,51,54,60],[],[7,8,9,10,62],[0,6,20,22,24,26,43],[320,402],[491,493]),
   ([11,12,13,14,31,32,33,34],[15,16,17,18,35,36,37,38],[],[1,7,10,23,24,27,30,41],[8,19,20,25,26,28,39,42],[237,395],[499,501]),
   ([11,12,13,14,31,32,33,34],[15,16,17,18,35,36,37,38],[],[0,7,10,19,24,25,27,30,41],[8,20,21,26,28,39,42],[105,130],[499,501]),
   ([11,12,13,14,31,32,33,34],[15,16,17,18,35,36,37,38],[],[1,7,10,21,24,27,30,41],[0,6,8,20,23,26,28,39,42],[105,130,146,279],[499,501])]

private def second001100Triad : ℕ → PackedTriad
  | 69 => ((19,0, false), (21,0, false), (23,0, false))
  | 90 => ((4,1, false), (7,0, false), (20,0, true))
  | 91 => ((1,0, false), (22,0, false), (24,0, true))
  | 105 => ((27,0, false), (28,0, false), (29,0, false))
  | 122 => ((1,0, true), (39,0, false), (41,0, true))
  | 125 => ((1,0, false), (41,0, false), (42,0, true))
  | 128 => ((0,0, false), (25,0, false), (26,0, true))
  | 130 => ((0,0, false), (21,0, false), (22,0, true))
  | 145 => ((1,0, true), (8,0, false), (10,0, true))
  | 146 => ((1,0, true), (21,0, false), (25,0, true))
  | 173 => ((19,0, false), (42,0, false), (61,0, true))
  | 190 => ((40,0, false), (41,0, false), (42,0, false))
  | 191 => ((46,0, true), (49,1, true), (56,0, false))
  | 207 => ((0,0, false), (19,0, false), (20,0, true))
  | 227 => ((1,1, false), (7,0, false), (10,0, true))
  | 234 => ((6,0, false), (8,0, false), (21,0, true))
  | 236 => ((25,0, false), (27,0, false), (55,0, true))
  | 237 => ((1,0, false), (8,0, false), (9,0, true))
  | 251 => ((1,0, false), (27,0, false), (28,0, true))
  | 274 => ((4,1, false), (10,0, false), (26,0, true))
  | 277 => ((8,0, false), (9,0, false), (10,0, false))
  | 279 => ((6,0, false), (7,0, false), (19,0, true))
  | 294 => ((1,1, false), (20,0, false), (26,0, true))
  | 308 => ((1,0, false), (7,0, false), (8,0, true))
  | 313 => ((1,0, false), (29,0, false), (30,0, true))
  | 316 => ((22,0, false), (24,0, false), (26,0, false))
  | 320 => ((46,0, false), (49,0, false), (52,0, false))
  | 329 => ((30,0, true), (33,1, true), (39,0, false))
  | 373 => ((1,0, false), (24,0, false), (26,0, true))
  | 395 => ((28,0, false), (36,1, true), (40,0, true))
  | 402 => ((49,0, false), (52,0, false), (56,0, false))
  | 405 => ((39,0, false), (40,0, false), (41,0, false))
  | 409 => ((2,1, false), (30,0, false), (42,0, true))
  | 425 => ((1,0, true), (27,0, false), (29,0, true))
  | 465 => ((1,0, true), (28,0, false), (30,0, true))
  | 476 => ((1,0, false), (20,0, false), (22,0, true))
  | _ => default

private theorem second001100TriadLaw :
    ∀ k ∈ [69,90,91,105,122,125,128,130,145,146,173,190,191,207,227,234,236,237,251,274,277,279,294,308,313,316,320,329,373,395,402,405,409,425,465,476], k ∈ disjointTriadIndicesLinear ∧
      disjointTriadAtLinear k = second001100Triad k := by
  decide +kernel

private theorem second001100OtherLaw :
    ∀ k ∈ [491,492,493,494,495,496,497,499,501], k ∉ disjointTriadIndicesLinear := by decide +kernel

private theorem second001100CoreFacts :
    ∀ j : Fin 18,
      let c := second001100Cores[j.val]!
      (∀ k ∈ c.1, k < 63 ∧ disjointResidueLinear 3 k = 1) ∧
      (∀ k ∈ c.2.1, k < 63 ∧ disjointResidueLinear 3 k = 2) ∧
      (∀ k ∈ c.2.2.1, k < 63 ∧ disjointResidueLinear 3 k = 0 ∧ disjointSecondDigit 3 k (second001100 j) = 0) ∧
      (∀ k ∈ c.2.2.2.1, k < 63 ∧ disjointResidueLinear 3 k = 0 ∧ disjointSecondDigit 3 k (second001100 j) = 1) ∧
      (∀ k ∈ c.2.2.2.2.1, k < 63 ∧ disjointResidueLinear 3 k = 0 ∧ disjointSecondDigit 3 k (second001100 j) = 2) ∧
      (∀ k ∈ c.2.2.2.2.2.1, k ∈ [69,90,91,105,122,125,128,130,145,146,173,190,191,207,227,234,236,237,251,274,277,279,294,308,313,316,320,329,373,395,402,405,409,425,465,476]) ∧
      (∀ k ∈ c.2.2.2.2.2.2, k ∈ [491,492,493,494,495,496,497,499,501]) := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 32768 in
private theorem second001100Impossible (v m : ℕ → ℤ) (u : ℕ → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (hres : ∀ k, k < 63 → residueFacts (v k) (u k) (disjointResidueLinear 3 k))
    (j : Fin 18) (hs : ∀ k, k < 63 → disjointResidueLinear 3 k = 0 →
      secondResidueFacts (v k) (u k) (disjointSecondDigit 3 k (second001100 j))) : False := by
  let c := second001100Cores[j.val]!
  obtain ⟨ha,hb,hc,hd,he,hf,hg⟩ := second001100CoreFacts j
  have z1 : ∀ k ∈ c.1, v k = 0 ∧ ¬u k := by
    intro k hk
    obtain ⟨b,d⟩ := ha k hk
    simpa [residueFacts,d] using hres k b
  have z2 : ∀ k ∈ c.2.1, v k = 0 ∧ u k := by
    intro k hk
    obtain ⟨b,d⟩ := hb k hk
    simpa [residueFacts,d] using hres k b
  have s0 : ∀ k ∈ c.2.2.1,1 < v k := by
    intro k hk
    obtain ⟨b,d,t⟩ := hc k hk
    simpa [secondResidueFacts,t] using hs k b d
  have s1 : ∀ k ∈ c.2.2.2.1, v k = 1 ∧ ¬u k := by
    intro k hk
    obtain ⟨b,d,t⟩ := hd k hk
    simpa [secondResidueFacts,t] using hs k b d
  have s2 : ∀ k ∈ c.2.2.2.2.1, v k = 1 ∧ u k := by
    intro k hk
    obtain ⟨b,d,t⟩ := he k hk
    simpa [secondResidueFacts,t,show (2 : F) ≠ 0 by decide,show (2 : F) ≠ 1 by decide] using hs k b d
  have tt : ∀ k ∈ c.2.2.2.2.2.1, packedTriad v u (second001100Triad k) := by
    intro k hk
    obtain ⟨isTriad, payload⟩ := second001100TriadLaw k (hf k hk)
    simpa only [disjointRulesLinear, ite_eq_left isTriad, payload] using rules k
  have rr : ∀ k ∈ c.2.2.2.2.2.2, disjointNonTriadRulesLinear v m u k := by
    intro k hk
    simpa only [disjointRulesLinear, ite_eq_right (second001100OtherLaw k (hg k hk))] using rules k
  clear hres rules hs ha hb hc hd he hf hg
  have index := List.mem_range.mpr j.isLt
  change j.val ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17] at index
  simp only [List.mem_cons, List.not_mem_nil, or_false] at index
  rcases index with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals
    simp [c,h,second001100Cores] at z1 z2 s0 s1 s2 tt rr
    try simp only [second001100Triad,packedTriad,packedVal,packedUnit] at tt
    try simp only [disjointNonTriadRulesLinear] at rr
    clear c
    first
    | have _ : j.val = 6 := h
      simp [z1,z2,s1,s2] at tt rr
    | try simp_all
    all_goals
      first
      | omega (config := {splitDisjunctions := false})
      | grind (qlia := true) (ring := false) (ematch := 0) (splits := 35) (liaSteps := 60000)

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234.Triadic.APState
open PEqualNP.Outside.L_gct_234
open scoped Classical

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 32768 in
private theorem first001100_middle_high (v m : ℕ → ℤ) (u : ℕ → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (hres : ∀ k, k < 63 → residueFacts (v k) (u k) (disjointResidueLinear 3 k)) :
    1 < v 49 ∧ 1 < v 52 := by
  have zp : ∀ k ∈ [3,4,5,11,12,13,14,15,16,17,18,31,32,33,34,35,36,37,38,44,45,47,48,50,51,53,54,57,58,59,60],
      k < 63 ∧ disjointResidueLinear 3 k ≠ 0 := by decide +kernel
  have pp : ∀ k ∈ [0,6,7,8,9,10,20,22,24,26,27,28,29,30,39,40,41,42,43,46,49,52,55,56,61,62],
      k < 63 ∧ disjointResidueLinear 3 k = 0 := by decide +kernel
  have z : ∀ k ∈ [3,4,5,11,12,13,14,15,16,17,18,31,32,33,34,35,36,37,38,44,45,47,48,50,51,53,54,57,58,59,60],
      v k = 0 := by
    intro k hk
    obtain ⟨bound, digit⟩ := zp k hk
    have h := hres k bound
    rw [residueFacts, ite_eq_right digit] at h
    exact h.1
  have p : ∀ k ∈ [0,6,7,8,9,10,20,22,24,26,27,28,29,30,39,40,41,42,43,46,49,52,55,56,61,62],
      0 < v k := by
    intro k hk
    obtain ⟨bound, digit⟩ := pp k hk
    simpa [residueFacts,digit] using hres k bound
  have tr : ∀ k ∈ [115,302,320,402,429], packedTriad v u (disjointTriadAtLinear k) := by
    intro k hk
    have member : ∀ j ∈ [115,302,320,402,429], j ∈ disjointTriadIndicesLinear := by decide +kernel
    simpa only [disjointRulesLinear, ite_eq_left (member k hk)] using rules k
  have rr : ∀ k ∈ [491,493,495,497], disjointNonTriadRulesLinear v m u k := by
    intro k hk
    have notMember : ∀ j ∈ [491,493,495,497], j ∉ disjointTriadIndicesLinear := by decide +kernel
    simpa only [disjointRulesLinear, ite_eq_right (notMember k hk)] using rules k
  clear hres rules zp pp
  simp only [List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true] at p z tr rr
  obtain ⟨z3,z4,z5,z11,z12,z13,z14,z15,z16,z17,z18,z31,z32,z33,z34,z35,z36,z37,z38,z44,z45,
    z47,z48,z50,z51,z53,z54,z57,z58,z59,z60⟩ := z
  obtain ⟨r115,r302,r320,r402,r429⟩ := tr
  change packedTriad v u ((0,0,false),(55,0,false),(56,0,true)) at r115
  change packedTriad v u ((0,0,false),(4,1,true),(6,0,false)) at r302
  change packedTriad v u ((46,0,false),(49,0,false),(52,0,false)) at r320
  change packedTriad v u ((49,0,false),(52,0,false),(56,0,false)) at r402
  change packedTriad v u ((6,0,false),(46,0,false),(61,0,true)) at r429
  simp [packedTriad, packedVal, packedUnit,z4] at r115 r302 r320 r402 r429
  simp [disjointNonTriadRulesLinear,z3,z5,z11,z12,z13,z14,z15,z16,z17,z18,z31,z32,z33,z34,z35,z36,
    z37,z38,z44,z45,z47,z48,z50,z51,z53,z54,z57,z58,z59,z60] at rr
  obtain ⟨g491,g493,g495,g497⟩ := rr
  have rootStart (mid : v 52 = 1) : 1 < v 0 ∧ 1 < v 55 :=
    ⟨by omega (config := {splitDisjunctions := false}), by omega (config := {splitDisjunctions := false})⟩
  have rootEnd (mid : v 49 = 1) : 1 < v 6 ∧ 1 < v 61 :=
    ⟨by omega (config := {splitDisjunctions := false}), by omega (config := {splitDisjunctions := false})⟩
  have cases (z : ℤ) (pos : 0 < z) : z = 1 ∨ 1 < z := by omega
  have middleCases := And.intro (cases (v 52) (by omega (config := {splitDisjunctions := false})))
    (cases (v 49) (by omega (config := {splitDisjunctions := false})))
  rcases middleCases with ⟨midA|midA, midB|midB⟩
  · obtain ⟨p0,_⟩ := rootStart midA
    obtain ⟨p6,_⟩ := rootEnd midB
    rcases r302 with h | h | h | h <;> omega (config := {splitDisjunctions := false})
  · obtain ⟨p0,p55⟩ := rootStart midA
    have p56 : 1 < v 56 := by
      rcases r115 with h | h | h | h <;> omega (config := {splitDisjunctions := false})
    rcases r402 with h | h | h | h <;> omega (config := {splitDisjunctions := false})
  · obtain ⟨p6,p61⟩ := rootEnd midB
    have p46 : 1 < v 46 := by
      rcases r429 with h | h | h | h <;> omega (config := {splitDisjunctions := false})
    rcases r320 with h | h | h | h <;> omega (config := {splitDisjunctions := false})
  · exact ⟨midB,midA⟩

theorem disjointImpossibleLinear001100 (v m : ℕ → ℤ) (u : ℕ → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (hres : ∀ k, k < 63 → residueFacts (v k) (u k) (disjointResidueLinear 3 k))
    (e : Fin 5 → F)
    (hs : ∀ k, k < 63 → disjointResidueLinear 3 k = 0 →
      secondResidueFacts (v k) (u k) (disjointSecondDigit 3 k e)) : False := by
  obtain ⟨midB,midA⟩ := first001100_middle_high v m u rules hres
  have middleZero (k : ℕ) (small : k < 63) (res : disjointResidueLinear 3 k = 0)
      (high : 1 < v k) : disjointSecondDigit 3 k e = 0 := by
    by_contra hn
    have fact := hs k small res
    rw [secondResidueFacts, ite_eq_right hn] at fact
    omega
  have dormantPos : ¬u 1 := by
    have h := rules 66
    have hn : 66 ∉ disjointTriadIndicesLinear := by decide
    simpa only [disjointRulesLinear, ite_eq_right hn, disjointNonTriadRulesLinear] using h
  have dormantDigit : disjointSecondDigit 3 1 e ≠ 2 := by
    intro hz
    have fact := hs 1 (by decide) (by decide)
    rw [hz] at fact
    have valAndUnit : v 1 = 1 ∧ u 1 := by
      simpa [secondResidueFacts, show (2 : F) ≠ 0 by decide, show (2 : F) ≠ 1 by decide] using fact
    exact dormantPos valAndUnit.2
  obtain ⟨j, rfl⟩ := second001100Cover e (middleZero 49 (by decide) (by decide) midB)
    (middleZero 52 (by decide) (by decide) midA) dormantDigit
  exact second001100Impossible v m u rules hres j hs

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

def nextDigit (n pos : ℕ) : ℤ := ((n / 3^pos % 3 : ℕ) : ℤ)

def liftResidueRow (d : DisjointRow) (n : ℕ) : DisjointRow :=
  (d.1, d.2.1 + 3*nextDigit n 4, d.2.2.1 + 3*nextDigit n 3, d.2.2.2.1,
    d.2.2.2.2.1 + 3*nextDigit n 2, d.2.2.2.2.2.1 + 3*nextDigit n 1,
    d.2.2.2.2.2.2 + 3*nextDigit n 0)

def liftedResidue (d : DisjointRow) (n k : ℕ) : ℤ :=
  disjointDot disjointFormsLinear[k]! (liftResidueRow d n) % 9

def liftedOrder (r : ℤ) : ℤ := if r % 3 = 0 then 1 else 0

def liftedNegative (r : ℤ) : Prop := (if r % 3 = 0 then r/3 else r % 3) = 2

def liftedFacts (v : ℤ) (u : Prop) (r : ℤ) : Prop :=
  if r = 0 then 1 < v else v = liftedOrder r ∧ (u ↔ liftedNegative r)

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234
open scoped Classical

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def trits (n : Nat) : Fin 5 → F := fun i => (nextDigit n (4-i.val) : F)

theorem trits_exhaustive (e : Fin 5 → F) : ∃ n < 243, trits n = e := by
  let p := (e 0).val
  let q := (e 1).val
  let r := (e 2).val
  let s := (e 3).val
  let t := (e 4).val
  have hp : p < 3 := ZMod.val_lt _
  have hq : q < 3 := ZMod.val_lt _
  have hr : r < 3 := ZMod.val_lt _
  have hs : s < 3 := ZMod.val_lt _
  have ht : t < 3 := ZMod.val_lt _
  let w := 81*p+27*q+9*r+3*s+t
  have someP : w/81 % 3 = p := by dsimp [w]; omega
  have someQ : w/27 % 3 = q := by dsimp [w]; omega
  have someR : w/9 % 3 = r := by dsimp [w]; omega
  have someS : w/3 % 3 = s := by dsimp [w]; omega
  have someT : w % 3 = t := by dsimp [w]; omega
  refine ⟨w, by dsimp [w]; omega, ?_⟩
  funext i
  fin_cases i
  · change ((↑(w/81 % 3 : Nat) : ℤ) : F) = e 0
    rw [someP,Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  · change ((↑(w/27 % 3 : Nat) : ℤ) : F) = e 1
    rw [someQ,Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  · change ((↑(w/9 % 3 : Nat) : ℤ) : F) = e 2
    rw [someR,Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  · change ((↑(w/3 % 3 : Nat) : ℤ) : F) = e 3
    rw [someS,Int.cast_natCast]
    exact ZMod.natCast_zmod_val _
  · change ((↑(w/1 % 3 : Nat) : ℤ) : F) = e 4
    rw [Nat.div_one,someT,Int.cast_natCast]
    exact ZMod.natCast_zmod_val _

def secondVector (n : Nat) : DisjointRow :=
  (0,nextDigit n 4,nextDigit n 3,0,nextDigit n 2,nextDigit n 1,nextDigit n 0)

theorem disjointDot_lift (f r : DisjointRow) (n : Nat) :
    disjointDot f (liftResidueRow r n) = disjointDot f r + 3*disjointDot f (secondVector n) := by
  simp [disjointDot,liftResidueRow,secondVector]
  ring

theorem lifted_first_digit (a n k : Nat) :
    liftedResidue disjointResiduesLinear[a]! n k % 3 = disjointResidueLinear a k := by
  unfold liftedResidue disjointResidueLinear
  rw [disjointDot_lift]
  omega

private theorem lifted_second_digit (a n k : Nat) (hfirst : disjointResidueLinear a k = 0) :
    ((liftedResidue disjointResiduesLinear[a]! n k / 3 : ℤ) : F) = disjointSecondDigit a k (trits n) := by
  let f := disjointFormsLinear[k]!
  let c := disjointResiduesLinear[a]!
  have h₁ : disjointDot f c % 3 = 0 := hfirst
  have h₂ : (liftedResidue c n k / 3) = (disjointDot f c / 3+disjointDot f (secondVector n)) % 3 := by
    unfold liftedResidue
    rw [show disjointFormsLinear[k]! = f from rfl,disjointDot_lift]
    omega
  unfold disjointSecondDigit
  change ((liftedResidue c n k / 3 : ℤ) : F) = _
  let u := disjointDot f c / 3 + disjointDot f (secondVector n)
  have cast : ((u % 3 : ℤ) : F) = (u : F) := ZMod.intCast_mod u 3
  rw [h₂, cast]
  dsimp only [u]
  rw [Int.cast_add]
  congr 1
  simp [f,disjointDot,formEval,Fin.sum_univ_succ,rowForm,secondVector,trits] <;> ring

private theorem liftedFacts_from_digits (v : ℤ) (u : Prop) (d : ℤ)
    (d0 : 0 ≤ d) (d9 : d < 9)
    (h1 : residueFacts v u (d % 3))
    (h2 : d % 3 = 0 → secondResidueFacts v u ((d/3 : ℤ) : F)) :
    liftedFacts v u d := by
  interval_cases d <;>
    first
    | have h := h2 (by decide)
      norm_num [liftedFacts,liftedOrder,liftedNegative,secondResidueFacts,
        show (2 : F) ≠ 0 by decide,show (2 : F) ≠ 1 by decide] at h ⊢
      exact h
    | simpa [liftedFacts,liftedOrder,liftedNegative,residueFacts] using h1

theorem lifted_facts_from_state {A : APState} (D : PrimitiveCoordinates A) (r : O)
    (a : Fin 39) (same : disjointDigits disjointResiduesLinear[a.val]! = PadicInt.toZMod ∘ D.vars r)
    (pivot : rowForm disjointResiduesLinear[a.val]! 3 = 1)
    (startZero : rowForm disjointResiduesLinear[a.val]! 0 = 0)
    (nz : ∀ k < disjointFormsLinear.size, formValue disjointFormsLinear (A.fieldVars r) k ≠ 0) :
    let value := formValue disjointFormsLinear (A.fieldVars r)
    ∃ n < 243, ∀ k < disjointFormsLinear.size,
      liftedFacts (val (value k)) (Negative (value k)) (liftedResidue disjointResiduesLinear[a.val]! n k) := by
  obtain ⟨e, order⟩ := disjoint_second_residue_facts D r a same pivot startZero nz
  obtain ⟨n, hn, rn⟩ := trits_exhaustive e
  refine ⟨n, hn, ?_⟩
  intro k hk
  have first := disjoint_linear_residue_facts D r a _ same (fun _ _ => rfl) nz k hk
  have h := lifted_first_digit a.val n k
  let d := liftedResidue disjointResiduesLinear[a.val]! n k
  have dn : 0 ≤ d := Int.emod_nonneg _ (by decide)
  have dl : d < 9 := Int.emod_lt_of_pos _ (by decide)
  apply liftedFacts_from_digits _ _ d dn dl
  · rw [h]
    exact first
  · intro r₀
    have e₀ : disjointResidueLinear a.val k = 0 := h.symm.trans r₀
    rw [lifted_second_digit a.val n k e₀,rn]
    exact order k hk e₀

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234

def liftedConstResidue (a n k : Nat) : Int :=
  let d := disjointResiduesConst[a]!
  disjointDot disjointFormsConst[k]!
    (d.1, d.2.1 + 3*nextDigit n 3, d.2.2.1 + 3*nextDigit n 2, d.2.2.2.1,
      d.2.2.2.2.1 + 3*nextDigit n 1, d.2.2.2.2.2.1 + 3*nextDigit n 0, d.2.2.2.2.2.2) % 9

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def constTrits (n : Nat) : Fin 5 → F :=
  ![(nextDigit n 3 : F), (nextDigit n 2 : F), (nextDigit n 1 : F), (nextDigit n 0 : F),0]

private def dropPoleTrit (e : Fin 5 → F) : Fin 5 → F := ![e 0, e 1, e 2, e 3,0]

private theorem constTrits_exhaustive (e : Fin 5 → F) :
    ∃ n < 81, constTrits n = dropPoleTrit e := by
  obtain ⟨w, bound, eq⟩ := trits_exhaustive e
  refine ⟨w/3, by omega, ?_⟩
  have shift (p : ℕ) : nextDigit (w/3) p = nextDigit w (p+1) := by
    unfold nextDigit
    rw [Nat.div_div_eq_div_mul, pow_succ']
  funext i
  fin_cases i
  · change (nextDigit (w/3) 3 : F) = e 0
    rw [shift]
    exact congrFun eq 0
  · change (nextDigit (w/3) 2 : F) = e 1
    rw [shift]
    exact congrFun eq 1
  · change (nextDigit (w/3) 1 : F) = e 2
    rw [shift]
    exact congrFun eq 2
  · change (nextDigit (w/3) 0 : F) = e 3
    rw [shift]
    exact congrFun eq 3
  · rfl

private theorem constForm_pole_zero :
    ∀ k : Fin 51, (disjointFormsConst[k.val]!).2.2.2.2.2.2 = 0 := by decide +kernel

private theorem constSecondDigit_drop (a k : Nat) (hk : k < 51) (e : Fin 5 → F) :
    constSecondDigit a k (dropPoleTrit e) = constSecondDigit a k e := by
  simp [constSecondDigit,rowSecondDigit,dropPoleTrit,formEval,Fin.sum_univ_succ,
    rowForm,constForm_pole_zero ⟨k,hk⟩]

private def constSecondVector (n : Nat) : DisjointRow :=
  (0,nextDigit n 3,nextDigit n 2,0,nextDigit n 1,nextDigit n 0,0)

private theorem constLift_eq (a n k : Nat) :
    liftedConstResidue a n k = (disjointDot disjointFormsConst[k]! disjointResiduesConst[a]! +
      3*disjointDot disjointFormsConst[k]! (constSecondVector n)) % 9 := by
  unfold liftedConstResidue
  dsimp only
  congr 1
  simp [disjointDot,constSecondVector]
  ring

private theorem constLift_first (a n k : Nat) :
    liftedConstResidue a n k % 3 = disjointResidueConst a k := by
  rw [constLift_eq]
  unfold disjointResidueConst
  omega

private theorem constLift_second (a n k : Nat)
    (h : disjointResidueConst a k = 0) :
    ((liftedConstResidue a n k / 3 : Int) : F) = constSecondDigit a k (constTrits n) := by
  let c := disjointResiduesConst[a]!
  let f := disjointFormsConst[k]!
  have hd : disjointDot f c % 3 = 0 := h
  have split : liftedConstResidue a n k / 3 =
      (disjointDot f c / 3 + disjointDot f (constSecondVector n)) % 3 := by
    rw [constLift_eq]
    change (disjointDot f c + 3*disjointDot f (constSecondVector n)) % 9 / 3 = _
    omega
  let u := disjointDot f c / 3 + disjointDot f (constSecondVector n)
  have modCast : ((u % 3 : ℤ) : F) = (u : F) := ZMod.intCast_mod u 3
  rw [split, show (((disjointDot f c / 3 + disjointDot f (constSecondVector n)) % 3 : ℤ) : F) =
    (disjointDot f c / 3 + disjointDot f (constSecondVector n) : ℤ) from modCast, Int.cast_add]
  unfold constSecondDigit rowSecondDigit
  change ((disjointDot f c / 3 : ℤ) : F) + _ = ((disjointDot f c / 3 : ℤ) : F) + _
  congr 1
  simp [disjointDot,constSecondVector,constTrits,formEval,Fin.sum_univ_succ,rowForm] <;> ring

theorem lifted_const_facts_from_state {A : APState} (D : PrimitiveCoordinates A)
    (a : Fin 13)
    (same : disjointDigits disjointResiduesConst[a.val]! = PadicInt.toZMod ∘ D.vars 0)
    (pivot : rowForm disjointResiduesConst[a.val]! 3 = 1)
    (startZero : rowForm disjointResiduesConst[a.val]! 0 = 0)
    (nz : ∀ k < disjointFormsConst.size, formValue disjointFormsConst (A.fieldVars 0) k ≠ 0) :
    let x := formValue disjointFormsConst (A.fieldVars 0)
    ∃ n < 81, ∀ k < disjointFormsConst.size,
      liftedFacts (val (x k)) (Negative (x k)) (liftedConstResidue a.val n k) := by
  obtain ⟨e, orders⟩ := const_second_residue_facts D a same pivot startZero nz
  obtain ⟨n, bound, digit⟩ := constTrits_exhaustive e
  refine ⟨n,bound,?_⟩
  intro k hk
  have first := disjoint_const_residue_facts D a _ same (fun _ _ => rfl) nz k hk
  have h := constLift_first a.val n k
  let d := liftedConstResidue a.val n k
  have dn : 0 ≤ d := Int.emod_nonneg _ (by decide)
  have dl : d < 9 := Int.emod_lt_of_pos _ (by decide)
  apply liftedFacts_from_digits _ _ d dn dl
  · rw [h]
    exact first
  · intro pr
    have base : disjointResidueConst a.val k = 0 := h.symm.trans pr
    rw [constLift_second a.val n k base,digit,constSecondDigit_drop a.val k hk e]
    exact orders k hk base

theorem lifted_const_row2_from_state {A : APState} (D : PrimitiveCoordinates A)
    (same : disjointDigits disjointResiduesConst[2]! = PadicInt.toZMod ∘ D.vars 0)
    (nz : ∀ k < disjointFormsConst.size, formValue disjointFormsConst (A.fieldVars 0) k ≠ 0) :
    let x := formValue disjointFormsConst (A.fieldVars 0)
    ∃ n < 81, ∀ k < disjointFormsConst.size,
      liftedFacts (val (x k)) (Negative (x k)) (liftedConstResidue 2 n k) :=
  lifted_const_facts_from_state D ⟨2,by decide⟩ same rfl rfl nz

end PEqualNP.Outside.L_gct_234.Triadic.APState

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

private def constRow2Digits : Array Int := #[1,1,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0]
private def constRow2Zeros : List Nat := [3,6,9,12,15,18,19,22,25,28,31,34,35,38,41,44,47,50]
private def constRow2Boxes : Array (List Nat × List Nat) := #[([409],[12,25]), ([411],[9,28]), ([405],[25,44]), ([401],[12,44]), ([403],[9,41]), ([407],[28,41]), ([210,403,407,411],[3,18,19,34,35,50])]
private def constRow2Choices : Array Nat := #[6,0,0,2,3,0,2,0,3,0,0,1,1,0,2,0,3,1,0,1,0,0,1,3,1,2,0,2,1,0,2,0,1,5,0,0,3,0,1,0,3,1,0,0,4,0,2,3,1,1,0,0,1,0,2,0,1,5,0,0,2,1,0,0,3,2,0,0,1,1,0,1,3,1,0,0,4,0,0,1,3]

private def constRow2Order (ones : List Nat) (v : Nat → Int) (k : Nat) : Int :=
  if k < 51 ∧ constRow2Digits[k]! ≠ 0 then 0 else if k ∈ ones then 1 else v k

private def constRow2Unit (u : Nat → Prop) (k : Nat) : Prop :=
  if k < 51 ∧ constRow2Digits[k]! ≠ 0 then constRow2Digits[k]! = 2 else u k

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem constRow2DataValid :
    ((List.range 51).all (fun k => decide (constRow2Digits[k]! = disjointResidueConst 2 k)) &&
      constRow2Zeros.all (fun k => decide (k < 51 ∧ disjointResidueConst 2 k = 0)) &&
      (List.range 81).all (fun n =>
        let i := constRow2Choices[n]!
        decide (i < constRow2Boxes.size) &&
          constRow2Boxes[i]!.2.all (fun k => decide (k < 51 ∧
            (liftedConstResidue 2 n k = 3 ∨ liftedConstResidue 2 n k = 6))))) = true := by
  decide +kernel

set_option maxRecDepth 24000 in
set_option maxHeartbeats 0 in
private theorem constRow2Arithmetic (v m : Nat → Int) (u : Nat → Prop)
    (i : Nat) (hi : i < constRow2Boxes.size)
    (hr : ∀ k ∈ constRow2Boxes[i]!.1,
      disjointRulesConst (constRow2Order constRow2Boxes[i]!.2 v) m (constRow2Unit u) k)
    (hz : ∀ k ∈ constRow2Zeros,0 < v k) : False := by
  have ip := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6] at ip
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ip
  rcases ip with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [constRow2Boxes,constRow2Zeros,List.forall_mem_cons] at hr hz
    simp [disjointRulesConst,disjointNonTriadRulesConst,disjointTriadIndicesConst,disjointTriadAtConst,
      disjointCoeffTriadAtConst,disjointEncodedCoeffTriadsConst,packCoeffTriad,packCoeffTerm,
      coeffOrder,coeffUnit,packedTriad,packedVal,packedUnit,constRow2Order,constRow2Unit,
      constRow2Digits,constRow2Boxes] at hr
    all_goals first
    | omega (splitDisjunctions := false)
    | grind (qlia := true) (ring := false) (ematch := 0) (splits := 25) (liaSteps := 18000)

theorem disjointConstRow2Impossible (v m : Nat → Int) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesConst v m u k)
    (first : ∀ k < 51, residueFacts (v k) (u k) (disjointResidueConst 2 k))
    (n : Nat) (hn : n < 81)
    (actual : ∀ k < 51, liftedFacts (v k) (u k) (liftedConstResidue 2 n k)) : False := by
  obtain ⟨left, coverage⟩ := Bool.and_eq_true_iff.mp constRow2DataValid
  obtain ⟨known, zeros⟩ := Bool.and_eq_true_iff.mp left
  let i := constRow2Choices[n]!
  obtain ⟨hi, fits⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp coverage n (List.mem_range.mpr hn))
  have dh (k : Nat) (bound : k < 51) : constRow2Digits[k]! = disjointResidueConst 2 k :=
    of_decide_eq_true (List.all_eq_true.mp known k (List.mem_range.mpr bound))
  have firstValue (k : Nat) (d : k < 51 ∧ constRow2Digits[k]! ≠ 0) :
      v k = 0 ∧ (u k ↔ constRow2Digits[k]! = 2) := by
    have firstK := first k d.1
    rw [← dh k d.1] at firstK
    have bound : 0 ≤ constRow2Digits[k]! ∧ constRow2Digits[k]! < 3 := by
      rw [dh k d.1]
      unfold disjointResidueConst
      exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
    have e : constRow2Digits[k]! = 1 ∨ constRow2Digits[k]! = 2 := by omega
    rcases e with e | e
    · simpa [residueFacts,e] using firstK
    · simpa [residueFacts,e] using firstK
  have orderEq : constRow2Order constRow2Boxes[i]!.2 v = v := by
    funext k
    by_cases d : k < 51 ∧ constRow2Digits[k]! ≠ 0
    · simp [constRow2Order,d,(firstValue k d).1]
    · by_cases h : k ∈ constRow2Boxes[i]!.2
      · obtain ⟨hk,e|e⟩ := of_decide_eq_true (List.all_eq_true.mp fits k h)
        · have h' : v k = 1 ∧ ¬u k := by
            simpa [liftedFacts,liftedOrder,liftedNegative,e] using actual k hk
          simp [constRow2Order,d,h,h'.1]
        · have h' : v k = 1 ∧ u k := by
            simpa [liftedFacts,liftedOrder,liftedNegative,e] using actual k hk
          simp [constRow2Order,d,h,h'.1]
      · simp [constRow2Order,d,h]
  have signEq : constRow2Unit u = u := by
    funext k
    apply propext
    by_cases d : k < 51 ∧ constRow2Digits[k]! ≠ 0
    · simpa [constRow2Unit,d] using (firstValue k d).2.symm
    · simp [constRow2Unit,d]
  apply constRow2Arithmetic v m u i (of_decide_eq_true hi) ?_ ?_
  · intro k _
    rw [orderEq, signEq]
    exact rules k
  · intro k hk
    obtain ⟨bound, z⟩ := of_decide_eq_true (List.all_eq_true.mp zeros k hk)
    simpa [residueFacts,z] using first k bound

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234

open scoped Classical

structure DigitBox where
  rules : List Nat
  ones : List Nat
  bigger : List Nat
  positiveUnits : List Nat
  negativeUnits : List Nat
  deriving Inhabited

def DigitBox.fits (c : DigitBox) (a n : Nat) : Bool :=
  let d := liftedResidue disjointResiduesLinear[a]! n
  c.ones.all (fun k => decide (k < 63 ∧ (d k = 3 ∨ d k = 6))) &&
  c.bigger.all (fun k => decide (k < 63 ∧ d k = 0)) &&
  c.positiveUnits.all (fun k => decide (k < 63 ∧ d k = 3)) &&
  c.negativeUnits.all (fun k => decide (k < 63 ∧ d k = 6))

def DigitBox.order (c : DigitBox) (digits : Nat → ℤ) (v : Nat → ℤ) (k : Nat) : ℤ :=
  if k < 63 ∧ digits k ≠ 0 then 0
  else if k ∈ c.ones then 1 else v k

def DigitBox.sign (c : DigitBox) (digits : Nat → ℤ) (u : Nat → Prop) (k : Nat) : Prop :=
  if k < 63 ∧ digits k ≠ 0 then digits k = 2
  else if k ∈ c.positiveUnits then False else if k ∈ c.negativeUnits then True else u k

theorem DigitBox.reflect (c : DigitBox) (a n : Nat) (fits : c.fits a n = true)
    (v : Nat → ℤ) (u : Nat → Prop) (digits : Nat → ℤ)
    (matchDigits : ∀ k < 63, digits k = disjointResidueLinear a k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear a k))
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[a]! n k)) :
    c.order digits v = v ∧ c.sign digits u = u ∧ (∀ k ∈ c.bigger,1 < v k) := by
  simp only [DigitBox.fits, Bool.and_eq_true_iff] at fits
  obtain ⟨⟨⟨ones,bigger⟩,positiveUnits⟩,negativeUnits⟩ := fits
  have order1 : ∀ k ∈ c.ones, v k = 1 := by
    intro k kc
    obtain ⟨hk,e|e⟩ := of_decide_eq_true (List.all_eq_true.mp ones k kc)
    · have h : v k = 1 ∧ ¬u k := by
        simpa [liftedFacts,liftedOrder,liftedNegative,e] using actual k hk
      exact h.1
    · have h : v k = 1 ∧ u k := by
        simpa [liftedFacts,liftedOrder,liftedNegative,e] using actual k hk
      exact h.1
  have plus : ∀ k ∈ c.positiveUnits, ¬u k := by
    intro k kc
    have ⟨hk,e⟩ := of_decide_eq_true (List.all_eq_true.mp positiveUnits k kc)
    have h : v k = 1 ∧ ¬u k := by
      simpa [liftedFacts,liftedOrder,liftedNegative,e] using actual k hk
    exact h.2
  have minus : ∀ k ∈ c.negativeUnits, u k := by
    intro k kc
    have ⟨hk,e⟩ := of_decide_eq_true (List.all_eq_true.mp negativeUnits k kc)
    have h : v k = 1 ∧ u k := by
      simpa [liftedFacts,liftedOrder,liftedNegative,e] using actual k hk
    exact h.2
  have firstValue (k : Nat) (d : k < 63 ∧ digits k ≠ 0) :
      v k = 0 ∧ (u k ↔ digits k = 2) := by
    have h := first k d.1
    have ne : disjointResidueLinear a k ≠ 0 := matchDigits k d.1 ▸ d.2
    simp only [residueFacts, ite_eq_right ne] at h
    rw [matchDigits k d.1]
    have lim : 0 ≤ disjointResidueLinear a k ∧ disjointResidueLinear a k < 3 := by
      unfold disjointResidueLinear
      exact ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
    have case : disjointResidueLinear a k = 1 ∨ disjointResidueLinear a k = 2 := by omega
    rcases case with e|e
    · simpa [e] using h
    · simpa [e] using h
  refine ⟨?_,?_,?_⟩
  · funext k
    by_cases q : k < 63 ∧ digits k ≠ 0
    · simp [DigitBox.order,q,(firstValue k q).1]
    · by_cases t : k ∈ c.ones
      · simp [DigitBox.order,q,t,order1 k t]
      · simp [DigitBox.order,q,t]
  · funext k
    apply propext
    by_cases q : k < 63 ∧ digits k ≠ 0
    · simpa [DigitBox.sign,q] using (firstValue k q).2.symm
    · by_cases p : k ∈ c.positiveUnits
      · simp [DigitBox.sign,q,p,plus k p]
      · by_cases m : k ∈ c.negativeUnits
        · simp [DigitBox.sign,q,p,m,minus k m]
        · simp [DigitBox.sign,q,p,m]
  · intro k kc
    have ⟨hk,e⟩ := of_decide_eq_true (List.all_eq_true.mp bigger k kc)
    simpa [liftedFacts,e] using actual k hk

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxedRuleIds : List Nat := [66,72,79,96,97,98,114,119,130,132,134,142,144,162,165,169,205,218,225,234,235,248,250,256,257,258,259,271,272,279,280,281,316,317,320,359,361,372,376,377,402,411,415,429,444,446,448,450,471,480,485,491,492,493,494,495,496,497,498,499,500,501,502,525,535]

noncomputable def boxedRule (v m : Nat → ℤ) (u : Nat → Prop) : Nat → Prop

  | 72 => packedTriad v u (packCoeffTriad ((1,2), (19,1), (23, -1)))

  | 79 => packedTriad v u (packCoeffTriad ((23,1), (40,1), (61, -1)))

  | 96 => packedTriad v u (packCoeffTriad ((15,1), (16, -2), (17,1)))

  | 97 => packedTriad v u (packCoeffTriad ((18,1), (31,1), (52, -1)))

  | 98 => packedTriad v u (packCoeffTriad ((14,1), (31,1), (48, -1)))

  | 114 => packedTriad v u (packCoeffTriad ((46,1), (52, -3), (56,2)))

  | 119 => packedTriad v u (packCoeffTriad ((1,1), (33,1), (34, -1)))

  | 130 => packedTriad v u (packCoeffTriad ((0,1), (21,1), (22, -1)))

  | 132 => packedTriad v u (packCoeffTriad ((5,1), (48,1), (57, -1)))

  | 134 => packedTriad v u (packCoeffTriad ((16,1), (33,1), (52, -1)))

  | 142 => packedTriad v u (packCoeffTriad ((19,1), (34,1), (57, -1)))

  | 144 => packedTriad v u (packCoeffTriad ((12,1), (37,1), (49, -1)))

  | 162 => packedTriad v u (packCoeffTriad ((5,1), (14,1), (25, -1)))

  | 165 => packedTriad v u (packCoeffTriad ((15,1), (34,1), (52, -1)))

  | 169 => packedTriad v u (packCoeffTriad ((8,1), (37,1), (45, -1)))

  | 205 => packedTriad v u (packCoeffTriad ((30,1), (36, -3), (39,2)))

  | 218 => packedTriad v u (packCoeffTriad ((3,1), (16,1), (21, -1)))

  | 225 => packedTriad v u (packCoeffTriad ((31,1), (32, -2), (33,1)))

  | 234 => packedTriad v u (packCoeffTriad ((6,1), (8,1), (21, -1)))

  | 235 => packedTriad v u (packCoeffTriad ((16,1), (17, -2), (18,1)))

  | 248 => packedTriad v u (packCoeffTriad ((23,1), (28,1), (55, -1)))

  | 250 => packedTriad v u (packCoeffTriad ((3,1), (54,1), (61, -1)))

  | 256 => packedTriad v u (packCoeffTriad ((33,1), (36, -2), (39,1)))

  | 257 => packedTriad v u (packCoeffTriad ((19,1), (38,1), (59, -1)))

  | 258 => packedTriad v u (packCoeffTriad ((21,1), (33,1), (57, -1)))

  | 259 => packedTriad v u (packCoeffTriad ((9,1), (12, -2), (15,1)))

  | 271 => packedTriad v u (packCoeffTriad ((3,1), (51,1), (55, -1)))

  | 272 => packedTriad v u (packCoeffTriad ((45,1), (48, -2), (51,1)))

  | 279 => packedTriad v u (packCoeffTriad ((6,1), (7,1), (19, -1)))

  | 280 => packedTriad v u (packCoeffTriad ((5,1), (11,1), (19, -1)))

  | 281 => packedTriad v u (packCoeffTriad ((0,1), (59,1), (60, -1)))

  | 316 => packedTriad v u (packCoeffTriad ((22,1), (24, -2), (26,1)))

  | 317 => packedTriad v u (packCoeffTriad ((23,1), (32,1), (57, -1)))

  | 320 => packedTriad v u (packCoeffTriad ((46,1), (49, -2), (52,1)))

  | 359 => packedTriad v u (packCoeffTriad ((6,1), (43,1), (55, -1)))

  | 361 => packedTriad v u (packCoeffTriad ((6,1), (9,1), (23, -1)))

  | 372 => packedTriad v u (packCoeffTriad ((34,1), (37, -2), (40,1)))

  | 376 => packedTriad v u (packCoeffTriad ((14,1), (17, -2), (22,1)))

  | 377 => packedTriad v u (packCoeffTriad ((22,1), (37,1), (60, -1)))

  | 402 => packedTriad v u (packCoeffTriad ((49,1), (52, -2), (56,1)))

  | 411 => packedTriad v u (packCoeffTriad ((0,1), (61,1), (62, -1)))

  | 415 => packedTriad v u (packCoeffTriad ((25,1), (31,1), (57, -1)))

  | 429 => packedTriad v u (packCoeffTriad ((6,1), (46,1), (61, -1)))

  | 444 => packedTriad v u (packCoeffTriad ((5,1), (49,1), (59, -1)))

  | 446 => packedTriad v u (packCoeffTriad ((1,1), (19,1), (21, -1)))

  | 448 => packedTriad v u (packCoeffTriad ((17,1), (40,1), (54, -1)))

  | 450 => packedTriad v u (packCoeffTriad ((3,1), (52,1), (57, -1)))

  | 471 => packedTriad v u (packCoeffTriad ((20,1), (22, -2), (24,1)))

  | 480 => packedTriad v u (packCoeffTriad ((3,1), (15,1), (19, -1)))

  | 485 => packedTriad v u (packCoeffTriad ((3,1), (17,1), (23, -1)))

  | j => disjointNonTriadRulesLinear v m u j

set_option maxRecDepth 32768 in
private theorem boxedRule_eq (v m : Nat → ℤ) (u : Nat → Prop) (k : Nat)
    (member : k ∈ boxedRuleIds) :
    boxedRule v m u k = disjointRulesLinear v m u k := by
  rcases (show k = 66 ∨ k = 72 ∨ k = 79 ∨ k = 96 ∨ k = 97 ∨ k = 98 ∨ k = 114 ∨ k = 119 ∨ k = 130 ∨ k = 132 ∨ k = 134 ∨ k = 142 ∨ k = 144 ∨ k = 162 ∨ k = 165 ∨ k = 169 ∨ k = 205 ∨ k = 218 ∨ k = 225 ∨ k = 234 ∨ k = 235 ∨ k = 248 ∨ k = 250 ∨ k = 256 ∨ k = 257 ∨ k = 258 ∨ k = 259 ∨ k = 271 ∨ k = 272 ∨ k = 279 ∨ k = 280 ∨ k = 281 ∨ k = 316 ∨ k = 317 ∨ k = 320 ∨ k = 359 ∨ k = 361 ∨ k = 372 ∨ k = 376 ∨ k = 377 ∨ k = 402 ∨ k = 411 ∨ k = 415 ∨ k = 429 ∨ k = 444 ∨ k = 446 ∨ k = 448 ∨ k = 450 ∨ k = 471 ∨ k = 480 ∨ k = 485 ∨ k = 491 ∨ k = 492 ∨ k = 493 ∨ k = 494 ∨ k = 495 ∨ k = 496 ∨ k = 497 ∨ k = 498 ∨ k = 499 ∨ k = 500 ∨ k = 501 ∨ k = 502 ∨ k = 525 ∨ k = 535 from by
    simpa only [boxedRuleIds,List.mem_cons,List.not_mem_nil,or_false] using member) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rfl

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

structure BoxTable where
  row : Nat
  digits : Array Int
  zeros : List Nat
  boxes : Array DigitBox
  choices : Array Nat

def BoxTable.digit (c : BoxTable) (k : Nat) : Int := c.digits[k]!
def BoxTable.atBox (c : BoxTable) (i : Nat) : DigitBox := c.boxes[i]!

def BoxTable.valid (c : BoxTable) : Bool :=
  (List.range 63).all (fun k => decide (c.digit k = disjointResidueLinear c.row k)) &&
  c.zeros.all (fun k => decide (k < 63 ∧ disjointResidueLinear c.row k = 0)) &&
  (List.range c.boxes.size).all (fun i =>
    (c.atBox i).rules.all (fun k => decide (k ∈ boxedRuleIds))) &&
  (List.range 243).all (fun t =>
    let i := c.choices[t]!
    decide (i < c.boxes.size) && (c.atBox i).fits c.row t)

theorem BoxTable.impossible (c : BoxTable) (valid : c.valid = true)
    (calculate : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < c.boxes.size →
      (∀ k ∈ (c.atBox i).rules,
        boxedRule ((c.atBox i).order c.digit v) m ((c.atBox i).sign c.digit u) k) →
      (∀ k ∈ (c.atBox i).bigger,1 < v k) → (∀ k ∈ c.zeros,0 < v k) → False)
    (v m : Nat → ℤ) (u : Nat → Prop) (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear c.row k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[c.row]! t k)) :
    False := by
  obtain ⟨h, cover⟩ := Bool.and_eq_true_iff.mp valid
  obtain ⟨h, certified⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨digits, positive⟩ := Bool.and_eq_true_iff.mp h
  let i := c.choices[t]!
  let item := c.atBox i
  obtain ⟨bound, fit⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp cover t (List.mem_range.mpr ht))
  let hi : i < c.boxes.size := of_decide_eq_true bound
  obtain ⟨orderEq, signEq, big⟩ := item.reflect c.row t fit v u c.digit
    (fun k hk => of_decide_eq_true (List.all_eq_true.mp digits k (List.mem_range.mpr hk))) first actual
  have pos : ∀ k ∈ c.zeros,0 < v k := by
    intro k hk
    obtain ⟨bk, z⟩ := of_decide_eq_true (List.all_eq_true.mp positive k hk)
    simpa [residueFacts, z] using first k bk
  have checked := List.all_eq_true.mp certified i (List.mem_range.mpr hi)
  apply calculate v m u i hi _ big pos
  intro k hk
  have drawn := of_decide_eq_true (List.all_eq_true.mp checked k hk)
  change boxedRule (item.order c.digit v) m (item.sign c.digit u) k
  rw [orderEq, signEq, boxedRule_eq v m u k drawn]
  exact rules k

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable001110 : BoxTable := ⟨6, #[0,1,1,1,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,0],[0,6,7,10,13,16,19,20,25,26,27,30,33,36,39,42,43,46,49,52,55,56,61,62],
  #[⟨[501],[13,25,36],[],[],[]⟩,
    ⟨[499],[16,19,33],[],[],[]⟩,
    ⟨[497],[36,49,61],[],[],[]⟩,
    ⟨[495],[33,52,55],[],[],[]⟩,
    ⟨[493],[6,13,49],[],[],[]⟩,
    ⟨[491],[0,16,52],[],[],[]⟩,
    ⟨[493,497,501],[6,7,25,26,27,42,43,61,62],[],[],[]⟩,
    ⟨[501],[10,16,26,27,33,39],[13],[],[]⟩,
    ⟨[499],[7,13,20,30,36,42],[16],[],[]⟩,
    ⟨[497],[33,39,42,46,52,62],[36],[],[]⟩,
    ⟨[491],[13,20,26,49,56,62],[16],[],[]⟩,
    ⟨[495],[27,30,36,43,49,56],[33],[],[]⟩,
    ⟨[493],[7,10,16,43,46,52],[13],[],[]⟩,
    ⟨[491,497,499,501],[13,19,25,33,46,56,62],[],[],[]⟩,
    ⟨[493,495,497,499],[7,10,20,36,52,55,61],[],[],[]⟩,
    ⟨[491,493,495,501],[0,6,16,27,30,39,49],[],[],[]⟩,
    ⟨[493,495,499,501],[16,19,25,36,43,46,56],[],[],[]⟩,
    ⟨[491,495,497,501],[10,20,26,33,49,55,61],[],[],[]⟩,
    ⟨[491,493,497,499],[0,6,13,30,39,42,52],[],[],[]⟩,
    ⟨[491,495,499],[0,7,19,26,27,42,43,55,62],[],[],[]⟩,
    ⟨[491,493,495,497,499],[0,6,10,13,19,20,26,27,30,36,39,43,55,61,62],[],[],[]⟩,
    ⟨[491,493,495,497,501],[0,6,7,10,16,20,25,30,33,39,42,43,55,61,62],[],[],[]⟩,
    ⟨[491,493,495,499,501],[0,6,7,19,25,26,30,36,39,42,46,49,55,56,62],[],[],[]⟩,
    ⟨[493,495,497,499,501],[6,10,16,19,20,25,26,27,42,46,52,55,56,61,62],[],[],[]⟩,
    ⟨[491,493,497,499,501],[0,6,7,19,25,26,27,30,33,39,43,46,52,56,61],[],[],[]⟩,
    ⟨[491,495,497,499,501],[0,7,10,13,19,20,25,27,42,43,46,49,55,56,61],[],[],[]⟩], #[6,19,6,0,1,0,0,1,0,2,3,2,4,5,4,0,1,0,2,3,2,0,1,0,4,5,4,0,0,1,1,7,1,0,0,20,0,0,2,1,3,1,4,3,3,1,3,1,2,5,2,0,0,2,1,0,0,8,0,0,1,1,21,1,1,3,2,0,0,2,5,2,2,0,0,4,3,3,1,1,2,2,2,3,0,2,0,3,1,1,3,9,3,0,1,0,0,5,0,2,2,22,4,1,1,0,1,0,4,5,4,1,2,1,0,0,3,0,0,1,23,5,5,0,0,3,0,0,1,1,2,1,4,10,4,1,0,0,3,13,3,2,2,5,14,0,0,3,0,0,1,1,3,1,1,4,2,0,0,1,1,15,3,2,2,3,1,1,0,2,0,11,2,2,0,1,0,4,1,1,3,3,24,0,5,0,0,1,0,0,0,1,16,2,2,3,3,4,1,17,1,1,2,1,0,0,2,0,0,5,1,3,1,0,0,18,4,5,4,3,0,0,1,1,2,1,0,0,4,25,4,1,1,2,1,0,0,3,0,0,12,5,5]⟩

private def sparseVal (v : Nat → Int) (one free k : Nat) : Int :=
  if one.testBit k then 1 else if free.testBit k then v k else 0

private def ruleConj (pred : Nat → Prop) : List Nat → Prop
  | [] => True
  | k :: more => pred k ∧ ruleConj pred more

private theorem ruleConj_of_mem {pred : Nat → Prop} {indices : List Nat}
    (h : ∀ k ∈ indices, pred k) : ruleConj pred indices := by
  induction indices with
  | nil => trivial
  | cons k more ih =>
    exact ⟨h k (List.mem_cons_self ..), ih (fun n hn => h n (List.mem_cons_of_mem _ hn))⟩

private def valuationMasks001110 : Array (Nat × Nat × List Nat) := #[
  (68753039360,7030766090784933057,[501]),
  (8590524416,7030766150947448001,[499]),
  (2306406027886592000,4724360131651380417,[497]),
  (40532405236269056,6990233754301703361,[495]),
  (562949953429568,7030203209584542849,[493]),
  (4503599627436033,7026262559910536384,[491]),
  (6917542222015496384,113223937522476033,[493,497,501]),
  (558547141632,7030765600990830785,[501]),
  (4467840786560,7030761691697185857,[499]),
  (4616264943191195648,2414501216346776769,[497]),
  (4684306562486902784,2346459597051069633,[491]),
  (72629410011807744,6958136749526164673,[495]),
  (4582764464637056,7026183395073335361,[493]),
  (4683813989833515008,2346952169704457409,[491,497,499,501]),
  (2346375474580554880,4684390684957417537,[493,495,497,499]),
  (563500917260353,7030202658620712064,[491,493,495,501]),
  (72136827628748800,6958629331909223617,[493,495,499,501]),
  (2342434764844172288,4688331394693800129,[491,495,497,501]),
  (4508548503445569,7026257611034526848,[491,493,497,499]),
  (4647728009787736193,2383038149750236224,[491,495,499]),
  (6953567240505009217,77198919032963200,[491,493,495,497,499]),
  (6953571578253739201,77194581284233216,[491,493,495,497,501]),
  (4720410745878610113,2310355413659362304,[491,493,495,499,501]),
  (7030193785352553536,572374185418881,[493,495,497,499,501]),
  (2382483927371088065,4648282232166884352,[491,493,497,499,501]),
  (2414575913277072513,4616190246260899904,[491,495,497,499,501])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic001110 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable001110.boxes.size →
    (∀ k ∈ (boxTable001110.atBox i).rules,
      boxedRule ((boxTable001110.atBox i).order boxTable001110.digit v) m ((boxTable001110.atBox i).sign boxTable001110.digit u) k) →
    (∀ k ∈ (boxTable001110.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable001110.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable001110, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks001110[j]!).1 (valuationMasks001110[j]!).2.1) m u) (valuationMasks001110[j]!).2.2 := by
         simp [j,valuationMasks001110]
         exact eqs
       clear eqs hr
       simp [boxTable001110, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks001110,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid001110 : boxTable001110.valid = true := by decide +kernel

theorem secondBoxImpossible001110 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 6 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[6]! t k)) :
    False :=
  boxTable001110.impossible boxTableValid001110 boxesArithmetic001110 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable001111 : BoxTable := ⟨7, #[1,1,1,0,1,1,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,0,1,1,2,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,2,0,0,1,1,2,2,0],[3,7,10,13,16,20,21,26,27,30,33,36,39,42,43,46,49,52,56,57,62],
  #[⟨[499],[16,33],[],[],[]⟩,
    ⟨[499,501],[13,36],[],[],[]⟩,
    ⟨[495],[33,52],[],[],[]⟩,
    ⟨[491],[16,52],[],[],[]⟩,
    ⟨[495,497],[36,49],[],[],[]⟩,
    ⟨[491,493],[13,49],[],[],[]⟩,
    ⟨[205,256,450,491,493,495,497,499,501],[7,26,43,62],[],[],[]⟩], #[6,6,6,0,0,0,0,0,0,2,2,2,3,3,3,0,0,0,2,2,2,0,0,0,3,3,3,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,2,2,2,0,0,0,3,3,3,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,1,1,1,3,3,3,1,1,1,2,2,2,0,0,0,2,2,2,1,1,1,0,0,0,2,2,2,0,0,0,1,1,1,4,4,4,0,0,0,0,0,0,3,3,3,0,0,0,1,1,1,0,0,0,3,3,3,1,1,1,0,0,0,0,0,0,5,5,5,0,0,0,2,2,2,3,3,3,1,1,1,1,1,1,0,0,0,0,0,0,1,1,1,0,0,0,2,2,2,0,0,0,1,1,1,4,4,4,0,0,0,0,0,0,2,2,2,1,1,1,0,0,0,0,0,0,3,3,3,2,2,2,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,1,1,1,3,3,3,1,1,1,0,0,0,0,0,0,5,5,5,0,0,0,0,0,0,1,1,1,3,3,3]⟩

private def valuationMasks001111 : Array (Nat × Nat × List Nat) := #[
  (8590000128,4833009532759188616,[499]),
  (68719484928,4833009472629703816,[499,501]),
  (4503608217305088,4828505933131883656,[495]),
  (4503599627436032,4828505941721752712,[491]),
  (563018672898048,4832446522676290696,[495,497]),
  (562949953429504,4832446591395759240,[491,493]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic001111 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable001111.boxes.size →
    (∀ k ∈ (boxTable001111.atBox i).rules,
      boxedRule ((boxTable001111.atBox i).order boxTable001111.digit v) m ((boxTable001111.atBox i).sign boxTable001111.digit u) k) →
    (∀ k ∈ (boxTable001111.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable001111.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable001111, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks001111[j]!).1 (valuationMasks001111[j]!).2.1) m u) (valuationMasks001111[j]!).2.2 := by
         simp [j,valuationMasks001111]
         exact eqs
       clear eqs hr
       simp [boxTable001111, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks001111,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable001111, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable001111] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid001111 : boxTable001111.valid = true := by decide +kernel

theorem secondBoxImpossible001111 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 7 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[7]! t k)) :
    False :=
  boxTable001111.impossible boxTableValid001111 boxesArithmetic001111 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable001112 : BoxTable := ⟨8, #[2,1,1,2,1,0,1,0,1,2,0,1,2,0,1,2,0,1,2,1,0,2,1,0,2,1,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,2,0,1,2,0,1,2,0,1,2,1,0,2,1,0,2,1,0],[5,7,10,13,16,20,23,26,27,30,33,36,39,42,43,46,49,52,56,59,62],
  #[⟨[501],[13,36],[],[],[]⟩,
    ⟨[499,501],[16,33],[],[],[]⟩,
    ⟨[497],[36,49],[],[],[]⟩,
    ⟨[493],[13,49],[],[],[]⟩,
    ⟨[491,493],[16,52],[],[],[]⟩,
    ⟨[495,497],[33,52],[],[],[]⟩,
    ⟨[256,444,491,493,495,497,499,501],[7,26,27,42,43,62],[],[],[]⟩], #[6,6,6,0,0,0,0,0,0,2,2,2,3,3,3,0,0,0,2,2,2,0,0,0,3,3,3,0,0,0,1,1,1,0,0,0,0,0,0,1,1,1,3,3,3,1,1,1,2,2,2,0,0,0,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,2,2,2,0,0,0,3,3,3,1,1,1,2,2,2,0,0,0,1,1,1,5,5,5,0,0,0,0,0,0,2,2,2,1,1,1,0,0,0,3,3,3,1,1,1,0,0,0,0,0,0,4,4,4,0,0,0,0,0,0,1,1,1,3,3,3,0,0,0,3,3,3,2,2,2,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,1,1,1,2,2,2,1,1,1,0,0,0,2,2,2,0,0,0,1,1,1,5,5,5,0,0,0,0,0,0,0,0,0,2,2,2,3,3,3,1,1,1,1,1,1,0,0,0,0,0,0,1,1,1,0,0,0,3,3,3,0,0,0,1,1,1,0,0,0,3,3,3,1,1,1,0,0,0,0,0,0,4,4,4]⟩

private def valuationMasks001112 : Array (Nat × Nat × List Nat) := #[
  (68719484928,5265355036863562912,[501]),
  (8590000128,5265355096993047712,[499,501]),
  (563018672898048,5264792086910149792,[497]),
  (562949953429504,5264792155629618336,[493]),
  (4503599627436032,5260851505955611808,[491,493]),
  (4503608217305088,5260851497365742752,[495,497]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic001112 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable001112.boxes.size →
    (∀ k ∈ (boxTable001112.atBox i).rules,
      boxedRule ((boxTable001112.atBox i).order boxTable001112.digit v) m ((boxTable001112.atBox i).sign boxTable001112.digit u) k) →
    (∀ k ∈ (boxTable001112.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable001112.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable001112, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks001112[j]!).1 (valuationMasks001112[j]!).2.1) m u) (valuationMasks001112[j]!).2.2 := by
         simp [j,valuationMasks001112]
         exact eqs
       clear eqs hr
       simp [boxTable001112, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks001112,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable001112, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable001112] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid001112 : boxTable001112.valid = true := by decide +kernel

theorem secondBoxImpossible001112 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 8 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[8]! t k)) :
    False :=
  boxTable001112.impossible boxTableValid001112 boxesArithmetic001112 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable011100 : BoxTable := ⟨15, #[0,0,1,1,1,2,0,1,1,1,1,2,2,2,2,0,0,0,0,1,1,1,1,1,1,1,1,2,2,2,2,0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,0],[0,1,6,15,16,17,18,31,32,33,34,43,46,49,52,55,56,61,62],
  #[⟨[429,493,497],[49],[],[],[]⟩,
    ⟨[66],[],[],[],[1]⟩,
    ⟨[359,493,495,497],[46,56,62],[],[],[]⟩,
    ⟨[411,491,493,497],[43,46,56],[],[],[]⟩,
    ⟨[320,402,491,493],[6,43,62],[],[],[]⟩,
    ⟨[96,97,119,134,165,225,235,491,495,499,525,535],[0,43,55,62],[],[],[]⟩], #[4,5,4,4,5,4,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,4,4,5,4,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,5,4,4,5,4,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,2,2,2,2,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,3,3,3,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,3,3,3,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,3,3,3,3,3,1,1,1]⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic011100 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable011100.boxes.size →
    (∀ k ∈ (boxTable011100.atBox i).rules,
      boxedRule ((boxTable011100.atBox i).order boxTable011100.digit v) m ((boxTable011100.atBox i).sign boxTable011100.digit u) k) →
    (∀ k ∈ (boxTable011100.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable011100.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [boxTable011100, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable011100] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid011100 : boxTable011100.valid = true := by decide +kernel

theorem secondBoxImpossible011100 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 15 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[15]! t k)) :
    False :=
  boxTable011100.impossible boxTableValid011100 boxesArithmetic011100 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable011101 : BoxTable := ⟨16, #[1,0,1,0,1,1,2,1,1,1,1,2,2,2,2,0,0,0,0,0,1,0,1,0,1,0,1,2,2,2,2,0,0,0,0,1,1,1,1,2,2,2,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,0,1,1,2,2,0],[1,3,15,16,17,18,19,21,23,25,31,32,33,34,43,46,49,52,56,57,62],
  #[⟨[497],[49,57],[],[],[]⟩,
    ⟨[66],[],[],[],[1]⟩,
    ⟨[72,218,235,258,317,320,402,415,446,485,491,493,495,501,525,535],[43,62],[],[],[]⟩,
    ⟨[493,495,497],[3,46,56,62],[],[],[]⟩,
    ⟨[491,493,495,497],[3,43,46,56],[],[],[]⟩,
    ⟨[491],[49,56,62],[],[],[]⟩,
    ⟨[495],[43,49,56],[],[],[]⟩,
    ⟨[491,493,497],[43,46,56,57],[],[],[]⟩,
    ⟨[491,493,495,497],[46,56,57,62],[],[],[]⟩], #[2,2,2,2,2,2,1,1,1,0,2,0,0,2,0,0,1,0,0,0,2,0,0,2,0,0,1,2,2,2,2,2,2,1,1,1,0,2,0,0,2,0,0,1,0,0,0,2,0,0,2,0,0,1,2,2,2,2,2,2,1,1,1,0,2,0,0,2,0,0,1,0,0,0,2,0,0,2,0,0,1,0,3,0,0,3,0,0,1,0,8,3,3,8,3,3,1,1,1,5,0,0,5,0,0,1,0,0,0,3,0,0,3,0,0,1,0,8,3,3,8,3,3,1,1,1,5,0,0,5,0,0,1,0,0,0,3,0,0,3,0,0,1,0,8,3,3,8,3,3,1,1,1,5,0,0,5,0,0,1,0,0,0,0,4,0,0,4,0,0,1,6,0,0,6,0,0,1,0,0,7,4,4,7,4,4,1,1,1,0,0,4,0,0,4,0,0,1,6,0,0,6,0,0,1,0,0,7,4,4,7,4,4,1,1,1,0,0,4,0,0,4,0,0,1,6,0,0,6,0,0,1,0,0,7,4,4,7,4,4,1,1,1]⟩

theorem nearestBox011101 (v1 v16 v21 v33 m : Int) (u16 u21 u33 : Prop)
    (h1 : 0 < v1) (h16 : 0 < v16) (h21 : 0 < v21) (h33 : 0 < v33)
    (candidate : m = 0 ∨ m = v16 ∨ m = v21 ∨ m = v33)
    (cancellation : v1 ≤ m ∨
      (((if v33 = m then 1 else 0) + (if v16 = m then 1 else 0) +
        (if v21 = m then -1 else 0)) % 3 = 0) ∧
      (((if v33 = m then (if u33 then 1 else -1) else 0) +
        (if 0 = m then 2 else 0) +
        (if v16 = m then (if u16 then -1 else 1) else 0) +
        (if v21 = m then (if u21 then 1 else -1) else 0)) % 3 = 0)) :
    v1 ≤ v16 ∨ v1 ≤ v21 ∨ v1 ≤ v33 ∨
      (v16 = v21 ∧ v33 ≠ v21 ∧ (u16 ↔ u21)) ∨
      (v33 = v21 ∧ v16 ≠ v21 ∧ ¬(u33 ↔ u21)) := by
  rcases cancellation with le | ⟨cnt, sgn⟩
  · rcases candidate with rfl | rfl | rfl | rfl <;> omega
  · have nz : m ≠ 0 := by
      rintro rfl
      simp [Int.ne_of_gt h16, Int.ne_of_gt h21, Int.ne_of_gt h33] at sgn
    by_cases a : v16 = m <;> by_cases b : v21 = m <;> by_cases c : v33 = m <;>
      simp [a,b,c,Ne.symm nz] at cnt sgn
    all_goals try (exfalso; omega (splitDisjunctions := false))
    · have same : u16 ↔ u21 := by
        by_cases su : u16 <;> by_cases sv : u21 <;> simp [su,sv] at sgn ⊢
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨a.trans b.symm, by omega, same⟩)))
    · have different : ¬(u33 ↔ u21) := by
        by_cases su : u33 <;> by_cases sv : u21 <;> simp [su,sv] at sgn ⊢
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c.trans b.symm, by omega, different⟩)))
    · rcases candidate with h | h | h | h
      · exact (nz h).elim
      · exact (a h.symm).elim
      · exact (b h.symm).elim
      · exact (c h.symm).elim

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem nearestBox011101Actual (v m : Nat → Int) (u : Nat → Prop)
    (p1 : 0 < v 1) (p16 : 0 < v 16) (p21 : 0 < v 21) (p33 : 0 < v 33)
    (h525 : boxedRule ((boxTable011101.atBox 2).order boxTable011101.digit v) m
      ((boxTable011101.atBox 2).sign boxTable011101.digit u) 525)
    (h535 : boxedRule ((boxTable011101.atBox 2).order boxTable011101.digit v) m
      ((boxTable011101.atBox 2).sign boxTable011101.digit u) 535) :
    v 1 ≤ v 16 ∨ v 1 ≤ v 21 ∨ v 1 ≤ v 33 ∨
      (v 16 = v 21 ∧ v 33 ≠ v 21 ∧ (u 16 ↔ u 21)) ∨
      (v 33 = v 21 ∧ v 16 ≠ v 21 ∧ ¬(u 33 ↔ u 21)) := by
  simp [boxedRule, disjointNonTriadRulesLinear, DigitBox.order, DigitBox.sign,
    BoxTable.atBox, BoxTable.digit, boxTable011101] at h525 h535
  apply nearestBox011101 _ _ _ _ (m 2) _ _ _ p1 p16 p21 p33
  · rcases h525 with h | h | h | h <;> omega
  · rcases h535 with le | ⟨cnt, sgn⟩
    · exact Or.inl le
    · by_cases zero : 0 = m 2
      · have e : m 2 = 0 := zero.symm
        simp [e,Int.ne_of_gt p16,Int.ne_of_gt p21,Int.ne_of_gt p33] at sgn
      · right
        simpa [zero] using And.intro cnt sgn

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic011101 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable011101.boxes.size →
    (∀ k ∈ (boxTable011101.atBox i).rules,
      boxedRule ((boxTable011101.atBox i).order boxTable011101.digit v) m ((boxTable011101.atBox i).sign boxTable011101.digit u) k) →
    (∀ k ∈ (boxTable011101.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable011101.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  case inr.inr.inl =>
    have near := nearestBox011101Actual v m u
      (hz 1 (by decide)) (hz 16 (by decide)) (hz 21 (by decide)) (hz 33 (by decide))
      (hr 525 (by decide)) (hr 535 (by decide))
    have r (k : Nat) (mem : k ∈ [72,218,235,258,317,320,402,415,446,485,491,493,495,501]) :=
      hr k (List.mem_append_left [525,535] mem)
    clear hr hb hi
    simp [List.forall_mem_cons] at r
    simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.atBox, BoxTable.digit, boxTable011101] at r
    simp [boxTable011101] at hz
    rcases r with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
    have sumHigh : v 56 + 2 * v 46 = 3 * v 49 - 3 := by
      apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have collapse : v 46 = v 52 ∧ v 56 = v 52 ∧ v 49 = v 52 + 1 := by
      clear near hz h0 h1 h2 h3 h4 h7 h8 h9 h10 h11 h12 h13
      rcases h5 with ⟨a,b,c⟩ | ⟨a,b,c⟩ | ⟨a,b,c⟩ | ⟨a,b,c,d⟩ <;>
        rcases h6 with ⟨p,q,r⟩ | ⟨p,q,r⟩ | ⟨p,q,r⟩ | ⟨p,q,r,s⟩ <;>
        refine ⟨?_,?_,?_⟩ <;>
        apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    obtain ⟨c46,c56,c49⟩ := collapse
    have x3 : v 3 = v 15 + v 16 + v 17 + v 18 - 1 := by
      apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have x57 : v 57 = v 31 + v 32 + v 33 + v 34 - 1 := by
      apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have t16 : v 16 = v 21 ∧ (u 16 ↔ u 21) := by
      rcases h1 with ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s,t⟩
      · omega (splitDisjunctions := false)
      · omega (splitDisjunctions := false)
      · refine ⟨e,?_⟩
        by_cases a : u 16 <;> by_cases b : u 21 <;> simp [a,b] at s ⊢
      · omega (splitDisjunctions := false)
    have t17 : v 17 = v 23 ∧ (u 17 ↔ u 23) := by
      rcases h9 with ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s,t⟩
      · omega (splitDisjunctions := false)
      · omega (splitDisjunctions := false)
      · refine ⟨e,?_⟩
        by_cases a : u 17 <;> by_cases b : u 23 <;> simp [a,b] at s ⊢
      · omega (splitDisjunctions := false)
    have t21 : v 21 = v 33 := by
      rcases h3 with ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s,t⟩ <;>
        apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have t23 : v 23 = v 32 := by
      rcases h4 with ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s,t⟩ <;>
        apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have t25 : v 25 = v 31 := by
      rcases h7 with ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s,t⟩ <;>
        apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have average : v 16 + v 18 = 2 * v 17 := by
      obtain ⟨e16,_⟩ := t16
      obtain ⟨e17,_⟩ := t17
      apply Int.le_antisymm <;> omega (splitDisjunctions := false)
    have tAll : v 16 = v 17 ∧ (u 16 ↔ u 17) := by
      rcases h2 with ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s⟩ | ⟨e,l,s,t⟩
      · omega (splitDisjunctions := false)
      · omega (splitDisjunctions := false)
      · omega (splitDisjunctions := false)
      · exact ⟨e,s⟩
    have low : v 1 ≤ v 21 := by
      rcases near with h | h | h | ⟨_,h,_⟩ | ⟨_,h,_⟩
      · rwa [t16.1] at h
      · exact h
      · rwa [← t21] at h
      · exact (h t21.symm).elim
      · exact (h t16.1).elim
    have sameValue : v 23 = v 21 := t17.1.symm.trans (tAll.1.symm.trans t16.1)
    have sameSign : u 23 = u 21 := propext (t17.2.symm.trans (tAll.2.symm.trans t16.2))
    rw [sameValue, sameSign] at h0
    clear near hz h1 h2 h3 h4 h5 h6 h7 h9 h10 h11 h12 h13 sumHigh c46 c56 c49
      x3 x57 t16 t17 t21 t23 t25 average tAll sameValue sameSign
    by_cases a : u 1 <;> by_cases b : u 19 <;> by_cases c : u 21 <;>
      simp [a,b,c] at h0 h8
    all_goals omega
  all_goals simp [boxTable011101, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable011101] at hr
  all_goals first
  | omega (splitDisjunctions := false)
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid011101 : boxTable011101.valid = true := by decide +kernel

theorem secondBoxImpossible011101 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 16 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[16]! t k)) :
    False :=
  boxTable011101.impossible boxTableValid011101 boxesArithmetic011101 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable011110 : BoxTable := ⟨18, #[0,1,1,1,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,1,2,2,0,0,1,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,0],[0,6,9,12,15,18,23,24,28,31,34,37,40,43,46,49,52,55,56,61,62],
  #[⟨[497],[37,49,61],[],[],[]⟩,
    ⟨[499],[12,23,37],[],[],[]⟩,
    ⟨[493],[6,12,49],[],[],[]⟩,
    ⟨[79,259,497,499],[24,28,34,37,49],[],[],[]⟩,
    ⟨[411,491,495,497,499,501],[23,43,49,56],[],[],[]⟩,
    ⟨[499,501],[12,37],[31],[],[]⟩,
    ⟨[499,501],[12,37],[34],[],[]⟩,
    ⟨[361,372,493,499],[12,15,24,28,49],[],[],[]⟩,
    ⟨[499,501],[15,18,31,34],[37],[],[]⟩,
    ⟨[497],[31,34,40,46,52,62],[37],[],[]⟩,
    ⟨[491],[0,15,18,52],[12,24,49],[],[]⟩,
    ⟨[493,495,499,501],[6,15,28,49,56],[],[],[]⟩,
    ⟨[499],[9,15,24,28,34,40],[37],[],[]⟩,
    ⟨[359,493,495,497],[12,28,40,46,56,62],[],[],[]⟩,
    ⟨[144,493,499,501],[6,9,15,31,34,43,46,52],[],[],[]⟩,
    ⟨[495],[31,34,52,55],[28,37,56],[],[]⟩,
    ⟨[491],[0,15,18,52],[12,24,56],[],[]⟩,
    ⟨[491,493,495,499,501],[6,23,49,56,62],[],[],[]⟩,
    ⟨[493,497,499],[6,18,23,24,28,31,43,61,62],[],[],[]⟩,
    ⟨[411,491,495,497,501],[18,24,28,34,40,43,46,52,55,56],[],[],[]⟩,
    ⟨[79,493,495,497,499,501],[6,9,15,24,28,31,46,52,55,56,62],[],[],[]⟩,
    ⟨[502],[],[],[12,31],[18,37]⟩,
    ⟨[502],[],[],[31,37],[12,18]⟩,
    ⟨[499,501],[12,37],[18],[],[]⟩,
    ⟨[491],[12,24,49,56,62],[],[],[]⟩,
    ⟨[493],[9,15,18,43,46,52],[49],[],[]⟩,
    ⟨[495],[31,34,52,55],[28,37,49],[],[]⟩,
    ⟨[491,495,499,501],[24,31,34,55,62],[15],[],[]⟩,
    ⟨[492,496,502],[],[],[0,18,24,62],[28,31,43,55]⟩,
    ⟨[491,495,501],[9,24,28,34,40,55,62],[15,37],[],[]⟩,
    ⟨[491,495,501],[0,9,15,24,28,40,43],[12,34],[],[]⟩,
    ⟨[144,497,499,501],[15,18,34,40,46,52,61,62],[],[],[]⟩,
    ⟨[359,372,493,495,497,499,501],[9,15,23,24,28,31,46,52,56,61,62],[],[],[]⟩,
    ⟨[491,493,497,499,501],[0,6,18,23,24,28,34,40,43,46,52,56,61],[],[],[]⟩], #[18,28,18,6,1,1,1,1,6,0,3,0,0,1,0,2,29,2,0,3,0,2,15,2,0,1,0,1,1,21,1,22,1,8,8,8,0,1,0,2,7,2,0,16,0,2,7,2,0,3,0,0,16,0,5,1,1,12,12,12,1,5,1,2,15,2,0,3,0,0,3,0,0,1,0,0,30,0,2,7,2,0,0,17,2,13,2,0,0,2,9,9,9,13,1,1,1,1,27,0,0,17,0,0,1,2,24,2,2,7,2,0,0,1,0,0,11,1,1,5,1,5,1,31,10,10,0,0,2,2,8,2,0,0,11,0,0,1,0,0,3,2,9,2,6,1,1,20,32,20,1,6,1,2,13,2,0,0,3,0,0,1,3,0,0,2,0,0,2,4,2,4,0,0,2,4,2,1,0,0,19,19,33,5,1,1,1,1,5,1,0,0,2,7,2,11,0,0,2,4,2,1,0,0,11,0,0,1,1,6,1,6,1,25,10,10,2,4,2,4,0,0,1,0,0,2,0,0,4,0,0,2,7,2,14,1,1,14,26,14,1,23,1]⟩

private def valuationMasks011110 : Array (Nat × Nat × List Nat) := #[
  (2306406096606068736,4724356293081731649,[497]),
  (137447346176,7030762252240454209,[499]),
  (562949953425472,7030199439734374913,[493]),
  (0,0,[]),
  (0,0,[]),
  (137438957568,7030762252248842817,[499,501]),
  (137438957568,7030762252248842817,[499,501]),
  (0,0,[]),
  (19327647744,7030762370360152641,[499,501]),
  (4616261105637916672,2414501284049883713,[497]),
  (4503599627665409,7026258790060134976,[491]),
  (72620544259817536,6958141845427982849,[493,495,499,501]),
  (1116976742912,7030761272711057473,[499]),
  (0,0,[]),
  (0,0,[]),
  (40532415973687296,6990229973714113089,[495]),
  (4503599627665409,7026258790060134976,[491]),
  (4684306562427125824,2346455827260674561,[491,493,495,499,501]),
  (6917537826175451200,113224563512349185,[493,497,499]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (137438957568,7030762252248842817,[499,501]),
  (4684306562435518464,2346455827252281921,[491]),
  (4582764464865792,7026179625222934593,[493]),
  (40532415973687296,6990229973714113089,[495]),
  (4647714834790481920,2383047554897318465,[491,495,499,501]),
  (0,0,[]),
  (4647715932423062016,2383046457264738369,[491,495,501]),
  (9895889895937,7030752493797904448,[491,495,501]),
  (0,0,[]),
  (0,0,[]),
  (2382484484701552705,4648277904986247680,[491,493,497,499,501])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic011110 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable011110.boxes.size →
    (∀ k ∈ (boxTable011110.atBox i).rules,
      boxedRule ((boxTable011110.atBox i).order boxTable011110.digit v) m ((boxTable011110.atBox i).sign boxTable011110.digit u) k) →
    (∀ k ∈ (boxTable011110.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable011110.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable011110, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks011110[j]!).1 (valuationMasks011110[j]!).2.1) m u) (valuationMasks011110[j]!).2.2 := by
         simp [j,valuationMasks011110]
         exact eqs
       clear eqs hr
       simp [boxTable011110, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks011110,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable011110, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable011110] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid011110 : boxTable011110.valid = true := by decide +kernel

theorem secondBoxImpossible011110 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 18 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[18]! t k)) :
    False :=
  boxTable011110.impossible boxTableValid011110 boxesArithmetic011110 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable011111 : BoxTable := ⟨19, #[1,1,1,0,1,1,2,1,2,0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,0,1,1,2,2,0],[3,9,12,15,18,19,24,25,28,31,34,37,40,43,46,49,52,56,57,62],
  #[⟨[495,497],[37,49],[],[],[]⟩,
    ⟨[491,493],[12,49],[],[],[]⟩,
    ⟨[499],[12,19,37],[],[],[]⟩,
    ⟨[495],[31,34,52],[],[],[]⟩,
    ⟨[491],[15,18,52],[],[],[]⟩,
    ⟨[499,501],[15,18,31,34],[],[],[]⟩,
    ⟨[499],[9,15,24,28,34,40],[12],[],[]⟩,
    ⟨[491,495,501],[18,24,25,28,31,43,62],[],[],[]⟩,
    ⟨[480,491,493,495,499],[18,24,28,34,40,43,46,52,56],[],[],[]⟩,
    ⟨[142,495,499],[12,31,37,52],[],[],[]⟩,
    ⟨[491,493,497,501],[18,37,43,46,56,57],[],[],[]⟩,
    ⟨[114,402,491,493,495,501],[3,12,37,43,57,62],[],[],[]⟩,
    ⟨[491,497,499],[9,15,19,24,28,31,46,52,56,57,62],[],[],[]⟩,
    ⟨[501],[12,18,31,37],[],[],[]⟩,
    ⟨[493,497,499],[3,18,19,24,28,31,43,57,62],[],[],[]⟩,
    ⟨[142,491,497,499,501],[3,9,15,24,28,31,46,52,56,62],[],[],[]⟩], #[7,14,7,13,2,2,7,2,2,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,2,5,2,2,5,2,5,5,5,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,2,2,11,6,6,6,2,2,11,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,3,3,3,3,2,2,3,2,2,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0,0,2,4,2,2,4,2,4,4,4,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,1,1,1,2,2,9,12,12,15,2,2,9,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,8,8,8,10,2,2,10,2,2,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,2,4,2,2,4,2,4,4,4,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,2,2,3,3,3,3,2,2,3]⟩

private def valuationMasks011111 : Array (Nat × Nat × List Nat) := #[
  (563087392374784,4832442684164313608,[495,497]),
  (562949953425408,4832442821603262984,[491,493]),
  (137439481856,4833005634117206536,[499]),
  (4503618954723328,4828502152601965064,[495]),
  (4503599627665408,4828502171929022984,[491]),
  (19327647744,4833005752229040648,[499,501]),
  (1116976742912,4833004654579945480,[499]),
  (4611694816986923008,221310954569765384,[491,495,501]),
  (0,0,[]),
  (0,0,[]),
  (216252084390199296,4616753687166489096,[491,493,497,501]),
  (0,0,[]),
  (4832432771345973760,573000210714632,[491,497,499]),
  (139586703360,4833005631969985032,[501]),
  (4755810005029748744,77195766526939648,[493,497,499]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic011111 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable011111.boxes.size →
    (∀ k ∈ (boxTable011111.atBox i).rules,
      boxedRule ((boxTable011111.atBox i).order boxTable011111.digit v) m ((boxTable011111.atBox i).sign boxTable011111.digit u) k) →
    (∀ k ∈ (boxTable011111.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable011111.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable011111, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks011111[j]!).1 (valuationMasks011111[j]!).2.1) m u) (valuationMasks011111[j]!).2.2 := by
         simp [j,valuationMasks011111]
         exact eqs
       clear eqs hr
       simp [boxTable011111, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks011111,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable011111, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable011111] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid011111 : boxTable011111.valid = true := by decide +kernel

theorem secondBoxImpossible011111 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 19 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[19]! t k)) :
    False :=
  boxTable011111.impossible boxTableValid011111 boxesArithmetic011111 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable011112 : BoxTable := ⟨20, #[2,1,1,2,1,0,1,1,2,0,1,2,0,1,2,0,1,2,0,2,1,0,2,1,0,2,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,0,2,1,0,2,1,0],[5,9,12,15,18,21,24,28,31,34,37,40,43,46,49,52,56,59,62],
  #[⟨[497],[37,49],[],[],[]⟩,
    ⟨[493],[12,49],[],[],[]⟩,
    ⟨[499],[12,37],[],[],[]⟩,
    ⟨[495,497],[31,34,52],[28],[],[]⟩,
    ⟨[259,372,491,493,495,497,499,501],[18,31,43,62],[],[],[]⟩,
    ⟨[491],[5,15,18,52],[12,24,49],[],[]⟩,
    ⟨[500],[],[],[9,28,34],[15,24,40]⟩,
    ⟨[493,495,497,499,501],[9,15,24,28,31,46,52,56,62],[],[],[]⟩,
    ⟨[491,493,497,499,501],[18,24,28,34,40,43,46,52,56],[],[],[]⟩,
    ⟨[491,493],[15,18,52],[43],[],[]⟩,
    ⟨[494],[],[],[15,43,52],[9,18,46]⟩], #[4,4,4,2,2,2,2,2,2,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,2,2,2,2,2,2,4,4,4,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,2,2,2,6,6,6,2,2,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,3,3,3,2,2,2,2,2,2,0,0,0,0,0,0,1,1,1,1,1,1,0,0,0,0,0,0,2,2,2,2,2,2,9,5,5,0,0,0,1,1,1,0,0,0,0,0,0,0,0,0,1,1,1,2,2,2,7,7,7,2,2,2,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,8,8,8,2,2,2,2,2,2,0,0,0,1,1,1,0,0,0,1,1,1,0,0,0,0,0,0,2,2,2,2,2,2,10,5,5,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,1,1,1,2,2,2,3,3,3,2,2,2]⟩

private def valuationMasks011112 : Array (Nat × Nat × List Nat) := #[
  (563087392374784,5264788248359899680,[497]),
  (562949953425408,5264788385798849056,[493]),
  (137438957568,5265351198313316896,[499]),
  (4503618954723328,5260847716797551136,[495,497]),
  (0,0,[]),
  (4503599627665440,5260847736124609024,[491]),
  (0,0,[]),
  (4688317583269593600,577033752482680864,[493,495,497,499,501]),
  (76641475479470080,5188709860272804384,[491,493,497,499,501]),
  (4503599627665408,5260847736124609056,[491,493]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic011112 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable011112.boxes.size →
    (∀ k ∈ (boxTable011112.atBox i).rules,
      boxedRule ((boxTable011112.atBox i).order boxTable011112.digit v) m ((boxTable011112.atBox i).sign boxTable011112.digit u) k) →
    (∀ k ∈ (boxTable011112.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable011112.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable011112, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks011112[j]!).1 (valuationMasks011112[j]!).2.1) m u) (valuationMasks011112[j]!).2.2 := by
         simp [j,valuationMasks011112]
         exact eqs
       clear eqs hr
       simp [boxTable011112, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks011112,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable011112, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable011112] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid011112 : boxTable011112.valid = true := by decide +kernel

theorem secondBoxImpossible011112 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 20 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[20]! t k)) :
    False :=
  boxTable011112.impossible boxTableValid011112 boxesArithmetic011112 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable101100 : BoxTable := ⟨21, #[0,0,1,1,1,2,0,0,0,0,0,1,1,1,1,2,2,2,2,0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,0,0,0,0,1,1,1,1,1,2,0,1,2,0,1,2,0,1,2,0,1,1,2,2,0,0,1,1],[0,1,6,7,8,9,10,19,20,21,22,23,24,25,26,35,36,37,38,45,48,51,54,59,60],
  #[⟨[493],[6,48],[],[],[]⟩,
    ⟨[272,495,497],[54,59],[],[],[]⟩,
    ⟨[493,495,497],[6,51],[],[],[]⟩,
    ⟨[495,497],[48],[54],[],[]⟩,
    ⟨[66],[],[],[],[1]⟩,
    ⟨[491],[0,51,54],[],[],[]⟩,
    ⟨[491,497],[0,20,22,24,26,54,60],[],[],[]⟩,
    ⟨[279,491,493,495,497,499],[8,22,23,26,51,59],[],[],[]⟩,
    ⟨[499,501],[9,19,24,25,36],[20],[],[]⟩,
    ⟨[491,495,497,499,501],[7,10,20,21,24,26,59],[],[],[]⟩,
    ⟨[492,498,502],[],[],[0,10,24,25,37,54,60],[8,20,21,35]⟩,
    ⟨[257,279,491,493,495,497,499,501],[8,20,22,23,26,37],[7],[],[]⟩,
    ⟨[491,495],[0,20,22,24,26,35,36,37,38,45,51,59,60],[],[],[]⟩,
    ⟨[234,491,493,495,499,501],[0,19,22,23,35,37,38,51,60],[20],[],[]⟩,
    ⟨[316,471,492,498,501],[8,9,10,21,23,25,35,36,37],[],[0,54,60],[]⟩,
    ⟨[316,471,491,495,501],[0,8,9,10,21,23,25,36,38,45,51,59,60],[],[],[]⟩], #[1,14,1,1,8,1,1,4,1,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,1,6,1,1,11,1,1,4,1,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,1,6,1,1,10,1,1,4,1,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,1,0,0,5,0,0,5,0,0,4,0,2,1,1,2,1,1,2,1,1,0,1,0,0,1,0,0,1,0,0,5,0,0,5,0,0,4,0,2,1,1,2,1,1,2,1,1,0,1,0,0,1,0,0,1,0,0,5,0,0,5,0,0,4,0,2,1,1,2,1,1,2,1,1,0,3,0,0,3,0,0,3,0,2,15,2,2,13,2,2,4,2,0,3,0,0,3,0,0,3,0,0,3,0,0,3,0,0,3,0,2,12,2,2,7,2,2,4,2,0,3,0,0,3,0,0,3,0,0,3,0,0,3,0,0,3,0,2,7,2,2,9,2,2,4,2,0,3,0,0,3,0,0,3,0]⟩

private def valuationMasks101100 : Array (Nat × Nat × List Nat) := #[
  (281474976710720,1749684155135297411,[493]),
  (0,0,[]),
  (2251799813685312,1747713830298322819,[493,495,497]),
  (281474976710656,1749684155135297475,[495,497]),
  (0,0,[]),
  (20266198323167233,1729699431788840898,[491]),
  (1170935903205457921,579029726906550210,[491,497]),
  (0,0,[]),
  (68770333184,1749965561341674947,[499,501]),
  (576460752390456448,1173504877721551683,[491,495,497,499,501]),
  (0,0,[]),
  (0,0,[]),
  (1731669756581249025,18295873530759106,[491,495]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic101100 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable101100.boxes.size →
    (∀ k ∈ (boxTable101100.atBox i).rules,
      boxedRule ((boxTable101100.atBox i).order boxTable101100.digit v) m ((boxTable101100.atBox i).sign boxTable101100.digit u) k) →
    (∀ k ∈ (boxTable101100.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable101100.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable101100, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks101100[j]!).1 (valuationMasks101100[j]!).2.1) m u) (valuationMasks101100[j]!).2.2 := by
         simp [j,valuationMasks101100]
         exact eqs
       clear eqs hr
       simp [boxTable101100, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks101100,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable101100, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable101100] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid101100 : boxTable101100.valid = true := by decide +kernel

theorem secondBoxImpossible101100 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 21 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[21]! t k)) :
    False :=
  boxTable101100.impossible boxTableValid101100 boxesArithmetic101100 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable121110 : BoxTable := ⟨36, #[0,1,1,1,1,2,0,2,0,1,2,0,1,2,0,1,2,0,1,2,2,0,0,1,1,2,2,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,1,2,0,1,2,0,1,2,0,1,1,2,2,0,0,1,1],[0,6,8,11,14,17,21,22,28,31,34,37,40,45,48,51,54,59,60],
  #[⟨[491,493,495,497,499,501],[21,59],[],[],[]⟩,
    ⟨[499],[8,22,37],[],[],[]⟩,
    ⟨[497],[37,45,60],[],[],[]⟩,
    ⟨[491,493],[8,22,45,60],[],[],[]⟩,
    ⟨[499,501],[11,14,31,34],[],[],[]⟩,
    ⟨[493,495,497,499,501],[6,11,14,48],[],[],[]⟩,
    ⟨[491,495,497,499,501],[0,17,51,54],[],[],[]⟩,
    ⟨[495,497],[28,40,51,54],[],[],[]⟩,
    ⟨[499],[11,17,28,34,40],[],[],[]⟩,
    ⟨[491,495,497,499,501],[11,14,22,59],[],[],[]⟩,
    ⟨[493,495,497,499,501],[21,45,51,54],[],[],[]⟩,
    ⟨[491,495,497,499,501],[17,21,28,40,60],[],[],[]⟩,
    ⟨[493,495,497,499,501],[8,31,34,48,59],[],[],[]⟩,
    ⟨[130,491,495,497,499,501],[8,14,17,34,37,40,48,51,60],[],[],[]⟩,
    ⟨[497],[31,34,40,48,54],[],[],[]⟩,
    ⟨[493],[8,17,45,51,54],[],[],[]⟩,
    ⟨[491],[11,14,22,48,60],[],[],[]⟩,
    ⟨[130,491,493,495,497,501],[8,17,28,40,59],[],[],[]⟩,
    ⟨[493,497],[6,8,17,31,34,40,45,48,51],[],[],[]⟩,
    ⟨[491,499],[0,14,17,22,28,34,40,48,60],[],[],[]⟩,
    ⟨[493,495,497,499,501],[8,17,28,34,40,45,54],[],[],[]⟩,
    ⟨[493,495,499],[6,8,11,34,37,40,54,59,60],[],[],[]⟩,
    ⟨[491,497,501],[0,8,11,21,34,37,40,54,60],[],[],[]⟩,
    ⟨[491,495,497,499,501],[11,22,31,34,40,48,60],[],[],[]⟩,
    ⟨[234,272,491,493,495,497,499,501],[0,14,22,54,60],[],[],[]⟩,
    ⟨[494,498,502],[],[],[6,14,17,21,22],[34,37,40,45,48,51]⟩,
    ⟨[492,496,500],[],[],[0,14,17,22],[34,37,40,45,48,51,59]⟩,
    ⟨[491,497,501],[0,8,11,21,28,31,34,37,48,51,60],[],[],[]⟩,
    ⟨[281,491,493,495,497,501],[6,14,17,21,22,28,34,37,45,48,54],[],[],[]⟩,
    ⟨[234,491,493,495,497,501],[0,14,17,22,28,34,37,45,48,54,59],[],[],[]⟩,
    ⟨[281,491,493,495,497,501],[6,11,17,21,22,31,37,40,45,48,51],[],[],[]⟩,
    ⟨[234,491,493,495,497,501],[0,11,17,22,31,37,40,45,48,51,59],[],[],[]⟩,
    ⟨[281,372,376,448,491,493,497,499,501],[6,8,11,31,45,48,51],[21,40],[],[]⟩], #[0,24,0,0,1,1,17,11,0,28,29,0,1,0,1,20,0,0,0,2,2,0,0,3,2,0,2,0,1,1,4,4,0,0,4,0,1,0,1,5,0,0,5,9,0,0,0,3,2,0,2,0,2,2,21,22,0,0,8,0,0,1,1,14,0,0,8,8,0,1,0,1,2,0,2,0,2,2,0,0,3,0,2,2,0,0,3,2,0,2,0,6,0,0,1,1,12,6,0,10,6,0,1,0,1,15,0,0,0,0,3,2,0,2,0,2,2,0,1,1,5,6,0,0,7,0,1,0,1,4,0,0,4,4,0,2,0,2,0,2,2,0,0,3,7,7,0,0,6,0,0,1,1,7,0,0,10,6,0,1,0,1,25,26,0,1,0,1,18,0,0,0,2,2,0,0,3,2,0,2,0,19,0,0,1,1,13,13,0,1,0,1,5,0,0,5,9,0,0,0,3,2,0,2,0,2,2,0,1,1,5,11,0,0,16,0,32,0,0,30,31,0,1,0,1,2,0,2,0,2,2,0,0,3,12,27,0,0,23,0,0,1,1]⟩

private def valuationMasks121110 : Array (Nat × Nat × List Nat) := #[
  (576460752305520640,1173505618829527361,[491,493,495,497,499,501]),
  (137443148032,1749966233691899969,[499]),
  (1152956826417889280,597009544717158721,[497]),
  (1152956688983130368,597009682151917633,[491,493]),
  (19327371264,1749966351807676737,[499,501]),
  (281474976729152,1749684896158318849,[493,495,497,499,501]),
  (20266198323298305,1729700172811749696,[491,495,497,499,501]),
  (20267298103230464,1729699073031817537,[495,497]),
  (1116960065536,1749965254174982465,[499]),
  (576460752307636224,1173505618827411777,[491,495,497,499,501]),
  (20301382697353216,1729664988437694785,[493,495,497,499,501]),
  (1152922604389138432,597043766745909569,[491,495,497,499,501]),
  (576742246607487232,1173224124527560769,[493,495,497,499,501]),
  (0,0,[]),
  (18296992325173248,1731669378809874753,[497]),
  (20301382695387392,1729664988439660609,[493]),
  (1153202979587770368,596763391547277633,[491]),
  (0,0,[]),
  (2569578001596736,1747396793133451265,[493,497]),
  (1153204096547831809,596762274587216192,[491,499]),
  (18050699841634560,1731915671293413441,[493,495,497,499,501]),
  (1747397909550205248,2568461584842753,[493,495,499]),
  (1170937157248878849,579029213886169152,[491,497,501]),
  (1153204098426734592,596762272708313409,[491,495,497,499,501]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (1155454936434084097,594511434700963904,[491,497,501]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic121110 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable121110.boxes.size →
    (∀ k ∈ (boxTable121110.atBox i).rules,
      boxedRule ((boxTable121110.atBox i).order boxTable121110.digit v) m ((boxTable121110.atBox i).sign boxTable121110.digit u) k) →
    (∀ k ∈ (boxTable121110.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable121110.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable121110, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks121110[j]!).1 (valuationMasks121110[j]!).2.1) m u) (valuationMasks121110[j]!).2.2 := by
         simp [j,valuationMasks121110]
         exact eqs
       clear eqs hr
       simp [boxTable121110, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks121110,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable121110, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable121110] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid121110 : boxTable121110.valid = true := by decide +kernel

theorem secondBoxImpossible121110 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 36 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[36]! t k)) :
    False :=
  boxTable121110.impossible boxTableValid121110 boxesArithmetic121110 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable121111 : BoxTable := ⟨37, #[1,1,1,0,1,1,2,2,0,1,2,0,1,2,0,1,2,0,1,1,2,2,0,0,1,1,2,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,1,2,0,1,2,0,1,2,0,0,1,1,2,2,0,0,1],[3,8,11,14,17,22,23,28,31,34,37,40,45,48,51,54,55,60,61],
  #[⟨[491,493,495,497,499,501],[3,23],[],[],[]⟩,
    ⟨[501],[17,28,40],[],[],[]⟩,
    ⟨[491],[17,51,54],[],[],[]⟩,
    ⟨[495,497],[28,40,51,54],[],[],[]⟩,
    ⟨[499,501],[11,14,31,34],[],[],[]⟩,
    ⟨[491,493,497,499,501],[37,45,60,61],[],[],[]⟩,
    ⟨[491,493,495,499,501],[31,34,48,55],[],[],[]⟩,
    ⟨[491,493],[8,22,45,60],[],[],[]⟩,
    ⟨[501],[8,14,22,31,37],[],[],[]⟩,
    ⟨[491,493,497,499,501],[3,31,34,40],[],[],[]⟩,
    ⟨[491,493,495,499,501],[23,45,51,60],[],[],[]⟩,
    ⟨[491,493,495,499,501],[3,11,14,28,48],[],[],[]⟩,
    ⟨[491,493,497,499,501],[8,22,23,37,54],[],[],[]⟩,
    ⟨[497],[31,34,40,48,54],[],[],[]⟩,
    ⟨[491],[11,14,22,48,60],[],[],[]⟩,
    ⟨[495],[28,37,45,51,60],[],[],[]⟩,
    ⟨[497,501],[8,14,22,34,37,40,48,54,61],[],[],[]⟩,
    ⟨[271,493,495,497,499,501],[11,14,23,48,54],[],[],[]⟩,
    ⟨[79,491,493,495,497,499],[3,8,22,28,37],[],[],[]⟩,
    ⟨[491,495],[11,14,22,28,37,45,48,51,55],[],[],[]⟩,
    ⟨[491,497,499],[14,17,22,23,28,31,54,60,61],[],[],[]⟩,
    ⟨[493,495,501],[3,14,17,22,28,31,54,55,60],[],[],[]⟩,
    ⟨[491,493,497,499,501],[11,14,22,31,40,48,54],[],[],[]⟩,
    ⟨[491,493,495,499,501],[8,14,22,28,37,51,60],[],[],[]⟩,
    ⟨[248,272,491,493,495,497,499,501],[34,40,54,60,61],[],[],[]⟩,
    ⟨[492,496,500],[],[],[34,37,40],[14,17,22,23,45,48,51,55]⟩,
    ⟨[494,498,502],[],[],[3,34,37,40,61],[14,17,22,45,48,51]⟩,
    ⟨[372,377,485,491,493,495,497,499,501],[28,31,45,51,55],[],[],[]⟩,
    ⟨[491,493,495,499,501],[3,14,17,22,28,34,37,45,48,54,55],[],[],[]⟩,
    ⟨[491,493,495,499,501],[11,17,22,23,31,37,40,45,48,51,55],[],[],[]⟩,
    ⟨[271,491,495,497,499,501],[14,17,22,23,28,34,37,45,48,54,61],[],[],[]⟩,
    ⟨[250,493,495,497,499,501],[8,14,17,23,34,37,40,48,51,55,60],[],[],[]⟩,
    ⟨[248,493,495,497,499,501],[3,8,14,17,34,37,40,48,51,60,61],[],[],[]⟩,
    ⟨[248,493,495,497,499,501],[3,11,17,22,31,37,40,45,48,51,61],[],[],[]⟩], #[20,21,0,8,0,0,1,0,1,30,28,0,16,0,0,1,0,1,5,6,0,7,0,0,1,0,1,1,0,1,4,4,0,4,0,0,1,0,1,17,11,0,22,0,0,1,0,1,5,11,0,5,0,0,24,0,0,1,0,1,12,18,0,13,0,0,1,0,1,12,6,0,5,0,0,1,0,1,7,7,0,2,2,0,3,0,0,2,0,2,2,2,0,3,0,0,2,0,2,2,2,0,3,0,0,2,0,2,2,0,2,2,2,0,3,0,0,2,0,2,2,2,0,3,0,0,2,0,2,2,2,0,3,0,0,3,0,0,2,0,2,2,2,0,3,0,0,2,0,2,2,2,0,3,0,0,2,0,2,2,2,0,1,1,0,6,0,0,6,0,9,1,1,0,7,0,0,10,0,5,1,1,0,23,0,0,31,0,32,25,0,26,1,1,0,19,0,0,4,0,4,1,1,0,4,0,0,8,0,8,1,1,0,14,0,0,27,0,0,29,0,33,1,1,0,15,0,0,10,0,5,1,1,0,6,0,0,6,0,9,1,1,0]⟩

private def valuationMasks121111 : Array (Nat × Nat × List Nat) := #[
  (8388616,3515377425062185216,[491,493,495,497,499,501]),
  (1099780194304,3515376325290379528,[501]),
  (20266198323298304,3495111226747275528,[491]),
  (20267298103230464,3495110126967343368,[495,497]),
  (19327371264,3515377405743202568,[499,501]),
  (3458799835631583232,56577589438990600,[491,493,497,499,501]),
  (36310291323027456,3479067133747546376,[491,493,495,499,501]),
  (1152956688983130368,2362420736087443464,[491,493]),
  (139590648064,3515377285479925768,[501]),
  (1118838980616,3515376306231593216,[491,493,497,499,501]),
  (1155208488801009664,2360168936269564168,[491,493,495,499,501]),
  (281475245164552,3515095949825409280,[491,493,495,499,501]),
  (18014535961018624,3497362889109555208,[491,493,497,499,501]),
  (18296992325173248,3497080432745400584,[497]),
  (1153202979587770368,2362174445482803464,[491]),
  (1155208626500009984,2360168798570563848,[495]),
  (2324140136834547968,1191237288236025864,[497,501]),
  (0,0,[]),
  (0,0,[]),
  (38597393893050368,3476780031177523464,[491,495]),
  (3476778914758672384,38598510311901448,[491,497,499]),
  (1206964702555553800,2308412722515020032,[493,495,501]),
  (18296975149516800,3497080449921057032,[491,493,497,499,501]),
  (1155173442132132096,2360203982938441736,[491,493,495,499,501]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (54360009768845320,3461017415301728512,[491,493,495,499,501]),
  (38598495292229632,3476778929778344200,[491,493,495,499,501]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic121111 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable121111.boxes.size →
    (∀ k ∈ (boxTable121111.atBox i).rules,
      boxedRule ((boxTable121111.atBox i).order boxTable121111.digit v) m ((boxTable121111.atBox i).sign boxTable121111.digit u) k) →
    (∀ k ∈ (boxTable121111.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable121111.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable121111, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks121111[j]!).1 (valuationMasks121111[j]!).2.1) m u) (valuationMasks121111[j]!).2.2 := by
         simp [j,valuationMasks121111]
         exact eqs
       clear eqs hr
       simp [boxTable121111, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks121111,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable121111, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable121111] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid121111 : boxTable121111.valid = true := by decide +kernel

theorem secondBoxImpossible121111 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 37 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[37]! t k)) :
    False :=
  boxTable121111.impossible boxTableValid121111 boxesArithmetic121111 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234
open scoped Classical

private def boxTable121112 : BoxTable := ⟨38, #[2,1,1,2,1,0,1,2,0,1,2,0,1,2,0,1,2,0,1,0,2,1,0,2,1,0,2,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,1,2,0,1,2,0,1,2,0,1,2,0,2,1,0,2,1,0,2,1],[5,8,11,14,17,19,22,25,28,31,34,37,40,45,48,51,54,57,60],
  #[⟨[491,493,495,497,499,501],[5,57],[],[],[]⟩,
    ⟨[495],[31,34,48],[],[],[]⟩,
    ⟨[493],[11,14,48],[],[],[]⟩,
    ⟨[499,501],[11,14,31,34],[],[],[]⟩,
    ⟨[491,493],[8,22,45,60],[],[],[]⟩,
    ⟨[491,493,495,497,501],[17,25,28,40],[],[],[]⟩,
    ⟨[491,493,495,497,499],[8,19,22,37],[],[],[]⟩,
    ⟨[495,497],[28,40,51,54],[],[],[]⟩,
    ⟨[493],[8,17,45,51,54],[],[],[]⟩,
    ⟨[98,132,272,491,493,495,497,499,501],[11,34,37,60],[],[],[]⟩,
    ⟨[491,493,495,497,501],[8,14,22,57],[],[],[]⟩,
    ⟨[491,493,495,497,499],[5,28,34,40],[],[],[]⟩,
    ⟨[491,493,495,497,499],[11,37,45,57,60],[],[],[]⟩,
    ⟨[491,493,495,497,501],[5,17,31,51,54],[],[],[]⟩,
    ⟨[142,493,495,497,499],[8,11,28,31,45,48,51],[],[],[]⟩,
    ⟨[501],[8,14,22,31,37],[],[],[]⟩,
    ⟨[499],[11,17,28,34,40],[],[],[]⟩,
    ⟨[493,501],[14,17,22,25,31,37,45,51,54],[],[],[]⟩,
    ⟨[162,491,495,497,499,501],[11,17,51,54,57],[],[],[]⟩,
    ⟨[142,493,495,497,499,501],[5,31,37,45,60],[28],[],[]⟩,
    ⟨[491,493,495,497,499],[11,17,28,34,45,51,54],[],[],[]⟩,
    ⟨[491,493,495,497,501],[8,14,31,37,45,51,60],[],[],[]⟩,
    ⟨[132,169,372,491,493,495,497,499,501],[14,22,25,28,31],[],[],[]⟩,
    ⟨[494,498,502],[],[],[14,17,22,25,34,37,40,45,48,51,57],[]⟩,
    ⟨[492,496,500],[],[],[14,17,22,34,37,40,45,48,51],[5,19]⟩,
    ⟨[280,491,495,497,499,501],[14,17,22,25,28,34,37,45,48,54,57],[],[],[]⟩,
    ⟨[415,491,495,497,499,501],[5,14,17,19,22,28,34,37,45,48,54],[],[],[]⟩,
    ⟨[280,493,495,497,499,501],[8,14,17,25,34,37,40,48,51,57,60],[],[],[]⟩,
    ⟨[415,493,495,497,499,501],[5,8,14,17,19,34,37,40,48,51,60],[],[],[]⟩,
    ⟨[162,493,495,497,499,501],[11,17,19,22,31,37,40,45,48,51,57],[],[],[]⟩,
    ⟨[142,493,495,497,499,501],[5,11,17,22,25,31,37,40,45,48,51],[],[],[]⟩], #[22,0,0,15,0,0,5,0,0,25,26,0,10,6,0,5,11,0,1,0,1,1,0,1,1,0,1,3,0,0,3,0,0,3,0,0,2,2,0,2,2,0,2,2,0,2,0,2,2,0,2,2,0,2,9,0,0,16,0,0,6,0,0,1,1,0,1,1,0,1,1,0,12,0,19,12,0,5,4,0,4,23,24,0,4,4,0,8,8,0,1,0,1,1,0,1,1,0,1,17,0,0,7,0,0,8,0,0,2,2,0,2,2,0,2,2,0,2,0,2,2,0,2,2,0,2,3,0,0,3,0,0,3,0,0,1,1,0,1,1,0,1,1,0,7,0,7,18,0,13,6,0,13,7,0,0,20,0,0,6,0,0,1,0,1,1,0,1,1,0,1,5,0,0,4,0,0,21,0,0,5,11,0,10,6,0,27,28,0,2,0,2,2,0,2,2,0,2,3,0,0,3,0,0,3,0,0,2,2,0,2,2,0,2,2,0,14,0,14,29,0,30,6,0,5,9,0,0,9,0,0,4,0,0,1,1,0,1,1,0,1,1,0]⟩

private def valuationMasks121112 : Array (Nat × Nat × List Nat) := #[
  (144115188075855904,1173505618863606016,[491,493,495,497,499,501]),
  (281494304063488,1317339312635398432,[495]),
  (281474976729088,1317339331962732832,[493]),
  (19327371264,1317620787612090656,[499,501]),
  (1152956688983130368,164664117956331552,[491,493]),
  (1099813748736,1317619707125713184,[491,493,495,497,501]),
  (137443672320,1317620669495789600,[491,493,495,497,499]),
  (20267298103230464,1297353508836231456,[495,497]),
  (20301382695387392,1297319424244074528,[493]),
  (0,0,[]),
  (144115188080066816,1173505618859395104,[491,493,495,497,501]),
  (1116959932448,1317619689979529472,[491,493,495,497,499]),
  (1297072014493747200,20548792445714720,[491,493,495,497,499]),
  (20266200470781984,1297354606468679936,[491,493,495,497,501]),
  (0,0,[]),
  (139590648064,1317620667348813856,[501]),
  (1116960065536,1317619689979396384,[499]),
  (20301522319589376,1297319284619872544,[493,501]),
  (0,0,[]),
  (0,0,[]),
  (20301400143693824,1297319406795768096,[491,493,495,497,499]),
  (1155208628379074816,162412178560387104,[491,493,495,497,501]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[]),
  (0,0,[])]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxesArithmetic121112 : ∀ (v m : Nat → ℤ) (u : Nat → Prop) i, i < boxTable121112.boxes.size →
    (∀ k ∈ (boxTable121112.atBox i).rules,
      boxedRule ((boxTable121112.atBox i).order boxTable121112.digit v) m ((boxTable121112.atBox i).sign boxTable121112.digit u) k) →
    (∀ k ∈ (boxTable121112.atBox i).bigger,1 < v k) → (∀ k ∈ boxTable121112.zeros,0 < v k) → False := by
  intro v m u i hi hr hb hz
  let j := i
  have eqs := ruleConj_of_mem hr
  simp [boxTable121112, List.forall_mem_cons] at hz
  have members := List.mem_range.mpr hi
  change i ∈ [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30] at members
  simp only [List.mem_cons,List.not_mem_nil,or_false] at members
  rcases members with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | (have small : ruleConj (disjointNonTriadRulesLinear (sparseVal v (valuationMasks121112[j]!).1 (valuationMasks121112[j]!).2.1) m u) (valuationMasks121112[j]!).2.2 := by
         simp [j,valuationMasks121112]
         exact eqs
       clear eqs hr
       simp [boxTable121112, BoxTable.atBox, List.forall_mem_cons] at hb
       simp (config := {decide := true}) [j,valuationMasks121112,ruleConj,disjointNonTriadRulesLinear,sparseVal] at small
       omega)
    | skip
  all_goals clear eqs
  all_goals simp [boxTable121112, BoxTable.atBox, List.forall_mem_cons] at hr hb hz
  all_goals simp [boxedRule, disjointNonTriadRulesLinear, packCoeffTriad, packCoeffTerm,
      packedTriad, packedVal, packedUnit, coeffOrder, coeffUnit, DigitBox.order, DigitBox.sign,
      BoxTable.digit, boxTable121112] at hr
  all_goals first
  | omega
  | grind (qlia := true) (ring := false) (ematch := 0) (splits := 28) (liaSteps := 30000)
  | grind (splits := 35) (liaSteps := 140000)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
private theorem boxTableValid121112 : boxTable121112.valid = true := by decide +kernel

theorem secondBoxImpossible121112 (v m : Nat → ℤ) (u : Nat → Prop)
    (rules : ∀ k, disjointRulesLinear v m u k)
    (first : ∀ k < 63, residueFacts (v k) (u k) (disjointResidueLinear 38 k))
    (t : Nat) (ht : t < 243)
    (actual : ∀ k < 63, liftedFacts (v k) (u k) (liftedResidue disjointResiduesLinear[38]! t k)) :
    False :=
  boxTable121112.impossible boxTableValid121112 boxesArithmetic121112 v m u rules first t ht actual

end PEqualNP.Outside.L_gct_234

namespace PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside.L_gct_234
open scoped Classical

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

noncomputable section

theorem disjointImpossibleOfStateConst (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) (D : PrimitiveCoordinates A) (far : ∀ q ∈ A.root, val q < 0)
    (a : Fin 13) (row : disjointDigits disjointResiduesConst[a.val]! = PadicInt.toZMod ∘ D.vars 0) :
    False := by

  let x := formValue disjointFormsConst (A.fieldVars 0)
  let v := val ∘ x
  let u := Negative ∘ x
  have nz : ∀ k, k < disjointFormsConst.size → x k ≠ 0 :=
    disjointFieldNonzeroConst A 0 D.start_zero (A.apart_constant disjoint)

  obtain ⟨h401, h403, h405, h406, h407, h409, h410, h411⟩ := disjointGeometryConst A disjoint sep geo D far (fun q h i j => D.far_root q (far q h) i j)

  obtain ⟨h422, h442⟩ := disjointNearestConst A disjoint sep geo D far

  have data : NonExtremaConst v u := ⟨h401, h403, h405, h406, h407, h409, h410, h411, h422, h442⟩
  have rules (k : Nat) : disjointRulesConst v (disjointAuxConst v) u k := by
    unfold disjointRulesConst
    split
    · rename_i q
      exact disjointTriadRealizedConst A 0 nz k q
    · exact derivedNonTriadConst v u data k
  have res := disjoint_const_residue_facts D a x row (fun _ _ => rfl) nz
  apply disjointImpossibleConst v (disjointAuxConst v) u rules a.val a.isLt res
  intro skipped
  have eqA : a = (2 : Fin 13) := Fin.ext skipped
  subst a
  obtain ⟨n, hn, lifted⟩ := lifted_const_row2_from_state D row nz
  exact disjointConstRow2Impossible v (disjointAuxConst v) u rules res n hn lifted

theorem disjointImpossibleOfStateLinear (A : APState) (disjoint : A.Disjoint) (sep : A.Separate)
    (geo : A.Geometric) (D : PrimitiveCoordinates A) (r : O) (rEq : A.root = some (r : K))
    (a : Fin 39) (row : disjointDigits disjointResiduesLinear[a.val]! = PadicInt.toZMod ∘ D.vars r) :
    False := by

  let x := formValue disjointFormsLinear (A.fieldVars r)
  let v := val ∘ x
  let u := Negative ∘ x
  have nz : ∀ k, k < disjointFormsLinear.size → x k ≠ 0 :=
    disjointFieldNonzeroLinear A r D.start_zero (A.apart_linear r disjoint sep rEq)

  obtain ⟨h491, h492, h493, h494, h495, h496, h497, h498, h499, h500, h501, h502⟩ := disjointGeometryLinear A disjoint sep geo D r rEq

  obtain ⟨h65, h66, h513, h524, h535⟩ := disjointNearestLinear A disjoint sep geo D r rEq

  have data : NonExtremaLinear v u := ⟨h65, h66, h491, h492, h493, h494, h495, h496, h497, h498, h499, h500, h501, h502, h513, h524, h535⟩
  have rules (k : Nat) : disjointRulesLinear v (disjointAuxLinear v) u k := by
    unfold disjointRulesLinear
    split
    · rename_i q
      exact disjointTriadRealizedLinear A r nz k q
    · exact derivedNonTriadLinear v u data k
  have res := disjoint_linear_residue_facts D r a x row (fun _ _ => rfl) nz
  apply disjointImpossibleLinear v (disjointAuxLinear v) u rules a.val a.isLt res
  intro skipped
  have pivotRows : ∀ q : Fin 39, q.val ∈ disjointSkippedLinear →
      rowForm disjointResiduesLinear[q.val]! 3 = 1 ∧ rowForm disjointResiduesLinear[q.val]! 0 = 0 := by
    decide +kernel
  have ⟨pivot, zero⟩ := pivotRows a skipped
  have cases : a.val = 3 ∨ a.val = 6 ∨ a.val = 7 ∨ a.val = 8 ∨ a.val = 15 ∨ a.val = 16 ∨ a.val = 18 ∨ a.val = 19 ∨ a.val = 20 ∨ a.val = 21 ∨ a.val = 36 ∨ a.val = 37 ∨ a.val = 38 := by
    simpa [disjointSkippedLinear] using skipped
  rcases cases with eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq | eq
  · have eqA : a = (3 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨e, he⟩ := disjoint_second_residue_facts D r (3 : Fin 39) row pivot zero nz
    exact disjointImpossibleLinear001100 v (disjointAuxLinear v) u rules res e he
  · have eqA : a = (6 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (6 : Fin 39) row pivot zero nz
    exact secondBoxImpossible001110 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (7 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (7 : Fin 39) row pivot zero nz
    exact secondBoxImpossible001111 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (8 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (8 : Fin 39) row pivot zero nz
    exact secondBoxImpossible001112 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (15 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (15 : Fin 39) row pivot zero nz
    exact secondBoxImpossible011100 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (16 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (16 : Fin 39) row pivot zero nz
    exact secondBoxImpossible011101 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (18 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (18 : Fin 39) row pivot zero nz
    exact secondBoxImpossible011110 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (19 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (19 : Fin 39) row pivot zero nz
    exact secondBoxImpossible011111 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (20 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (20 : Fin 39) row pivot zero nz
    exact secondBoxImpossible011112 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (21 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (21 : Fin 39) row pivot zero nz
    exact secondBoxImpossible101100 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (36 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (36 : Fin 39) row pivot zero nz
    exact secondBoxImpossible121110 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (37 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (37 : Fin 39) row pivot zero nz
    exact secondBoxImpossible121111 v (disjointAuxLinear v) u rules res n hn hnres
  · have eqA : a = (38 : Fin 39) := Fin.ext eq
    subst a
    obtain ⟨n, hn, hnres⟩ := lifted_facts_from_state D r (38 : Fin 39) row pivot zero nz
    exact secondBoxImpossible121112 v (disjointAuxLinear v) u rules res n hn hnres

theorem impossible_of_disjoint (A : APState) (disjoint : A.Disjoint) (sep : A.Separate) (geo : A.Geometric) : False := by
  obtain ⟨B,noCollision,sepB,geoB,⟨D⟩⟩ := A.primitive_state disjoint sep geo
  rcases dispatch_disjoint_root D noCollision with ⟨hr, a, row⟩ | ⟨r, rEq, a, row⟩
  · have far (q : K) (hq : q ∈ B.root) : val q < 0 := by
      rcases hr with h|⟨q',hq',neg⟩
      · simp [h] at hq
      · simp [hq'] at hq
        simpa [hq] using neg
    exact disjointImpossibleOfStateConst B noCollision sepB geoB D far a row
  · exact disjointImpossibleOfStateLinear B noCollision sepB geoB D r rEq a row

end

end PEqualNP.Outside.L_gct_234.Triadic.APState

open PEqualNP.Outside Polynomial

theorem PEqualNP.Outside.L_gct_234 : (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) → (∀ i, (g i).support.card ≤ 2) → ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 → ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9) := by
  intro s g sign sparse nonzero x pos
  apply L_gct_234.bound_of_table_obstruction _ s g sign sparse nonzero x pos
  intro σ a b m d hs nd U large A B constType h
  obtain ⟨T⟩ := L_gct_234.TableGeometry.exists_rational_table σ a b m d hs nd large A B constType h
  let G := L_gct_234.TableGeometry.initialState T
  by_cases disjoint : Function.Injective (L_gct_234.CubeAP.exponents m d)
  · obtain ⟨distinct, sep, geo⟩ := L_gct_234.TableGeometry.initial_disjoint_data T disjoint
    exact G.impossible_of_disjoint distinct sep geo
  · have dpos (i : Fin 3) := (nd i).1
    obtain ⟨l, r, coll, none, share, unit, total, geo⟩ :=
      L_gct_234.TableGeometry.initial_overlap_data T large dpos disjoint
    have step (i : Fin 3) : G.step i ≠ 0 := by
      change ((d i : ℕ) : PEqualNP.Outside.L_gct_234.Triadic.K) ≠ 0
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (dpos i))
    obtain ⟨G',⟨D⟩⟩ := G.normalized_overlap l r coll step none _ share unit total geo
    exact D.impossible
