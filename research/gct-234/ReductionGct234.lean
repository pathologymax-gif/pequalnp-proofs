/-
Independent partial result for the open L-gct-234 assignment.
Brett Snodgrass and collaborating agents.
The support-cardinality argument adapts williamzheng0711's proof in
https://github.com/open-goat/pequalnp-proofs/pull/23279 at commit
623f0fcd3f27c6f292736e9949bf34727ae1ff07 (Apache-2.0).
The normalization and the statement combining the remaining cases appear here.
-/

import Mathlib
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.BigOperators

theorem PEqualNP.Outside.R_gct_234_1 :
  (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, (g i).support.card ≤ 2) →
    ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 →
    ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3).support.card = 11 →
    Polynomial.rootMultiplicity 1 ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9) →
  (∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ),
    (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, (g i).support.card ≤ 2) →
    ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 →
    12 ≤ ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3).support.card →
    Polynomial.rootMultiplicity 1 ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9) →
  ∀ (s : Fin 3 → ℝ) (g : Fin 3 → Polynomial ℝ), (∀ i, s i = 1 ∨ s i = -1) →
    (∀ i, (g i).support.card ≤ 2) →
    ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≠ 0 →
    ∀ x : ℝ, 0 < x → Polynomial.rootMultiplicity x ((Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3) ≤ 9 := by
  intro eleven twelve s g signs sparse nonzero x pos
  classical
  have variation (p : Polynomial ℝ) (hp : p ≠ 0) :
      p.signVariations < p.support.card := by
    have byCard (n : ℕ) : ∀ q : Polynomial ℝ, q.support.card = n →
        q ≠ 0 → q.signVariations < q.support.card := by
      induction n with
      | zero =>
        intro q hq hn
        exact (hn (Polynomial.card_support_eq_zero.mp hq)).elim
      | succ n ih =>
        intro q hq hn
        by_cases erased : q.eraseLead = 0
        · have mono := Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff q
          rw [erased, zero_add] at mono
          calc
            q.signVariations = 0 := by rw [← mono, Polynomial.signVariations_monomial]
            _ < q.support.card := hq ▸ Nat.succ_pos n
        · have count : q.eraseLead.support.card = n := by
            have eq := Polynomial.card_support_eraseLead_add_one hn
            omega
          have lower := ih q.eraseLead count erased
          have upper := Polynomial.signVariations_le_eraseLead_succ q
          omega
    exact byCard _ p rfl hp
  have support_scale (p : Polynomial ℝ) :
      (p.comp (Polynomial.C x * Polynomial.X)).support = p.support := by
    ext k
    simp [Polynomial.mem_support_iff, ne_of_gt pos]
  let G (i : Fin 3) := (g i).comp (Polynomial.C x * Polynomial.X)
  let P := (Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * g i ^ 3
  let Q := (Finset.univ : Finset (Fin 3)).sum fun i => Polynomial.C (s i) * G i ^ 3
  have scale : P.comp (Polynomial.C x * Polynomial.X) = Q := by
    simp [P, Q, G, Polynomial.sum_comp, Polynomial.mul_comp, Polynomial.pow_comp]
  have cardScale : Q.support = P.support := scale ▸ support_scale P
  have qnz : Q ≠ 0 := by
    intro h
    rw [h, Polynomial.support_zero] at cardScale
    exact nonzero (Polynomial.support_eq_empty.mp cardScale.symm)
  have gsparse : ∀ i, (G i).support.card ≤ 2 := fun i => by
    change ((g i).comp (Polynomial.C x * Polynomial.X)).support.card ≤ 2
    rw [support_scale]
    exact sparse i
  have multiplicity : Q.rootMultiplicity 1 = P.rootMultiplicity x := by
    rw [← scale]
    simpa using Polynomial.rootMultiplicity_comp_C_mul_X_add_C P x 0 1 (IsUnit.mk0 x (ne_of_gt pos))
  change P.rootMultiplicity x ≤ 9
  rw [← multiplicity]
  by_cases hsmall : Q.support.card ≤ 10
  · have posBound : Q.rootMultiplicity 1 ≤ Q.signVariations := by
      rw [← Polynomial.count_roots Q]
      calc
        Q.roots.count 1 = (Q.roots.filter (0 < ·)).count 1 :=
          (Multiset.count_filter_of_pos (show (0 : ℝ) < 1 by norm_num)).symm
        _ ≤ (Q.roots.filter (0 < ·)).card := Multiset.count_le_card _ _
        _ = Q.roots.countP (0 < ·) := (Multiset.countP_eq_card_filter _ _).symm
        _ ≤ Q.signVariations := Polynomial.roots_countP_pos_le_signVariations Q
    have strict := variation Q qnz
    omega
  · by_cases h11 : Q.support.card = 11
    · exact eleven s G signs gsparse qnz h11
    · exact twelve s G signs gsparse qnz (by omega : 12 ≤ Q.support.card)

#print axioms PEqualNP.Outside.R_gct_234_1

