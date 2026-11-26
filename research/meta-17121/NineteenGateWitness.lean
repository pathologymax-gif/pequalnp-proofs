import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Nineteen-gate witnesses for the four rows of PEqualNP L-meta-17121

Each list is evaluated as a sequence of 32-bit words. The check uses exactly
the earlier-input and error-mask conditions in the desk statement. Its
existential theorem confirms the attainable upper bound of 19 in every row.
Research contribution coordinated by Brett Snodgrass.
-/

namespace Meta17121Nineteen

abbrev Word := BitVec 32

def target : Word := 16383

def allowedStep (p : List Word) (v : Word) : Prop :=
  (∃ a ∈ p, ∃ b ∈ p, v = (a &&& b) ∨ v = (a ||| b)) ∧
    ∀ a ∈ p, ((a ^^^ target) &&& (v ^^^ target)) ≠ (a ^^^ target)

def checkedStep (p : List Word) (v : Word) : Bool :=
  (p.any fun a => p.any fun b => decide (v = (a &&& b) ∨ v = (a ||| b))) &&
    (p.all fun a => decide (((a ^^^ target) &&& (v ^^^ target)) ≠ (a ^^^ target)))

theorem step_sound (p : List Word) (v : Word) (h : checkedStep p v = true) :
    allowedStep p v := by
  simpa [checkedStep, allowedStep, List.any_eq_true, List.all_eq_true] using h

def checked (xs gates : List Word) : Bool :=
  (List.finRange gates.length).all fun i =>
    checkedStep (xs ++ gates.take i.val) (gates.get i)

theorem checked_sound (xs gates : List Word) (h : checked xs gates = true)
    (i : Fin gates.length) : allowedStep (xs ++ gates.take i.val) (gates.get i) := by
  exact step_sound _ _ (List.all_eq_true.mp h i (by simp))

def input0 : List Word :=
  [0, 2592243715, 133562380, 2844803120, 84754625, 403292932, 102861840, 1347294240, 1617961282, 2273325568, 4160751752]

def gates0 : List Word :=
  [1702715843, 1450155056, 1744183630, 3891671886, 2275524112, 2274194113, 134168781, 134204637, 3, 48, 772, 5120, 8256, 2184, 51, 823, 5943, 14199, 16383]

set_option maxHeartbeats 0 in
theorem check0 : checked input0 gates0 = true := by decide +kernel

def input1 : List Word :=
  [8372227, 0, 32849932, 714129456, 26198208, 101352196, 19074064, 340530208, 410001728, 562049537, 1040189578]

def gates1 : List Word :=
  [1065368203, 359603248, 435511628, 972387149, 564346385, 563081921, 33538252, 33541340, 3, 48, 772, 5120, 8256, 2184, 51, 823, 5943, 14199, 16383]

set_option maxHeartbeats 0 in
theorem check1 : checked input1 gates1 = true := by decide +kernel

def input2 : List Word :=
  [8372227, 1292189708, 0, 1418772528, 42631364, 202359552, 52628496, 676074528, 812654920, 1132474881, 2080376962]

def gates2 : List Word :=
  [2139110019, 728702000, 2104844620, 2104846798, 2085362850, 1292878604, 1334833933, 743429920, 3, 48, 196, 3072, 8456, 4608, 51, 247, 3319, 11775, 16383]

set_option maxHeartbeats 0 in
theorem check2 : checked input2 gates2 = true := by decide +kernel

def input3 : List Word :=
  [16760835, 353714188, 63750192, 0, 36339908, 70451984, 54774784, 213652480, 146809160, 318779905, 469764258]

def gates3 : List Word :=
  [520108707, 183149004, 197976440, 466416505, 323223041, 321565381, 65978612, 66047220, 3, 12, 784, 5120, 8256, 2208, 15, 799, 5919, 14175, 16383]

set_option maxHeartbeats 0 in
theorem check3 : checked input3 gates3 = true := by decide +kernel

def inputs : List (List Word) := [input0, input1, input2, input3]

theorem attainable_at_nineteen :
    ∀ xs ∈ inputs, ∃ gates : List Word,
      gates.length = 19 ∧
      (∀ i : Fin gates.length, allowedStep (xs ++ gates.take i.val) (gates.get i)) ∧
      target ∈ xs ++ gates := by
  intro xs hx
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact ⟨gates0, by decide, checked_sound _ _ check0, by decide +kernel⟩
  · exact ⟨gates1, by decide, checked_sound _ _ check1, by decide +kernel⟩
  · exact ⟨gates2, by decide, checked_sound _ _ check2, by decide +kernel⟩
  · exact ⟨gates3, by decide, checked_sound _ _ check3, by decide +kernel⟩

#print axioms attainable_at_nineteen

end Meta17121Nineteen
