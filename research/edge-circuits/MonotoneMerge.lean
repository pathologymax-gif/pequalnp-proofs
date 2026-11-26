import Std

/-!
# Removing a complemented signal at an AND/OR reconvergence

The complementary and positive arms receive independent private inputs X and Y.
The complemented arm must be sensitive to its signal at one setting of X. If
the merged output is nondecreasing in the shared signal at every X and Y,
then the other arm masks a constant replacement of the complemented signal.
The converse masking criterion and the replacement identity are both proved.
-/

namespace MonotoneMerge

inductive Gate where
  | both
  | either

def Gate.eval : Gate → Bool → Bool → Bool
  | .both, l, r => l && r
  | .either, l, r => l || r

def Gate.absorber : Gate → Bool
  | .both => false
  | .either => true

def Below (a b : Bool) : Prop := a = true → b = true

variable {X Y : Type}

def merge (g : Gate) (A : Bool → X → Bool) (B : Bool → Y → Bool)
    (z : Bool) (x : X) (y : Y) : Bool :=
  g.eval (A (!z) x) (B z y)

def Rising (g : Gate) (A : Bool → X → Bool) (B : Bool → Y → Bool) : Prop :=
  ∀ x y, Below (merge g A B false x y) (merge g A B true x y)

def Sensitive (A : Bool → X → Bool) : Prop :=
  ∃ x, A false x = false ∧ A true x = true

theorem rising_iff_mask
    (g : Gate) (A : Bool → X → Bool) (B : Bool → Y → Bool)
    (sensitive : Sensitive A) :
    Rising g A B ↔ ∀ y, B g.absorber y = g.absorber := by
  obtain ⟨witness, off, onValue⟩ := sensitive
  cases g with
  | either =>
    constructor
    · intro rises y
      have lo : merge .either A B false witness y = true := by
        simp [merge, Gate.eval, onValue]
      have hi := rises witness y lo
      simpa [merge, Gate.eval, off, Gate.absorber] using hi
    · intro mask x y _
      have hi : B true y = true := mask y
      simp [merge, Gate.eval, hi]
  | both =>
    constructor
    · intro rises y
      change B false y = false
      cases h : B false y with
      | false => rfl
      | true =>
        have lo : merge .both A B false witness y = true := by
          simp [merge, Gate.eval, onValue, h]
        have hi := rises witness y lo
        simp [merge, Gate.eval, off] at hi
    · intro mask x y low
      have lo : B false y = false := mask y
      simp [merge, Gate.eval, lo] at low

/-- Replacing NOT(z) by the absorbing constant for the merge gate preserves
the output for every assignment, including private inputs outside the witness. -/
theorem replace_complement
    (g : Gate) (A : Bool → X → Bool) (B : Bool → Y → Bool)
    (sensitive : Sensitive A) (rises : Rising g A B) :
    ∀ z x y, merge g A B z x y = g.eval (A g.absorber x) (B z y) := by
  have mask := (rising_iff_mask g A B sensitive).mp rises
  intro z x y
  cases g with
  | either =>
    have m : B true y = true := mask y
    cases z <;> simp [merge, Gate.eval, Gate.absorber, m]
  | both =>
    have m : B false y = false := mask y
    cases z <;> simp [merge, Gate.eval, Gate.absorber, m]

/-- A path from one variable through a positive read-once formula. Each layer
has its own disjoint side input, represented here by its Boolean output. -/
inductive Path where
  | hole
  | layer (gate : Gate) (inner : Path)

def Path.Private : Path → Type
  | .hole => Unit
  | .layer _ inner => inner.Private × Bool

def Path.eval : (p : Path) → Bool → p.Private → Bool
  | .hole, z, _ => z
  | .layer g inner, z, x => g.eval (inner.eval z x.1) x.2

def Path.neutral : (p : Path) → p.Private
  | .hole => ()
  | .layer g inner => (inner.neutral, !g.absorber)

theorem Path.eval_neutral (p : Path) (z : Bool) : p.eval z p.neutral = z := by
  induction p with
  | hole => rfl
  | layer g inner ih =>
    cases g <;> simp [Path.eval, Path.neutral, Gate.absorber, Gate.eval, ih]

theorem Path.sensitive (p : Path) : Sensitive p.eval :=
  ⟨p.neutral, p.eval_neutral false, p.eval_neutral true⟩

/-- The comparison at the merge follows from monotonicity of the whole output
when an increasing upstream pair realizes 0 and 1 and a common outer setting
transmits the merge unchanged at either Boolean value. -/
theorem rising_of_sensitized_context
    {W O : Type} (g : Gate) (A : Bool → X → Bool) (B : Bool → Y → Bool)
    (up : W → Bool) (outer : O → Bool → Bool) (canIncrease : W → W → Prop)
    (realizes : ∃ lo hi, canIncrease lo hi ∧ up lo = false ∧ up hi = true)
    (transmits : ∃ o, ∀ z, outer o z = z)
    (globalRise : ∀ lo hi, canIncrease lo hi → ∀ o x y,
      Below (outer o (merge g A B (up lo) x y)) (outer o (merge g A B (up hi) x y))) :
    Rising g A B := by
  obtain ⟨lo, hi, le, atLo, atHi⟩ := realizes
  obtain ⟨o, neutral⟩ := transmits
  intro x y
  simpa only [atLo, atHi, neutral] using globalRise lo hi le o x y

end MonotoneMerge

#print axioms MonotoneMerge.rising_iff_mask
#print axioms MonotoneMerge.replace_complement
#print axioms MonotoneMerge.Path.sensitive
#print axioms MonotoneMerge.rising_of_sensitized_context
