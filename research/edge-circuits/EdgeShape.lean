import Std

/-!
# Read-once monotone formulas with two-variable minterms

Variables are leaf occurrences. The two subtrees at every binary node therefore
have disjoint variables. At an OR node a minterm comes from exactly one child.
At an AND node it consists of one minterm from each child. Consequently a pair
of OR trees joined by AND represents precisely one complete bipartite graph,
and OR combinations of such pairs are vertex-disjoint unions of bicliques.
-/

namespace EdgeShape

inductive Formula where
  | leaf
  | disj (left right : Formula)
  | conj (left right : Formula)

namespace Formula

def Term : Formula → Type
  | .leaf => Unit
  | .disj l r => Sum (Term l) (Term r)
  | .conj l r => Term l × Term r

def size : (f : Formula) → Term f → Nat
  | .leaf, _ => 1
  | .disj l _, .inl t => size l t
  | .disj _ r, .inr t => size r t
  | .conj l r, (s, t) => size l s + size r t

def witness : (f : Formula) → Term f
  | .leaf => ()
  | .disj l _ => .inl (witness l)
  | .conj l r => (witness l, witness r)

theorem size_pos (f : Formula) : ∀ t : Term f, 0 < size f t := by
  induction f with
  | leaf => intro t; exact Nat.zero_lt_succ 0
  | disj l r hl hr =>
    intro t
    cases t with
    | inl s => exact hl s
    | inr s => exact hr s
  | conj l r hl hr =>
    intro t
    rcases t with ⟨u, v⟩
    change 0 < size l u + size r v
    have hu := hl u
    omega

def Uniform (f : Formula) (n : Nat) : Prop :=
  ∀ t : Term f, size f t = n

theorem uniform_disj (l r : Formula) (n : Nat) :
    Uniform (.disj l r) n ↔ Uniform l n ∧ Uniform r n := by
  constructor
  · intro h
    exact ⟨fun t => h (.inl t), fun t => h (.inr t)⟩
  · rintro ⟨hl, hr⟩ t
    cases t with
    | inl s => exact hl s
    | inr s => exact hr s

def OrTree : Formula → Prop
  | .leaf => True
  | .disj l r => OrTree l ∧ OrTree r
  | .conj _ _ => False

theorem uniform_one_iff (f : Formula) : Uniform f 1 ↔ OrTree f := by
  induction f with
  | leaf =>
    constructor
    · intro h; trivial
    · intro h t; rfl
  | disj l r hl hr =>
    exact (uniform_disj l r 1).trans (and_congr hl hr)
  | conj l r _ _ =>
    constructor
    · intro h
      have eqn : size l (witness l) + size r (witness r) = 1 :=
        h (witness l, witness r)
      have hl := size_pos l (witness l)
      have hr := size_pos r (witness r)
      change False
      omega
    · intro h; exact False.elim h

theorem uniform_two_conj (l r : Formula) :
    Uniform (.conj l r) 2 ↔ Uniform l 1 ∧ Uniform r 1 := by
  constructor
  · intro h
    constructor
    · intro t
      have eqn : size l t + size r (witness r) = 2 := h (t, witness r)
      have hl := size_pos l t
      have hr := size_pos r (witness r)
      omega
    · intro t
      have eqn : size l (witness l) + size r t = 2 := h (witness l, t)
      have hl := size_pos l (witness l)
      have hr := size_pos r t
      omega
  · rintro ⟨hl, hr⟩ ⟨u, v⟩
    change size l u + size r v = 2
    rw [hl u, hr v]

def BicliqueUnion : Formula → Prop
  | .leaf => False
  | .disj l r => BicliqueUnion l ∧ BicliqueUnion r
  | .conj l r => OrTree l ∧ OrTree r

theorem uniform_two_iff_bicliqueUnion (f : Formula) :
    Uniform f 2 ↔ BicliqueUnion f := by
  induction f with
  | leaf =>
    constructor
    · intro h
      have eqn : 1 = 2 := h ()
      change False
      omega
    · intro h; exact False.elim h
  | disj l r hl hr =>
    exact (uniform_disj l r 2).trans (and_congr hl hr)
  | conj l r _ _ =>
    exact (uniform_two_conj l r).trans
      (and_congr (uniform_one_iff l) (uniform_one_iff r))

end Formula
end EdgeShape


namespace EdgeShape.Formula

/-- One Boolean input for every leaf position. -/
def Input : Formula → Type
  | .leaf => Bool
  | .disj l r => Input l × Input r
  | .conj l r => Input l × Input r

def Truth : (f : Formula) → Input f → Prop
  | .leaf, x => x = true
  | .disj l r, x => Truth l x.1 ∨ Truth r x.2
  | .conj l r, x => Truth l x.1 ∧ Truth r x.2

def zero : (f : Formula) → Input f
  | .leaf => false
  | .disj l r => (zero l, zero r)
  | .conj l r => (zero l, zero r)

/-- Characteristic vector of the leaf set in a term. -/
def mark : (f : Formula) → Term f → Input f
  | .leaf, _ => true
  | .disj l r, .inl t => (mark l t, zero r)
  | .disj l r, .inr t => (zero l, mark r t)
  | .conj l r, (s, t) => (mark l s, mark r t)

def weight : (f : Formula) → Input f → Nat
  | .leaf, x => Bool.toNat x
  | .disj l r, x => weight l x.1 + weight r x.2
  | .conj l r, x => weight l x.1 + weight r x.2

theorem weight_zero (f : Formula) : weight f (zero f) = 0 := by
  induction f <;> simp_all [weight, zero]

theorem weight_mark (f : Formula) : ∀ t : Term f, weight f (mark f t) = size f t := by
  induction f with
  | leaf => intro t; rfl
  | disj l r hl hr =>
    intro t
    cases t <;> simp [weight, mark, size, weight_zero, hl, hr]
  | conj l r hl hr =>
    rintro ⟨s, t⟩
    simp [weight, mark, size, hl, hr]

/-- Coordinatewise inclusion of the bits set to true. -/
def Below : (f : Formula) → Input f → Input f → Prop
  | .leaf, x, y => x = true → y = true
  | .disj l r, x, y => Below l x.1 y.1 ∧ Below r x.2 y.2
  | .conj l r, x, y => Below l x.1 y.1 ∧ Below r x.2 y.2

theorem below_refl (f : Formula) : ∀ x : Input f, Below f x x := by
  induction f with
  | leaf => intro x h; exact h
  | disj l r hl hr => intro x; exact ⟨hl x.1, hr x.2⟩
  | conj l r hl hr => intro x; exact ⟨hl x.1, hr x.2⟩

theorem below_trans (f : Formula) :
    ∀ {x y z : Input f}, Below f x y → Below f y z → Below f x z := by
  induction f with
  | leaf => intro x y z h k a; exact k (h a)
  | disj l r hl hr => intro x y z h k; exact ⟨hl h.1 k.1, hr h.2 k.2⟩
  | conj l r hl hr => intro x y z h k; exact ⟨hl h.1 k.1, hr h.2 k.2⟩

private theorem bool_antisymm (x y : Bool)
    (h : x = true → y = true) (k : y = true → x = true) : x = y := by
  cases x <;> cases y <;> simp_all

theorem below_antisymm (f : Formula) :
    ∀ {x y : Input f}, Below f x y → Below f y x → x = y := by
  induction f with
  | leaf => intro x y h k; exact bool_antisymm x y h k
  | disj l r hl hr => intro x y h k; exact Prod.ext (hl h.1 k.1) (hr h.2 k.2)
  | conj l r hl hr => intro x y h k; exact Prod.ext (hl h.1 k.1) (hr h.2 k.2)

theorem zero_below (f : Formula) : ∀ x : Input f, Below f (zero f) x := by
  induction f with
  | leaf => intro x; simp [Below, zero]
  | disj l r hl hr => intro x; exact ⟨hl x.1, hr x.2⟩
  | conj l r hl hr => intro x; exact ⟨hl x.1, hr x.2⟩

theorem not_truth_zero (f : Formula) : ¬ Truth f (zero f) := by
  induction f <;> simp_all [Truth, zero]

theorem truth_iff_contains (f : Formula) :
    ∀ x : Input f, Truth f x ↔ ∃ t : Term f, Below f (mark f t) x := by
  induction f with
  | leaf =>
    intro x
    constructor
    · exact fun h => ⟨(), fun _ => h⟩
    · rintro ⟨_, h⟩; exact h rfl
  | disj l r hl hr =>
    intro x
    constructor
    · rintro (h | h)
      · obtain ⟨t, ht⟩ := (hl x.1).mp h
        exact ⟨.inl t, ht, zero_below r x.2⟩
      · obtain ⟨t, ht⟩ := (hr x.2).mp h
        exact ⟨.inr t, zero_below l x.1, ht⟩
    · rintro ⟨t, ht⟩
      cases t with
      | inl u => exact Or.inl ((hl x.1).mpr ⟨u, ht.1⟩)
      | inr v => exact Or.inr ((hr x.2).mpr ⟨v, ht.2⟩)
  | conj l r hl hr =>
    intro x
    constructor
    · rintro ⟨a, b⟩
      obtain ⟨u, hu⟩ := (hl x.1).mp a
      obtain ⟨v, hv⟩ := (hr x.2).mp b
      exact ⟨(u, v), hu, hv⟩
    · rintro ⟨⟨u, v⟩, hu, hv⟩
      exact ⟨(hl x.1).mpr ⟨u, hu⟩, (hr x.2).mpr ⟨v, hv⟩⟩

theorem mark_not_below_zero (f : Formula) (t : Term f) : ¬ Below f (mark f t) (zero f) :=
  fun h => not_truth_zero f ((truth_iff_contains f (zero f)).mpr ⟨t, h⟩)

theorem mark_antichain (f : Formula) :
    ∀ s t : Term f, Below f (mark f s) (mark f t) → s = t := by
  induction f with
  | leaf => intro s t h; cases s; cases t; rfl
  | disj l r hl hr =>
    intro s t h
    cases s with
    | inl a =>
      cases t with
      | inl b => exact congrArg Sum.inl (hl a b h.1)
      | inr b => exact False.elim (mark_not_below_zero l a h.1)
    | inr a =>
      cases t with
      | inl b => exact False.elim (mark_not_below_zero r a h.2)
      | inr b => exact congrArg Sum.inr (hr a b h.2)
  | conj l r hl hr =>
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    exact Prod.ext (hl a c h.1) (hr b d h.2)

def MinimalTrue (f : Formula) (x : Input f) : Prop :=
  Truth f x ∧ ∀ y : Input f, Truth f y → Below f y x → Below f x y

theorem minimalTrue_iff_mark (f : Formula) (x : Input f) :
    MinimalTrue f x ↔ ∃ t : Term f, x = mark f t := by
  constructor
  · rintro ⟨hx, hmin⟩
    obtain ⟨t, ht⟩ := (truth_iff_contains f x).mp hx
    have truth_t := (truth_iff_contains f (mark f t)).mpr ⟨t, below_refl f _⟩
    exact ⟨t, below_antisymm f (hmin _ truth_t ht) ht⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(truth_iff_contains f _).mpr ⟨t, below_refl f _⟩, ?_⟩
    intro y hy hyt
    obtain ⟨s, hs⟩ := (truth_iff_contains f y).mp hy
    have hst := mark_antichain f s t (below_trans f hs hyt)
    cases hst
    exact hs

/-- An exact semantic criterion in terms of the ordinary minimal satisfying
Boolean assignments and the number of their true input bits. -/
theorem minimal_two_iff_bicliqueUnion (f : Formula) :
    (∀ x : Input f, MinimalTrue f x → weight f x = 2) ↔ BicliqueUnion f := by
  rw [← uniform_two_iff_bicliqueUnion]
  constructor
  · intro h t
    rw [← weight_mark]
    exact h _ ((minimalTrue_iff_mark f _).mpr ⟨t, rfl⟩)
  · intro h x hx
    obtain ⟨t, rfl⟩ := (minimalTrue_iff_mark f x).mp hx
    exact (weight_mark f t).trans (h t)

end EdgeShape.Formula

#print axioms EdgeShape.Formula.uniform_two_iff_bicliqueUnion
#print axioms EdgeShape.Formula.minimal_two_iff_bicliqueUnion
