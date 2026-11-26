import Std

/-!
# A single Boolean wire across a graph partition

If every influence of the inside inputs on the edge-existence function passes
through one Boolean signal, any crossing edge forces the inside graph to be
independent. All crossing edges form a complete bipartite graph on their
supports. Up to negation, the wire is the OR of the inside vertices in that
support. Without isolated inside vertices it is the OR of every inside input.

The proof allows the signal and downstream Boolean computation to be arbitrary.
The result is conditional on the single-wire factorization. Applying it to a
particular circuit DAG requires identifying a cut with that property.
-/

namespace OneWire

universe u v
variable {S : Type u} {T : Type v}

def empty {A : Type u} : A → Prop := fun _ => False
def one {A : Type u} (a : A) : A → Prop := fun x => x = a

def internal {A : Type u} (edge : A → A → Prop) (X : A → Prop) : Prop :=
  ∃ a, X a ∧ ∃ b, X b ∧ edge a b

def crossing (E : S → T → Prop) (X : S → Prop) (Y : T → Prop) : Prop :=
  ∃ a, X a ∧ ∃ b, Y b ∧ E a b

def edgeFn (R : S → S → Prop) (E : S → T → Prop) (U : T → T → Prop)
    (X : S → Prop) (Y : T → Prop) : Prop :=
  internal R X ∨ crossing E X Y ∨ internal U Y

/-- Downstream computation cannot distinguish two inside assignments that put
the same Boolean value on the wire. -/
def OneSignal (R : S → S → Prop) (E : S → T → Prop) (U : T → T → Prop)
    (wire : (S → Prop) → Bool) : Prop :=
  ∀ X Z, wire X = wire Z → ∀ Y, edgeFn R E U X Y ↔ edgeFn R E U Z Y

theorem oneSignal_of_factorization
    {R : S → S → Prop} {E : S → T → Prop} {U : T → T → Prop}
    {wire : (S → Prop) → Bool} (readout : Bool → (T → Prop) → Prop)
    (h : ∀ X Y, edgeFn R E U X Y ↔ readout (wire X) Y) :
    OneSignal R E U wire := by
  intro X Z eq Y
  rw [h X Y, h Z Y, eq]

private theorem two_values {a b : Bool} (hab : a ≠ b) (x : Bool) : x = a ∨ x = b := by
  cases a <;> cases b <;> cases x <;> simp_all

theorem crossing_forces_biclique
    {R : S → S → Prop} {E : S → T → Prop} {U : T → T → Prop}
    (noLoopS : ∀ s, ¬ R s s) (noLoopT : ∀ t, ¬ U t t)
    {a : S} {b : T} (ab : E a b)
    (wire : (S → Prop) → Bool) (hwire : OneSignal R E U wire) :
    (∀ s t, ¬ R s t) ∧
    (∀ s t, E s t ↔ E s b ∧ E a t) ∧
    (∀ X, wire X = wire (one a) ↔ ∃ s, X s ∧ E s b) := by
  have singles (s : S) (t : T) : edgeFn R E U (one s) (one t) ↔ E s t := by
    simp [edgeFn, internal, crossing, one, noLoopS, noLoopT]
  have blankAt (t : T) : ¬ edgeFn R E U empty (one t) := by
    simp [edgeFn, internal, crossing, one, empty, noLoopT]
  have different : wire empty ≠ wire (one a) := by
    intro eq
    exact blankAt b ((hwire empty (one a) eq (one b)).mpr ((singles a b).mpr ab))
  have noInternal (X : S → Prop) : ¬ internal R X := by
    intro hx
    have output : edgeFn R E U X empty := Or.inl hx
    rcases two_values different (wire X) with hz | ha
    · have bad := (hwire X empty hz empty).mp output
      simp [edgeFn, internal, crossing, empty] at bad
    · have bad := (hwire X (one a) ha empty).mp output
      simp [edgeFn, internal, crossing, empty, one, noLoopS] at bad
  have independent (s t : S) : ¬ R s t :=
    fun h => noInternal (fun _ => True) ⟨s, trivial, t, trivial, h⟩
  have atPort (X : S → Prop) :
      edgeFn R E U X (one b) ↔ ∃ s, X s ∧ E s b := by
    change (internal R X ∨ crossing E X (one b) ∨ internal U (one b)) ↔ _
    simp only [noInternal X, false_or]
    simp [crossing, internal, one, noLoopT]
  have encodes (X : S → Prop) :
      wire X = wire (one a) ↔ ∃ s, X s ∧ E s b := by
    constructor
    · intro eq
      exact (atPort X).mp ((hwire X (one a) eq (one b)).mpr ((singles a b).mpr ab))
    · intro hx
      rcases two_values different (wire X) with hz | ha
      · exact False.elim (blankAt b ((hwire X empty hz (one b)).mp ((atPort X).mpr hx)))
      · exact ha
  refine ⟨independent, ?_, encodes⟩
  intro s t
  have signalOn : wire (one s) = wire (one a) ↔ E s b := by
    simpa [one] using encodes (one s)
  constructor
  · intro st
    rcases two_values different (wire (one s)) with hz | ha
    · exact False.elim (blankAt t ((hwire _ _ hz (one t)).mp ((singles s t).mpr st)))
    · exact ⟨signalOn.mp ha, (singles a t).mp
        ((hwire _ _ ha (one t)).mp ((singles s t).mpr st))⟩
  · rintro ⟨sb, at'⟩
    exact (singles s t).mp
      ((hwire _ _ (signalOn.mpr sb) (one t)).mpr ((singles a t).mpr at'))

/-- Conversely, a crossing rectangle and independence give an explicit
factorization of the graph function into the two port disjunctions. -/
theorem edgeFn_of_rectangle
    {R : S → S → Prop} {E : S → T → Prop} {U : T → T → Prop}
    {a : S} {b : T}
    (indep : ∀ s t, ¬ R s t)
    (rect : ∀ s t, E s t ↔ E s b ∧ E a t)
    (X : S → Prop) (Y : T → Prop) :
    edgeFn R E U X Y ↔
      ((∃ s, X s ∧ E s b) ∧ (∃ t, Y t ∧ E a t)) ∨ internal U Y := by
  constructor
  · rintro (⟨s, _, t, _, st⟩ | ⟨s, hs, t, ht, st⟩ | hy)
    · exact False.elim (indep s t st)
    · obtain ⟨sb, at'⟩ := (rect s t).mp st
      exact Or.inl ⟨⟨s, hs, sb⟩, ⟨t, ht, at'⟩⟩
    · exact Or.inr hy
  · rintro (⟨⟨s, hs, sb⟩, ⟨t, ht, at'⟩⟩ | hy)
    · exact Or.inr (Or.inl ⟨s, hs, t, ht, (rect s t).mpr ⟨sb, at'⟩⟩)
    · exact Or.inr (Or.inr hy)

/-- Complete characterization for a specified wire and a nonempty crossing. -/
theorem oneSignal_iff
    {R : S → S → Prop} {E : S → T → Prop} {U : T → T → Prop}
    (noLoopS : ∀ s, ¬ R s s) (noLoopT : ∀ t, ¬ U t t)
    {a : S} {b : T} (ab : E a b) (wire : (S → Prop) → Bool) :
    OneSignal R E U wire ↔
    ((∀ s t, ¬ R s t) ∧
     (∀ s t, E s t ↔ E s b ∧ E a t) ∧
     (∀ X, wire X = wire (one a) ↔ ∃ s, X s ∧ E s b)) := by
  refine ⟨crossing_forces_biclique noLoopS noLoopT ab wire, ?_⟩
  rintro ⟨indep, rect, encodes⟩ X Z eq Y
  have same : (∃ s, X s ∧ E s b) ↔ ∃ s, Z s ∧ E s b := by
    rw [← encodes X, ← encodes Z, eq]
  rw [edgeFn_of_rectangle indep rect X Y, edgeFn_of_rectangle indep rect Z Y, same]

theorem nonisolated_inside_vertices
    {R : S → S → Prop} {E : S → T → Prop} {U : T → T → Prop}
    (noLoopS : ∀ s, ¬ R s s) (noLoopT : ∀ t, ¬ U t t)
    {a : S} {b : T} (ab : E a b)
    (covered : ∀ s, (∃ v, R s v ∨ R v s) ∨ ∃ t, E s t)
    (wire : (S → Prop) → Bool) (hwire : OneSignal R E U wire) :
    (∀ s t, ¬ R s t) ∧ (∀ s t, E s t ↔ E a t) ∧
    (∀ X, wire X = wire (one a) ↔ ∃ s, X s) := by
  obtain ⟨indep, rect, encodes⟩ := crossing_forces_biclique noLoopS noLoopT ab wire hwire
  have active (s : S) : E s b := by
    rcases covered s with ⟨v, sv | vs⟩ | ⟨t, st⟩
    · exact False.elim (indep s v sv)
    · exact False.elim (indep v s vs)
    · exact ((rect s t).mp st).1
  refine ⟨indep, ?_, ?_⟩
  · intro s t
    simp [rect s t, active s]
  · intro X
    refine (encodes X).trans ⟨?_, ?_⟩
    · rintro ⟨s, h, _⟩; exact ⟨s, h⟩
    · rintro ⟨s, h⟩; exact ⟨s, h, active s⟩

end OneWire

#print axioms OneWire.oneSignal_of_factorization
#print axioms OneWire.crossing_forces_biclique
#print axioms OneWire.edgeFn_of_rectangle
#print axioms OneWire.oneSignal_iff
#print axioms OneWire.nonisolated_inside_vertices
