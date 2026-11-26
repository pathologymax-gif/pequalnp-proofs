import Mathlib

namespace BackwardRectangles

variable {α : Type*} [DecidableEq α]

abbrev Word (α : Type*) := Finset α

structure Need (α : Type*) where
  yes : Word α
  no : Word α
  deriving DecidableEq

def Need.matches (r : Need α) (w : Word α) : Prop := r.yes ⊆ w ∧ Disjoint r.no w

def ready (ws : List (Word α)) (goals : List (Need α)) : Prop :=
  ∀ r ∈ goals, ∃ w ∈ ws, r.matches w

def pool : List (Need α) → Need α
  | [] => ⟨∅, ∅⟩
  | r :: rs => ⟨r.yes ∪ (pool rs).yes, r.no ∪ (pool rs).no⟩

theorem matches_pool (rs : List (Need α)) (w : Word α) :
    (pool rs).matches w ↔ ∀ r ∈ rs, r.matches w := by
  induction rs with
  | nil => simp [pool, Need.matches]
  | cons r rs ih =>
    simp only [pool, Need.matches, Finset.union_subset_iff, Finset.disjoint_union_left,
      List.forall_mem_cons] at *
    tauto

def gate (andGate : Bool) (x y : Word α) : Word α := if andGate then x ∩ y else x ∪ y

def splitNeed (andGate : Bool) (r : Need α) (mask : Word α) : Need α × Need α :=
  if andGate then (⟨r.yes, r.no ∩ mask⟩, ⟨r.yes, r.no \ mask⟩)
  else (⟨r.yes ∩ mask, r.no⟩, ⟨r.yes \ mask, r.no⟩)

theorem split_matches (b : Bool) (r : Need α) (x y : Word α) :
    r.matches (gate b x y) ↔ ∃ mask : Word α,
      (splitNeed b r mask).1.matches x ∧ (splitNeed b r mask).2.matches y := by
  cases b
  · constructor
    · intro h
      refine ⟨x, ?_⟩
      simp only [Need.matches, gate, splitNeed, Bool.false_eq_true, ite_false,
        Finset.subset_iff, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.disjoint_left] at *
      grind
    · rintro ⟨mask,h⟩
      simp only [Need.matches, gate, splitNeed, Bool.false_eq_true, ite_false,
        Finset.subset_iff, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
        Finset.disjoint_left] at *
      grind
  · constructor
    · intro h
      refine ⟨r.no \ x, ?_⟩
      simp only [Need.matches, gate, splitNeed, ite_true, Finset.subset_iff,
        Finset.mem_inter, Finset.mem_sdiff, Finset.disjoint_left] at *
      grind
    · rintro ⟨mask,h⟩
      simp only [Need.matches, gate, splitNeed, ite_true, Finset.subset_iff,
        Finset.mem_inter, Finset.mem_sdiff, Finset.disjoint_left] at *
      grind

inductive Forward (seeds : List (Word α)) : Nat → List (Word α) → Prop
  | start : Forward seeds 0 seeds
  | wait {n ws} : Forward seeds n ws → Forward seeds (n+1) ws
  | add {n ws x y} (b : Bool) : Forward seeds n ws → x ∈ ws → y ∈ ws →
      Forward seeds (n+1) (gate b x y :: ws)

inductive Back (seeds : List (Word α)) : Nat → List (Need α) → Prop
  | start {gs} : ready seeds gs → Back seeds 0 gs
  | wait {n gs} : Back seeds n gs → Back seeds (n+1) gs
  | split {n gs used keep} (b : Bool) (mask : Word α)
      (part : ∀ g, g ∈ gs ↔ g ∈ used ∨ g ∈ keep) :
      Back seeds n ((splitNeed b (pool used) mask).1 :: (splitNeed b (pool used) mask).2 :: keep) →
      Back seeds (n+1) gs

theorem forward_to_back {seeds : List (Word α)} {n ws} (f : Forward seeds n ws)
    (gs : List (Need α)) (h : ready ws gs) : Back seeds n gs := by
  classical
  induction f generalizing gs with
  | start => exact .start h
  | wait f ih => exact .wait (ih _ h)
  | @add n ws x y b f hx hy ih =>
    let used := gs.filter (fun g => decide (g.matches (gate b x y)))
    let keep := gs.filter (fun g => !decide (g.matches (gate b x y)))
    have part (g) : g ∈ gs ↔ g ∈ used ∨ g ∈ keep := by
      simp [used,keep]; tauto
    have hm : (pool used).matches (gate b x y) := by
      apply (matches_pool ..).mpr
      intro g hg
      exact of_decide_eq_true (List.mem_filter.mp hg).2
    obtain ⟨mask,hl,hr⟩ := (split_matches ..).mp hm
    apply Back.split b mask part
    apply ih
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨x,hx,hl⟩
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨y,hy,hr⟩
    have hk := List.mem_filter.mp hg
    obtain ⟨w,hw,hmw⟩ := h g hk.1
    rcases List.mem_cons.mp hw with rfl | hw
    · simp [hmw] at hk
    · exact ⟨w,hw,hmw⟩

theorem back_to_forward {seeds : List (Word α)} {n gs} (bwd : Back seeds n gs) :
    ∃ ws, Forward seeds n ws ∧ ready ws gs := by
  induction bwd with
  | start h => exact ⟨_,.start,h⟩
  | wait f ih => obtain ⟨ws,h,r⟩ := ih; exact ⟨ws,.wait h,r⟩
  | @split n gs used keep b mask part _ ih =>
    obtain ⟨ws,h,ready'⟩ := ih
    obtain ⟨x,hx,hmx⟩ := ready' (splitNeed b (pool used) mask).1 (by simp)
    obtain ⟨y,hy,hmy⟩ := ready' (splitNeed b (pool used) mask).2 (by simp)
    have hm := (split_matches b (pool used) x y).mpr ⟨mask,hmx,hmy⟩
    refine ⟨_,.add b h hx hy,?_⟩
    intro g hg
    rcases (part g).mp hg with hu | hk
    · exact ⟨_,List.mem_cons_self ..,(matches_pool ..).mp hm g hu⟩
    · obtain ⟨v,hv,hmv⟩ := ready' g (by simp [hk])
      exact ⟨v,List.mem_cons_of_mem _ hv,hmv⟩

theorem backward_iff_forward (seeds : List (Word α)) (n : Nat) (gs : List (Need α)) :
    Back seeds n gs ↔ ∃ ws, Forward seeds n ws ∧ ready ws gs :=
  ⟨back_to_forward,fun ⟨_,h,r⟩ => forward_to_back h _ r⟩

/-- Finite-test semantics of the 32-bit truth words from the assigned trace. -/
def bits (w : BitVec 32) : Word (Fin 32) := Finset.univ.filter (fun i => w.getLsbD i.val)

theorem bits_meet (x y : BitVec 32) : bits (x &&& y) = gate true (bits x) (bits y) := by
  ext i
  simp [bits,gate]

theorem bits_join (x y : BitVec 32) : bits (x ||| y) = gate false (bits x) (bits y) := by
  ext i
  simp [bits,gate]

def exactNeed (t : BitVec 32) : Need (Fin 32) := ⟨bits t, Finset.univ \ bits t⟩

theorem exact_matches (t : BitVec 32) (v : Word (Fin 32)) :
    (exactNeed t).matches v ↔ v = bits t := by
  simp only [exactNeed,Need.matches,Finset.subset_iff,Finset.disjoint_left,
    Finset.mem_sdiff,Finset.mem_univ,true_and]
  constructor
  · intro h
    ext i
    grind
  · rintro rfl
    grind

def wireTrace (z s : List (BitVec 32)) : Prop := ∀ j : Fin s.length,
  let ws := z ++ s.take j.val
  ∃ x ∈ ws, ∃ y ∈ ws, s.get j = x &&& y ∨ s.get j = x ||| y

theorem forward_of_word_trace {z s : List (BitVec 32)} (h : wireTrace z s) :
    Forward (z.map bits) s.length ((s.reverse ++ z).map bits) := by
  have acc (k : Nat) (hk : k ≤ s.length) :
      Forward (z.map bits) k (((s.take k).reverse ++ z).map bits) := by
    induction k with
    | zero => simpa using Forward.start (seeds := z.map bits)
    | succ k ih =>
      have hlt : k < s.length := by omega
      have prog := ih (by omega)
      obtain ⟨x,hx,y,hy,op⟩ := h ⟨k,hlt⟩
      have hx' : x ∈ (s.take k).reverse ++ z := by simpa [List.mem_append,or_comm] using hx
      have hy' : y ∈ (s.take k).reverse ++ z := by simpa [List.mem_append,or_comm] using hy
      have bx := List.mem_map_of_mem (f := bits) hx'
      have by' := List.mem_map_of_mem (f := bits) hy'
      rw [List.take_succ_eq_append_getElem hlt]
      rcases op with hxy | hxy
      · simpa [show s[k] = x &&& y from hxy,bits_meet] using Forward.add true prog bx by'
      · simpa [show s[k] = x ||| y from hxy,bits_join] using Forward.add false prog bx by'
  simpa using acc s.length (by rfl)

theorem backward_of_word_trace {z s : List (BitVec 32)} {t : BitVec 32}
    (h : wireTrace z s) (hit : t ∈ z ++ s) : Back (z.map bits) s.length [exactNeed t] := by
  apply forward_to_back (forward_of_word_trace h)
  intro g hg
  have ht : t ∈ s.reverse ++ z := by simpa [List.mem_append,or_comm] using hit
  have eqg : g = exactNeed t := by simpa using hg
  exact ⟨bits t,List.mem_map_of_mem (f := bits) ht,eqg ▸ (exact_matches t _).mpr rfl⟩

end BackwardRectangles

#print axioms BackwardRectangles.backward_iff_forward
#print axioms BackwardRectangles.backward_of_word_trace
