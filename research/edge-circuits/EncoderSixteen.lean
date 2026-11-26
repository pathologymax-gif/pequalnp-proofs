import Mathlib
import PEqualNP.Defs


namespace PEqualNP.EncoderSignatures

def code (p : Fin 16) (b : Fin 4) : Bool := p.val.testBit b.val

theorem code_injective : Function.Injective code := by
  change ∀ ⦃p q : Fin 16⦄, code p = code q → p = q
  decide +kernel

theorem code_surjective : Function.Surjective code := by
  change ∀ z : Fin 4 → Bool, ∃ p : Fin 16, code p = z
  decide +kernel

theorem fifteen_codes (baseline : Fin 4 → Bool) :
    ∃ A : Finset (Fin 16), A.card = 15 ∧ ∀ p ∈ A, code p ≠ baseline := by
  obtain ⟨q, hq⟩ := code_surjective baseline
  refine ⟨Finset.univ.erase q, ?_, ?_⟩
  · simp
  · intro p hp he
    exact (Finset.mem_erase.mp hp).1 (code_injective (he.trans hq.symm))

def signature {W : Type*} (D : Finset W) (f baseline : W → Bool) : Finset W :=
  D.filter fun i => f i ≠ baseline i

theorem signature_self {W : Type*} (D : Finset W) (f : W → Bool) :
    signature D f f = ∅ := by
  simp [signature]

theorem frontier_agreement {W : Type*} {D : Finset W} {f g baseline : W → Bool}
    (h : signature D f baseline = signature D g baseline) :
    ∀ i ∈ D, f i = g i := by
  intro i hi
  have hx : i ∈ signature D f baseline ↔ i ∈ signature D g baseline := by rw [h]
  simp only [signature, Finset.mem_filter, hi, true_and] at hx
  cases hf : f i <;> cases hg : g i <;> cases hb : baseline i <;> simp_all

theorem output_eq_of_signature_eq {X Y W : Type*} {D : Finset W}
    (values : X → W → Bool) (output : X → Y) (baseline : W → Bool)
    (determines : ∀ a b, (∀ i ∈ D, values a i = values b i) → output a = output b)
    {a b : X} (h : signature D (values a) baseline = signature D (values b) baseline) :
    output a = output b :=
  determines a b (frontier_agreement h)

theorem signature_nonempty {X Y W : Type*} {D : Finset W}
    (values : X → W → Bool) (output : X → Y) (zero a : X)
    (determines : ∀ x y, (∀ i ∈ D, values x i = values y i) → output x = output y)
    (hne : output a ≠ output zero) :
    (signature D (values a) (values zero)).Nonempty := by
  by_contra h
  have he : signature D (values a) (values zero) = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp h
  exact hne (output_eq_of_signature_eq values output (values zero) determines
    (he.trans (signature_self D (values zero)).symm))

def singletonCount {X W : Type*} (A : Finset X) (records : X → Finset W) : ℕ :=
  (A.filter fun x => (records x).card = 1).card

theorem singletonCount_le {X W : Type*} (A : Finset X) (D : Finset W)
    (records : X → Finset W) (hinj : Set.InjOn records ↑A)
    (hsub : ∀ x ∈ A, records x ⊆ D) :
    singletonCount A records ≤ D.card := by
  classical
  let T := A.filter fun x => (records x).card = 1
  have hi : Set.InjOn records ↑T := hinj.mono (Finset.filter_subset _ _)
  have incl : T.image records ⊆ D.image (fun d => ({d} : Finset W)) := by
    intro u hu
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hxA, hx1⟩ := Finset.mem_filter.mp hx
    obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hx1
    have hmem : d ∈ records x := by simp [hd]
    exact Finset.mem_image.mpr ⟨d, hsub x hxA hmem, hd.symm⟩
  change T.card ≤ D.card
  calc
    T.card = (T.image records).card := (Finset.card_image_of_injOn hi).symm
    _ ≤ (D.image (fun d => ({d} : Finset W))).card := Finset.card_le_card incl
    _ ≤ D.card := Finset.card_image_le

theorem singletonCount_all {X W : Type*} (A : Finset X) (records : X → Finset W)
    (h : ∀ x ∈ A, (records x).card = 1) : singletonCount A records = A.card := by
  simp [singletonCount, Finset.filter_eq_self.mpr h]

theorem signature_oneHot {W : Type*} [DecidableEq W] (D : Finset W) (p : W) :
    signature D (fun i => decide (i = p)) (fun _ => false) =
      if p ∈ D then {p} else ∅ := by
  by_cases hp : p ∈ D
  · simp only [hp, ite_true]
    ext i
    by_cases hi : i = p <;> simp_all [signature]
  · simp only [hp, ite_false]
    ext i
    by_cases hi : i = p <;> simp_all [signature]

end PEqualNP.EncoderSignatures

namespace PEqualNP.EncoderPotential

/-- Replacing a live gate by up to two operands adds at most one to the sum
of frontier size and number of singleton one-hot difference patterns. -/
theorem reverse_step {X W : Type*} [DecidableEq W]
    (A : Finset X) (C I : Finset W) (w : W) (old fresh : X → Finset W)
    (wout : w ∉ C) (arity : I.card ≤ 2)
    (nonempty : ∀ x ∈ A, (old x).Nonempty)
    (oldsub : ∀ x ∈ A, old x ⊆ insert w C)
    (agree : ∀ x ∈ A, ∀ j ∈ C, j ∈ old x ↔ j ∈ fresh x)
    (changed : ∀ x ∈ A, w ∈ old x → ∃ j ∈ I, j ∈ fresh x)
    (distinct : Set.InjOn fresh ↑A) :
    (C ∪ I).card + (A.filter (fun x => (fresh x).card = 1)).card ≤
      (insert w C).card + (A.filter (fun x => (old x).card = 1)).card + 1 := by
  classical
  let S := A.filter (fun x => (fresh x).card = 1)
  let T := A.filter (fun x => (old x).card = 1)
  let N := S \ T
  have newSingleton (x : X) (hx : x ∈ N) :
      ∃ j ∈ C ∩ I, fresh x = {j} := by
    have hxS : x ∈ S := (Finset.mem_sdiff.mp hx).1
    obtain ⟨hxA, h1⟩ := Finset.mem_filter.mp hxS
    have hnot : (old x).card ≠ 1 := by
      intro hc
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_filter.mpr ⟨hxA, hc⟩)
    have hpos := Finset.card_pos.mpr (nonempty x hxA)
    have htwo : 2 ≤ (old x).card := by omega
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h1
    have hw : w ∈ old x := by
      by_contra h
      have hsub : old x ⊆ fresh x := by
        intro v hv
        rcases Finset.mem_insert.mp (oldsub x hxA hv) with rfl | hvc
        · exact False.elim (h hv)
        · exact (agree x hxA v hvc).mp hv
      have := Finset.card_le_card hsub
      omega
    obtain ⟨i, hiI, hi⟩ := changed x hxA hw
    have hij : i = j := by simpa [hj] using hi
    subst i
    have hjC : j ∈ C := by
      by_contra hjC
      have hsub : old x ⊆ {w} := by
        intro v hv
        rcases Finset.mem_insert.mp (oldsub x hxA hv) with hvw | hvc
        · simpa using hvw
        · have hvj : v = j := by simpa [hj] using (agree x hxA v hvc).mp hv
          exact False.elim (hjC (hvj ▸ hvc))
      have hh := Finset.card_le_card hsub
      simp at hh
      omega
    exact ⟨j, Finset.mem_inter.mpr ⟨hjC, hiI⟩, hj⟩
  have subsetA : N ⊆ A := fun x hx =>
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp hx).1).1
  have hinj : Set.InjOn fresh ↑N := distinct.mono subsetA
  have himage : N.image fresh ⊆ (C ∩ I).image (fun j => ({j} : Finset W)) := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, hj, heq⟩ := newSingleton x hx
    exact Finset.mem_image.mpr ⟨j, hj, heq.symm⟩
  have hN : N.card ≤ (C ∩ I).card := calc
    N.card = (N.image fresh).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ ((C ∩ I).image (fun j => ({j} : Finset W))).card := Finset.card_le_card himage
    _ ≤ (C ∩ I).card := Finset.card_image_le
  have hsub : S ⊆ T ∪ N := by
    intro x hx
    by_cases ht : x ∈ T
    · exact Finset.mem_union_left _ ht
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, ht⟩)
  have hS := (Finset.card_le_card hsub).trans (Finset.card_union_le T N)
  have hCI := Finset.card_union_add_card_inter C I
  have hw := Finset.card_insert_of_notMem wout
  change (C ∪ I).card + S.card ≤ (insert w C).card + T.card + 1
  omega

end PEqualNP.EncoderPotential

namespace PEqualNP.EncoderInduction

open PEqualNP.EncoderSignatures PEqualNP.EncoderPotential

def determines {X Y : Type*} (values : X → ℕ → Bool) (output : X → Y) (D : Finset ℕ) : Prop :=
  ∀ a b, (∀ i ∈ D, values a i = values b i) → output a = output b

def potential {X : Type*} (A : Finset X) (values : X → ℕ → Bool) (zero : X)
    (D : Finset ℕ) : ℕ :=
  D.card + singletonCount A (fun x => signature D (values x) (values zero))

/-- Follow all observed wires backwards to the raw inputs, with the total
increase in potential bounded by the number of gates. -/
theorem backwards {X Y : Type*} (n : ℕ) (A : Finset X) (values : X → ℕ → Bool)
    (output : X → Y) (zero : X) (ins : ℕ → Finset ℕ) (gates : ℕ)
    (out_inj : Set.InjOn output ↑A) (out_ne : ∀ a ∈ A, output a ≠ output zero)
    (arity : ∀ k < gates, (ins k).card ≤ 2)
    (earlier : ∀ k < gates, ins k ⊆ Finset.range (n+k))
    (respect : ∀ k < gates, ∀ a b, (∀ i ∈ ins k, values a i = values b i) →
      values a (n+k) = values b (n+k))
    (D : Finset ℕ) (bounded : D ⊆ Finset.range (n+gates))
    (det : determines values output D) :
    ∃ P ⊆ Finset.range n, determines values output P ∧
      potential A values zero P ≤ potential A values zero D + gates := by
  classical
  induction gates generalizing D with
  | zero => exact ⟨D, by simpa using bounded, det, by omega⟩
  | succ k ih =>
    have hk : k < k+1 := by omega
    have descend := fun E (hb : E ⊆ Finset.range (n+k)) (hd : determines values output E) =>
      ih (fun i hi => arity i (by omega)) (fun i hi => earlier i (by omega))
        (fun i hi => respect i (by omega)) E hb hd
    let w := n+k
    let C := D.erase w
    have hc : C ⊆ Finset.range w := by
      intro i hi
      obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hi
      have hlt := Finset.mem_range.mp (bounded hmem)
      apply Finset.mem_range.mpr
      dsimp [w] at *
      omega
    by_cases hw : w ∈ D
    · let I := ins k
      let E := C ∪ I
      have hI : I ⊆ Finset.range w := earlier k hk
      have hb : E ⊆ Finset.range (n+k) := Finset.union_subset hc hI
      have he : insert w C = D := Finset.insert_erase hw
      have hwC : w ∉ C := Finset.notMem_erase _ _
      have hr : determines values output E := by
        intro a b ha
        apply det a b
        intro j hj
        by_cases hjw : j = w
        · subst j
          exact respect k hk a b (fun v hv => ha v (Finset.mem_union_right _ hv))
        · exact ha j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hjw,hj⟩))
      let old := fun x => signature D (values x) (values zero)
      let fresh := fun x => signature E (values x) (values zero)
      have hdis : Set.InjOn fresh ↑A := by
        intro x hx y hy hxy
        exact out_inj hx hy (output_eq_of_signature_eq values output (values zero) hr hxy)
      have hchg : ∀ x ∈ A, w ∈ old x → ∃ j ∈ I, j ∈ fresh x := by
        intro x hx hwx
        by_contra nh
        have hxw := (Finset.mem_filter.mp hwx).2
        apply hxw
        apply respect k hk
        intro j hj
        by_contra hne
        exact nh ⟨j, hj, Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hj, hne⟩⟩
      have step := reverse_step A C I w old fresh hwC (arity k hk)
        (fun x hx => signature_nonempty values output zero x det (out_ne x hx))
        (fun x _ => by rw [he]; exact Finset.filter_subset _ _)
        (fun x _ j hj => by
          have hD : j ∈ D := (Finset.mem_erase.mp hj).2
          have hE : j ∈ E := Finset.mem_union_left _ hj
          simp [old, fresh, signature, hD, hE])
        hchg hdis
      rw [he] at step
      obtain ⟨P, hp, hd, hh⟩ := descend E hb hr
      refine ⟨P, hp, hd, ?_⟩
      change potential A values zero E ≤ potential A values zero D + 1 at step
      omega
    · have he : C = D := Finset.erase_eq_of_notMem hw
      obtain ⟨P, hp, hd, hh⟩ := descend D (he ▸ hc) det
      exact ⟨P, hp, hd, by omega⟩

end PEqualNP.EncoderInduction

namespace PEqualNP.EncoderWireSemantics

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun ws gate => ws ++ [gate.op.eval (gate.inputs.map fun i => ws.getD i false)]) xs

theorem run_eq_circuit_wires (C : Circuit) (xs : List Bool) : run C.gates xs = C.wires xs := rfl

theorem run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (xs ++ [_])).length = _
    rw [ih]
    simp
    omega

theorem run_snoc (gs : List Gate) (g : Gate) (xs : List Bool) :
    run (gs ++ [g]) xs = run gs xs ++ [g.op.eval (g.inputs.map fun i => (run gs xs).getD i false)] := by
  simp [run, List.foldl_append]

theorem snoc_getD (ws : List Bool) (b : Bool) (i : ℕ) :
    (ws ++ [b]).getD i false = if i = ws.length then b else ws.getD i false := by
  induction ws generalizing i with
  | nil => cases i <;> simp [List.getD]
  | cons a ws ih =>
    cases i with
    | zero => simp [List.getD]
    | succ i => simpa [List.getD] using ih i

theorem missing_getD (ws : List Bool) {i : ℕ} (h : ws.length ≤ i) :
    ws.getD i false = false := by
  simp [List.getD, List.getElem?_eq_none h]

def operands (w : ℕ) (g : Gate) : Finset ℕ :=
  g.inputs.toFinset.filter fun i => i < w

theorem operands_card (w : ℕ) (g : Gate) (hg : g.inputs.length ≤ 2) :
    (operands w g).card ≤ 2 :=
  (Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans hg)

theorem operand_agreement (gs : List Gate) (g : Gate) (x y : List Bool)
    (hlen : y.length = x.length)
    (h : ∀ i ∈ operands (x.length + gs.length) g,
      (run gs x).getD i false = (run gs y).getD i false) :
    g.op.eval (g.inputs.map fun i => (run gs x).getD i false) =
      g.op.eval (g.inputs.map fun i => (run gs y).getD i false) := by
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i hi
  by_cases hb : i < x.length + gs.length
  · exact h i (by simp [operands, hi, hb])
  · rw [missing_getD _ (by rw [run_length]; omega), missing_getD _ (by rw [run_length]; omega)]

def previous (D : Finset ℕ) (w : ℕ) (g : Gate) : Finset ℕ :=
  if w ∈ D then D.erase w ∪ operands w g else D

theorem backstep (gs : List Gate) (g : Gate) (x y : List Bool) (D : Finset ℕ)
    (hlen : y.length = x.length)
    (h : ∀ i ∈ previous D (x.length + gs.length) g,
      (run gs x).getD i false = (run gs y).getD i false) :
    ∀ i ∈ D, (run (gs ++ [g]) x).getD i false = (run (gs ++ [g]) y).getD i false := by
  intro i hi
  simp only [run_snoc, snoc_getD, run_length, hlen]
  by_cases he : i = x.length + gs.length
  · subst i
    simp only [ite_true]
    apply operand_agreement gs g x y hlen
    intro j hj
    apply h
    simp [previous, hi, hj]
  · simp only [he, ite_false]
    apply h
    by_cases hw : x.length + gs.length ∈ D <;> simp [previous, hw, he, hi]

theorem changed_operand (gs : List Gate) (g : Gate) (x y : List Bool)
    (hlen : y.length = x.length)
    (hne : (run (gs ++ [g]) x).getD (x.length + gs.length) false ≠
      (run (gs ++ [g]) y).getD (x.length + gs.length) false) :
    ∃ i ∈ operands (x.length + gs.length) g,
      (run gs x).getD i false ≠ (run gs y).getD i false := by
  by_contra! h
  apply hne
  simp only [run_snoc, snoc_getD, run_length, hlen, ite_true]
  exact operand_agreement gs g x y hlen h

theorem prefix_read (pre post : List Gate) (x : List Bool) (i : ℕ)
    (hi : i < x.length + pre.length) :
    (run (pre ++ post) x).getD i false = (run pre x).getD i false := by
  induction post generalizing pre with
  | nil => simp
  | cons g post ih =>
    have hl : i < x.length + (pre ++ [g]).length := by simp; omega
    rw [show pre ++ g :: post = (pre ++ [g]) ++ post by simp,
      ih (pre ++ [g]) hl, run_snoc, snoc_getD, run_length]
    simp [Nat.ne_of_lt hi]

theorem raw_wire (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  simpa [run] using prefix_read [] gs x i (by simpa using hi)

theorem full_missing (gs : List Gate) (x : List Bool) (i : ℕ)
    (hi : x.length + gs.length ≤ i) : (run gs x).getD i false = false :=
  missing_getD _ (by rwa [run_length])

theorem full_respects_split (pre post : List Gate) (g : Gate) (x y : List Bool)
    (hlen : y.length = x.length)
    (h : ∀ i ∈ operands (x.length + pre.length) g,
      (run (pre ++ g :: post) x).getD i false = (run (pre ++ g :: post) y).getD i false) :
    (run (pre ++ g :: post) x).getD (x.length + pre.length) false =
      (run (pre ++ g :: post) y).getD (x.length + pre.length) false := by
  have hpre : ∀ i ∈ operands (x.length + pre.length) g,
      (run pre x).getD i false = (run pre y).getD i false := by
    intro i hi
    have hb := (Finset.mem_filter.mp hi).2
    simpa only [prefix_read pre (g :: post) x i hb,
      prefix_read pre (g :: post) y i (by simpa [hlen] using hb)] using h i hi
  have h1 : x.length + pre.length < x.length + (pre ++ [g]).length := by simp
  have h2 : x.length + pre.length < y.length + (pre ++ [g]).length := by simp [hlen]
  rw [show pre ++ g :: post = (pre ++ [g]) ++ post by simp,
    prefix_read (pre ++ [g]) post x _ h1, prefix_read (pre ++ [g]) post y _ h2]
  simp only [run_snoc, snoc_getD, run_length, hlen, ite_true]
  exact operand_agreement pre g x y hlen hpre

theorem full_gate_respects (gs : List Gate) {n j : ℕ} (hj : j < gs.length)
    (x y : List Bool) (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ operands (n+j) gs[j], (run gs x).getD i false = (run gs y).getD i false) :
    (run gs x).getD (n+j) false = (run gs y).getD (n+j) false := by
  let pre := gs.take j
  let post := gs.drop (j+1)
  have split : pre ++ gs[j] :: post = gs := by
    rw [show gs[j] :: post = gs.drop j from (List.drop_eq_getElem_cons hj).symm]
    exact List.take_append_drop j gs
  have plen : pre.length = j := by simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
  have step := full_respects_split pre post gs[j] x y (hy.trans hx.symm)
  simpa only [split, plen, hx] using (step (by simpa only [split, plen, hx] using h))

theorem operands_prior (w : ℕ) (g : Gate) {i : ℕ} (hi : i ∈ operands w g) : i < w :=
  (Finset.mem_filter.mp hi).2

theorem oneHot_getD {n : ℕ} (p : Fin n) (i : ℕ) :
    (List.ofFn (fun q : Fin n => decide (q = p))).getD i false = decide (i = p.val) := by
  by_cases hi : i < n
  · simp [List.getD, hi, Fin.ext_iff]
  · have hn : i ≠ p.val := by intro h; subst i; exact hi p.isLt
    simp [List.getD, hi, hn]

theorem zero_getD (n i : ℕ) :
    (List.ofFn (fun _ : Fin n => false)).getD i false = false := by
  by_cases hi : i < n <;> simp [List.getD, hi]

end PEqualNP.EncoderWireSemantics

namespace PEqualNP.EncoderConclusion

open PEqualNP.CircuitLowerBounds PEqualNP.EncoderSignatures PEqualNP.EncoderInduction
  PEqualNP.EncoderWireSemantics

private def query : Option (Fin 16) → List Bool
  | none => List.ofFn (fun _ : Fin 16 => false)
  | some p => List.ofFn (fun q : Fin 16 => decide (q = p))

private theorem query_len (x : Option (Fin 16)) : (query x).length = 16 := by
  cases x <;> simp [query]

theorem gate_lower (C : Circuit) (fan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (rep : ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false =
        Nat.testBit p.val v.val) : 22 ≤ C.size := by
  classical
  choose obs hobs using rep
  let values := fun (x : Option (Fin 16)) (j : ℕ) => (run C.gates (query x)).getD j false
  let output := fun (x : Option (Fin 16)) (b : Fin 4) => values x (obs b)
  have hot (p : Fin 16) : output (some p) = code p := funext (fun b => hobs b p)
  obtain ⟨B, hB, hne⟩ := fifteen_codes (output none)
  let A := B.image some
  have hA : A.card = 15 := by
    simpa only [A, Finset.card_image_of_injective _ (Option.some_injective _)] using hB
  have injA : Set.InjOn output ↑A := by
    intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact congrArg some (code_injective ((hot p).symm.trans (hxy.trans (hot q))))
  have neA : ∀ x ∈ A, output x ≠ output none := by
    intro x hx he
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact hne p hp ((hot p).symm.trans he)
  let ins := fun k => if h : k < C.gates.length then operands (16+k) C.gates[k] else ∅
  have hi (k : ℕ) (hk : k < C.gates.length) : ins k = operands (16+k) C.gates[k] := by
    simp [ins, hk]
  have arity : ∀ k < C.gates.length, (ins k).card ≤ 2 := by
    intro k hk
    rw [hi k hk]
    exact operands_card _ _ (fan _ (List.getElem_mem ..))
  have earlier : ∀ k < C.gates.length, ins k ⊆ Finset.range (16+k) := by
    intro k hk j hj
    exact Finset.mem_range.mpr (operands_prior _ _ ((hi k hk) ▸ hj))
  have respect : ∀ k < C.gates.length, ∀ a b,
      (∀ i ∈ ins k, values a i = values b i) → values a (16+k) = values b (16+k) := by
    intro k hk a b h
    exact full_gate_respects C.gates hk _ _ (query_len a) (query_len b) ((hi k hk) ▸ h)
  let S := Finset.univ.image obs
  let D := S.filter (fun j => j < 16+C.gates.length)
  have Dsize : D.card ≤ 4 := by
    calc
      D.card ≤ S.card := Finset.card_filter_le _ _
      _ ≤ (Finset.univ : Finset (Fin 4)).card := Finset.card_image_le
      _ = 4 := by decide
  have BD : D ⊆ Finset.range (16+C.gates.length) := by
    intro j hj
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2
  have det : determines values output D := by
    intro a b hw
    funext v
    by_cases h : obs v < 16+C.gates.length
    · exact hw _ (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩, h⟩)
    · have miss (x) : values x (obs v) = false :=
        full_missing _ _ _ (by rw [query_len]; omega)
      exact (miss a).trans (miss b).symm
  have count_le (E : Finset ℕ) (de : determines values output E) :
      singletonCount A (fun x => signature E (values x) (values none)) ≤ E.card := by
    apply singletonCount_le
    · intro x hx y hy hh
      exact injA hx hy (output_eq_of_signature_eq values output (values none) de hh)
    · intro x hx
      exact Finset.filter_subset _ _
  obtain ⟨P, hP, dp, bound⟩ :=
    backwards 16 A values output none ins C.gates.length injA neA arity earlier respect D BD det
  have raw (p : Fin 16) :
      signature P (values (some p)) (values none) =
        if p.val ∈ P then {p.val} else ∅ := by
    rw [← signature_oneHot]
    ext j
    by_cases hj : j ∈ P
    · have jlt := Finset.mem_range.mp (hP hj)
      have hp : values (some p) j = decide (j = p.val) :=
        (raw_wire _ _ j (by rw [query_len]; exact jlt)).trans (oneHot_getD p j)
      have hz : values none j = false :=
        (raw_wire _ _ j (by rw [query_len]; exact jlt)).trans (zero_getD 16 j)
      simp [signature, hj, hp, hz]
    · simp [signature, hj]
  have all1 : ∀ x ∈ A, (signature P (values x) (values none)).card = 1 := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have nne := signature_nonempty values output none (some p) dp
      (neA _ (Finset.mem_image.mpr ⟨p,hp,rfl⟩))
    rw [raw] at nne ⊢
    split <;> simp_all
  have card := singletonCount_all A _ all1
  have hps := count_le P dp
  have hds := count_le D det
  change P.card + _ ≤ D.card + _ + C.gates.length at bound
  change 22 ≤ C.gates.length
  omega

end PEqualNP.EncoderConclusion

namespace PEqualNP.EncoderConclusion

open PEqualNP.CircuitLowerBounds

theorem no_encoder_21 : ¬ ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 21 ∧
    ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false =
        Nat.testBit p.val v.val := by
  rintro ⟨C, hC, hc, h⟩
  have bound := gate_lower C (fun g hg => (hC g hg).2) h
  omega

private def positiveCircuit : Circuit :=
  ⟨[⟨.or, [14, 15]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [10, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [19, 16]⟩,
    ⟨.or, [1, 15]⟩,
    ⟨.or, [21, 7]⟩,
    ⟨.or, [22, 11]⟩,
    ⟨.or, [23, 13]⟩,
    ⟨.or, [24, 3]⟩,
    ⟨.or, [25, 5]⟩,
    ⟨.or, [26, 9]⟩,
    ⟨.or, [2, 16]⟩,
    ⟨.or, [28, 3]⟩,
    ⟨.or, [29, 17]⟩,
    ⟨.or, [30, 18]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [32, 17]⟩,
    ⟨.or, [33, 20]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [35, 18]⟩,
    ⟨.or, [36, 20]⟩], 27⟩

theorem positive_at_22 :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 22 ∧
      ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val := by
  refine ⟨positiveCircuit, ?_, by decide +kernel, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, positiveCircuit,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro v
    fin_cases v
    · exact ⟨27, by decide +kernel⟩
    · exact ⟨31, by decide +kernel⟩
    · exact ⟨34, by decide +kernel⟩
    · exact ⟨37, by decide +kernel⟩

private def bipolarCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [16, 2]⟩,
    ⟨.or, [17, 3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [19, 6]⟩,
    ⟨.or, [20, 7]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.or, [22, 10]⟩,
    ⟨.or, [23, 11]⟩,
    ⟨.or, [12, 13]⟩,
    ⟨.or, [25, 14]⟩,
    ⟨.or, [26, 15]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [28, 8]⟩,
    ⟨.or, [29, 12]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [31, 9]⟩,
    ⟨.or, [32, 13]⟩,
    ⟨.or, [2, 6]⟩,
    ⟨.or, [34, 10]⟩,
    ⟨.or, [35, 14]⟩,
    ⟨.or, [3, 7]⟩,
    ⟨.or, [37, 11]⟩,
    ⟨.or, [38, 15]⟩,
    ⟨.or, [33, 39]⟩,
    ⟨.or, [30, 36]⟩,
    ⟨.or, [36, 39]⟩,
    ⟨.or, [30, 33]⟩,
    ⟨.or, [21, 27]⟩,
    ⟨.or, [18, 24]⟩,
    ⟨.or, [24, 27]⟩,
    ⟨.or, [18, 21]⟩], 40⟩

theorem bipolar_at_32 :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size = 32 ∧
      ∀ v : Fin 4, (∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = Nat.testBit p.val v.val) ∧ (∃ w : ℕ, ∀ p : Fin 16,
      (C.wires (List.ofFn (fun q : Fin 16 => decide (q = p)))).getD w false = !(Nat.testBit p.val v.val)) := by
  refine ⟨bipolarCircuit, ?_, by decide +kernel, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2, bipolarCircuit,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro v
    fin_cases v
    · exact ⟨⟨40, by decide +kernel⟩, ⟨41, by decide +kernel⟩⟩
    · exact ⟨⟨42, by decide +kernel⟩, ⟨43, by decide +kernel⟩⟩
    · exact ⟨⟨44, by decide +kernel⟩, ⟨45, by decide +kernel⟩⟩
    · exact ⟨⟨46, by decide +kernel⟩, ⟨47, by decide +kernel⟩⟩

end PEqualNP.EncoderConclusion
