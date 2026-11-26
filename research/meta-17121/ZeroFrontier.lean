import Mathlib

namespace ZeroFrontier

abbrev W := BitVec 32
abbrev I := Fin 32
def bit (w : W) (p : I) := w.getLsbD p.val
def target : W := 16383
def full (w : W) : Bool := (w &&& target) == target
def good (q : I) (w : W) : Prop := bit w q = false ∧ full w = true
def cost (q : I) (w : W) : Nat := if bit w q then 0 else 1
def badCost (q : I) (w : W) : Nat := if bit w q || full w then 0 else 1

theorem no_first_meet {q x y} (h : good q (x &&& y)) : good q x ∨ good q y := by
  obtain ⟨hz,hf⟩ := h
  have eq : (x &&& y) &&& target = target := by simpa [full] using hf
  have ex : x &&& target = target := by
    calc x &&& target = x &&& ((x &&& y) &&& target) := by rw [eq]
         _ = (x &&& y) &&& target := by rw [← BitVec.and_assoc, ← BitVec.and_assoc, BitVec.and_self]
         _ = target := eq
  have ey : y &&& target = target := by
    calc y &&& target = y &&& ((x &&& y) &&& target) := by rw [eq]
         _ = (y &&& y) &&& (x &&& target) := by ac_rfl
         _ = (x &&& y) &&& target := by rw [BitVec.and_self]; ac_rfl
         _ = target := eq
  cases hq : bit x q with
  | false => exact Or.inl ⟨hq,by simpa [full] using ex⟩
  | true =>
    have hx : x.getLsbD q.val = true := hq
    exact Or.inr ⟨by simpa [bit,hx] using hz,by simpa [full] using ey⟩

inductive Run (z : List W) (q : I) : Nat → Nat → List W → Prop
  | start : Run z q 0 0 z
  | meet {a b ws x y} : Run z q a b ws → x ∈ ws → y ∈ ws →
      Run z q a b ((x &&& y)::ws)
  | join {a b ws x y} : Run z q a b ws → x ∈ ws → y ∈ ws →
      Run z q (a+cost q (x ||| y)) (b+badCost q (x ||| y)) ((x ||| y)::ws)

def frontier (q : I) (ws : List W) (f : Finset W) : Prop :=
  (∀ w ∈ f, w ∈ ws) ∧ (∀ w ∈ f, bit w q = false) ∧
    ∀ p, bit target p = true → ∃ w ∈ f, bit w p = true

theorem skip {q ws w f} (h : frontier q (w::ws) f) (hn : w ∉ f) : frontier q ws f := by
  refine ⟨?_,h.2⟩
  intro v hv
  rcases List.mem_cons.mp (h.1 v hv) with rfl | hh
  · exact False.elim (hn hv)
  · exact hh

theorem replace {q ws w f} (h : frontier q (w::ws) f) (hw : w ∈ f) (g : Finset W)
    (hg : ∀ z ∈ g, z ∈ ws) (hz : ∀ z ∈ g, bit z q = false)
    (hc : ∀ p, bit w p = true → ∃ z ∈ g, bit z p = true) :
    ∃ f', frontier q ws f' ∧ f'.card+1 ≤ f.card+g.card := by
  refine ⟨f.erase w ∪ g,⟨?_,?_,?_⟩,?_⟩
  · intro z hmem
    rcases Finset.mem_union.mp hmem with he | he
    · have hh := Finset.mem_erase.mp he
      exact (List.mem_cons.mp (h.1 z hh.2)).resolve_left hh.1
    · exact hg z he
  · intro z hmem
    rcases Finset.mem_union.mp hmem with he | he
    · exact h.2.1 z (Finset.mem_erase.mp he).2
    · exact hz z he
  · intro p hp
    obtain ⟨z,hz',hbit⟩ := h.2.2 p hp
    by_cases ze : z = w
    · subst z
      obtain ⟨y,hy,yp⟩ := hc p hbit
      exact ⟨y,Finset.mem_union_right _ hy,yp⟩
    · exact ⟨z,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ze,hz'⟩),hbit⟩
  · have h1 := Finset.card_union_le (f.erase w) g
    have h2 := Finset.card_erase_add_one hw
    omega

theorem extract {q z a b ws} (run : Run z q a b ws) (f : Finset W) (h : frontier q ws f) :
    ∃ g, frontier q z g ∧ g.card ≤ f.card+a := by
  induction run generalizing f with
  | start => exact ⟨f,h,by omega⟩
  | @meet a b ws x y run hx hy ih =>
    by_cases hw : x &&& y ∈ f
    · have zxy := h.2.1 _ hw
      have pick : ∃ v ∈ ws, bit v q = false ∧ ∀ p, bit (x &&& y) p = true → bit v p = true := by
        cases he : bit x q with
        | false => exact ⟨x,hx,he,fun p hp => (by simpa [bit] using hp : bit x p = true ∧ bit y p = true).1⟩
        | true =>
          have hxe : x.getLsbD q.val = true := he
          refine ⟨y,hy,by simpa [bit,hxe] using zxy,?_⟩
          intro p hp
          exact (by simpa [bit] using hp : bit x p = true ∧ bit y p = true).2
      obtain ⟨v,hv,hq,hh⟩ := pick
      obtain ⟨f',hf',hc⟩ := replace h hw {v} (by simpa using hv) (by simpa using hq)
        (by simpa using hh)
      obtain ⟨g,hg,bound⟩ := ih f' hf'
      exact ⟨g,hg,by simp at hc; omega⟩
    · exact ih f (skip h hw)
  | @join a b ws x y run hx hy ih =>
    by_cases hw : x ||| y ∈ f
    · have zxy := h.2.1 _ hw
      have h0 : bit x q = false ∧ bit y q = false := by simpa [bit] using zxy
      obtain ⟨f',hf',hc⟩ := replace h hw {x,y} (by simp [hx,hy]) (by simp [h0])
        (by intro p hp; simpa [bit] using hp)
      have hcard : ({x,y} : Finset W).card ≤ 2 := Finset.card_le_two
      obtain ⟨g,hg,bound⟩ := ih f' hf'
      exact ⟨g,hg,by simp [cost,zxy]; omega⟩
    · obtain ⟨g,hg,bound⟩ := ih f (skip h hw)
      exact ⟨g,hg,by omega⟩

def seeds : Fin 4 → List W := ![
  [0,2592243715,133562380,2844803120,84754625,403292932,102861840,1347294240,1617961282,2273325568,4160751752],
  [8372227,0,32849932,714129456,26198208,101352196,19074064,340530208,410001728,562049537,1040189578],
  [8372227,1292189708,0,1418772528,42631364,202359552,52628496,676074528,812654920,1132474881,2080376962],
  [16760835,353714188,63750192,0,36339908,70451984,54774784,213652480,146809160,318779905,469764258]]
def qrow : Fin 4 → I := ![14,25,20,27]
def forced (i : Fin 4) := (seeds i).filter (fun w => w != 0 && !bit w (qrow i))

def checked (i : Fin 4) := decide ((forced i).toFinset.card = 7) &&
  (forced i).all (fun w => (List.finRange 32).any fun p => bit target p &&
    (seeds i).all (fun s => decide (bit s (qrow i) = false → bit s p = true → s=w)))

theorem four_checked : ∀ i : Fin 4, checked i = true := by decide +kernel

theorem seven_le (i : Fin 4) {f : Finset W} (h : frontier (qrow i) (seeds i) f) : 7 ≤ f.card := by
  obtain ⟨card,chk⟩ := Bool.and_eq_true_iff.mp (four_checked i)
  have sub : (forced i).toFinset ⊆ f := by
    intro w hw
    obtain ⟨p,_,yes⟩ := List.any_eq_true.mp (List.all_eq_true.mp chk w (by simpa using hw))
    obtain ⟨pos,allSeeds⟩ := Bool.and_eq_true_iff.mp yes
    obtain ⟨z,hz,ze⟩ := h.2.2 p pos
    have eq := of_decide_eq_true (List.all_eq_true.mp allSeeds z (h.1 z hz)) (h.2.1 z hz) ze
    exact eq ▸ hz
  simpa [of_decide_eq_true card] using Finset.card_le_card sub

theorem singleton_frontier {q ws w} (hw : w ∈ ws) (h : good q w) : frontier q ws {w} := by
  refine ⟨by simpa using hw,by simpa using h.1,?_⟩
  intro p hp
  have eq : w &&& target = target := of_decide_eq_true (by simpa [full] using h.2)
  have he := congrArg (fun t => bit t p) eq
  refine ⟨w,by simp,?_⟩
  simpa [bit,show target.getLsbD p.val = true from hp] using he

theorem six_zero_OR (i : Fin 4) {a b ws w} (p : Run (seeds i) (qrow i) a b ws)
    (hw : w ∈ ws) (hgood : good (qrow i) w) : 6 ≤ a := by
  obtain ⟨g,hg,hb⟩ := extract p {w} (singleton_frontier hw hgood)
  have hs := seven_le i hg
  simp at hb
  omega

theorem before_good {z q a b ws} (p : Run z q a b ws) (h : ∀ w ∈ ws, ¬ good q w) : a=b := by
  induction p with
  | start => rfl
  | meet _ _ _ ih => exact ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
  | @join a b ws x y run hx hy ih =>
    have he := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    have hn := h _ (List.mem_cons_self ..)
    cases hq : bit (x ||| y) q <;> cases hf : full (x ||| y) <;> simp_all [cost,badCost,good]

theorem five_bad_OR (i : Fin 4) {a b ws} (p : Run (seeds i) (qrow i) a b ws)
    (hit : ∃ w ∈ ws, good (qrow i) w) : 5 ≤ b := by
  classical
  induction p with
  | start =>
    obtain ⟨w,hw,hg⟩ := hit
    have hs := six_zero_OR i (.start) hw hg
    omega
  | @meet a b ws x y run hx hy ih =>
    by_cases prev : ∃ w ∈ ws, good (qrow i) w
    · exact ih prev
    · obtain ⟨w,hw,hg⟩ := hit
      have hs := six_zero_OR i (.meet run hx hy) hw hg
      have eq := before_good run (by simpa using prev)
      omega
  | @join a b ws x y run hx hy ih =>
    by_cases prev : ∃ w ∈ ws, good (qrow i) w
    · have hh := ih prev
      omega
    · obtain ⟨w,hw,hg⟩ := hit
      have hs := six_zero_OR i (.join run hx hy) hw hg
      have eq := before_good run (by simpa using prev)
      have hc : cost (qrow i) (x ||| y) ≤ 1 := by unfold cost; split <;> omega
      omega

def wireTrace (z s : List W) : Prop := ∀ j : Fin s.length,
  let ws := z ++ s.take j.val
  ∃ x ∈ ws, ∃ y ∈ ws, s.get j = x &&& y ∨ s.get j = x ||| y

theorem run_of_trace {z s : List W} (q : I) (h : wireTrace z s) :
    ∃ a b, Run z q a b (s.reverse ++ z) := by
  have acc (k : Nat) (hk : k ≤ s.length) : ∃ a b, Run z q a b ((s.take k).reverse ++ z) := by
    induction k with
    | zero => exact ⟨0,0,by simpa using Run.start (z := z) (q := q)⟩
    | succ k ih =>
      have hlt : k < s.length := by omega
      obtain ⟨a,b,prog⟩ := ih (by omega)
      obtain ⟨x,hx,y,hy,op⟩ := h ⟨k,hlt⟩
      have hx' : x ∈ (s.take k).reverse ++ z := by simpa [List.mem_append,or_comm] using hx
      have hy' : y ∈ (s.take k).reverse ++ z := by simpa [List.mem_append,or_comm] using hy
      rw [List.take_succ_eq_append_getElem hlt]
      rcases op with hxy | hxy
      · exact ⟨_,_,by simpa [show s[k] = x &&& y from hxy] using Run.meet prog hx' hy'⟩
      · exact ⟨_,_,by simpa [show s[k] = x ||| y from hxy] using Run.join prog hx' hy'⟩
  simpa using acc s.length (by rfl)

theorem assigned_frontier_counts (i : Fin 4) (s : List W) (tr : wireTrace (seeds i) s)
    (hit : target ∈ seeds i ++ s) :
    ∃ a b, Run (seeds i) (qrow i) a b (s.reverse ++ seeds i) ∧ 6 ≤ a ∧ 5 ≤ b := by
  obtain ⟨a,b,prog⟩ := run_of_trace (qrow i) tr
  have hg : good (qrow i) target := by unfold good; fin_cases i <;> decide +kernel
  have hw : target ∈ s.reverse ++ seeds i := by simpa [List.mem_append,or_comm] using hit
  exact ⟨a,b,prog,six_zero_OR i prog hw hg,five_bad_OR i prog ⟨_,hw,hg⟩⟩

end ZeroFrontier

#print axioms ZeroFrontier.six_zero_OR
#print axioms ZeroFrontier.five_bad_OR
#print axioms ZeroFrontier.assigned_frontier_counts
