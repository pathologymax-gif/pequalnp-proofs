import Mathlib

namespace AndSignature

abbrev W := BitVec 32
abbrev I := Fin 32
def bit (w : W) (i : I) := w.getLsbD i.val

/-- The index counts AND gates. An OR gate can reuse any earlier wires for free. -/
inductive Run (seeds : List W) : Nat → List W → Prop
  | start : Run seeds 0 seeds
  | join {n ws x y} : Run seeds n ws → x ∈ ws → y ∈ ws → Run seeds n ((x ||| y)::ws)
  | meet {n ws x y} : Run seeds n ws → x ∈ ws → y ∈ ws → Run seeds (n+1) ((x &&& y)::ws)

def Good (seeds : List W) (c : I → Nat) (w : W) : Prop :=
  ∀ p q r, c q = c r → bit w p = true → bit w q = false → bit w r = false →
    ∃ z ∈ seeds, bit z p = true ∧ bit z q = false ∧ bit z r = false

def refineColor (c : I → Nat) (x : W) (q : I) : Nat := 2*c q + (bit x q).toNat

theorem refine_eq {c : I → Nat} {x : W} {q r : I}
    (h : refineColor c x q = refineColor c x r) : c q = c r ∧ bit x q = bit x r := by
  unfold refineColor at h
  cases hq : bit x q <;> cases hr : bit x r <;> simp [hq,hr] at h ⊢ <;> omega

theorem colors {seeds : List W} {n ws} (run : Run seeds n ws) :
    ∃ c : I → Nat, (∀ q, c q < 2^n) ∧ ∀ w ∈ ws, Good seeds c w := by
  induction run with
  | start =>
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro w hw p q r _ hp hq hr
    exact ⟨w,hw,hp,hq,hr⟩
  | @join n ws x y run hx hy ih =>
    obtain ⟨c,cb,cg⟩ := ih
    refine ⟨c,cb,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · intro p q r he hp hq hr
      simp [bit] at hp hq hr
      rcases hp with hp | hp
      · exact cg x hx p q r he hp hq.1 hr.1
      · exact cg y hy p q r he hp hq.2 hr.2
    · exact cg w hw
  | @meet n ws x y run hx hy ih =>
    obtain ⟨c,cb,cg⟩ := ih
    refine ⟨refineColor c x,?_,?_⟩
    · intro q
      have hc := cb q
      simp only [refineColor,pow_succ]
      cases bit x q <;> simp <;> omega
    · intro w hw p q r he hp hq hr
      obtain ⟨hc,hxqr⟩ := refine_eq he
      rcases List.mem_cons.mp hw with rfl | hw
      · simp [bit] at hp hq hr
        cases hxb : bit x q with
        | false => exact cg x hx p q r hc hp.1 hxb (hxqr.symm.trans hxb)
        | true =>
          have xq : x.getLsbD q.val = true := hxb
          have xr : x.getLsbD r.val = true := hxqr.symm.trans hxb
          exact cg y hy p q r hc hp.2 (by simpa [bit,xq] using hq) (by simpa [bit,xr] using hr)
      · exact cg w hw p q r hc hp hq hr

def separated (seeds : List W) (target : W) {m : Nat} (row : Fin m → I) : Prop :=
  ∀ q r : Fin m, q ≠ r → ∃ p : I, bit target p = true ∧ bit target (row q) = false ∧
    bit target (row r) = false ∧ ∀ z ∈ seeds,
      bit z p = true → bit z (row q) = true ∨ bit z (row r) = true

theorem separated_le_pow {seeds : List W} {n ws target m} (row : Fin m → I)
    (run : Run seeds n ws) (hit : target ∈ ws) (sep : separated seeds target row) : m ≤ 2^n := by
  obtain ⟨c,cb,cg⟩ := colors run
  let key (q : Fin m) : Fin (2^n) := ⟨c (row q),cb _⟩
  have inj : Function.Injective key := by
    intro q r eqkey
    by_contra hne
    obtain ⟨p,hp,hq,hr,imp⟩ := sep q r hne
    obtain ⟨z,hz,zp,zq,zr⟩ := cg target hit p (row q) (row r) (Fin.mk.inj eqkey) hp hq hr
    rcases imp z hz zp with t | t <;> simp_all
  simpa using Fintype.card_le_of_injective key inj

def seeds : Fin 4 → List W := ![
  [0,2592243715,133562380,2844803120,84754625,403292932,102861840,1347294240,1617961282,2273325568,4160751752],
  [8372227,0,32849932,714129456,26198208,101352196,19074064,340530208,410001728,562049537,1040189578],
  [8372227,1292189708,0,1418772528,42631364,202359552,52628496,676074528,812654920,1132474881,2080376962],
  [16760835,353714188,63750192,0,36339908,70451984,54774784,213652480,146809160,318779905,469764258]]

def count : Fin 4 → Nat := ![18,16,17,15]
def minAnd : Fin 4 → Nat := ![5,4,5,4]
def negativeRow {m} (j : Fin m) : I := ⟨(14+j.val)%32, Nat.mod_lt _ (by decide)⟩

def checkSeparation (z : List W) (target : W) {m : Nat} (row : Fin m → I) : Bool :=
  (List.finRange m).all fun q => (List.finRange m).all fun r =>
    decide (q = r) || (List.finRange 32).any fun p =>
      decide (bit target p = true ∧ bit target (row q) = false ∧ bit target (row r) = false) &&
      z.all (fun w => decide (bit w p = true → bit w (row q) = true ∨ bit w (row r) = true))

theorem separation_of_check {z t m} {row : Fin m → I} (h : checkSeparation z t row = true) :
    separated z t row := by
  intro q r hqr
  have h1 := List.all_eq_true.mp h q (by simp)
  have h2 := List.all_eq_true.mp h1 r (by simp)
  simp only [hqr,decide_false,Bool.false_or] at h2
  obtain ⟨p,_,hp⟩ := List.any_eq_true.mp h2
  obtain ⟨pos,win⟩ := Bool.and_eq_true_iff.mp hp
  obtain ⟨pp,pq,pr⟩ := of_decide_eq_true pos
  exact ⟨p,pp,pq,pr,fun w hw => of_decide_eq_true (List.all_eq_true.mp win w hw)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem four_separations : ∀ i : Fin 4,
    separated (seeds i) 16383 (negativeRow (m := count i)) := by
  intro i
  apply separation_of_check
  fin_cases i <;> decide +kernel

theorem assigned_and_lower (i : Fin 4) {n ws} (run : Run (seeds i) n ws) (hit : 16383 ∈ ws) :
    minAnd i ≤ n := by
  have bound := separated_le_pow _ run hit (four_separations i)
  have strict : 2^(minAnd i-1) < count i := by fin_cases i <;> decide
  by_contra! h
  have le : n ≤ minAnd i-1 := by omega
  have p : 2^n ≤ 2^(minAnd i-1) := Nat.pow_le_pow_right (by decide) le
  omega

/-- Counts both types of gates while retaining all previous wires for further uses. -/
inductive Counts (seeds : List W) : Nat → Nat → List W → Prop
  | start : Counts seeds 0 0 seeds
  | join {a o ws x y} : Counts seeds a o ws → x ∈ ws → y ∈ ws →
      Counts seeds a (o+1) ((x ||| y)::ws)
  | meet {a o ws x y} : Counts seeds a o ws → x ∈ ws → y ∈ ws →
      Counts seeds (a+1) o ((x &&& y)::ws)

theorem Counts.primal {z a o ws} (p : Counts z a o ws) : Run z a ws := by
  induction p with
  | start => exact .start
  | join _ hx hy ih => exact .join ih hx hy
  | meet _ hx hy ih => exact .meet ih hx hy

def flip (x : W) := ~~~x

theorem Counts.dual {z a o ws} (p : Counts z a o ws) : Run (z.map flip) o (ws.map flip) := by
  induction p with
  | start => exact .start
  | join _ hx hy ih =>
    simpa [flip,BitVec.not_or] using Run.meet ih (List.mem_map_of_mem (f := flip) hx) (List.mem_map_of_mem (f := flip) hy)
  | meet _ hx hy ih =>
    simpa [flip,BitVec.not_and] using Run.join ih (List.mem_map_of_mem (f := flip) hx) (List.mem_map_of_mem (f := flip) hy)

def positiveRow (j : Fin 14) : I := ⟨j.val, by omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem four_dual_separations : ∀ i : Fin 4,
    separated ((seeds i).map flip) (flip 16383) positiveRow := by
  intro i
  apply separation_of_check
  fin_cases i <;> decide +kernel

theorem assigned_gate_counts (i : Fin 4) {a o ws} (p : Counts (seeds i) a o ws)
    (hit : 16383 ∈ ws) : minAnd i ≤ a ∧ 4 ≤ o := by
  refine ⟨assigned_and_lower i p.primal hit,?_⟩
  have bound := separated_le_pow positiveRow p.dual (List.mem_map_of_mem (f := flip) hit) (four_dual_separations i)
  by_contra! h
  have le : o ≤ 3 := by omega
  have pow : 2^o ≤ 2^3 := Nat.pow_le_pow_right (by decide) le
  omega

def legalTrace (z s : List W) : Prop := ∀ j : Fin s.length,
  let ws := z ++ s.take j.val
  ∃ x ∈ ws, ∃ y ∈ ws, s.get j = x &&& y ∨ s.get j = x ||| y

theorem counts_of_trace {z s : List W} (h : legalTrace z s) :
    ∃ a o, a + o = s.length ∧ Counts z a o (s.reverse ++ z) := by
  have acc (k : Nat) (hk : k ≤ s.length) :
      ∃ a o, a+o=k ∧ Counts z a o ((s.take k).reverse ++ z) := by
    induction k with
    | zero => exact ⟨0,0,rfl,by simpa using Counts.start (seeds := z)⟩
    | succ k ih =>
      have hlt : k < s.length := by omega
      obtain ⟨a,o,he,prog⟩ := ih (by omega)
      obtain ⟨x,hx,y,hy,op⟩ := h ⟨k,hlt⟩
      have hx' : x ∈ (s.take k).reverse ++ z := by simpa [List.mem_append,or_comm] using hx
      have hy' : y ∈ (s.take k).reverse ++ z := by simpa [List.mem_append,or_comm] using hy
      rw [List.take_succ_eq_append_getElem hlt]
      rcases op with hxy | hxy
      · refine ⟨a+1,o,by omega,?_⟩
        simpa [show s[k] = x &&& y from hxy] using Counts.meet prog hx' hy'
      · refine ⟨a,o+1,by omega,?_⟩
        simpa [show s[k] = x ||| y from hxy] using Counts.join prog hx' hy'
  simpa using acc s.length (by rfl)

theorem assigned_trace_lower (i : Fin 4) (s : List W) (h : legalTrace (seeds i) s)
    (hit : 16383 ∈ seeds i ++ s) : ∃ a o, a+o=s.length ∧ minAnd i ≤ a ∧ 4 ≤ o := by
  obtain ⟨a,o,he,p⟩ := counts_of_trace h
  have ht : 16383 ∈ s.reverse ++ seeds i := by simpa [List.mem_append,or_comm] using hit
  exact ⟨a,o,he,assigned_gate_counts i p ht⟩

end AndSignature

#print axioms AndSignature.assigned_and_lower
#print axioms AndSignature.assigned_gate_counts
#print axioms AndSignature.assigned_trace_lower
