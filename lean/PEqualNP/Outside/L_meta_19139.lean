import Mathlib

namespace PEqualNP.Outside.L_meta_19139

structure Row where
  op : Bool
  a : ℕ
  b : ℕ
  val : ℕ

def gateVal (xs : List ℕ) (op : Bool) (a b : ℕ) : ℕ :=
  if op then xs.getD a 0 &&& xs.getD b 0 else xs.getD a 0 ||| xs.getD b 0

def dirty (mask : ℕ) (r : Row) : Bool := decide (r.op = true ∧ r.val &&& mask ≠ 0)

def correct (mark : ℕ → Bool) (mask : ℕ) (xs : List ℕ) (r : Row) : Prop :=
  r.a < xs.length ∧ r.b < xs.length ∧ r.val = gateVal xs r.op r.a r.b ∧
    ((r.op = true ∨ mark xs.length = true) → mark r.a = true ∧ mark r.b = true) ∧
    (r.op = true → r.val &&& mask = 0 → mark xs.length = false)

def checked (mark : ℕ → Bool) (mask : ℕ) (xs : List ℕ) : List Row → Prop
  | [] => True
  | r :: rs => correct mark mask xs r ∧ checked mark mask (xs ++ [r.val]) rs

theorem checked_append (m : ℕ → Bool) (k : ℕ) (xs : List ℕ) (rs ss : List Row) :
    checked m k xs (rs ++ ss) ↔ checked m k xs rs ∧ checked m k (xs ++ rs.map Row.val) ss := by
  induction rs generalizing xs with
  | nil => simp [checked]
  | cons r rs ih => simp [checked, ih, List.append_assoc, and_assoc]

theorem checked_at (m : ℕ → Bool) (k : ℕ) (xs : List ℕ) (rs : List Row)
    (h : checked m k xs rs) (i : Fin rs.length) :
    correct m k (xs ++ (rs.take i.val).map Row.val) (rs.get i) := by
  induction rs generalizing xs with
  | nil => exact Fin.elim0 i
  | cons r rs ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have hi' : i < rs.length := by simpa using hi
      simpa [List.append_assoc] using ih (xs ++ [r.val]) h.2 ⟨i,hi'⟩

abbrev Gate := Bool × Fin 32 × Fin 32

def encode (r : Row) : Gate := (r.op, Fin.ofNat 32 r.a, Fin.ofNat 32 r.b)

def update (xs : List ℕ) (g : Gate) : List ℕ := xs ++ [gateVal xs g.1 g.2.1.val g.2.2.val]

theorem encoded_eval (m : ℕ → Bool) (k : ℕ) (xs : List ℕ) (rs : List Row)
    (h : checked m k xs rs) (bound : xs.length + rs.length ≤ 32) :
    (rs.map encode).foldl update xs = xs ++ rs.map Row.val := by
  induction rs generalizing xs with
  | nil => simp
  | cons r rs ih =>
    obtain ⟨⟨ha,hb,hval,_,_⟩,ht⟩ := h
    have a32 : r.a < 32 := by simp at bound; omega
    have b32 : r.b < 32 := by simp at bound; omega
    have hstep : update xs (encode r) = xs ++ [r.val] := by
      simp [update, encode, Fin.ofNat, Nat.mod_eq_of_lt a32, Nat.mod_eq_of_lt b32, hval]
    simp only [List.map_cons, List.foldl_cons, hstep]
    simpa [List.append_assoc] using ih (xs ++ [r.val]) ht (by simp at bound ⊢; omega)

theorem getD_before_append {α : Type*} (xs ys : List α) (j : ℕ) (d : α) (h : j < xs.length) :
    (xs ++ ys).getD j d = xs.getD j d := by
  simp [List.getD, List.getElem?_append_left h]

theorem getD_next {α : Type*} (xs ys : List α) (i : Fin ys.length) (d : α) :
    (xs ++ ys).getD (xs.length+i.val) d = ys.get i := by
  simp [List.getD, i.isLt]

theorem find_wire {xs : List ℕ} {x : ℕ} (hx : x ∈ xs) :
    ∃ j < xs.length, xs.getD j 0 = x := by
  obtain ⟨i,hi⟩ := List.get_of_mem hx
  exact ⟨i.val,i.isLt, by simpa [List.getD, i.isLt] using hi⟩

end PEqualNP.Outside.L_meta_19139

namespace PEqualNP.Outside.L_meta_19139

theorem assemble_prefix (x1 x2 : List ℕ) (x3 : Finset ℕ) (mask : ℕ)
    (shape : ∀ i : Fin x2.length,
      ∃ a ∈ x1 ++ x2.take i.val, ∃ b ∈ x1 ++ x2.take i.val,
        x2.get i = if x2.get i ∈ x3 then a &&& b else a ||| b)
    (nclean : ∀ v ∈ x3, v &&& mask ≠ 0) :
    ∃ rs : List Row, checked (fun j => decide (j < x1.length + x2.length)) mask x1 rs ∧
      rs.map Row.val = x2 ∧ rs.map (dirty mask) = x2.map (fun v => decide (v ∈ x3)) := by
  let m := fun j : ℕ => decide (j < x1.length + x2.length)
  have pref (n : ℕ) (h : n ≤ x2.length) :
      ∃ rs : List Row, checked m mask x1 rs ∧ rs.map Row.val = x2.take n ∧
        rs.map (dirty mask) = (x2.take n).map (fun v => decide (v ∈ x3)) := by
    induction n with
    | zero => exact ⟨[], trivial, rfl, by simp⟩
    | succ n ih =>
      have hn : n < x2.length := by omega
      let i : Fin x2.length := ⟨n,hn⟩
      obtain ⟨rs,hrs,hval,hmarks⟩ := ih (Nat.le_of_lt hn)
      obtain ⟨a,ha,b,hb,hop⟩ := shape i
      obtain ⟨u,hu,heu⟩ := find_wire ha
      obtain ⟨v,hv,hev⟩ := find_wire hb
      let r : Row := ⟨decide (x2.get i ∈ x3), u, v, x2.get i⟩
      have hlen : (x1 ++ x2.take i.val).length < x1.length + x2.length := by
        simp [i, List.length_take, Nat.min_eq_left (Nat.le_of_lt hn), hn]
      have hcorrect : correct m mask (x1 ++ x2.take i.val) r := by
        refine ⟨hu,hv,?_,?_,?_⟩
        · change x2.get i = gateVal _ (decide (x2.get i ∈ x3)) u v
          unfold gateVal
          rw [heu, hev]
          simpa only [decide_eq_true_eq] using hop
        · intro _
          exact ⟨decide_eq_true (Nat.lt_trans hu hlen), decide_eq_true (Nat.lt_trans hv hlen)⟩
        · intro hand hclean
          have e : x2.get i ∈ x3 := of_decide_eq_true hand
          exact False.elim (nclean _ e hclean)
      have hdirty : dirty mask r = decide (x2.get i ∈ x3) := by
        change decide ((decide (x2.get i ∈ x3)) = true ∧ x2.get i &&& mask ≠ 0) = decide (x2.get i ∈ x3)
        by_cases hin : x2.get i ∈ x3
        · rw [decide_eq_true hin]
          exact decide_eq_true ⟨rfl,nclean _ hin⟩
        · rw [decide_eq_false hin]
          exact decide_eq_false (by simp)
      have htake : x2.take (n+1) = x2.take n ++ [x2.get i] :=
        List.take_succ_eq_append_getElem hn
      refine ⟨rs ++ [r], ?_, ?_, ?_⟩
      · apply (checked_append ..).mpr
        refine ⟨hrs,?_,trivial⟩
        simpa only [hval] using hcorrect
      · simp [List.map_append,hval,htake,r]
      · simp [List.map_append,hmarks,htake,hdirty]
  simpa only [List.take_length] using pref x2.length (Nat.le_refl _)

end PEqualNP.Outside.L_meta_19139
namespace PEqualNP.Outside.L_meta_19139

def markBase (base : List ℕ) (i : ℕ) : Bool := decide (i < base.length)

def termStep (acc : ℕ) (p : ℕ × ℕ) : ℕ := acc ||| (p.1 &&& p.2)

def cleanTerm (base : List ℕ) (mask : ℕ) (p : ℕ × ℕ) : Prop :=
  p.1 ∈ base ∧ p.2 ∈ base ∧ (p.1 &&& p.2) &&& mask = 0

theorem terminal_and (base extra : List ℕ) (mask : ℕ) (p : ℕ × ℕ)
    (hp : cleanTerm base mask p) :
    ∃ r : Row, correct (markBase base) mask (base ++ extra) r ∧
      r.val = p.1 &&& p.2 ∧ dirty mask r = false := by
  obtain ⟨a,ha,hea⟩ := find_wire hp.1
  obtain ⟨b,hb,heb⟩ := find_wire hp.2.1
  refine ⟨⟨true,a,b,p.1 &&& p.2⟩, ?_, rfl, ?_⟩
  · refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_⟩
    · change p.1 &&& p.2 = (base ++ extra).getD a 0 &&& (base ++ extra).getD b 0
      rw [getD_before_append _ _ _ _ ha, getD_before_append _ _ _ _ hb, hea, heb]
    · intro _
      simp [markBase, ha, hb]
    · intro _ _
      simp [markBase]
  · simp [dirty, hp.2.2]

theorem or_correct (base xs : List ℕ) (mask a b va vb : ℕ)
    (hb : base.length ≤ xs.length) (ha1 : a < xs.length) (hb1 : b < xs.length)
    (ea : xs.getD a 0 = va) (eb : xs.getD b 0 = vb) :
    correct (markBase base) mask xs ⟨false,a,b,va ||| vb⟩ := by
  refine ⟨ha1,hb1,?_, ?_, by simp⟩
  · change va ||| vb = xs.getD a 0 ||| xs.getD b 0
    rw [ea,eb]
  · intro h
    simp [markBase, Nat.not_lt.mpr hb] at h

theorem end_value (xs : List ℕ) (v : ℕ) : (xs ++ [v]).getD xs.length 0 = v := by
  simp

theorem accumulate (base : List ℕ) (mask : ℕ) (ys : List (ℕ × ℕ))
    (valid : ∀ p ∈ ys, cleanTerm base mask p) (pre : List ℕ) (acc : ℕ) :
    ∃ (rs : List Row) (post : List ℕ),
      checked (markBase base) mask (base ++ pre ++ [acc]) rs ∧
      rs.length = 2 * ys.length ∧ (∀ r ∈ rs, dirty mask r = false) ∧
      (base ++ pre ++ [acc]) ++ rs.map Row.val = base ++ post ++ [ys.foldl termStep acc] := by
  induction ys generalizing pre acc with
  | nil => exact ⟨[],pre,by trivial,by simp,by simp,by simp⟩
  | cons p ys ih =>
    let xs := base ++ pre ++ [acc]
    let z := p.1 &&& p.2
    obtain ⟨r,hr,rv,rd⟩ := terminal_and base (pre ++ [acc]) mask p (valid p (by simp))
    have hr' : correct (markBase base) mask xs r := by simpa [xs,List.append_assoc] using hr
    let a := (base ++ pre).length
    let b := xs.length
    let s : Row := ⟨false,a,b,acc ||| z⟩
    have hacc : xs.getD a 0 = acc := end_value (base ++ pre) acc
    have ha : a < xs.length := by simp [a,xs]
    have hs : correct (markBase base) mask (xs ++ [z]) s := by
      apply or_correct
      · simp [xs]
      · simp; omega
      · simp [b]
      · exact (getD_before_append _ _ _ _ ha).trans hacc
      · exact end_value xs z
    obtain ⟨rs,post,hchecked,hlen,hclean,hend⟩ :=
      ih (fun q hq => valid q (by simp [hq])) (pre ++ [acc,z]) (acc ||| z)
    refine ⟨r :: s :: rs, post, ?_, ?_, ?_, ?_⟩
    · refine ⟨hr', ?_, ?_⟩
      · simpa [xs,z,rv] using hs
      · simpa [xs,s,z,rv,List.append_assoc] using hchecked
    · simp [hlen]; omega
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact rd
      · rcases List.mem_cons.mp hv with rfl | hv
        · simp [s,dirty]
        · exact hclean v hv
    · simpa [termStep,z,rv,s,List.append_assoc] using hend

theorem terms (base : List ℕ) (mask : ℕ) (ys : List (ℕ × ℕ)) (hy : ys ≠ [])
    (valid : ∀ p ∈ ys, cleanTerm base mask p) :
    ∃ (rs : List Row) (post : List ℕ),
      checked (markBase base) mask base rs ∧ rs.length + 1 = 2*ys.length ∧
      (∀ r ∈ rs, dirty mask r = false) ∧
      base ++ rs.map Row.val = base ++ post ++ [ys.foldl termStep 0] := by
  cases ys with
  | nil => exact False.elim (hy rfl)
  | cons p ys =>
    obtain ⟨r,hr,rv,rd⟩ := terminal_and base [] mask p (valid p (by simp))
    obtain ⟨rs,post,hc,hl,hd,he⟩ :=
      accumulate base mask ys (fun q hq => valid q (by simp [hq])) [] (p.1 &&& p.2)
    refine ⟨r::rs,post,⟨by simpa using hr,by simpa [rv] using hc⟩, ?_, ?_, ?_⟩
    · simp [hl]; omega
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | h
      · exact rd
      · exact hd s h
    · simpa [termStep,rv,List.append_assoc] using he

theorem padding (base pre : List ℕ) (acc mask n : ℕ) :
    ∃ (rs : List Row) (post : List ℕ),
      checked (markBase base) mask (base ++ pre ++ [acc]) rs ∧ rs.length = n ∧
      (∀ r ∈ rs, dirty mask r = false) ∧
      (base ++ pre ++ [acc]) ++ rs.map Row.val = base ++ post ++ [acc] := by
  induction n generalizing pre with
  | zero => exact ⟨[],pre,by trivial,rfl,by simp,by simp⟩
  | succ n ih =>
    let a := (base ++ pre).length
    let s : Row := ⟨false,a,a,acc⟩
    have ha : a < (base ++ pre ++ [acc]).length := by simp [a]
    have hs : correct (markBase base) mask (base ++ pre ++ [acc]) s := by
      have ht := or_correct base (base ++ pre ++ [acc]) mask a a acc acc
        (by simp) ha ha (end_value _ _) (end_value _ _)
      simpa [s] using ht
    obtain ⟨rs,post,hc,hl,hd,he⟩ := ih (pre ++ [acc])
    refine ⟨s :: rs,post,⟨hs,?_⟩,by simp [hl],?_,?_⟩
    · simpa [s,List.append_assoc] using hc
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | h
      · simp [s,dirty]
      · exact hd v h
    · simpa [s,List.append_assoc] using he

end PEqualNP.Outside.L_meta_19139

namespace PEqualNP.Outside.L_meta_19139

private theorem countMarked {α : Type} (p : α → Bool) (xs : List α) :
    (xs.map p).count true = (xs.filter p).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases h : p a <;> simp [h, ih]

theorem mark_count {α : Type} [DecidableEq α] (xs : List α) (chosen : Finset α)
    (hn : xs.Nodup) (hs : chosen ⊆ xs.toFinset) :
    (xs.map (fun x => decide (x ∈ chosen))).count true = chosen.card := by
  have hf : (xs.filter (fun x => decide (x ∈ chosen))).toFinset = chosen := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun hx => ⟨List.mem_toFinset.mp (hs hx), hx⟩⟩
  rw [countMarked, ← List.toFinset_card_of_nodup (hn.filter _), hf]

theorem mark_count_append_false {α : Type} [DecidableEq α]
    (xs : List α) (chosen : Finset α) (rest : ℕ)
    (hn : xs.Nodup) (hs : chosen ⊆ xs.toFinset) :
    ((xs.map (fun x => decide (x ∈ chosen))) ++ List.replicate rest false).count true = chosen.card := by
  rw [List.count_append, mark_count xs chosen hn hs]
  suffices h : (List.replicate rest false).count true = 0 by simp [h]
  induction rest with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem ofFn_get_map {α β : Type} (es : List α) (f : α → β) :
    List.ofFn (fun i : Fin es.length => f (es.get i)) = es.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

end PEqualNP.Outside.L_meta_19139

namespace PEqualNP.Outside.L_meta_19139

theorem count_clean (mask : ℕ) (rs : List Row) (h : ∀ r ∈ rs, dirty mask r = false) :
    (rs.map (dirty mask)).count true = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp [h r (by simp), ih (fun r hr => h r (by simp [hr]))]

theorem assemble (x1 x2 : List ℕ) (x3 : Finset ℕ) (x4 : List (ℕ × ℕ)) (x5 : ℕ)
    (h1 : x1.length = 11) (hn : x2.Nodup) (hs : x3 ⊆ x2.toFinset) (h4 : x4 ≠ [])
    (budget : x2.length + 2*x4.length ≤ 22)
    (shape : ∀ i : Fin x2.length, let p := x1 ++ x2.take i.val
      ∃ u ∈ p, ∃ v ∈ p, x2.get i = if x2.get i ∈ x3 then u &&& v else u ||| v)
    (nc : ∀ x ∈ x3, x &&& x5 ≠ 0)
    (vt : ∀ p ∈ x4, cleanTerm (x1++x2) x5 p) :
    ∃ rs : List Row, rs.length = 21 ∧ checked (markBase (x1++x2)) x5 x1 rs ∧
      (x1 ++ rs.map Row.val).getD 31 0 = x4.foldl termStep 0 ∧
      (rs.map (dirty x5)).count true = x3.card := by
  let base := x1 ++ x2
  let target := x4.foldl termStep 0
  obtain ⟨pre,hpre,hvals,hmarks⟩ := assemble_prefix x1 x2 x3 x5 shape nc
  obtain ⟨ts,post,hts,htlen,htclean,htend⟩ := terms base x5 x4 h4 vt
  have hplen : pre.length = x2.length := by simpa using congrArg List.length hvals
  have beforePad : pre.length + ts.length ≤ 21 := by omega
  let pads := 21 - (pre.length + ts.length)
  obtain ⟨ss,finalPrefix,hss,hslen,hsclean,hsend⟩ := padding base post target x5 pads
  let rs := (pre ++ ts) ++ ss
  have hrlen : rs.length = 21 := by simp only [rs,List.length_append,hslen,pads]; omega
  have hwhole : checked (markBase base) x5 x1 rs := by
    apply (checked_append ..).mpr
    constructor
    · apply (checked_append ..).mpr
      refine ⟨?_,?_⟩
      · change checked (fun j => decide (j < (x1 ++ x2).length)) x5 x1 pre
        simpa only [List.length_append] using hpre
      · simpa only [hvals] using hts
    · simpa only [List.map_append, ← List.append_assoc, hvals, htend, base, target] using hss
  have vals : x1 ++ rs.map Row.val = base ++ finalPrefix ++ [target] := by
    calc
      x1 ++ rs.map Row.val = (base ++ ts.map Row.val) ++ ss.map Row.val := by
        simp only [rs,base,List.map_append,hvals,List.append_assoc]
      _ = (base ++ post ++ [target]) ++ ss.map Row.val := by rw [htend]
      _ = _ := hsend
  have total : (base ++ finalPrefix).length = 31 := by
    have eq := congrArg List.length vals
    simp only [List.length_append,List.length_map,hrlen,h1,List.length_singleton] at eq
    simp only [List.length_append]
    omega
  refine ⟨rs,hrlen,hwhole,?_,?_⟩
  · rw [vals,←total]
    exact end_value _ _
  · simp only [rs,List.map_append,List.count_append,hmarks,
      mark_count x2 x3 hn hs,count_clean x5 ts htclean,count_clean x5 ss hsclean,Nat.add_zero]

end PEqualNP.Outside.L_meta_19139

namespace PEqualNP.Outside.L_meta_19139

theorem assemble_readback (x1 : List ℕ) (rs : List Row) (mark : ℕ → Bool) (mask : ℕ)
    (hx : x1.length = 11) (hr : rs.length = 21) (hc : checked mark mask x1 rs) :
    ∃ g : Fin 21 → Gate,
      (List.ofFn g).foldl update x1 = x1 ++ rs.map Row.val ∧
      (∀ i : Fin 21, (g i).2.1.val < 11+i.val ∧ (g i).2.2.val < 11+i.val ∧
        (((g i).1 = true ∨ mark (11+i.val) = true) →
          mark (g i).2.1.val = true ∧ mark (g i).2.2.val = true) ∧
        ((g i).1 = true → (x1 ++ rs.map Row.val).getD (11+i.val) 0 &&& mask = 0 →
          mark (11+i.val) = false)) ∧
      List.ofFn (fun i : Fin 21 => decide ((g i).1 = true ∧
        (x1 ++ rs.map Row.val).getD (11+i.val) 0 &&& mask ≠ 0)) = rs.map (dirty mask) := by
  let idx (i : Fin 21) : Fin rs.length := ⟨i.val, by rw [hr]; exact i.isLt⟩
  let g (i : Fin 21) := encode (rs.get (idx i))
  have allG : List.ofFn g = rs.map encode := by
    apply List.ext_getElem
    · simp [hr]
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getElem_map]
      rfl
  have valAt (i : Fin 21) : (x1 ++ rs.map Row.val).getD (11+i.val) 0 =
      (rs.get (idx i)).val := by
    let j : Fin (rs.map Row.val).length := ⟨i.val, by simp [hr]⟩
    simpa [j, idx, hx] using getD_next x1 (rs.map Row.val) j 0
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [allG]
    exact encoded_eval mark mask x1 rs hc (by omega)
  · intro i
    have hp : (x1 ++ (rs.take (idx i).val).map Row.val).length = 11+i.val := by
      simp [idx,hx, Nat.min_eq_left (Nat.le_of_lt (idx i).isLt)]
    obtain ⟨ha,hb,_,hm,hclean⟩ := checked_at mark mask x1 rs hc (idx i)
    rw [hp] at ha hb hm hclean
    have h₁ : (rs.get (idx i)).a < 32 := by have := i.isLt; omega
    have h₂ : (rs.get (idx i)).b < 32 := by have := i.isLt; omega
    simpa only [g,encode,Fin.ofNat,Fin.val_mk,Nat.mod_eq_of_lt h₁,
      Nat.mod_eq_of_lt h₂, valAt] using And.intro ha (And.intro hb (And.intro hm hclean))
  · apply List.ext_getElem
    · simp [hr]
    · intro j hl hj
      have hj21 : j < 21 := by simpa using hl
      have hv := valAt ⟨j,hj21⟩
      simp only [List.getElem_ofFn, List.getElem_map, g, encode, dirty]
      rw [hv]
      rfl

end PEqualNP.Outside.L_meta_19139
open PEqualNP.Outside.L_meta_19139 in
theorem PEqualNP.Outside.L_meta_19139 : ∀ (x1 x2 : List ℕ) (x3 : Finset ℕ) (x4 : List (ℕ × ℕ)) (x5 : ℕ), x1.length = (11 : ℕ) → x2.Nodup → x3 ⊆ x2.toFinset → x4 ≠ [] → x2.length + (2 : ℕ) * x4.length ≤ (22 : ℕ) → (∀ (x11 : Fin x2.length), have x12 : List ℕ := x1 ++ List.take (↑x11) x2; ∃ x13 ∈ x12, ∃ x14 ∈ x12, x2.get x11 = if x2.get x11 ∈ x3 then x13 &&& x14 else x13 ||| x14) → (∀ x12 ∈ x3, x12 &&& x5 ≠ (0 : ℕ)) → (∀ x13 ∈ x4, x13.1 ∈ x1 ++ x2 ∧ x13.2 ∈ x1 ++ x2 ∧ x13.1 &&& x13.2 &&& x5 = (0 : ℕ)) → ∃ (x14 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) (x15 : ℕ → Bool), have x16 : List ℕ := List.foldl (fun (x16 : List ℕ) (x17 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x16 ++ [if x17.1 = Bool.true then x16.getD ↑x17.2.1 (0 : ℕ) &&& x16.getD ↑x17.2.2 (0 : ℕ) else x16.getD ↑x17.2.1 (0 : ℕ) ||| x16.getD ↑x17.2.2 (0 : ℕ)]) x1 (List.ofFn x14); (∀ (x17 : Fin (21 : ℕ)), ↑(x14 x17).2.1 < (11 : ℕ) + ↑x17 ∧ ↑(x14 x17).2.2 < (11 : ℕ) + ↑x17) ∧ x16.getD (31 : ℕ) (0 : ℕ) = List.foldl (fun (x17 : ℕ) (x18 : ℕ × ℕ) => x17 ||| x18.1 &&& x18.2) (0 : ℕ) x4 ∧ List.count Bool.true (List.ofFn fun (x17 : Fin (21 : ℕ)) => Decidable.decide ((x14 x17).1 = Bool.true ∧ x16.getD ((11 : ℕ) + ↑x17) (0 : ℕ) &&& x5 ≠ (0 : ℕ))) = x3.card ∧ (∀ (x17 : Fin (21 : ℕ)), (x14 x17).1 = Bool.true ∨ x15 ((11 : ℕ) + ↑x17) = Bool.true → x15 ↑(x14 x17).2.1 = Bool.true ∧ x15 ↑(x14 x17).2.2 = Bool.true) ∧ ∀ (x17 : Fin (21 : ℕ)), (x14 x17).1 = Bool.true → x16.getD ((11 : ℕ) + ↑x17) (0 : ℕ) &&& x5 = (0 : ℕ) → x15 ((11 : ℕ) + ↑x17) = Bool.false := by
  intro x1 x2 x3 x4 x5 hlen hn hs hne budget shape nc vt
  obtain ⟨rs,n21,hc,output,counts⟩ := assemble x1 x2 x3 x4 x5 hlen hn hs hne budget shape nc vt
  let mark := markBase (x1 ++ x2)
  obtain ⟨g,eval,guards,eqdirty⟩ := assemble_readback x1 rs mark x5 hlen n21 hc
  refine ⟨g,mark,?_⟩
  change (∀ i : Fin 21, (g i).2.1.val < 11+i.val ∧ (g i).2.2.val < 11+i.val) ∧
    ((List.ofFn g).foldl update x1).getD 31 0 = x4.foldl termStep 0 ∧
    (List.ofFn (fun i : Fin 21 => decide ((g i).1 = true ∧
      ((List.ofFn g).foldl update x1).getD (11+i.val) 0 &&& x5 ≠ 0))).count true = x3.card ∧
    (∀ i : Fin 21, ((g i).1 = true ∨ mark (11+i.val) = true) →
      mark (g i).2.1.val = true ∧ mark (g i).2.2.val = true) ∧
    (∀ i : Fin 21, (g i).1 = true →
       ((List.ofFn g).foldl update x1).getD (11+i.val) 0 &&& x5 = 0 → mark (11+i.val) = false)
  rw [eval, eqdirty]
  exact ⟨fun i => ⟨(guards i).1,(guards i).2.1⟩,output,counts,
     fun i => (guards i).2.2.1,fun i => (guards i).2.2.2⟩
