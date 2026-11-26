import Mathlib

namespace PEqualNP.Outside.L_meta_19137

def termFold (zs : List (Nat × Nat)) (seed : Nat) : Nat :=
  zs.foldl (fun z p => z ||| (p.1 &&& p.2)) seed

theorem fold_merge (pre post : List (Nat × Nat)) (a v b seed : Nat) :
    termFold (pre ++ (a, v ||| b) :: post) seed =
      termFold ((a, b) :: (pre ++ (a, v) :: post)) seed := by
  induction pre generalizing seed with
  | nil =>
    change termFold post (seed ||| (a &&& (v ||| b))) =
      termFold post ((seed ||| (a &&& b)) ||| (a &&& v))
    apply congrArg (termFold post)
    rw [Nat.and_or_distrib_left]
    ac_rfl
  | cons p pre ih =>
    calc
      _ = termFold ((a, b) :: (pre ++ (a, v) :: post))
          (seed ||| (p.1 &&& p.2)) := ih (seed ||| (p.1 &&& p.2))
      _ = _ := by
        change termFold (pre ++ (a, v) :: post)
            ((seed ||| (p.1 &&& p.2)) ||| (a &&& b)) =
          termFold (pre ++ (a, v) :: post)
            ((seed ||| (a &&& b)) ||| (p.1 &&& p.2))
        apply congrArg (termFold (pre ++ (a, v) :: post))
        ac_rfl

theorem clean_merge (a v b mask : Nat)
    (hv : (a &&& v) &&& mask = 0) (hb : (a &&& b) &&& mask = 0) :
    (a &&& (v ||| b)) &&& mask = 0 := by
  rw [Nat.and_or_distrib_left, Nat.and_or_distrib_right, hv, hb]
  rfl

def Builds (base built : List Nat) : Prop :=
  ∀ i : Fin built.length, ∃ u ∈ base ++ built.take i.val,
    ∃ v ∈ base ++ built.take i.val, built.get i = u ||| v

theorem extendBuild (base built : List Nat) (hn : built.Nodup)
    (hd : ∀ z ∈ built, z ∉ base) (hw : Builds base built) (a b : Nat)
    (ha : a ∈ base ++ built) (hb : b ∈ base ++ built) :
    ∃ ys : List Nat, ys.Nodup ∧ (∀ z ∈ ys, z ∉ base) ∧ Builds base ys ∧
      (∀ z ∈ base ++ built, z ∈ base ++ ys) ∧
      (a ||| b) ∈ base ++ ys ∧ ys.length ≤ built.length + 1 := by
  let z := a ||| b
  by_cases old : z ∈ base ++ built
  · exact ⟨built, hn, hd, hw, fun _ h => h, old, by omega⟩
  have hz₁ : z ∉ base := fun h => old (List.mem_append_left _ h)
  have hz₂ : z ∉ built := fun h => old (List.mem_append_right _ h)
  refine ⟨built ++ [z], ?_, ?_, ?_, ?_, ?_, by simp⟩
  · simp [List.nodup_append, hn]
    intro x hx eq
    exact hz₂ (eq ▸ hx)
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact hd _ h
    · obtain rfl := List.mem_singleton.mp h
      exact hz₁
  · intro i
    have hi := i.isLt
    simp only [List.length_append, List.length_singleton] at hi
    by_cases inside : i.val < built.length
    · obtain ⟨u,hu,v,hv,h⟩ := hw ⟨i.val, inside⟩
      rw [List.take_append_of_le_length (Nat.le_of_lt inside)]
      refine ⟨u,hu,v,hv,?_⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left inside] using h
    · have last : i.val = built.length := by omega
      simp only [last, List.take_append_of_le_length (Nat.le_refl _), List.take_length]
      refine ⟨a,ha,b,hb,?_⟩
      change (built ++ [z])[i.val] = z
      rw [List.getElem_append_right (by omega : built.length ≤ i.val)]
      simp [last]
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_left _ h)
  · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self z))

def centers (ps : List (ℕ × ℕ)) : Finset ℕ := (ps.map Prod.fst).toFinset

theorem centers_cons (a b : ℕ) (ps : List (ℕ × ℕ)) :
    centers ((a,b) :: ps) = insert a (centers ps) := by simp [centers]

theorem centers_split (pre post : List (ℕ × ℕ)) (a v b : ℕ) :
    centers (pre ++ (a,v ||| b) :: post) = centers (pre ++ (a,v) :: post) := by
  simp [centers]

theorem center_witness {ps : List (ℕ × ℕ)} {a : ℕ} (h : a ∈ centers ps) :
    ∃ v, (a,v) ∈ ps := by
  have hm : a ∈ ps.map Prod.fst := by simpa [centers] using h
  obtain ⟨⟨c,v⟩, hv, hc⟩ := List.mem_map.mp hm
  simpa [← hc] using (show ∃ k, (c,k) ∈ ps from ⟨v,hv⟩)

def Clean (S : List ℕ) (m : ℕ) (ps : List (ℕ × ℕ)) : Prop :=
  ∀ p ∈ ps, p.1 ∈ S ∧ p.2 ∈ S ∧ p.1 &&& p.2 &&& m = 0

theorem compress (base : List ℕ) (m : ℕ) (ps : List (ℕ × ℕ)) (h : Clean base m ps) :
    ∃ (ys : List ℕ) (ts : List (ℕ × ℕ)), ys.Nodup ∧
      (∀ z ∈ ys, z ∉ base) ∧ Builds base ys ∧ centers ts = centers ps ∧
      Clean (base ++ ys) m ts ∧ ys.length + 2 * ts.length ≤ ps.length + (centers ps).card ∧
      ∀ seed, termFold ts seed = termFold ps seed := by
  induction ps with
  | nil =>
    exact ⟨[], [], by simp, by simp, by simp [Builds], rfl, by simp [Clean],
      by simp [centers], fun _ => rfl⟩
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    have hab := h (a,b) (by simp)
    have hrest : Clean base m ps := fun p hp => h p (by simp [hp])
    obtain ⟨ys,ts,hn,hd,hw,hc,hclean,hsize,hfold⟩ := ih hrest
    by_cases ha : a ∈ centers ps
    · obtain ⟨v,hv⟩ := center_witness (ps := ts) (hc.symm ▸ ha)
      have hold := hclean (a,v) hv
      obtain ⟨pre,post,hsp⟩ := List.append_of_mem hv
      subst ts
      have hb : b ∈ base ++ ys := List.mem_append_left _ hab.2.1
      obtain ⟨zs,zn,zd,zw,mono,hnew,hlen⟩ := extendBuild base ys hn hd hw v b hold.2.1 hb
      refine ⟨zs, pre ++ (a,v ||| b) :: post, zn, zd, zw, ?_, ?_, ?_, ?_⟩
      · rw [centers_split, hc, centers_cons, Finset.insert_eq_of_mem ha]
      · intro t ht
        rcases List.mem_append.mp ht with hpre | hpost
        · have ht' := hclean t (List.mem_append_left _ hpre)
          exact ⟨mono _ ht'.1, mono _ ht'.2.1, ht'.2.2⟩
        · rcases List.mem_cons.mp hpost with rfl | hpost
          · exact ⟨mono _ hold.1, hnew, clean_merge a v b m hold.2.2 hab.2.2⟩
          · have ht' := hclean t (List.mem_append_right _ (List.mem_cons_of_mem _ hpost))
            exact ⟨mono _ ht'.1, mono _ ht'.2.1, ht'.2.2⟩
      · rw [centers_cons, Finset.insert_eq_of_mem ha]
        simp only [List.length_append, List.length_cons] at hsize ⊢
        omega
      · intro seed
        rw [fold_merge]
        exact hfold (seed ||| (a &&& b))
    · refine ⟨ys, (a,b)::ts, hn, hd, hw, ?_, ?_, ?_, ?_⟩
      · simp [centers_cons, hc]
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨List.mem_append_left _ hab.1, List.mem_append_left _ hab.2.1, hab.2.2⟩
        · exact hclean p hp
      · rw [centers_cons, Finset.card_insert_of_notMem ha]
        simp only [List.length_cons]
        omega
      · intro seed
        exact hfold (seed ||| (a &&& b))

end PEqualNP.Outside.L_meta_19137


theorem PEqualNP.Outside.L_meta_19137 :
    ∀ (x1 : List ℕ) (x2 : List (ℕ × ℕ)) (x3 x4 : ℕ), x2 ≠ [] →
      (∀ x6 ∈ x2, x6.1 ∈ x1 ∧ x6.2 ∈ x1 ∧ x6.1 &&& x6.2 &&& x3 = (0 : ℕ)) →
      ∃ (x7 : List ℕ) (x8 : List (ℕ × ℕ)), x7.Nodup ∧ (∀ x9 ∈ x7, x9 ∉ x1) ∧ x8 ≠ [] ∧
      x7.length + (2 : ℕ) * x8.length ≤ x2.length + (List.map Prod.fst x2).toFinset.card ∧
      (∀ (x9 : Fin x7.length), have x10 : List ℕ := x1 ++ List.take (↑x9) x7;
        ∃ x11 ∈ x10, ∃ x12 ∈ x10, x7.get x9 = x11 ||| x12) ∧
      (∀ x9 ∈ x8, x9.1 ∈ x1 ++ x7 ∧ x9.2 ∈ x1 ++ x7 ∧ x9.1 &&& x9.2 &&& x3 = (0 : ℕ)) ∧
      List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x8 =
      List.foldl (fun (x9 : ℕ) (x10 : ℕ × ℕ) => x9 ||| x10.1 &&& x10.2) x4 x2 := by
  intro base ps m seed hne hc
  obtain ⟨ys,ts,hn,hd,hw,hsets,hclean,hsize,hfold⟩ :=
    PEqualNP.Outside.L_meta_19137.compress base m ps hc
  refine ⟨ys,ts,hn,hd,?_,hsize,hw,hclean,hfold seed⟩
  intro ht
  subst ts
  cases ps with
  | nil => exact hne rfl
  | cons p ps =>
    have hm : p.1 ∈ PEqualNP.Outside.L_meta_19137.centers (p :: ps) :=
      by simp [PEqualNP.Outside.L_meta_19137.centers]
    rw [← hsets] at hm
    simpa [PEqualNP.Outside.L_meta_19137.centers] using hm
