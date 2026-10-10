import Rudin.PMA.Chapter06.Basic

noncomputable section
open Set
open scoped BigOperators

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.3: Refinement and common refinement -/

/-- Every coarse partition point occurs in the fine partition; repetitions do not matter. -/
def Partition.Refines {a b : ℝ} (Q P : Partition a b) : Prop :=
  Set.range P.point ⊆ Set.range Q.point

private def pathCost (c : ℝ → ℝ → ℝ) (b x : ℝ) : List ℝ → ℝ
  | [] => c x b
  | y :: ys => c x y + pathCost c b y ys

private theorem pathCost_refinement (c : ℝ → ℝ → ℝ) {a b : ℝ}
    (hzero : ∀ x ∈ Icc a b, c x x = 0)
    (hsplit : ∀ x y z, a ≤ x → x ≤ y → y ≤ z → z ≤ b →
      c x z ≤ c x y + c y z)
    (ys : List ℝ) :
    ∀ (xs : List ℝ) (x : ℝ), a ≤ x → x ≤ b →
      xs.Pairwise (· ≤ ·) → ys.Pairwise (· ≤ ·) →
      (∀ z ∈ xs, x ≤ z ∧ z ≤ b) → (∀ z ∈ ys, x ≤ z ∧ z ≤ b) →
      (∀ z ∈ xs, z = x ∨ z ∈ ys) →
      pathCost c b x xs ≤ pathCost c b x ys := by
  induction ys with
  | nil =>
      intro xs
      induction xs with
      | nil => intros; exact le_rfl
      | cons z zs ih =>
          intro x hax hxb hxs hys hx hy hsub
          have hzx : z = x := (hsub z (by simp)).resolve_right (by simp)
          subst z
          have ih' := ih x hax hxb hxs.tail hys
            (fun t ht => hx t (by simp [ht])) hy
            (fun t ht => hsub t (by simp [ht]))
          simpa [pathCost, hzero x ⟨hax, hxb⟩] using ih'
  | cons y ys ih =>
      intro xs
      induction xs with
      | nil =>
          intro x hax hxb hxs hys hx hy hsub
          have hxy := (hy y (by simp)).1
          have hyb := (hy y (by simp)).2
          have ih' := ih [] y (hax.trans hxy) hyb (by simp) hys.tail
            (by simp) (fun t ht => ⟨(List.pairwise_cons.mp hys).1 t ht,
              (hy t (by simp [ht])).2⟩) (by simp)
          exact (hsplit x y b hax hxy hyb le_rfl).trans
            (by simpa [pathCost] using add_le_add_left ih' (c x y))
      | cons z zs ihxs =>
          intro x hax hxb hxs hys hx hy hsub
          have hxz := (hx z (by simp)).1
          have hzb := (hx z (by simp)).2
          have hxy := (hy y (by simp)).1
          have hyb := (hy y (by simp)).2
          by_cases hzx : z = x
          · subst z
            have ih' := ihxs x hax hxb hxs.tail hys
              (fun t ht => hx t (by simp [ht])) hy
              (fun t ht => hsub t (by simp [ht]))
            simpa [pathCost, hzero x ⟨hax, hxb⟩] using ih'
          · have hzmem : z ∈ y :: ys := (hsub z (by simp)).resolve_left hzx
            have hyz : y ≤ z := by
              rcases List.mem_cons.mp hzmem with h | h
              · exact le_of_eq h.symm
              · exact (List.pairwise_cons.mp hys).1 z h
            have hysbounds : ∀ t ∈ ys, y ≤ t ∧ t ≤ b := fun t ht =>
              ⟨(List.pairwise_cons.mp hys).1 t ht, (hy t (by simp [ht])).2⟩
            by_cases hzy : z = y
            · subst z
              have ih' := ih zs y (hax.trans hxy) hyb hxs.tail hys.tail
                (fun t ht => ⟨(List.pairwise_cons.mp hxs).1 t ht,
                  (hx t (by simp [ht])).2⟩) hysbounds (by
                    intro t ht
                    rcases hsub t (by simp [ht]) with h | h
                    · have hyt := (List.pairwise_cons.mp hxs).1 t ht
                      exact False.elim (hzx (le_antisymm (h ▸ hyt) hxy))
                    · exact List.mem_cons.mp h)
              simpa [pathCost] using add_le_add_left ih' (c x y)
            · have hyzlt : y < z := lt_of_le_of_ne hyz (Ne.symm hzy)
              have ih' := ih (z :: zs) y (hax.trans hxy) hyb hxs hys.tail
                (fun t ht => ⟨hyz.trans (by
                  rcases List.mem_cons.mp ht with h | h
                  · exact le_of_eq h.symm
                  · exact (List.pairwise_cons.mp hxs).1 t h),
                  (hx t ht).2⟩) hysbounds (by
                    intro t ht
                    have hzt : z ≤ t := by
                      rcases List.mem_cons.mp ht with h | h
                      · exact le_of_eq h.symm
                      · exact (List.pairwise_cons.mp hxs).1 t h
                    rcases hsub t ht with h | h
                    · exact False.elim (hzx (le_antisymm (h ▸ hzt) hxz))
                    · rcases List.mem_cons.mp h with h | h
                      · exact False.elim ((not_le_of_gt hyzlt) (h ▸ hzt))
                      · exact Or.inr h)
              calc
                pathCost c b x (z :: zs) = c x z + pathCost c b z zs := rfl
                _ ≤ (c x y + c y z) + pathCost c b z zs := by
                  linarith [hsplit x y z hax hxy hyz hzb]
                _ = c x y + pathCost c b y (z :: zs) := by simp [pathCost, add_assoc]
                _ ≤ c x y + pathCost c b y ys := by linarith [ih']
                _ = pathCost c b x (y :: ys) := rfl

private theorem pathCost_ofFn (c : ℝ → ℝ → ℝ) (x b : ℝ) :
    ∀ {n : ℕ} (p : Fin (n + 1) → ℝ),
      pathCost c b x (List.ofFn p) = c x (p 0) +
        (∑ i : Fin n, c (p i.castSucc) (p i.succ)) + c (p (Fin.last n)) b := by
  intro n
  induction n generalizing x with
  | zero => intro p; simp [List.ofFn_succ, pathCost]
  | succ n ih =>
      intro p
      rw [List.ofFn_succ, pathCost, ih]
      simp [Fin.sum_univ_succ, add_assoc]

private theorem refinement_point_mem {a b : ℝ} (P : Partition a b)
    (i : Fin (P.n + 1)) : P.point i ∈ Icc a b := by
  constructor
  · simpa only [P.left] using P.mono (Fin.zero_le i)
  · simpa only [P.right] using P.mono (Fin.le_last i)

theorem pma6_3_common_refinement {a b : ℝ} (P Q : Partition a b) :
    ∃ R : Partition a b,
      Set.range R.point = Set.range P.point ∪ Set.range Q.point ∧
        R.Refines P ∧ R.Refines Q := by
  classical
  let s : Finset ℝ := Finset.univ.image P.point ∪ Finset.univ.image Q.point
  have ha : a ∈ s := by simp [s, ← P.left]
  have hb : b ∈ s := by simp [s, ← P.right]
  have hs : s.Nonempty := ⟨a, ha⟩
  have hc : s.card = (s.card - 1) + 1 := by have := hs.card_pos; omega
  let e : Fin (s.card - 1 + 1) ↪o ℝ := s.orderEmbOfFin hc
  have herange : Set.range e = (s : Set ℝ) := Finset.range_orderEmbOfFin s hc
  have hemem (i) : e i ∈ Icc a b := by
    have h := s.orderEmbOfFin_mem hc i
    simp only [s, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at h
    rcases h with ⟨j, hj⟩ | ⟨j, hj⟩
    · have he : e i = P.point j := hj.symm
      rw [he]; exact refinement_point_mem P j
    · have he : e i = Q.point j := hj.symm
      rw [he]; exact refinement_point_mem Q j
  have hel : e 0 = a := by
    have ha' : a ∈ Set.range e := by rw [herange]; exact ha
    obtain ⟨i, hi⟩ := ha'
    exact le_antisymm (hi ▸ e.monotone (Fin.zero_le i)) (hemem 0).1
  have her : e (Fin.last (s.card - 1)) = b := by
    have hb' : b ∈ Set.range e := by rw [herange]; exact hb
    obtain ⟨i, hi⟩ := hb'
    exact le_antisymm (hemem _).2 (hi ▸ e.monotone (Fin.le_last i))
  let R : Partition a b := ⟨s.card - 1, e, e.monotone, hel, her⟩
  have hR : Set.range R.point = Set.range P.point ∪ Set.range Q.point := by
    change Set.range e = _
    rw [herange]
    ext x
    simp [s]
  exact ⟨R, hR, by rw [Partition.Refines, hR]; exact subset_union_left,
    by rw [Partition.Refines, hR]; exact subset_union_right⟩

private theorem chain_sum_refinement {a b : ℝ} (P Q : Partition a b)
    (hQP : Q.Refines P) (c : ℝ → ℝ → ℝ)
    (hzero : ∀ x ∈ Icc a b, c x x = 0)
    (hsplit : ∀ x y z, a ≤ x → x ≤ y → y ≤ z → z ≤ b →
      c x z ≤ c x y + c y z) :
    (∑ i : Fin P.n, c (P.point i.castSucc) (P.point i.succ)) ≤
      ∑ i : Fin Q.n, c (Q.point i.castSucc) (Q.point i.succ) := by
  have hab : a ≤ b := by simpa [P.right] using (refinement_point_mem P (Fin.last P.n)).1
  have h := pathCost_refinement c hzero hsplit (List.ofFn Q.point)
    (List.ofFn P.point) a le_rfl hab
    (List.pairwise_ofFn.mpr (fun _ _ hij => P.mono hij.le))
    (List.pairwise_ofFn.mpr (fun _ _ hij => Q.mono hij.le))
    (by intro z hz; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz; exact refinement_point_mem P i)
    (by intro z hz; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz; exact refinement_point_mem Q i)
    (by
      intro z hz
      apply Or.inr
      rw [List.mem_ofFn'] at hz ⊢
      exact hQP hz)
  rw [pathCost_ofFn, pathCost_ofFn] at h
  simpa only [P.left, P.right, Q.left, Q.right,
    zero_add, add_zero,
    hzero a ⟨le_rfl, hab⟩, hzero b ⟨hab, le_rfl⟩] using h

private theorem refinement_image_bounds {f : ℝ → ℝ} {a b x z : ℝ}
    (hf : BoundedOn f a b) (hax : a ≤ x) (hzb : z ≤ b) :
    BddBelow (f '' Icc x z) ∧ BddAbove (f '' Icc x z) := by
  obtain ⟨M, hM⟩ := hf
  constructor
  · refine ⟨-M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (abs_le.mp (hM t ⟨hax.trans ht.1, ht.2.trans hzb⟩)).1
  · refine ⟨M, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact (abs_le.mp (hM t ⟨hax.trans ht.1, ht.2.trans hzb⟩)).2

/-! ### PMA-6.4: Monotonicity of weighted sums under refinement -/

theorem pma6_4_lower {f α : ℝ → ℝ} {a b : ℝ} (P Q : Partition a b)
    (hQP : Q.Refines P) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    lowerSum f α P ≤ lowerSum f α Q := by
  apply chain_sum_refinement P Q hQP
    (fun x y => sInf (f '' Icc x y) * (α y - α x))
  · intro x hx; simp
  · intro x y z hax hxy hyz hzb
    have hx : x ∈ Icc a b := ⟨hax, (hxy.trans hyz).trans hzb⟩
    have hy : y ∈ Icc a b := ⟨hax.trans hxy, hyz.trans hzb⟩
    have hz : z ∈ Icc a b := ⟨hax.trans (hxy.trans hyz), hzb⟩
    have h₁ : sInf (f '' Icc x z) ≤ sInf (f '' Icc x y) :=
      csInf_le_csInf (refinement_image_bounds hf hax hzb).1
        ((nonempty_Icc.mpr hxy).image f) (image_mono (Icc_subset_Icc_right hyz))
    have h₂ : sInf (f '' Icc x z) ≤ sInf (f '' Icc y z) :=
      csInf_le_csInf (refinement_image_bounds hf hax hzb).1
        ((nonempty_Icc.mpr hyz).image f) (image_mono (Icc_subset_Icc_left hxy))
    have hm₁ := mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr (hα hx hy hxy))
    have hm₂ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr (hα hy hz hyz))
    nlinarith

theorem pma6_4_upper {f α : ℝ → ℝ} {a b : ℝ} (P Q : Partition a b)
    (hQP : Q.Refines P) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    upperSum f α Q ≤ upperSum f α P := by
  have h := chain_sum_refinement P Q hQP
    (fun x y => -(sSup (f '' Icc x y) * (α y - α x)))
    (by intro x hx; simp) (by
      intro x y z hax hxy hyz hzb
      have hx : x ∈ Icc a b := ⟨hax, (hxy.trans hyz).trans hzb⟩
      have hy : y ∈ Icc a b := ⟨hax.trans hxy, hyz.trans hzb⟩
      have hz : z ∈ Icc a b := ⟨hax.trans (hxy.trans hyz), hzb⟩
      have h₁ : sSup (f '' Icc x y) ≤ sSup (f '' Icc x z) :=
        csSup_le_csSup (refinement_image_bounds hf hax hzb).2
          ((nonempty_Icc.mpr hxy).image f) (image_mono (Icc_subset_Icc_right hyz))
      have h₂ : sSup (f '' Icc y z) ≤ sSup (f '' Icc x z) :=
        csSup_le_csSup (refinement_image_bounds hf hax hzb).2
          ((nonempty_Icc.mpr hyz).image f) (image_mono (Icc_subset_Icc_left hxy))
      have hm₁ := mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr (hα hx hy hxy))
      have hm₂ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr (hα hy hz hyz))
      nlinarith)
  simpa [upperSum, cellUpper, Partition.cell, Partition.weight] using h

theorem pma6_4 {f α : ℝ → ℝ} {a b : ℝ} (P Q : Partition a b)
    (hQP : Q.Refines P) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    lowerSum f α P ≤ lowerSum f α Q ∧ upperSum f α Q ≤ upperSum f α P :=
  ⟨pma6_4_lower P Q hQP hf hα, pma6_4_upper P Q hQP hf hα⟩

theorem pma6_3_repetition_invariant {f α : ℝ → ℝ} {a b : ℝ}
    (P Q : Partition a b) (hPQ : Set.range P.point = Set.range Q.point)
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    lowerSum f α P = lowerSum f α Q ∧ upperSum f α P = upperSum f α Q := by
  have h₁ := pma6_4 P Q hPQ.subset hf hα
  have h₂ := pma6_4 Q P hPQ.symm.subset hf hα
  exact ⟨le_antisymm h₁.1 h₂.1, le_antisymm h₂.2 h₁.2⟩

end Rudin.PMA.Chapter06
