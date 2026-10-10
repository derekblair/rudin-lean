import Rudin.PMA.Chapter06.Basic
import Rudin.PMA.Chapter06.Refinement
import Rudin.PMA.Chapter06.Criterion

noncomputable section
open Set
open scoped BigOperators

namespace Rudin.PMA.Chapter06

/-! Native interval splitting, including cuts at either endpoint. -/

def splitLeftPartition {a b c : ℝ} (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b) :
    Partition a c where
  n := P.n
  point i := min (P.point i) c
  mono := fun _ _ hij => min_le_min (P.mono hij) le_rfl
  left := by simp [P.left, min_eq_left hac]
  right := by simp [P.right, min_eq_right hcb]

def splitRightPartition {a b c : ℝ} (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b) :
    Partition c b where
  n := P.n
  point i := max (P.point i) c
  mono := fun _ _ hij => max_le_max (P.mono hij) le_rfl
  left := by simp [P.left, max_eq_right hac]
  right := by simp [P.right, max_eq_left hcb]

theorem split_bounded_left {a b c : ℝ} {f : ℝ → ℝ}
    (hf : BoundedOn f a b) (hcb : c ≤ b) : BoundedOn f a c := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun x hx => hM x ⟨hx.1, hx.2.trans hcb⟩⟩

theorem split_bounded_right {a b c : ℝ} {f : ℝ → ℝ}
    (hf : BoundedOn f a b) (hac : a ≤ c) : BoundedOn f c b := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun x hx => hM x ⟨hac.trans hx.1, hx.2⟩⟩

private theorem split_cost_clamp {a b c x y : ℝ} (cost : ℝ → ℝ → ℝ)
    (hzero : ∀ t ∈ Icc a b, cost t t = 0)
    (hsplit : ∀ u v w, a ≤ u → u ≤ v → v ≤ w → w ≤ b →
      cost u w ≤ cost u v + cost v w)
    (hac : a ≤ c) (hcb : c ≤ b) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    cost x y ≤ cost (min x c) (min y c) + cost (max x c) (max y c) := by
  by_cases hyc : y ≤ c
  · have hxc := hxy.trans hyc
    simp [min_eq_left hxc, min_eq_left hyc, max_eq_right hxc, max_eq_right hyc,
      hzero c ⟨hac, hcb⟩]
  · by_cases hcx : c ≤ x
    · have hcy := hcx.trans hxy
      simp [min_eq_right hcx, min_eq_right hcy, max_eq_left hcx, max_eq_left hcy,
        hzero c ⟨hac, hcb⟩]
    · have hxc : x ≤ c := le_of_not_ge hcx
      have hcy : c ≤ y := le_of_not_ge hyc
      simpa [min_eq_left hxc, min_eq_right hcy, max_eq_right hxc, max_eq_left hcy]
        using hsplit x c y hax hxc hcy hyb

theorem split_lower_sums {a b c : ℝ} {f α : ℝ → ℝ}
    (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    lowerSum f α P ≤ lowerSum f α (splitLeftPartition P hac hcb) +
      lowerSum f α (splitRightPartition P hac hcb) := by
  change (∑ i : Fin P.n, cellLower f P i * P.weight α i) ≤
    (∑ i : Fin P.n, cellLower f (splitLeftPartition P hac hcb) i *
      (splitLeftPartition P hac hcb).weight α i) +
    (∑ i : Fin P.n, cellLower f (splitRightPartition P hac hcb) i *
      (splitRightPartition P hac hcb).weight α i)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (sInf (f '' Icc (P.point i.castSucc) (P.point i.succ))) *
    (α (P.point i.succ) - α (P.point i.castSucc)) ≤ _
  apply split_cost_clamp (fun x y => sInf (f '' Icc x y) * (α y - α x))
    (by intro x hx; simp) ?_ hac hcb
    (P.point_mem i.castSucc).1 (P.cell_order i) (P.point_mem i.succ).2
  intro x y z hax hxy hyz hzb
  have hx : x ∈ Icc a b := ⟨hax, (hxy.trans hyz).trans hzb⟩
  have hy : y ∈ Icc a b := ⟨hax.trans hxy, hyz.trans hzb⟩
  have hz : z ∈ Icc a b := ⟨hax.trans (hxy.trans hyz), hzb⟩
  have hbdd := hf.bddBelow_image (s := Icc x z) (Icc_subset_Icc hax hzb)
  have h₁ : sInf (f '' Icc x z) ≤ sInf (f '' Icc x y) :=
    csInf_le_csInf hbdd ((nonempty_Icc.mpr hxy).image f)
      (image_mono (Icc_subset_Icc_right hyz))
  have h₂ : sInf (f '' Icc x z) ≤ sInf (f '' Icc y z) :=
    csInf_le_csInf hbdd ((nonempty_Icc.mpr hyz).image f)
      (image_mono (Icc_subset_Icc_left hxy))
  have hm₁ := mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr (hα hx hy hxy))
  have hm₂ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr (hα hy hz hyz))
  nlinarith

theorem split_upper_sums {a b c : ℝ} {f α : ℝ → ℝ}
    (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    upperSum f α (splitLeftPartition P hac hcb) +
      upperSum f α (splitRightPartition P hac hcb) ≤ upperSum f α P := by
  change (∑ i : Fin P.n, cellUpper f (splitLeftPartition P hac hcb) i *
      (splitLeftPartition P hac hcb).weight α i) +
    (∑ i : Fin P.n, cellUpper f (splitRightPartition P hac hcb) i *
      (splitRightPartition P hac hcb).weight α i) ≤
    ∑ i : Fin P.n, cellUpper f P i * P.weight α i
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have h := split_cost_clamp (a := a) (b := b) (c := c)
    (x := P.point i.castSucc) (y := P.point i.succ)
    (fun x y => -(sSup (f '' Icc x y) * (α y - α x)))
    (by intro x hx; simp) (by
      intro x y z hax hxy hyz hzb
      have hx : x ∈ Icc a b := ⟨hax, (hxy.trans hyz).trans hzb⟩
      have hy : y ∈ Icc a b := ⟨hax.trans hxy, hyz.trans hzb⟩
      have hz : z ∈ Icc a b := ⟨hax.trans (hxy.trans hyz), hzb⟩
      have hbdd := hf.bddAbove_image (s := Icc x z) (Icc_subset_Icc hax hzb)
      have h₁ : sSup (f '' Icc x y) ≤ sSup (f '' Icc x z) :=
        csSup_le_csSup hbdd ((nonempty_Icc.mpr hxy).image f)
          (image_mono (Icc_subset_Icc_right hyz))
      have h₂ : sSup (f '' Icc y z) ≤ sSup (f '' Icc x z) :=
        csSup_le_csSup hbdd ((nonempty_Icc.mpr hyz).image f)
          (image_mono (Icc_subset_Icc_left hxy))
      have hm₁ := mul_le_mul_of_nonneg_right h₁ (sub_nonneg.mpr (hα hx hy hxy))
      have hm₂ := mul_le_mul_of_nonneg_right h₂ (sub_nonneg.mpr (hα hy hz hyz))
      nlinarith) hac hcb (P.point_mem i.castSucc).1 (P.cell_order i) (P.point_mem i.succ).2
  change _ ≤ sSup (f '' Icc (P.point i.castSucc) (P.point i.succ)) *
    (α (P.point i.succ) - α (P.point i.castSucc))
  dsimp only [cellUpper, Partition.cell, Partition.weight, splitLeftPartition,
    splitRightPartition]
  linarith

theorem split_gap_bounds {a b c : ℝ} {f α : ℝ → ℝ}
    (P : Partition a b) (hac : a ≤ c) (hcb : c ≤ b)
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    (upperSum f α (splitLeftPartition P hac hcb) -
      lowerSum f α (splitLeftPartition P hac hcb) ≤ upperSum f α P - lowerSum f α P) ∧
    (upperSum f α (splitRightPartition P hac hcb) -
      lowerSum f α (splitRightPartition P hac hcb) ≤ upperSum f α P - lowerSum f α P) := by
  have hl := split_lower_sums P hac hcb hf hα
  have hu := split_upper_sums P hac hcb hf hα
  have hnL := lowerSum_le_upperSum (split_bounded_left hf hcb)
    (hα.mono (Icc_subset_Icc_right hcb)) (splitLeftPartition P hac hcb)
  have hnR := lowerSum_le_upperSum (split_bounded_right hf hac)
    (hα.mono (Icc_subset_Icc_left hac)) (splitRightPartition P hac hcb)
  constructor <;> linarith

theorem split_rsIntegrable {a b c : ℝ} {f α : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (h : RSIntegrable f α a b) :
    RSIntegrable f α a c ∧ RSIntegrable f α c b := by
  have hleft := rsIntegrable_iff_gap hac (split_bounded_left h.2.1 hcb)
    (h.2.2.1.mono (Icc_subset_Icc_right hcb))
  have hright := rsIntegrable_iff_gap hcb (split_bounded_right h.2.1 hac)
    (h.2.2.1.mono (Icc_subset_Icc_left hac))
  have hgap := (rsIntegrable_iff_gap h.1 h.2.1 h.2.2.1).mp h
  constructor
  · apply hleft.mpr
    intro ε hε
    obtain ⟨P, hP⟩ := hgap ε hε
    exact ⟨splitLeftPartition P hac hcb, (split_gap_bounds P hac hcb h.2.1 h.2.2.1).1.trans_lt hP⟩
  · apply hright.mpr
    intro ε hε
    obtain ⟨P, hP⟩ := hgap ε hε
    exact ⟨splitRightPartition P hac hcb, (split_gap_bounds P hac hcb h.2.1 h.2.2.1).2.trans_lt hP⟩

theorem split_rsIntegral {a b c : ℝ} {f α : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (h : RSIntegrable f α a b) :
    RSIntegral f α a b = RSIntegral f α a c + RSIntegral f α c b := by
  have hpieces := split_rsIntegrable hac hcb h
  have hgap := (rsIntegrable_iff_gap h.1 h.2.1 h.2.2.1).mp h
  have hnear : ∀ ε : ℝ, 0 < ε →
      |RSIntegral f α a b - (RSIntegral f α a c + RSIntegral f α c b)| < ε := by
    intro ε hε
    obtain ⟨P, hP⟩ := hgap ε hε
    have hl := split_lower_sums P hac hcb h.2.1 h.2.2.1
    have hu := split_upper_sums P hac hcb h.2.1 h.2.2.1
    have hPL := rsIntegral_bounds hpieces.1 (splitLeftPartition P hac hcb)
    have hPR := rsIntegral_bounds hpieces.2 (splitRightPartition P hac hcb)
    have hI := rsIntegral_bounds h P
    apply abs_lt.mpr
    constructor <;> linarith [hPL.1, hPL.2, hPR.1, hPR.2, hI.1, hI.2]
  apply sub_eq_zero.mp
  apply abs_eq_zero.mp
  apply le_antisymm _ (abs_nonneg _)
  exact le_of_forall_pos_le_add (fun ε hε => by simpa using (hnear ε hε).le)

theorem split_ordered {a b c : ℝ} {f α : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) (h : RSIntegrable f α a b) :
    RSIntegrable f α a c ∧ RSIntegrable f α c b ∧
      RSIntegral f α a b = RSIntegral f α a c + RSIntegral f α c b :=
  ⟨(split_rsIntegrable hac hcb h).1, (split_rsIntegrable hac hcb h).2,
    split_rsIntegral hac hcb h⟩

/-- The source's strict interior split, with no added integrator regularity. -/
theorem pma6_12_split {a b c : ℝ} {f α : ℝ → ℝ}
    (hac : a < c) (hcb : c < b) (h : RSIntegrable f α a b) :
    RSIntegrable f α a c ∧ RSIntegrable f α c b ∧
      RSIntegral f α a b = RSIntegral f α a c + RSIntegral f α c b :=
  split_ordered hac.le hcb.le h

/-- Concatenation retains the common endpoint twice, creating one zero-width cell. -/
def splitAppendPartition {a b c : ℝ} (P : Partition a c) (Q : Partition c b) :
    Partition a b where
  n := P.n + Q.n + 1
  point i := Fin.append P.point Q.point
    (Fin.cast (show P.n + Q.n + 1 + 1 = (P.n + 1) + (Q.n + 1) by omega) i)
  mono := by
    have hp : (List.ofFn (Fin.append P.point Q.point)).Pairwise (· ≤ ·) := by
      rw [List.ofFn_fin_append, List.pairwise_append]
      refine ⟨List.pairwise_ofFn.mpr (fun _ _ hij => P.mono hij.le),
        List.pairwise_ofFn.mpr (fun _ _ hij => Q.mono hij.le), ?_⟩
      intro x hx y hy
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      exact (P.point_mem i).2.trans (Q.point_mem j).1
    have hm : Monotone (Fin.append P.point Q.point) := by
      intro i j hij
      rcases lt_or_eq_of_le hij with h | rfl
      · exact List.pairwise_ofFn.mp hp h
      · exact le_rfl
    intro i j hij
    apply hm
    exact hij
  left := by
    change Fin.append P.point Q.point (Fin.castAdd (Q.n + 1) 0) = a
    rw [Fin.append_left, P.left]
  right := by
    have hi : Fin.cast (show P.n + Q.n + 1 + 1 = (P.n + 1) + (Q.n + 1) by omega)
        (Fin.last (P.n + Q.n + 1)) = Fin.natAdd (P.n + 1) (Fin.last Q.n) := by
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_last, Fin.val_natAdd]
      omega
    rw [hi, Fin.append_right, Q.right]

theorem split_append_points {a b c : ℝ} (P : Partition a c) (Q : Partition c b) :
    List.ofFn (splitAppendPartition P Q).point = List.ofFn P.point ++ List.ofFn Q.point := by
  change List.ofFn (fun i : Fin (P.n + Q.n + 1 + 1) =>
    Fin.append P.point Q.point
      (Fin.cast (show P.n + Q.n + 1 + 1 = (P.n + 1) + (Q.n + 1) by omega) i)) = _
  rw [← List.ofFn_congr (show (P.n + 1) + (Q.n + 1) = P.n + Q.n + 1 + 1 by omega)]
  exact List.ofFn_fin_append P.point Q.point

private def splitPathCost (cost : ℝ → ℝ → ℝ) (x : ℝ) : List ℝ → ℝ
  | [] => 0
  | y :: ys => cost x y + splitPathCost cost y ys

private theorem splitPathCost_ofFn (cost : ℝ → ℝ → ℝ) (x : ℝ) :
    ∀ {n : ℕ} (p : Fin (n + 1) → ℝ),
      splitPathCost cost x (List.ofFn p) = cost x (p 0) +
        ∑ i : Fin n, cost (p i.castSucc) (p i.succ) := by
  intro n
  induction n generalizing x with
  | zero => intro p; simp [List.ofFn_succ, splitPathCost]
  | succ n ih =>
      intro p
      rw [List.ofFn_succ, splitPathCost, ih]
      simp [Fin.sum_univ_succ]

private theorem splitPathCost_append (cost : ℝ → ℝ → ℝ) (x : ℝ) (ys : List ℝ) :
    ∀ {n : ℕ} (p : Fin (n + 1) → ℝ),
      splitPathCost cost x (List.ofFn p ++ ys) = cost x (p 0) +
        (∑ i : Fin n, cost (p i.castSucc) (p i.succ)) +
          splitPathCost cost (p (Fin.last n)) ys := by
  intro n
  induction n generalizing x with
  | zero => intro p; simp [List.ofFn_succ, splitPathCost]
  | succ n ih =>
      intro p
      rw [List.ofFn_succ, List.cons_append, splitPathCost, ih]
      simp [Fin.sum_univ_succ, add_assoc]

private theorem split_append_cost {a b c : ℝ} (P : Partition a c) (Q : Partition c b)
    (cost : ℝ → ℝ → ℝ) (hzero : ∀ x, cost x x = 0) :
    (∑ i : Fin (splitAppendPartition P Q).n,
      cost ((splitAppendPartition P Q).point i.castSucc)
        ((splitAppendPartition P Q).point i.succ)) =
    (∑ i : Fin P.n, cost (P.point i.castSucc) (P.point i.succ)) +
      ∑ i : Fin Q.n, cost (Q.point i.castSucc) (Q.point i.succ) := by
  have h := congrArg (splitPathCost cost a) (split_append_points P Q)
  rw [splitPathCost_ofFn, splitPathCost_append, splitPathCost_ofFn] at h
  simpa only [(splitAppendPartition P Q).left, P.left, P.right, Q.left,
    hzero, zero_add] using h

theorem split_append_lowerSum {a b c : ℝ} (P : Partition a c) (Q : Partition c b)
    (f α : ℝ → ℝ) :
    lowerSum f α (splitAppendPartition P Q) = lowerSum f α P + lowerSum f α Q :=
  split_append_cost P Q (fun x y => sInf (f '' Icc x y) * (α y - α x))
    (by intro x; simp)

theorem split_append_upperSum {a b c : ℝ} (P : Partition a c) (Q : Partition c b)
    (f α : ℝ → ℝ) :
    upperSum f α (splitAppendPartition P Q) = upperSum f α P + upperSum f α Q :=
  split_append_cost P Q (fun x y => sSup (f '' Icc x y) * (α y - α x))
    (by intro x; simp)

theorem split_bounded_append {a b c : ℝ} {f : ℝ → ℝ}
    (hL : BoundedOn f a c) (hR : BoundedOn f c b) : BoundedOn f a b := by
  obtain ⟨M, hM⟩ := hL
  obtain ⟨N, hN⟩ := hR
  refine ⟨max M N, ?_⟩
  intro x hx
  rcases le_total x c with h | h
  · exact (hM x ⟨hx.1, h⟩).trans (le_max_left M N)
  · exact (hN x ⟨h, hx.2⟩).trans (le_max_right M N)

theorem split_monotone_append {a b c : ℝ} {α : ℝ → ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (hL : MonotoneOn α (Icc a c)) (hR : MonotoneOn α (Icc c b)) :
    MonotoneOn α (Icc a b) := by
  intro x hx y hy hxy
  by_cases hyc : y ≤ c
  · exact hL ⟨hx.1, hxy.trans hyc⟩ ⟨hy.1, hyc⟩ hxy
  · by_cases hcx : c ≤ x
    · exact hR ⟨hcx, hx.2⟩ ⟨hcx.trans hxy, hy.2⟩ hxy
    · have hxc : x ≤ c := le_of_not_ge hcx
      have hcy : c ≤ y := le_of_not_ge hyc
      exact (hL ⟨hx.1, hxc⟩ ⟨hac, le_rfl⟩ hxc).trans
        (hR ⟨le_rfl, hcb⟩ ⟨hcy, hy.2⟩ hcy)

theorem split_rsIntegrable_append {a b c : ℝ} {f α : ℝ → ℝ}
    (hL : RSIntegrable f α a c) (hR : RSIntegrable f α c b) :
    RSIntegrable f α a b := by
  have hf := split_bounded_append hL.2.1 hR.2.1
  have hα := split_monotone_append hL.1 hR.1 hL.2.2.1 hR.2.2.1
  apply (rsIntegrable_iff_gap (hL.1.trans hR.1) hf hα).mpr
  intro ε hε
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hL.1 hL.2.1 hL.2.2.1).mp hL
    (ε / 2) (by positivity)
  obtain ⟨Q, hQ⟩ := (rsIntegrable_iff_gap hR.1 hR.2.1 hR.2.2.1).mp hR
    (ε / 2) (by positivity)
  refine ⟨splitAppendPartition P Q, ?_⟩
  rw [split_append_lowerSum, split_append_upperSum]
  linarith

theorem split_append {a b c : ℝ} {f α : ℝ → ℝ}
    (hL : RSIntegrable f α a c) (hR : RSIntegrable f α c b) :
    RSIntegrable f α a b ∧
      RSIntegral f α a b = RSIntegral f α a c + RSIntegral f α c b := by
  have h := split_rsIntegrable_append hL hR
  exact ⟨h, split_rsIntegral hL.1 hR.1 h⟩

end Rudin.PMA.Chapter06
