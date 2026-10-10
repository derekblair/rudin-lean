import Rudin.PMA.Chapter06.Integrability
import Rudin.PMA.Chapter06.Split

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter06

/-! Local Darboux control when either function is continuous at the reference point. -/

theorem endpoint_local_gap_lt {f α : ℝ → ℝ} {a b e ε : ℝ}
    (he : e ∈ Icc a b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousWithinAt f (Icc a b) e ∨ ContinuousWithinAt α (Icc a b) e)
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ (u v : ℝ) (huv : u ≤ v), Icc u v ⊆ Icc a b →
      (∀ x ∈ Icc u v, dist x e < δ) →
      upperSum f α (Partition.single huv) - lowerSum f α (Partition.single huv) < ε := by
  have hab : a ≤ b := he.1.trans he.2
  have hmass : 0 ≤ α b - α a := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  rcases hc with hc | hc
  · let η := ε / (2 * (α b - α a + 1))
    have hden : 0 < 2 * (α b - α a + 1) := by positivity
    have hη : 0 < η := div_pos hε hden
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hc η hη
    refine ⟨δ, hδ, fun u v huv hsub hnear => ?_⟩
    let P := Partition.single huv
    have hgap : upperSum f α P - lowerSum f α P ≤ 2 * η * (α v - α u) := by
      apply gap_le_of_cell_gaps (hα.mono hsub) P
      intro i
      apply cell_gap_le_of_oscillation P i
      intro x hx y hy
      have hx' := P.cell_subset i hx
      have hy' := P.cell_subset i hy
      have hfx : |f x - f e| < η := by
        simpa only [Real.dist_eq] using hcont (hsub hx') (hnear x hx')
      have hfy : |f y - f e| < η := by
        simpa only [Real.dist_eq] using hcont (hsub hy') (hnear y hy')
      have ht := abs_sub_le (f x) (f e) (f y)
      rw [abs_sub_comm (f e) (f y)] at ht
      linarith
    have hu := hsub (show u ∈ Icc u v from ⟨le_rfl, huv⟩)
    have hv := hsub (show v ∈ Icc u v from ⟨huv, le_rfl⟩)
    have hαu := hα ⟨le_rfl, hab⟩ hu hu.1
    have hαv := hα hv ⟨hab, le_rfl⟩ hv.2
    have hmul : 2 * η * (α v - α u) ≤ 2 * η * (α b - α a) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have heq : η * (2 * (α b - α a + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    exact hgap.trans_lt (by nlinarith)
  · obtain ⟨M, hM⟩ := hf
    let η := ε / (4 * (|M| + 1))
    have hden : 0 < 4 * (|M| + 1) := by positivity
    have hη : 0 < η := div_pos hε hden
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuousWithinAt_iff.mp hc η hη
    refine ⟨δ, hδ, fun u v huv hsub hnear => ?_⟩
    let P := Partition.single huv
    have hgap : upperSum f α P - lowerSum f α P ≤ 2 * |M| * (α v - α u) := by
      apply gap_le_of_cell_gaps (hα.mono hsub) P
      intro i
      apply cell_gap_le_of_oscillation P i
      intro x hx y hy
      have hfx := (hM x (hsub (P.cell_subset i hx))).trans (le_abs_self M)
      have hfy := (hM y (hsub (P.cell_subset i hy))).trans (le_abs_self M)
      have ht := abs_sub (f x) (f y)
      linarith
    have hu : u ∈ Icc u v := ⟨le_rfl, huv⟩
    have hv : v ∈ Icc u v := ⟨huv, le_rfl⟩
    have hαu : |α u - α e| < η := by
      simpa only [Real.dist_eq] using hcont (hsub hu) (hnear u hu)
    have hαv : |α v - α e| < η := by
      simpa only [Real.dist_eq] using hcont (hsub hv) (hnear v hv)
    have hvu : α v - α u ≤ 2 * η := by
      have hu' := abs_lt.mp hαu
      have hv' := abs_lt.mp hαv
      linarith
    have hmul := mul_le_mul_of_nonneg_left hvu (show 0 ≤ 2 * |M| by positivity)
    have heq : η * (4 * (|M| + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    exact hgap.trans_lt (by nlinarith)

/-! The accepted endpoint helper for the finite-discontinuity theorem. -/

theorem rsIntegrable_of_continuousOn_Ioo {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousOn f (Ioo a b))
    (ha : ContinuousWithinAt f (Icc a b) a ∨ ContinuousWithinAt α (Icc a b) a)
    (hb : ContinuousWithinAt f (Icc a b) b ∨ ContinuousWithinAt α (Icc a b) b) :
    RSIntegrable f α a b := by
  apply (rsIntegrable_iff_gap hab.le hf hα).mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨δa, hδa, htaila⟩ := endpoint_local_gap_lt ⟨le_rfl, hab.le⟩ hf hα ha hthird
  obtain ⟨δb, hδb, htailb⟩ := endpoint_local_gap_lt ⟨hab.le, le_rfl⟩ hf hα hb hthird
  obtain ⟨u, hau, hu⟩ := exists_between (show a < min ((a + b) / 2) (a + δa) from
    lt_min (by linarith) (by linarith))
  obtain ⟨v, hv, hvb⟩ := exists_between (show max ((a + b) / 2) (b - δb) < b from
    max_lt (by linarith) (by linarith))
  have hu_mid := hu.trans_le (min_le_left _ _)
  have hu_delta := hu.trans_le (min_le_right _ _)
  have hv_mid := (le_max_left _ _).trans_lt hv
  have hv_delta := (le_max_right _ _).trans_lt hv
  have huv : u < v := hu_mid.trans hv_mid
  have hub : u < b := huv.trans hvb
  have hav : a < v := hau.trans huv
  have hsuba : Icc a u ⊆ Icc a b := fun _ hx => ⟨hx.1, hx.2.trans hub.le⟩
  have hsubb : Icc v b ⊆ Icc a b := fun _ hx => ⟨hav.le.trans hx.1, hx.2⟩
  have hLa := htaila a u hau.le hsuba (by
    intro x hx
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2])
  have hRb := htailb v b hvb.le hsubb (by
    intro x hx
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2)]
    linarith [hx.1])
  have hmiddle : RSIntegrable f α u v := rsIntegrable_of_continuousOn huv.le
    (hc.mono (fun _ hx => ⟨hau.trans_le hx.1, hx.2.trans_lt hvb⟩))
    (hα.mono (fun _ hx => ⟨hau.le.trans hx.1, hx.2.trans hvb.le⟩))
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hmiddle.1 hmiddle.2.1 hmiddle.2.2.1).mp hmiddle
    (ε / 3) hthird
  refine ⟨splitAppendPartition (Partition.single hau.le) (splitAppendPartition P (Partition.single hvb.le)), ?_⟩
  rw [split_append_upperSum, split_append_lowerSum, split_append_upperSum, split_append_lowerSum]
  linarith

#print axioms endpoint_local_gap_lt
#print axioms rsIntegrable_of_continuousOn_Ioo

end Rudin.PMA.Chapter06
