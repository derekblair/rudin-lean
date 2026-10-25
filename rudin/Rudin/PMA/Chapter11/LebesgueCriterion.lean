import Rudin.PMA.Chapter11.Darboux

/-!
# PMA 11.33: the reverse Lebesgue criterion

Uniform closed-cell upper and lower Darboux envelopes converge at each point
of interval-relative continuity. Dominated convergence applied to their gap
then produces native Chapter 6 Riemann integrability. In particular the proof
does not assume measurability of the original bounded function.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter11.SecondHalf
open Rudin.PMA.Chapter06

variable {a b : ℝ}

theorem partitionStep_eq_zero (P : Partition a b) (c : Fin P.n → ℝ)
    {x : ℝ} (hx : x ∉ Ioc a b) : partitionStep P c x = 0 := by
  unfold partitionStep
  apply Finset.sum_eq_zero
  intro i hi
  apply indicator_of_notMem
  intro h
  exact hx ⟨(P.point_mem i.castSucc).1.trans_lt h.1, h.2.trans (P.point_mem i.succ).2⟩

theorem cell_envelopes_bounded {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (P : Partition a b) (i : Fin P.n) :
    -M ≤ cellLower f P i ∧ cellUpper f P i ≤ M := by
  constructor
  · apply le_csInf ((P.cell_nonempty i).image f)
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (P.cell_subset i hx))).1
  · apply csSup_le ((P.cell_nonempty i).image f)
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hM x (P.cell_subset i hx))).2

theorem step_gap_bounds {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (P : Partition a b) (x : ℝ) :
    0 ≤ upperStep f P x - lowerStep f P x ∧
    |upperStep f P x - lowerStep f P x| ≤ (Ioc a b).indicator (fun _ => 2 * M) x := by
  by_cases hx : x ∈ Ioc a b
  · obtain ⟨i, hi⟩ := partition_cell_exists P hx
    simp only [lowerStep, upperStep, partitionStep_eq P _ hi, indicator_of_mem hx]
    have hb := cell_envelopes_bounded hM P i
    have hl := cellLower_le_value (show BoundedOn f a b from ⟨M, hM⟩) P i ⟨hi.1.le, hi.2⟩
    have hu := value_le_cellUpper (show BoundedOn f a b from ⟨M, hM⟩) P i ⟨hi.1.le, hi.2⟩
    have hn : 0 ≤ cellUpper f P i - cellLower f P i := by linarith
    exact ⟨hn, by rw [abs_of_nonneg hn]; linarith⟩
  · simp [lowerStep, upperStep, partitionStep_eq_zero P _ hx, indicator_of_notMem hx]

theorem step_abs_bounds {f : ℝ → ℝ} {M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (P : Partition a b) (x : ℝ) :
    |lowerStep f P x| ≤ (Ioc a b).indicator (fun _ => M) x ∧
    |upperStep f P x| ≤ (Ioc a b).indicator (fun _ => M) x := by
  by_cases hx : x ∈ Ioc a b
  · obtain ⟨i, hi⟩ := partition_cell_exists P hx
    simp only [lowerStep, upperStep, partitionStep_eq P _ hi, indicator_of_mem hx]
    have hb := cell_envelopes_bounded hM P i
    have hl := cellLower_le_value (show BoundedOn f a b from ⟨M, hM⟩) P i ⟨hi.1.le, hi.2⟩
    have hu := value_le_cellUpper (show BoundedOn f a b from ⟨M, hM⟩) P i ⟨hi.1.le, hi.2⟩
    have hxM := abs_le.mp (hM x (Ioc_subset_Icc_self hx))
    constructor <;> apply abs_le.mpr <;> constructor <;> linarith
  · simp [lowerStep, upperStep, partitionStep_eq_zero P _ hx, indicator_of_notMem hx]

theorem uniform_steps_tendsto {f : ℝ → ℝ} (hab : a ≤ b) (hf : BoundedOn f a b)
    {x : ℝ} (hx : x ∈ Ioc a b) (hc : ContinuousWithinAt f (Icc a b) x) :
    Tendsto (fun n => lowerStep f (Partition.uniform hab n) x) atTop (𝓝 (f x)) ∧
    Tendsto (fun n => upperStep f (Partition.uniform hab n) x) atTop (𝓝 (f x)) := by
  have hclose : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
      |lowerStep f (Partition.uniform hab n) x - f x| < ε ∧
      |upperStep f (Partition.uniform hab n) x - f x| < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp hc (ε / 2) (half_pos hε)
    obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
    refine ⟨N, fun n hn => ?_⟩
    let P := Partition.uniform hab n
    obtain ⟨i, hi⟩ := partition_cell_exists P hx
    have hwidth : P.point i.succ - P.point i.castSucc < δ := by
      rw [Partition.uniform_width]
      apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
      have h := (div_lt_iff₀ hδ).mp hN
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith
    have hvalues (y : ℝ) (hy : y ∈ P.cell i) : |f y - f x| < ε / 2 := by
      apply hd (P.cell_subset i hy)
      rw [Real.dist_eq]
      apply lt_of_le_of_lt _ hwidth
      apply abs_le.mpr
      constructor <;> dsimp [Partition.cell] at hy <;> linarith [hi.1, hi.2, hy.1, hy.2]
    have hl : f x - ε / 2 ≤ cellLower f P i := by
      apply le_csInf ((P.cell_nonempty i).image f)
      rintro y ⟨y, hy, rfl⟩
      have := (abs_lt.mp (hvalues y hy)).1
      linarith
    have hu : cellUpper f P i ≤ f x + ε / 2 := by
      apply csSup_le ((P.cell_nonempty i).image f)
      rintro y ⟨y, hy, rfl⟩
      have := (abs_lt.mp (hvalues y hy)).2
      linarith
    have hL := cellLower_le_value hf P i ⟨hi.1.le, hi.2⟩
    have hU := value_le_cellUpper hf P i ⟨hi.1.le, hi.2⟩
    change |lowerStep f P x - f x| < ε ∧ |upperStep f P x - f x| < ε
    simp only [lowerStep, upperStep, partitionStep_eq P _ hi]
    constructor <;> apply abs_lt.mpr <;> constructor <;> linarith
  constructor
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hclose ε hε
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using (hN n hn).1⟩
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hclose ε hε
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using (hN n hn).2⟩

/-- Dominated convergence of the uniform Darboux gaps. The premise allows any
bounded function which is continuous almost everywhere, with no separate
measurability hypothesis. -/
theorem uniform_darboux_gap_tendsto {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : BoundedOn f a b)
    (hc : ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x) :
    Tendsto (fun n => upperSum f id (Partition.uniform hab n) -
      lowerSum f id (Partition.uniform hab n)) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hf
  let gap (n : ℕ) (x : ℝ) :=
    upperStep f (Partition.uniform hab n) x - lowerStep f (Partition.uniform hab n) x
  have hmeas (n : ℕ) : AEStronglyMeasurable (gap n) volume :=
    ((partitionStep_measurable _ _).sub (partitionStep_measurable _ _)).aestronglyMeasurable
  have hint : Integrable ((Ioc a b).indicator (fun _ : ℝ => 2 * M)) volume :=
    (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp) (by finiteness))
  have hb (n : ℕ) : ∀ᵐ x ∂volume,
      ‖gap n x‖ ≤ (Ioc a b).indicator (fun _ => 2 * M) x := by
    filter_upwards with x
    exact (step_gap_bounds hM _ x).2
  have hlim : ∀ᵐ x ∂volume, Tendsto (fun n => gap n x) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hc] with x hx
    by_cases hi : x ∈ Ioc a b
    · have ht := uniform_steps_tendsto hab ⟨M, hM⟩ hi (hx (Ioc_subset_Icc_self hi))
      simpa only [gap, sub_self] using ht.2.sub ht.1
    · have heq (n : ℕ) : gap n x = 0 := by
        simp [gap, upperStep, lowerStep, partitionStep_eq_zero _ _ hi]
      simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have ht := tendsto_integral_of_dominated_convergence _ hmeas hint hb hlim
  have heq (n : ℕ) : (∫ x, gap n x) =
      upperSum f id (Partition.uniform hab n) - lowerSum f id (Partition.uniform hab n) := by
    change (∫ x, upperStep f (Partition.uniform hab n) x -
      lowerStep f (Partition.uniform hab n) x) = _
    rw [integral_sub (show Integrable (upperStep f (Partition.uniform hab n)) volume from
      partitionStep_integrable _ _) (show Integrable (lowerStep f (Partition.uniform hab n)) volume from
      partitionStep_integrable _ _),
      upperStep_integral, lowerStep_integral]
  simpa only [heq, integral_zero] using ht

/-- 11.33(b), reverse implication, using precisely the Chapter 6 native
Darboux definition. Continuity is relative to the source's closed interval. -/
theorem pma11_33_riemann_of_ae_continuous {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : BoundedOn f a b)
    (hc : ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x) :
    RIntegrable f a b := by
  apply (rsIntegrable_iff_gap hab hf (fun _ _ _ _ h => h)).mpr
  intro ε hε
  have h := (uniform_darboux_gap_tendsto hab hf hc).eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  exact ⟨Partition.uniform hab N, hN N le_rfl⟩

end Rudin.PMA.Chapter11.SecondHalf
