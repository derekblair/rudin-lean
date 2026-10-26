import Rudin.PMA.Chapter10.CoordinateDifferentiation
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option autoImplicit false
open Set Function Filter MeasureTheory Metric
open scoped Topology Interval

namespace Rudin.PMA.Chapter10
open Chapter09

lemma compact_parameter_local_bound {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U : Set (Euclidean n)} (hU : IsOpen U) {H : ℝ × Euclidean n → F}
    (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ U)) {x : Euclidean n} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall x r ⊆ U ∧ ∃ C : ℝ,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall x r, ‖H (t, y)‖ ≤ C := by
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hs : closedBall x (r / 2) ⊆ U :=
    (closedBall_subset_ball (half_lt_self hr)).trans hsub
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall x (r / 2))).exists_bound_of_continuousOn
    (hH.mono (prod_mono Subset.rfl hs))
  exact ⟨r / 2, half_pos hr, hs, C, fun t ht y hy => hC (t, y) ⟨ht, hy⟩⟩

lemma parameter_slice_continuous {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U : Set (Euclidean n)} {H : ℝ × Euclidean n → F}
    (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ U)) {x : Euclidean n} (hx : x ∈ U) :
    ContinuousOn (fun t => H (t, x)) (Icc (0 : ℝ) 1) :=
  hH.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, hx⟩)

lemma parameter_slice_intervalIntegrable {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    {U : Set (Euclidean n)} {H : ℝ × Euclidean n → F}
    (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ U)) {x : Euclidean n} (hx : x ∈ U) :
    IntervalIntegrable (fun t => H (t, x)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using parameter_slice_continuous hH hx

lemma continuousOn_parameter_integral {n : ℕ} {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {U : Set (Euclidean n)} (hU : IsOpen U)
    {H : ℝ × Euclidean n → F} (hH : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ U)) :
    ContinuousOn (fun x => ∫ t in (0 : ℝ)..1, H (t, x)) U := by
  intro x hx
  obtain ⟨r, hr, hsub, C, hC⟩ := compact_parameter_local_bound hU hH hx
  apply ContinuousAt.continuousWithinAt
  apply intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C)
  · filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (parameter_slice_intervalIntegrable hH hy).1.aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact ae_of_all _ fun t ht => hC t
      (Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)) y hy
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 :=
      Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
    exact (hH.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => ⟨ht', hy⟩)).continuousAt (hU.mem_nhds hx)

/-- The derivative in the parameter variables of a joint scalar integrand. -/
def parameterDerivative {n : ℕ} (H : ℝ × Euclidean n → ℝ) (p : ℝ × Euclidean n) :
    Euclidean n →L[ℝ] ℝ :=
  (fderiv ℝ H p).comp (ContinuousLinearMap.inr ℝ ℝ (Euclidean n))

lemma continuousOn_parameterDerivative {n : ℕ} {W : Set (ℝ × Euclidean n)}
    (hW : IsOpen W) {H : ℝ × Euclidean n → ℝ} (hH : ContDiffOn ℝ 1 H W) :
    ContinuousOn (parameterDerivative H) W :=
  (hH.continuousOn_fderiv_of_isOpen hW le_rfl).clm_comp continuousOn_const

lemma hasFDerivAt_parameter_slice {n : ℕ} {W : Set (ℝ × Euclidean n)}
    (hW : IsOpen W) {H : ℝ × Euclidean n → ℝ} (hH : ContDiffOn ℝ 1 H W)
    {t : ℝ} {x : Euclidean n} (h : (t, x) ∈ W) :
    HasFDerivAt (fun y => H (t, y)) (parameterDerivative H (t, x)) x := by
  have hj : HasFDerivAt (fun y : Euclidean n => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)) x := by
    convert! (ContinuousLinearMap.inr ℝ ℝ (Euclidean n)).hasFDerivAt.const_add (t, 0) using 1
    ext y <;> simp
  exact ((hH.differentiableOn_one).differentiableAt (hW.mem_nhds h)).hasFDerivAt.comp x hj

lemma hasFDerivAt_parameter_integral {n : ℕ} {W : Set (ℝ × Euclidean n)}
    {U : Set (Euclidean n)} (hW : IsOpen W) (hU : IsOpen U)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W) {H : ℝ × Euclidean n → ℝ}
    (hH : ContDiffOn ℝ 1 H W) {x : Euclidean n} (hx : x ∈ U) :
    HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, H (t, y))
      (∫ t in (0 : ℝ)..1, parameterDerivative H (t, x)) x := by
  have hc := hH.continuousOn.mono hUW
  have hD := (continuousOn_parameterDerivative hW hH).mono hUW
  obtain ⟨r, hr, hsub, C, hC⟩ := compact_parameter_local_bound hU hD hx
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun y t => parameterDerivative H (t, y))
    (s := closedBall x r) (bound := fun _ => C) (closedBall_mem_nhds x hr)
  · filter_upwards [hU.mem_nhds hx] with y hy
    simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (parameter_slice_intervalIntegrable hc hy).1.aestronglyMeasurable
  · exact parameter_slice_intervalIntegrable hc hx
  · simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using
      (parameter_slice_intervalIntegrable hD hx).1.aestronglyMeasurable
  · apply ae_restrict_of_forall_mem measurableSet_uIoc
    intro t ht y hy
    apply hC t _ y hy
    exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)
  · exact intervalIntegrable_const
  · apply ae_restrict_of_forall_mem measurableSet_uIoc
    intro t ht y hy
    apply hasFDerivAt_parameter_slice hW hH (hUW ⟨?_, hsub hy⟩)
    exact Ioc_subset_Icc_self (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht)

lemma contDiffOn_parameter_integral {n : ℕ} {W : Set (ℝ × Euclidean n)}
    {U : Set (Euclidean n)} (hW : IsOpen W) (hU : IsOpen U)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W) {H : ℝ × Euclidean n → ℝ}
    (hH : ContDiffOn ℝ 1 H W) :
    ContDiffOn ℝ 1 (fun y => ∫ t in (0 : ℝ)..1, H (t, y)) U := by
  apply (c1On_iff_contDiffOn hU).mp
  refine ⟨fun x hx => (hasFDerivAt_parameter_integral hW hU hUW hH hx).differentiableAt, ?_⟩
  have hc := continuousOn_parameter_integral hU ((continuousOn_parameterDerivative hW hH).mono hUW)
  exact hc.congr (fun x hx => (hasFDerivAt_parameter_integral hW hU hUW hH hx).fderiv)

end Rudin.PMA.Chapter10
