import Rudin.PMA.Chapter11.LebesgueCriterion
import Rudin.PMA.Chapter11.DarbouxContinuity

/-!
# PMA 11.33: the native Riemann–Lebesgue comparison

The Riemann predicate and integral are exactly those of Chapter 6. Lebesgue
integrability uses almost-everywhere measurability on the interval, so no
global Borel-measurability hypothesis is added. The continuity assertion is
relative to the closed interval; endpoints have measure zero.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace Rudin.PMA.Chapter11.SecondHalf
open Rudin.PMA.Chapter06

variable {a b : ℝ}

theorem partitionStep_setIntegral (P : Partition a b) (c : Fin P.n → ℝ) :
    (∫ x in Icc a b, partitionStep P c x) = ∫ x, partitionStep P c x := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc a b
  · simp [hx]
  · have hnot : x ∉ Ioc a b := fun hi => hx (Ioc_subset_Icc_self hi)
    simp [hx, partitionStep_eq_zero P c hnot]

theorem step_abs_le {f : ℝ → ℝ} {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (P : Partition a b) (x : ℝ) :
    |lowerStep f P x| ≤ M ∧ |upperStep f P x| ≤ M := by
  by_cases hx : x ∈ Ioc a b
  · obtain ⟨i, hi⟩ := partition_cell_exists P hx
    simp only [lowerStep, upperStep, partitionStep_eq P _ hi]
    have hb := cell_envelopes_bounded hM P i
    have hlu := cellLower_le_cellUpper (show BoundedOn f a b from ⟨M, hM⟩) P i
    exact ⟨abs_le.mpr ⟨hb.1, hlu.trans hb.2⟩,
      abs_le.mpr ⟨hb.1.trans hlu, hb.2⟩⟩
  · simpa [lowerStep, upperStep, partitionStep_eq_zero P _ hx] using And.intro hM0 hM0

/-- A bounded a.e. continuous function has integrable Lebesgue representatives,
and both sequences of Darboux step integrals converge to its integral. -/
theorem darboux_integrals_tendsto {f : ℝ → ℝ} (hab : a ≤ b)
    (hf : BoundedOn f a b)
    (hc : ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x) :
    IntegrableOn f (Icc a b) volume ∧
    Tendsto (fun n => lowerSum f id (Partition.uniform hab n)) atTop
      (𝓝 (∫ x in Icc a b, f x)) ∧
    Tendsto (fun n => upperSum f id (Partition.uniform hab n)) atTop
      (𝓝 (∫ x in Icc a b, f x)) := by
  obtain ⟨M, hM⟩ := hf
  have hM0 : 0 ≤ M := (abs_nonneg (f a)).trans (hM a ⟨le_rfl, hab⟩)
  have hlim : ∀ᵐ x ∂volume.restrict (Icc a b),
      Tendsto (fun n => lowerStep f (Partition.uniform hab n) x) atTop (𝓝 (f x)) ∧
      Tendsto (fun n => upperStep f (Partition.uniform hab n) x) atTop (𝓝 (f x)) := by
    have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ a := by
      rw [ae_iff]
      simp
    filter_upwards [hc, self_mem_ae_restrict measurableSet_Icc,
      ae_restrict_of_ae hne] with x hx hxab hxa
    exact uniform_steps_tendsto hab ⟨M, hM⟩ ⟨lt_of_le_of_ne hxab.1 (Ne.symm hxa), hxab.2⟩ hx
  have hmL (n : ℕ) : AEStronglyMeasurable (lowerStep f (Partition.uniform hab n))
      (volume.restrict (Icc a b)) := (partitionStep_measurable _ _).aestronglyMeasurable
  have hmU (n : ℕ) : AEStronglyMeasurable (upperStep f (Partition.uniform hab n))
      (volume.restrict (Icc a b)) := (partitionStep_measurable _ _).aestronglyMeasurable
  have hbL (n : ℕ) : ∀ᵐ x ∂volume.restrict (Icc a b),
      ‖lowerStep f (Partition.uniform hab n) x‖ ≤ M :=
    Eventually.of_forall (fun x => (step_abs_le hM0 hM _ x).1)
  have hbU (n : ℕ) : ∀ᵐ x ∂volume.restrict (Icc a b),
      ‖upperStep f (Partition.uniform hab n) x‖ ≤ M :=
    Eventually.of_forall (fun x => (step_abs_le hM0 hM _ x).2)
  have htL := tendsto_integral_of_dominated_convergence (fun _ => M) hmL
    (integrable_const M) hbL (hlim.mono fun _ h => h.1)
  have htU := tendsto_integral_of_dominated_convergence (fun _ => M) hmU
    (integrable_const M) hbU (hlim.mono fun _ h => h.2)
  refine ⟨⟨aestronglyMeasurable_of_tendsto_ae _ hmL (hlim.mono fun _ h => h.1),
    hasFiniteIntegral_of_dominated_convergence (integrable_const M).hasFiniteIntegral
      hbL (hlim.mono fun _ h => h.1)⟩, ?_, ?_⟩
  · simpa only [lowerStep, partitionStep_setIntegral, partitionStep_integral, lowerSum] using htL
  · simpa only [upperStep, partitionStep_setIntegral, partitionStep_integral, upperSum] using htU

/-- 11.33(a): every native Riemann-integrable function is Lebesgue integrable,
and the native Darboux integral equals its Lebesgue integral. -/
theorem pma11_33_comparison {f : ℝ → ℝ} (hf : RIntegrable f a b) :
    IntegrableOn f (Icc a b) volume ∧
      (∫ x in Icc a b, f x) = RIntegral f a b := by
  obtain ⟨hi, hL, hU⟩ := darboux_integrals_tendsto hf.1 hf.2.1
    (pma11_33_ae_continuous_of_riemann hf)
  refine ⟨hi, le_antisymm ?_ ?_⟩
  · exact le_of_tendsto hL (Eventually.of_forall fun n =>
      lowerSum_le_lowerIntegral hf.2.1 hf.2.2.1 _)
  · apply ge_of_tendsto hU
    filter_upwards with n
    change lowerIntegral f id a b ≤ upperSum f id _
    exact hf.2.2.2.le.trans (upperIntegral_le_upperSum hf.2.1 hf.2.2.1 _)

/-- 11.33(b): the full Lebesgue criterion for the native Darboux definition. -/
theorem pma11_33_criterion {f : ℝ → ℝ} (hab : a ≤ b) (hf : BoundedOn f a b) :
    RIntegrable f a b ↔
      ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x :=
  ⟨pma11_33_ae_continuous_of_riemann, pma11_33_riemann_of_ae_continuous hab hf⟩

/-- 11.33, both parts: the native integral comparison and the full bounded
Lebesgue criterion, with no measurability premise added to the latter. -/
theorem pma11_33 :
    (∀ (f : ℝ → ℝ) (a b : ℝ), RIntegrable f a b →
      IntegrableOn f (Icc a b) volume ∧
        (∫ x in Icc a b, f x) = RIntegral f a b) ∧
    (∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → BoundedOn f a b →
      (RIntegrable f a b ↔
        ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x)) :=
  ⟨fun _ _ _ => pma11_33_comparison,
    fun _ _ _ => pma11_33_criterion⟩

end Rudin.PMA.Chapter11.SecondHalf
