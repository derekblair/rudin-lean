import Rudin.PMA.Chapter07.Basic

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace Rudin.PMA.Chapter08

/-! Foundations for PMA 8.1 (third edition, pp.172–174).
These are supporting results, not a claim to have proved the complete numbered
node: termwise differentiation and the all-orders corollary remain outstanding.
The variable is real, coefficients complex, and sums use the Chapter 3 order.
The extended radius permits infinite radius without a finite-radius assumption.
-/

def realPowerSeriesTerm (c : ℕ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  c n * (x : ℂ) ^ n

def realPowerSeriesSum (c : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n, realPowerSeriesTerm c n x

theorem realPowerSeries_majorant (c : ℕ → ℂ) {r x : ℝ}
    (hx : x ∈ Icc (-r) r) (n : ℕ) :
    ‖realPowerSeriesTerm c n x‖ ≤ ‖c n‖ * r ^ n := by
  have hxr : |x| ≤ r := abs_le.mpr hx
  simp only [realPowerSeriesTerm, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg x) hxr n) (norm_nonneg _)

theorem realPowerSeries_majorant_summable (c : ℕ → ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hR : ENNReal.ofReal r < Chapter03.PowerSeriesRadius c) :
    Summable (fun n => ‖c n‖ * r ^ n) := by
  have hz : (‖(r : ℂ)‖₊ : ℝ≥0∞) < Chapter03.PowerSeriesRadius c := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    exact hR
  simpa [Chapter03.PowerSeriesTerms, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hr] using
    Chapter03.powerSeries_interior_summable_norm c (r : ℂ) hz

theorem realPowerSeries_uniform (c : ℕ → ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hR : ENNReal.ofReal r < Chapter03.PowerSeriesRadius c) :
    Chapter07.UniformSeriesConvergesOn (realPowerSeriesTerm c)
      (realPowerSeriesSum c) (Icc (-r) r) := by
  exact tendstoUniformlyOn_tsum_nat (realPowerSeries_majorant_summable c hr hR)
    (fun n x hx => realPowerSeries_majorant c hx n)

theorem realPowerSeries_hasSum (c : ℕ → ℂ) {r x : ℝ}
    (hr : 0 ≤ r) (hR : ENNReal.ofReal r < Chapter03.PowerSeriesRadius c)
    (hx : x ∈ Icc (-r) r) :
    Chapter03.SeriesHasSum (fun n => realPowerSeriesTerm c n x)
      (realPowerSeriesSum c x) :=
  (realPowerSeries_uniform c hr hR).tendsto_at hx

theorem realPowerSeries_continuousOn (c : ℕ → ℂ) {r : ℝ}
    (hr : 0 ≤ r) (hR : ENNReal.ofReal r < Chapter03.PowerSeriesRadius c) :
    ContinuousOn (realPowerSeriesSum c) (Icc (-r) r) := by
  apply (realPowerSeries_uniform c hr hR).continuousOn
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro N
  apply Continuous.continuousOn
  unfold Chapter03.PartialSums realPowerSeriesTerm
  fun_prop

theorem realPowerSeries_at_zero (c : ℕ → ℂ) : realPowerSeriesSum c 0 = c 0 := by
  unfold realPowerSeriesSum
  rw [tsum_eq_single 0]
  · simp [realPowerSeriesTerm]
  · intro n hn
    simp [realPowerSeriesTerm, zero_pow hn]

/-- Source-facing bridge: convergence at a positive real point bounds the radius.
No absolute convergence at that point is assumed. -/
theorem realPowerSeries_le_radius (c : ℕ → ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hc : Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n t)) :
    ENNReal.ofReal t ≤ Chapter03.PowerSeriesRadius c := by
  apply le_of_not_gt
  intro h
  have hz : Chapter03.PowerSeriesRadius c < (‖(t : ℂ)‖₊ : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht]
    exact h
  exact Chapter03.powerSeries_exterior c (t : ℂ) hz hc

/-- The uniform-convergence clause of 8.1 with its original convergence premise.
An arbitrary inner radius r represents R - epsilon. -/
theorem realPowerSeries_uniform_of_converges (c : ℕ → ℂ) {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hc : ∀ x : ℝ, |x| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n x)) :
    Chapter07.UniformSeriesConvergesOn (realPowerSeriesTerm c)
      (realPowerSeriesSum c) (Icc (-r) r) := by
  obtain ⟨t, hrt, htR⟩ := exists_between hrR
  have ht : 0 < t := lt_of_le_of_lt hr hrt
  apply realPowerSeries_uniform c hr
  apply lt_of_lt_of_le _ (realPowerSeries_le_radius c ht.le (hc t ?_))
  · exact (ENNReal.ofReal_lt_ofReal_iff ht).mpr hrt
  · simpa [abs_of_pos ht] using htR

#print axioms realPowerSeries_le_radius
#print axioms realPowerSeries_uniform_of_converges

#print axioms realPowerSeries_majorant
#print axioms realPowerSeries_majorant_summable
#print axioms realPowerSeries_uniform
#print axioms realPowerSeries_hasSum
#print axioms realPowerSeries_continuousOn
#print axioms realPowerSeries_at_zero

end Rudin.PMA.Chapter08
