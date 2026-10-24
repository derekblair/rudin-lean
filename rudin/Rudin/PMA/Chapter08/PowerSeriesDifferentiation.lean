import Rudin.PMA.Chapter08.PowerSeriesFoundations

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace Rudin.PMA.Chapter08

/-! Supporting first-derivative group for PMA 8.1, printed p.173.
The variable is real and the coefficients are complex. This does not claim the
all-orders corollary or completion of the numbered node. -/

def powerSeriesDerivativeCoeff (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  (n + 1 : ℂ) * c (n + 1)

/-- Every finite inner radius is strictly below the actual extended radius. -/
theorem realPowerSeries_inner_radius (c : ℕ → ℂ) {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hc : ∀ x : ℝ, |x| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n x)) :
    ENNReal.ofReal r < Chapter03.PowerSeriesRadius c := by
  obtain ⟨t, hrt, htR⟩ := exists_between hrR
  have ht : 0 < t := lt_of_le_of_lt hr hrt
  apply lt_of_lt_of_le _ (realPowerSeries_le_radius c ht.le (hc t ?_))
  · exact (ENNReal.ofReal_lt_ofReal_iff ht).mpr hrt
  · simpa [abs_of_pos ht] using htR

/-- A summable geometric majorant for the shifted derivative coefficients. -/
theorem derivativeCoeff_majorant_summable (c : ℕ → ℂ) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r < t)
    (htR : ENNReal.ofReal t < Chapter03.PowerSeriesRadius c) :
    Summable (fun n => ‖powerSeriesDerivativeCoeff c n‖ * r ^ n) := by
  have ht : 0 < t := lt_of_le_of_lt hr hrt
  let C := ∑' n, ‖c n‖ * t ^ n
  have hs := realPowerSeries_majorant_summable c ht.le htR
  have hb (n : ℕ) : ‖c n‖ * t ^ n ≤ C :=
    hs.le_tsum n (fun i _ => mul_nonneg (norm_nonneg _) (pow_nonneg ht.le _))
  have hq : ‖r / t‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr ht.le)]
    exact (div_lt_one ht).mpr hrt
  have hg : Summable (fun n : ℕ => ((n : ℝ) + 1) * (r / t) ^ n) := by
    simpa [pow_one, add_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hq).add
        (summable_geometric_of_norm_lt_one hq)
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hr _))
    (fun n => ?_) (hg.mul_left (C / t))
  have hn : ‖c (n + 1)‖ ≤ C / t ^ (n + 1) :=
    (le_div_iff₀ (pow_pos ht _)).mpr (hb (n + 1))
  calc
    ‖powerSeriesDerivativeCoeff c n‖ * r ^ n =
        ((n : ℝ) + 1) * ‖c (n + 1)‖ * r ^ n := by
          simp only [powerSeriesDerivativeCoeff, norm_mul, ← Nat.cast_add_one, norm_natCast]
    _ ≤ ((n : ℝ) + 1) * (C / t ^ (n + 1)) * r ^ n := by
      gcongr
    _ = (C / t) * (((n : ℝ) + 1) * (r / t) ^ n) := by
      rw [div_pow, pow_succ]
      field_simp

/-- Uniform ordered convergence of the shifted derivative series on inner intervals. -/
theorem derivativeSeries_uniform (c : ℕ → ℂ) {R r : ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hc : ∀ x : ℝ, |x| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n x)) :
    Chapter07.UniformSeriesConvergesOn (realPowerSeriesTerm (powerSeriesDerivativeCoeff c))
      (realPowerSeriesSum (powerSeriesDerivativeCoeff c)) (Icc (-r) r) := by
  obtain ⟨t, hrt, htR⟩ := exists_between hrR
  have hs := derivativeCoeff_majorant_summable c hr hrt
    (realPowerSeries_inner_radius c (hr.trans hrt.le) htR hc)
  exact tendstoUniformlyOn_tsum_nat hs
    (fun n x hx => realPowerSeries_majorant (powerSeriesDerivativeCoeff c) hx n)

/-- The unshifted textbook derivative term; the zero term vanishes. -/
def realPowerSeriesDerivativeTerm (c : ℕ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (n : ℂ) * c n * (x : ℂ) ^ (n - 1)

theorem realPowerSeries_term_hasDerivAt (c : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    HasDerivAt (realPowerSeriesTerm c n) (realPowerSeriesDerivativeTerm c n x) x := by
  simpa only [realPowerSeriesTerm, realPowerSeriesDerivativeTerm, mul_comm, mul_left_comm,
    mul_assoc] using! ((hasDerivAt_pow n (x : ℂ)).const_mul (c n)).comp_ofReal

theorem derivativeTerm_majorant_summable (c : ℕ → ℂ) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r < t)
    (htR : ENNReal.ofReal t < Chapter03.PowerSeriesRadius c) :
    Summable (fun n : ℕ => ‖(n : ℂ) * c n‖ * r ^ (n - 1)) := by
  apply (summable_nat_add_iff 1).mp
  simpa [powerSeriesDerivativeCoeff, Nat.cast_add, Nat.cast_one] using
    derivativeCoeff_majorant_summable c hr hrt htR

theorem realPowerSeries_hasDerivAt_unshifted (c : ℕ → ℂ) {R x : ℝ}
    (hx : |x| < R)
    (hc : ∀ y : ℝ, |y| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n y)) :
    HasDerivAt (realPowerSeriesSum c)
      (∑' n, realPowerSeriesDerivativeTerm c n x) x := by
  obtain ⟨r, hxr, hrR⟩ := exists_between hx
  obtain ⟨t, hrt, htR⟩ := exists_between hrR
  have hr : 0 < r := lt_of_le_of_lt (abs_nonneg x) hxr
  have hs := derivativeTerm_majorant_summable c hr.le hrt
    (realPowerSeries_inner_radius c (hr.le.trans hrt.le) htR hc)
  apply hasDerivAt_tsum_of_isPreconnected hs isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
    (fun n y _ => realPowerSeries_term_hasDerivAt c n y) _ (y₀ := 0) _ _ _
  · intro n y hy
    have hy' : |y| ≤ r := (abs_lt.mpr hy).le
    simp only [realPowerSeriesDerivativeTerm, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg y) hy' (n-1))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · exact ⟨neg_neg_of_pos hr, hr⟩
  · apply (summable_nat_add_iff 1).mp
    simp [realPowerSeriesTerm]
  · exact abs_lt.mp hxr

/-- Actual summability of the shifted derivative series at each interior point. -/
theorem derivativeSeries_summable (c : ℕ → ℂ) {R x : ℝ}
    (hx : |x| < R)
    (hc : ∀ y : ℝ, |y| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n y)) :
    Summable (fun n => realPowerSeriesTerm (powerSeriesDerivativeCoeff c) n x) := by
  obtain ⟨t, hxt, htR⟩ := exists_between hx
  have hs := derivativeCoeff_majorant_summable c (abs_nonneg x) hxt
    (realPowerSeries_inner_radius c ((abs_nonneg x).trans hxt.le) htR hc)
  apply hs.of_norm_bounded
  intro n
  exact realPowerSeries_majorant (powerSeriesDerivativeCoeff c)
    (abs_le.mp (le_refl |x|)) n

theorem derivativeSeries_hasSum (c : ℕ → ℂ) {R x : ℝ}
    (hx : |x| < R)
    (hc : ∀ y : ℝ, |y| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n y)) :
    Chapter03.SeriesHasSum (fun n => realPowerSeriesTerm (powerSeriesDerivativeCoeff c) n x)
      (realPowerSeriesSum (powerSeriesDerivativeCoeff c) x) :=
  (derivativeSeries_summable c hx hc).hasSum.tendsto_sum_nat

/-- First derivative in the source's real-variable, complex-coefficient scope.
The shifted series starts at n=0 and is exactly the source's series starting at 1. -/
theorem realPowerSeries_hasDerivAt (c : ℕ → ℂ) {R x : ℝ}
    (hx : |x| < R)
    (hc : ∀ y : ℝ, |y| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n y)) :
    HasDerivAt (realPowerSeriesSum c)
      (realPowerSeriesSum (powerSeriesDerivativeCoeff c) x) x := by
  have hs : Summable (fun n => realPowerSeriesDerivativeTerm c (n+1) x) := by
    simpa [realPowerSeriesDerivativeTerm, realPowerSeriesTerm,
      powerSeriesDerivativeCoeff, Nat.cast_add, Nat.cast_one] using
      derivativeSeries_summable c hx hc
  have he : (∑' n, realPowerSeriesDerivativeTerm c n x) =
      realPowerSeriesSum (powerSeriesDerivativeCoeff c) x := by
    calc
      _ = realPowerSeriesDerivativeTerm c 0 x +
          ∑' n, realPowerSeriesDerivativeTerm c (n+1) x := tsum_eq_zero_add' (f := fun n => realPowerSeriesDerivativeTerm c n x) hs
      _ = _ := by
        simp only [realPowerSeriesDerivativeTerm, realPowerSeriesSum, realPowerSeriesTerm,
          powerSeriesDerivativeCoeff, Nat.cast_zero, zero_mul, zero_add, Nat.add_sub_cancel,
          Nat.cast_add, Nat.cast_one]
  rw [← he]
  exact realPowerSeries_hasDerivAt_unshifted c hx hc

#print axioms derivativeSeries_summable
#print axioms derivativeSeries_hasSum
#print axioms realPowerSeries_hasDerivAt

#print axioms realPowerSeries_term_hasDerivAt
#print axioms derivativeTerm_majorant_summable
#print axioms realPowerSeries_hasDerivAt_unshifted

#print axioms realPowerSeries_inner_radius
#print axioms derivativeCoeff_majorant_summable
#print axioms derivativeSeries_uniform

end Rudin.PMA.Chapter08
