import Rudin.PMA.Chapter08.PowerSeriesDifferentiation
import Rudin.PMA.Chapter08.PowerSeries

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Rudin.PMA.Chapter08

/-!
Compatibility with the landed first-derivative development of PMA 8.1.
The previously reviewed all-orders candidate uses real scalar multiplication;
these bridges preserve the landed coefficient-left terms and ordinary ordered
convergence hypotheses. No absolute convergence assumption is added.
-/

theorem realPowerSeriesTerm_eq_smul (c : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    realPowerSeriesTerm c n x = x ^ n • c n := by
  simp [realPowerSeriesTerm, Complex.real_smul, mul_comm]

theorem powerSeriesDerivativeCoeff_eq_diffCoeffs (c : ℕ → ℂ) :
    powerSeriesDerivativeCoeff c = diffCoeffs c := by
  funext n
  simp [powerSeriesDerivativeCoeff, diffCoeffs, nsmul_eq_mul]

theorem realPowerSeriesSum_eq_realSeries_sum (c : ℕ → ℂ) :
    realPowerSeriesSum c = (realSeries c).sum := by
  funext x
  simp only [realPowerSeriesSum, FormalMultilinearSeries.sum,
    realSeries_apply, realPowerSeriesTerm_eq_smul]

/-- Ordinary convergence throughout the original interval identifies the
landed sum with the all-orders candidate's representation. -/
theorem realPowerSeries_represents_of_converges (c : ℕ → ℂ) {R : ℝ}
    (hR : 0 < R)
    (hc : ∀ x : ℝ, |x| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n x)) :
    Represents c (realPowerSeriesSum c) (ENNReal.ofReal R) := by
  intro x hx
  have hx' : |x| < R := by
    simpa only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs,
      ENNReal.ofReal_lt_ofReal_iff hR] using hx
  have hs := realPowerSeries_hasSum c (abs_nonneg x)
    (realPowerSeries_inner_radius c (abs_nonneg x) hx' hc)
    (abs_le.mp (le_refl |x|))
  simpa only [realPowerSeriesTerm_eq_smul] using hs

/-- PMA 8.1's full iterated termwise differentiation with the original
convergence premise and the landed coefficient convention. -/
theorem realPowerSeries_all_orders (c : ℕ → ℂ) {R x : ℝ}
    (hx : |x| < R)
    (hc : ∀ y : ℝ, |y| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n y)) (k : ℕ) :
    HasDerivAt (iteratedDeriv k (realPowerSeriesSum c))
      (iteratedDeriv (k + 1) (realPowerSeriesSum c) x) x ∧
    Chapter03.SeriesHasSum
      (fun n => realPowerSeriesTerm (derivedCoeffs c k) n x)
      (iteratedDeriv k (realPowerSeriesSum c) x) := by
  have hR : 0 < R := (abs_nonneg x).trans_lt hx
  have hp := realPowerSeries_represents_of_converges c hR hc
  have hx' : (‖x‖₊ : ℝ≥0∞) < ENNReal.ofReal R := by
    simpa only [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs,
      ENNReal.ofReal_lt_ofReal_iff hR] using hx
  have h := (pma8_1.1 c (realPowerSeriesSum c) (ENNReal.ofReal R)
    (ENNReal.ofReal_pos.mpr hR) hp).2.2.1 k x hx'
  simpa only [realPowerSeriesTerm_eq_smul, derivedCoeffs_eq] using h

/-- The explicit coefficient-left formula after shifting the source index
from `n ≥ k` to `n = m + k`. -/
theorem realPowerSeries_all_orders_explicit (c : ℕ → ℂ) {R x : ℝ}
    (hx : |x| < R)
    (hc : ∀ y : ℝ, |y| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n y)) (k : ℕ) :
    Chapter03.SeriesHasSum
      (fun n => ((n + 1).ascFactorial k : ℂ) * c (n + k) * (x : ℂ) ^ n)
      (iteratedDeriv k (realPowerSeriesSum c) x) := by
  simpa only [realPowerSeriesTerm, derivedCoeffs_eq, nsmul_eq_mul] using
    (realPowerSeries_all_orders c hx hc k).2

/-- PMA 8.1's factorial coefficient identity, including derivative order zero. -/
theorem realPowerSeries_factorial_coefficient (c : ℕ → ℂ) {R : ℝ}
    (hR : 0 < R)
    (hc : ∀ x : ℝ, |x| < R →
      Chapter03.SeriesConverges (fun n => realPowerSeriesTerm c n x)) (k : ℕ) :
    iteratedDeriv k (realPowerSeriesSum c) 0 = (k.factorial : ℂ) * c k := by
  simpa only [nsmul_eq_mul] using coefficient_formula
    (ENNReal.ofReal_pos.mpr hR) (realPowerSeries_represents_of_converges c hR hc) k

end Rudin.PMA.Chapter08
