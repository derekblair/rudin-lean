import Rudin.PMA.Chapter08.Exponential

/-! Independent boundary clients for the exponential/logarithmic continuation. -/
set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter08.FidelityProbes

/-- The factorial-series contract genuinely covers a nonreal argument. -/
theorem exponential_imaginary_argument :
    HasSum (fun n : ℕ => Complex.I ^ n / (n.factorial : ℂ)) (Complex.exp Complex.I) ∧
      Complex.exp Complex.I ≠ 0 := by
  exact ⟨pma8_6.1.1 Complex.I, pma8_6.1.2.2.1 Complex.I⟩

/-- The logarithmic integral includes a decreasing integration direction. -/
theorem logarithm_reverse_interval :
    Real.exp (-1) < 1 ∧
      orientedRIntegral (fun t : ℝ => t⁻¹) 1 (Real.exp (-1)) = -1 := by
  constructor
  · simp
  · simpa using log_native_integral_from_one (Real.exp_pos (-1))

/-- Exponent -1 uses the logarithmic branch, with a nonzero integral. -/
theorem exceptional_power_integral :
    orientedRIntegral (fun t : ℝ => t ^ (-1 : ℝ)) 1 (Real.exp 1) = 1 := by
  have h := pma8_6.2.2.2.2.2.2.2.2.2.2.1 1 (Real.exp 1)
    zero_lt_one (Real.exp_pos 1)
  simpa using h

/-- Negative rational numerators retain the positive-root interpretation. -/
theorem negative_rational_power_root :
    0 < (4 : ℝ) ^ ((-1 / 2 : ℚ) : ℝ) ∧
      ((4 : ℝ) ^ ((-1 / 2 : ℚ) : ℝ)) ^ 2 = 1 / 4 := by
  have h := rpow_rational_root (x := 4) (by norm_num) (-1 / 2 : ℚ)
  convert h using 1; norm_num

/-- The polynomial-decay clause retains the zero-power boundary. -/
theorem exponential_decay_order_zero :
    Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by
  have h := pma8_6.2.1.2.2.2.2.2.2.2.1 0
  simpa using h

end Rudin.PMA.Chapter08.FidelityProbes
