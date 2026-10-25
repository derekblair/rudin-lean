import Rudin.PMA.Chapter08.Orthogonality
import Rudin.PMA.Chapter08.FourierParsevalBase
import Rudin.PMA.Chapter08.IntegralAlgebra

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace ComplexConjugate

namespace Rudin.PMA.Chapter08

theorem fourier_native_gram (m n : ℤ) :
    Chapter06.ComplexRSIntegrable
      (fun x => fourierMonomial m x * star (fourierMonomial n x)) id (-Real.pi) Real.pi ∧
    Chapter06.ComplexRSIntegral
      (fun x => fourierMonomial m x * star (fourierMonomial n x)) id (-Real.pi) Real.pi =
      if m = n then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  simpa only [fourierMonomial_star, ← fourierMonomial_add, ← sub_eq_add_neg,
    sub_eq_zero, Complex.ofReal_mul, Complex.ofReal_ofNat] using
    fourierMonomial_integral (m - n)

theorem fourier_partial_norm_sq (c : ℤ → ℂ) (N : ℕ) :
    Chapter06.RIntegrable (fun x => ‖trigonometricPartialSum c N x‖ ^ 2)
      (-Real.pi) Real.pi ∧
    Chapter06.RIntegral (fun x => ‖trigonometricPartialSum c N x‖ ^ 2)
      (-Real.pi) Real.pi =
      (2 * Real.pi) * ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖c n‖ ^ 2 := by
  exact native_finsum_norm_sq (by linarith [Real.pi_pos]) _
    (fun m _ n _ => fourier_native_gram m n) c

/-- PMA 8.13's finite mean-square identity, including native integrability of
the remainder, for every Riemann-integrable complex function. -/
theorem fourier_error_identity {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) (N : ℕ) :
    Chapter06.RIntegrable (fun x => ‖f x - riemannFourierSum f N x‖ ^ 2)
      (-Real.pi) Real.pi ∧
    Chapter06.RIntegral (fun x => ‖f x - riemannFourierSum f N x‖ ^ 2)
      (-Real.pi) Real.pi =
      Chapter06.RIntegral (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi -
      (2 * Real.pi) * ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2 := by
  have hi (n : ℤ) := native_complex_integrable_mul hf
    (native_complex_integrable_star (fourierMonomial_integral n).1)
  have hp := native_pair_finsum_right hf.1.1 (Finset.Icc (-(N : ℤ)) N)
    (riemannFourierCoeff f) (fun n _ => hi n)
  have hsq := fourier_partial_norm_sq (riemannFourierCoeff f) N
  have he := native_error_expansion (native_norm_sq_integrable hf) hsq.1 hp.1
  refine ⟨he.1, ?_⟩
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  have hc (n : ℤ) : Chapter06.ComplexRSIntegral
      (fun x => f x * star (fourierMonomial n x)) id (-Real.pi) Real.pi =
      (2 * Real.pi : ℂ) * riemannFourierCoeff f n := by
    simp only [fourierMonomial_star, riemannFourierCoeff, ← mul_assoc,
      mul_inv_cancel₀ hpi, one_mul]
  have hcross : (Chapter06.ComplexRSIntegral
      (fun x => f x * star (riemannFourierSum f N x)) id (-Real.pi) Real.pi).re =
      (2 * Real.pi) * ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2 := by
    rw [show (fun x => f x * star (riemannFourierSum f N x)) =
        (fun x => f x * star (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
          riemannFourierCoeff f n * fourierMonomial n x)) from rfl,
      hp.2]
    simp_rw [hc]
    have hh (n : ℤ) : star (riemannFourierCoeff f n) *
        ((2 * Real.pi : ℂ) * riemannFourierCoeff f n) =
        (2 * Real.pi : ℂ) * (riemannFourierCoeff f n * star (riemannFourierCoeff f n)) := by
      ring
    simp_rw [hh, complex_mul_star]
    simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, ← Finset.mul_sum,
      -Complex.ofReal_pow]
  change Chapter06.RIntegral (fun x => ‖f x - trigonometricPartialSum
    (riemannFourierCoeff f) N x‖ ^ 2) (-Real.pi) Real.pi = _
  rw [he.2, hsq.2]
  change _ - 2 * (Chapter06.ComplexRSIntegral
    (fun x => f x * star (riemannFourierSum f N x)) id (-Real.pi) Real.pi).re = _
  rw [hcross]
  ring

theorem native_fourier_parseval_sq {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) :
    HasSum (fun n : ℤ => ‖riemannFourierCoeff f n‖ ^ 2)
      ((2 * Real.pi)⁻¹ * Chapter06.RIntegral (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi) := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have h := hasSum_sq_fourierCoeffOn hab (native_complex_memLp hf 2)
  simpa only [← riemannFourierCoeff_eq_fourierCoeffOn hf,
    sub_neg_eq_add, ← two_mul, smul_eq_mul,
    ← native_riemann_integral_eq (native_norm_sq_integrable hf)] using h

theorem native_fourier_parseval_inner {f g : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hg : Chapter06.ComplexRSIntegrable g id (-Real.pi) Real.pi) :
    HasSum (fun n : ℤ => riemannFourierCoeff f n * star (riemannFourierCoeff g n))
      ((2 * Real.pi : ℂ)⁻¹ * Chapter06.ComplexRSIntegral
        (fun x => f x * star (g x)) id (-Real.pi) Real.pi) := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have h := hasSum_interval_fourier_mul_star hab (native_complex_memLp hf 2)
    (native_complex_memLp hg 2)
  have hfg := native_complex_integrable_mul hf (native_complex_integrable_star hg)
  simpa only [← riemannFourierCoeff_eq_fourierCoeffOn hf,
    ← riemannFourierCoeff_eq_fourierCoeffOn hg, sub_neg_eq_add, ← two_mul,
    ← native_complex_integral_eq hfg, Complex.real_smul, Complex.ofReal_inv,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using h

theorem native_fourier_mean_square {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) :
    Tendsto (fun N : ℕ => (2 * Real.pi)⁻¹ * Chapter06.RIntegral
      (fun x => ‖f x - riemannFourierSum f N x‖ ^ 2) (-Real.pi) Real.pi)
      atTop (𝓝 0) := by
  have hsum := (native_fourier_parseval_sq hf).comp Finset.tendsto_Icc_neg
  have h := (tendsto_const_nhds (x := (2 * Real.pi)⁻¹ *
    Chapter06.RIntegral (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi)).sub hsum
  have hp : (2 * Real.pi : ℝ) ≠ 0 := Real.two_pi_pos.ne'
  convert h using 1
  · funext N
    rw [(fourier_error_identity hf N).2]
    simp only [Function.comp_def, mul_sub, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]
  · simp

/-- PMA 8.16. The symmetric ordered sums in the printed theorem are explicit;
the stronger unconditional sums are also established above. The proof does
not need periodicity beyond interpreting the data as periodic functions. -/
def pma8_16_contract : Prop :=
  ∀ f g : ℝ → ℂ,
    Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi →
    Chapter06.ComplexRSIntegrable g id (-Real.pi) Real.pi →
    Function.Periodic f (2 * Real.pi) → Function.Periodic g (2 * Real.pi) →
    (∀ N, Chapter06.RIntegrable (fun x => ‖f x - riemannFourierSum f N x‖ ^ 2)
      (-Real.pi) Real.pi) ∧
    Tendsto (fun N : ℕ => (2 * Real.pi)⁻¹ * Chapter06.RIntegral
      (fun x => ‖f x - riemannFourierSum f N x‖ ^ 2) (-Real.pi) Real.pi)
      atTop (𝓝 0) ∧
    Chapter06.ComplexRSIntegrable (fun x => f x * star (g x)) id (-Real.pi) Real.pi ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      riemannFourierCoeff f n * star (riemannFourierCoeff g n)) atTop
      (𝓝 ((2 * Real.pi : ℂ)⁻¹ * Chapter06.ComplexRSIntegral
        (fun x => f x * star (g x)) id (-Real.pi) Real.pi)) ∧
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2)
      atTop (𝓝 ((2 * Real.pi)⁻¹ * Chapter06.RIntegral
        (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi))

theorem pma8_16 : pma8_16_contract := by
  intro f g hf hg _ _
  exact ⟨fun N => (fourier_error_identity hf N).1, native_fourier_mean_square hf,
    native_complex_integrable_mul hf (native_complex_integrable_star hg),
    (native_fourier_parseval_inner hf hg).comp Finset.tendsto_Icc_neg,
    (native_fourier_parseval_sq hf).comp Finset.tendsto_Icc_neg⟩

end Rudin.PMA.Chapter08
