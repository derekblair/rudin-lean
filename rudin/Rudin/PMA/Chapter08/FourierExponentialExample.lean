import Rudin.PMA.Chapter08.FourierParseval

set_option autoImplicit false
noncomputable section
open Set

namespace Rudin.PMA.Chapter08

/-- The normalized complex exponentials in PMA 8.10. -/
def normalizedFourier (n : ℤ) (x : ℝ) : ℂ :=
  (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * fourierMonomial n x

/-- Enumerate all integer frequencies as a sequence, with no frequencies lost. -/
def normalizedFourierSystem (n : ℕ) : ℝ → ℂ :=
  normalizedFourier (Equiv.intEquivNat.symm n)

theorem normalizedFourier_gram (m n : ℤ) :
    Chapter06.ComplexRSIntegrable (fun x => normalizedFourier m x * star (normalizedFourier n x))
      id (-Real.pi) Real.pi ∧
    Chapter06.ComplexRSIntegral (fun x => normalizedFourier m x * star (normalizedFourier n x))
      id (-Real.pi) Real.pi = if m = n then 1 else 0 := by
  let A : ℂ := (Real.sqrt (2 * Real.pi) : ℂ)⁻¹
  have hA : star A = A := by
    change (starRingEnd ℂ) ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹) = _
    simp [A]
  have he : (fun x => normalizedFourier m x * star (normalizedFourier n x)) =
      fun x => A ^ 2 * (fourierMonomial m x * star (fourierMonomial n x)) := by
    funext x
    change (A * _) * star (A * _) = _
    rw [star_mul, hA]
    ring
  have hh := Chapter06.complexRSIntegrable_const_mul (fourier_native_gram m n).1 (A ^ 2)
  rw [he]
  refine ⟨hh.1, ?_⟩
  rw [hh.2, (fourier_native_gram m n).2]
  by_cases hmn : m = n
  · simp only [hmn, ite_true]
    have hs : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = (2 * Real.pi : ℂ) := by
      exact_mod_cast Real.sq_sqrt Real.two_pi_pos.le
    dsimp only [A]
    rw [inv_pow, hs]
    push_cast
    rw [inv_mul_cancel₀]
    exact_mod_cast Real.two_pi_pos.ne'
  · simp [hmn]

theorem normalizedFourierSystem_orthonormal :
    RiemannOrthonormal normalizedFourierSystem (-Real.pi) Real.pi := by
  constructor
  · intro m n hmn
    have hh := normalizedFourier_gram (Equiv.intEquivNat.symm m) (Equiv.intEquivNat.symm n)
    simpa only [normalizedFourierSystem, Equiv.apply_eq_iff_eq, hmn, ite_false] using hh
  · intro n
    have hh := normalizedFourier_gram (Equiv.intEquivNat.symm n) (Equiv.intEquivNat.symm n)
    have hi : Chapter06.RIntegrable (fun x => ‖normalizedFourierSystem n x‖ ^ 2)
        (-Real.pi) Real.pi := by
      simpa only [complex_mul_star, Complex.ofReal_re, normalizedFourierSystem] using hh.1.1
    refine ⟨hi, ?_⟩
    have he := congrArg Complex.re hh.2
    simpa only [complex_mul_star, Chapter06.ComplexRSIntegral, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, ite_true, Complex.one_re,
      normalizedFourierSystem] using he

theorem normalizedFourierSystem_all_frequencies (k : ℤ) :
    ∃ n : ℕ, normalizedFourierSystem n = normalizedFourier k :=
  ⟨Equiv.intEquivNat k, by simp [normalizedFourierSystem]⟩

end Rudin.PMA.Chapter08
