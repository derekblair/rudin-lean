import Rudin.PMA.Chapter08.FourierParseval
import Rudin.PMA.Chapter08.RiemannPeriodic
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter08

theorem fourierMonomial_sub (n : ℤ) (x t : ℝ) :
    fourierMonomial n (x - t) = fourierMonomial (-n) t * fourierMonomial n x := by
  unfold fourierMonomial
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem dirichletKernel_continuous (N : ℕ) : Continuous (dirichletKernel N) := by
  unfold dirichletKernel
  exact continuous_finsetSum _ (fun n _ => fourierMonomial_continuous n)

theorem dirichletKernel_periodic (N : ℕ) :
    Function.Periodic (dirichletKernel N) (2 * Real.pi) := by
  intro x
  unfold dirichletKernel
  apply Finset.sum_congr rfl
  intro n _
  exact fourierMonomial_periodic n x

/-- PMA 8.13: the first convolution expression for the symmetric Fourier sums.
The source function has precisely native Riemann integrability as its premise. -/
theorem riemannFourierSum_eq_integral {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    riemannFourierSum f N x = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t in (-Real.pi)..Real.pi, f t * dirichletKernel N (x - t) := by
  have hfi := native_complex_intervalIntegrable hf
  have hi (n : ℤ) : IntervalIntegrable
      (fun t => f t * fourierMonomial (-n) t) volume (-Real.pi) Real.pi :=
    hfi.mul_continuousOn (fourierMonomial_continuous (-n)).continuousOn
  unfold riemannFourierSum trigonometricPartialSum dirichletKernel
  simp_rw [riemannFourierCoeff_eq_integral hf]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← intervalIntegral.integral_mul_const]
  rw [← intervalIntegral.integral_finsetSum
    (fun n (_ : n ∈ Finset.Icc (-(N : ℤ)) N) => (hi n).mul_const _)]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [fourierMonomial_sub, mul_assoc]

theorem riemannFourierSum_eq_native_integral {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    Chapter06.ComplexRSIntegrable (fun t => f t * dirichletKernel N (x - t))
      id (-Real.pi) Real.pi ∧
    riemannFourierSum f N x = (2 * Real.pi : ℂ)⁻¹ *
      Chapter06.ComplexRSIntegral (fun t => f t * dirichletKernel N (x - t))
        id (-Real.pi) Real.pi := by
  have hi := complexRiemann_integrable_mul (g := fun t => dirichletKernel N (x - t)) hf
    (complexRiemann_integrable_of_continuousOn hf.1.1
      ((dirichletKernel_continuous N).comp (continuous_const.sub continuous_id)).continuousOn)
  refine ⟨hi, ?_⟩
  rw [native_complex_integral_eq hi]
  exact riemannFourierSum_eq_integral hf N x

theorem fourier_finite_mean_square {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) (N : ℕ) :
    Chapter06.RIntegrable (fun x => ‖riemannFourierSum f N x‖ ^ 2) (-Real.pi) Real.pi ∧
    (2 * Real.pi)⁻¹ * Chapter06.RIntegral
      (fun x => ‖riemannFourierSum f N x‖ ^ 2) (-Real.pi) Real.pi =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2 ∧
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ * Chapter06.RIntegral (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi := by
  have hs := fourier_partial_norm_sq (riemannFourierCoeff f) N
  have he := fourier_error_identity hf N
  have hn := native_integral_nonneg he.1 (fun x _ => sq_nonneg ‖f x - riemannFourierSum f N x‖)
  rw [he.2] at hn
  refine ⟨hs.1, ?_, ?_⟩
  · change (2 * Real.pi)⁻¹ * Chapter06.RIntegral
      (fun x => ‖trigonometricPartialSum (riemannFourierCoeff f) N x‖ ^ 2) _ _ = _
    rw [hs.2, ← mul_assoc, inv_mul_cancel₀ Real.two_pi_pos.ne', one_mul]
  · rw [← div_eq_inv_mul, le_div_iff₀ Real.two_pi_pos]
    nlinarith

theorem dirichletKernel_integral (N : ℕ) :
    (2 * Real.pi : ℂ)⁻¹ *
      ∫ t in (-Real.pi)..Real.pi, dirichletKernel N t = 1 := by
  have h := fourierCoeff_finite_sum (Finset.Icc (-(N : ℤ)) N) (fun _ => (1 : ℂ)) 0
  have he : (fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      (1 : ℂ) * fourierMonomial n x) = dirichletKernel N := by
    funext x
    simp [dirichletKernel]
  rw [he] at h
  have hi := complexRiemann_integrable_of_continuousOn
    (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])
    (dirichletKernel_continuous N).continuousOn
  rw [riemannFourierCoeff_eq_integral hi] at h
  simpa using h

theorem riemannFourierSum_eq_convolution {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (N : ℕ) (x : ℝ) :
    riemannFourierSum f N x = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t in (-Real.pi)..Real.pi, f (x - t) * dirichletKernel N t := by
  rw [riemannFourierSum_eq_integral hf]
  congr 1
  let h : ℝ → ℂ := fun t => f t * dirichletKernel N (x - t)
  have hh : Function.Periodic h (2 * Real.pi) := by
    intro t
    dsimp only [h]
    rw [hp t, show x - (t + 2 * Real.pi) = x - t - 2 * Real.pi by ring,
      (dirichletKernel_periodic N).sub_eq]
  have he := hh.intervalIntegral_add_eq (-Real.pi) (x - Real.pi)
  have ha : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have hb : x - Real.pi + 2 * Real.pi = x - -Real.pi := by ring
  rw [ha, hb] at he
  rw [show (fun t => f t * dirichletKernel N (x - t)) = h from rfl, he]
  rw [← intervalIntegral.integral_comp_sub_left h x]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [h]
  rw [sub_sub_cancel]

theorem fourier_convolution_native_of_translate_integrable {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (N : ℕ) (x : ℝ)
    (htranslate : Chapter06.ComplexRSIntegrable (fun t => f (x - t))
      id (-Real.pi) Real.pi) :
    Chapter06.ComplexRSIntegrable (fun t => f (x - t) * dirichletKernel N t)
      id (-Real.pi) Real.pi ∧
    riemannFourierSum f N x = (2 * Real.pi : ℂ)⁻¹ *
      Chapter06.ComplexRSIntegral (fun t => f (x - t) * dirichletKernel N t)
        id (-Real.pi) Real.pi := by
  have hi := complexRiemann_integrable_mul htranslate
    (complexRiemann_integrable_of_continuousOn hf.1.1
      (dirichletKernel_continuous N).continuousOn)
  refine ⟨hi, ?_⟩
  rw [native_complex_integral_eq hi]
  exact riemannFourierSum_eq_convolution hf hp N x

/-- PMA 8.13. The sine quotient is asserted away from a zero denominator, and
both convolution formulas use the native Chapter 6 Riemann integral. -/
def pma8_13_contract : Prop :=
  ∀ (f : ℝ → ℂ), Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi →
    Function.Periodic f (2 * Real.pi) → ∀ N : ℕ,
    (∀ x, riemannFourierSum f N x =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, riemannFourierCoeff f n * fourierMonomial n x) ∧
    Chapter06.RIntegrable (fun x => ‖riemannFourierSum f N x‖ ^ 2) (-Real.pi) Real.pi ∧
    (2 * Real.pi)⁻¹ * Chapter06.RIntegral
      (fun x => ‖riemannFourierSum f N x‖ ^ 2) (-Real.pi) Real.pi =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2 ∧
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖riemannFourierCoeff f n‖ ^ 2) ≤
      (2 * Real.pi)⁻¹ * Chapter06.RIntegral (fun x => ‖f x‖ ^ 2) (-Real.pi) Real.pi ∧
    (∀ t, dirichletKernel N t = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierMonomial n t) ∧
    (∀ t, Real.sin (t / 2) ≠ 0 → dirichletKernel N t =
      ((Real.sin (((N : ℝ) + 1 / 2) * t) / Real.sin (t / 2) : ℝ) : ℂ)) ∧
    (∀ x,
      Chapter06.ComplexRSIntegrable (fun t => f t * dirichletKernel N (x - t))
        id (-Real.pi) Real.pi ∧
      riemannFourierSum f N x = (2 * Real.pi : ℂ)⁻¹ *
        Chapter06.ComplexRSIntegral (fun t => f t * dirichletKernel N (x - t))
          id (-Real.pi) Real.pi ∧
      Chapter06.ComplexRSIntegrable (fun t => f (x - t) * dirichletKernel N t)
        id (-Real.pi) Real.pi ∧
      riemannFourierSum f N x = (2 * Real.pi : ℂ)⁻¹ *
        Chapter06.ComplexRSIntegral (fun t => f (x - t) * dirichletKernel N t)
          id (-Real.pi) Real.pi)

theorem pma8_13 : pma8_13_contract := by
  intro f hf hp N
  have hm := fourier_finite_mean_square hf N
  refine ⟨fun _ => rfl, hm.1, hm.2.1, hm.2.2, fun _ => rfl,
    fun t ht => dirichletKernel_eq_sin_quotient N t ht, ?_⟩
  intro x
  have hfirst := riemannFourierSum_eq_native_integral hf N x
  have hsecond := fourier_convolution_native_of_translate_integrable hf hp N x
    (periodic_riemann_translate_native_integrable hf hp x)
  exact ⟨hfirst.1, hfirst.2, hsecond.1, hsecond.2⟩

theorem periodic_riemann_integrable_every_interval {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (a b : ℝ) (hab : a ≤ b) :
    Chapter06.ComplexRSIntegrable f id a b := by
  have hf' : Chapter06.ComplexRSIntegrable f id (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert hf using 1
    ring
  exact native_complex_periodic_integrable Real.two_pi_pos hf' hp a b hab

/-- The integral over one full period is independent of its initial point. -/
theorem periodic_riemann_integral_one_period {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (a b : ℝ) :
    Chapter06.ComplexRSIntegral f id a (a + 2 * Real.pi) =
      Chapter06.ComplexRSIntegral f id b (b + 2 * Real.pi) := by
  have ha := periodic_riemann_integrable_every_interval hf hp a (a + 2 * Real.pi)
    (le_add_of_nonneg_right Real.two_pi_pos.le)
  have hb := periodic_riemann_integrable_every_interval hf hp b (b + 2 * Real.pi)
    (le_add_of_nonneg_right Real.two_pi_pos.le)
  rw [native_complex_integral_eq ha, native_complex_integral_eq hb]
  exact hp.intervalIntegral_add_eq a b

theorem periodic_riemann_bounded {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨A, hA⟩ := hf.1.2.1
  obtain ⟨B, hB⟩ := hf.2.2.1
  refine ⟨|A| + |B|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro x
  let y := toIcoMod Real.two_pi_pos (-Real.pi) x
  obtain ⟨hy, k, hk⟩ := (toIcoMod_eq_iff Real.two_pi_pos).mp (show
    toIcoMod Real.two_pi_pos (-Real.pi) x = y from rfl)
  have hy' : y ∈ Icc (-Real.pi) Real.pi := by
    refine ⟨hy.1, ?_⟩
    linarith [hy.2]
  rw [hk, hp.zsmul k y]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans
    (add_le_add ((hA y hy').trans (le_abs_self _)) ((hB y hy').trans (le_abs_self _)))

theorem periodic_riemann_translate_intervalIntegrable {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (x : ℝ) :
    IntervalIntegrable (fun t => f (x - t)) volume (-Real.pi) Real.pi := by
  have hi : IntervalIntegrable f volume (-Real.pi) (-Real.pi + 2 * Real.pi) := by
    convert native_complex_intervalIntegrable hf using 1
    ring
  have hj := (hp.intervalIntegrable Real.two_pi_pos.ne' hi (x - Real.pi) (x + Real.pi)).comp_sub_left x
  convert hj.symm using 1 <;> ring

/-- The quotient used in the proof of PMA 8.14 is bounded, with its removable
value at zero supplied by totalized field division. -/
theorem fourier_lipschitz_quotient_bounded {f : ℝ → ℂ} {x δ M : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (hδ : 0 < δ)
    (hl : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    ∃ C : ℝ, ∀ t ∈ Icc (-Real.pi) Real.pi,
      ‖(f (x - t) - f x) / (Real.sin (t / 2) : ℂ)‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := periodic_riemann_bounded hf hp
  refine ⟨|M| * Real.pi + 2 * B * Real.pi / δ, ?_⟩
  intro t ht
  have htπ : |t| ≤ Real.pi := abs_le.mpr ht
  have hs : |t| / Real.pi ≤ |Real.sin (t / 2)| := by
    have hh := Real.mul_abs_le_abs_sin (x := t / 2) (by
      rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      exact div_le_div_of_nonneg_right htπ (by norm_num))
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] at hh
    convert hh using 1
    ring
  by_cases ht0 : t = 0
  · simp only [ht0, sub_zero, sub_self, zero_div, norm_zero]
    positivity
  have hspos : 0 < |Real.sin (t / 2)| :=
    (div_pos (abs_pos.mpr ht0) Real.pi_pos).trans_le hs
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
  by_cases htd : |t| < δ
  · have hn : ‖f (x - t) - f x‖ ≤ |M| * |t| := by
      have hh := hl (-t) (by simpa using htd)
      have hh' : ‖f (x - t) - f x‖ ≤ M * |t| := by
        simpa only [abs_neg, ← sub_eq_add_neg] using hh
      exact hh'.trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _))
    have hsmall : ‖f (x - t) - f x‖ / |Real.sin (t / 2)| ≤ |M| * Real.pi := by
      apply (div_le_iff₀ hspos).mpr
      calc
        _ ≤ |M| * |t| := hn
        _ ≤ |M| * Real.pi * |Real.sin (t / 2)| := by
          have hh := (div_le_iff₀ Real.pi_pos).mp hs
          nlinarith [abs_nonneg M]
    exact hsmall.trans (le_add_of_nonneg_right (by positivity))
  · have hn : ‖f (x - t) - f x‖ ≤ 2 * B :=
      (norm_sub_le _ _).trans (by linarith [hb (x - t), hb x])
    have hlarge : ‖f (x - t) - f x‖ / |Real.sin (t / 2)| ≤ 2 * B * Real.pi / δ := by
      apply (div_le_iff₀ hspos).mpr
      have hd : δ ≤ |t| := le_of_not_gt htd
      have hd' : δ / Real.pi ≤ |Real.sin (t / 2)| :=
        (div_le_div_of_nonneg_right hd Real.pi_pos.le).trans hs
      have hmul := mul_le_mul_of_nonneg_left hd' (show 0 ≤ 2 * B * Real.pi / δ by positivity)
      have he : (2 * B * Real.pi / δ) * (δ / Real.pi) = 2 * B := by
        field_simp
      rw [he] at hmul
      exact hn.trans hmul
    exact hlarge.trans (le_add_of_nonneg_left (by positivity))

theorem fourier_lipschitz_quotient_intervalIntegrable {f : ℝ → ℂ} {x δ M : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (hδ : 0 < δ)
    (hl : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    IntervalIntegrable (fun t => (f (x - t) - f x) / (Real.sin (t / 2) : ℂ))
      volume (-Real.pi) Real.pi := by
  obtain ⟨C, hC⟩ := fourier_lipschitz_quotient_bounded hf hp hδ hl
  have ht := periodic_riemann_translate_intervalIntegrable hf hp x
  have hm : AEStronglyMeasurable
      (fun t => (f (x - t) - f x) / (Real.sin (t / 2) : ℂ))
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    apply AEStronglyMeasurable.div₀ (ht.1.aestronglyMeasurable.sub aestronglyMeasurable_const)
    exact (by fun_prop : Continuous (fun t : ℝ => (Real.sin (t / 2) : ℂ))).aestronglyMeasurable
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hf.1.1).mpr
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound hm C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hC t (Ioc_subset_Icc_self ht)

private theorem interval_oscillation_rl (g : ℝ → ℂ) (w : ℝ) :
    (∫ t : ℝ, Real.fourierChar (-(t * (-w / (2 * Real.pi)))) •
      (Ioc (-Real.pi) Real.pi).indicator g t) =
    ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp ((w : ℂ) * t * Complex.I) := by
  have hind : (fun t => Real.fourierChar (-(t * (-w / (2 * Real.pi)))) •
      (Ioc (-Real.pi) Real.pi).indicator g t) =
      (Ioc (-Real.pi) Real.pi).indicator
        (fun t => Real.fourierChar (-(t * (-w / (2 * Real.pi)))) • g t) := by
    funext t
    exact (Set.indicator_smul_apply (Ioc (-Real.pi) Real.pi)
      (fun t => Real.fourierChar (-(t * (-w / (2 * Real.pi))))) g t).symm
  rw [hind, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (show -Real.pi ≤ Real.pi by linarith [Real.pi_pos])]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

theorem interval_integral_mul_sin_tendsto_zero {g : ℝ → ℂ}
    (hg : IntervalIntegrable g volume (-Real.pi) Real.pi)
    {w : ℕ → ℝ} (hw : Tendsto w atTop atTop) :
    Tendsto (fun N => ∫ t in (-Real.pi)..Real.pi,
      g t * (Real.sin (w N * t) : ℂ)) atTop (𝓝 0) := by
  have hdiv := hw.atTop_div_const Real.two_pi_pos
  have hp := (Real.tendsto_integral_exp_smul_cocompact
    ((Ioc (-Real.pi) Real.pi).indicator g)).comp
      ((tendsto_neg_atTop_atBot.comp hdiv).mono_right atBot_le_cocompact)
  have hn := (Real.tendsto_integral_exp_smul_cocompact
    ((Ioc (-Real.pi) Real.pi).indicator g)).comp
      (hdiv.mono_right atTop_le_cocompact)
  have hp' : Tendsto (fun N => ∫ t in (-Real.pi)..Real.pi,
      g t * Complex.exp ((w N : ℂ) * t * Complex.I)) atTop (𝓝 0) := by
    have he (N : ℕ) :
        (∫ t : ℝ, Real.fourierChar (-(t * -(w N / (2 * Real.pi)))) •
          (Ioc (-Real.pi) Real.pi).indicator g t) =
        ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp ((w N : ℂ) * t * Complex.I) := by
      simpa only [neg_div] using interval_oscillation_rl g (w N)
    simpa only [Function.comp_def, he] using hp
  have hn' : Tendsto (fun N => ∫ t in (-Real.pi)..Real.pi,
      g t * Complex.exp ((-w N : ℂ) * t * Complex.I)) atTop (𝓝 0) := by
    have he (N : ℕ) :
        (∫ t : ℝ, Real.fourierChar (-(t * (w N / (2 * Real.pi)))) •
          (Ioc (-Real.pi) Real.pi).indicator g t) =
        ∫ t in (-Real.pi)..Real.pi, g t * Complex.exp ((-w N : ℂ) * t * Complex.I) := by
      simpa only [neg_neg, Complex.ofReal_neg] using interval_oscillation_rl g (-w N)
    simpa only [Function.comp_def, he] using hn
  have heq (N : ℕ) : (∫ t in (-Real.pi)..Real.pi, g t * (Real.sin (w N * t) : ℂ)) =
      ((∫ t in (-Real.pi)..Real.pi, g t * Complex.exp ((-w N : ℂ) * t * Complex.I)) -
        (∫ t in (-Real.pi)..Real.pi, g t * Complex.exp ((w N : ℂ) * t * Complex.I))) *
          Complex.I / 2 := by
    rw [← intervalIntegral.integral_sub
        (hg.mul_continuousOn (by fun_prop)) (hg.mul_continuousOn (by fun_prop)),
      ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [Complex.ofReal_sin, Complex.sin]
    push_cast
    ring_nf
  simp_rw [heq]
  simpa using ((hn'.sub hp').mul_const Complex.I).div_const (2 : ℂ)

theorem riemannFourierSum_sub_value {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (N : ℕ) (x : ℝ) :
    riemannFourierSum f N x - f x = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * dirichletKernel N t := by
  have hi := periodic_riemann_translate_intervalIntegrable hf hp x
  have hd : IntervalIntegrable (dirichletKernel N) volume (-Real.pi) Real.pi :=
    (dirichletKernel_continuous N).intervalIntegrable _ _
  rw [riemannFourierSum_eq_convolution hf hp]
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub (hi.mul_continuousOn
    (dirichletKernel_continuous N).continuousOn) (hd.const_mul _),
    intervalIntegral.integral_const_mul]
  have he := dirichletKernel_integral N
  linear_combination (f x) * he

theorem riemannFourierSum_sub_value_eq_sine_integral {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (N : ℕ) (x : ℝ) :
    riemannFourierSum f N x - f x = (2 * Real.pi : ℂ)⁻¹ *
      ∫ t in (-Real.pi)..Real.pi,
        ((f (x - t) - f x) / (Real.sin (t / 2) : ℂ)) *
          (Real.sin (((N : ℝ) + 1 / 2) * t) : ℂ) := by
  rw [riemannFourierSum_sub_value hf hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  by_cases ht0 : t = 0
  · simp [ht0]
  have htπ : |t| ≤ Real.pi := by
    rw [uIcc_of_le hf.1.1] at ht
    exact abs_le.mpr ht
  have hs := Real.mul_abs_le_abs_sin (x := t / 2) (by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact div_le_div_of_nonneg_right htπ (by norm_num))
  have hspos : 0 < |Real.sin (t / 2)| :=
    (mul_pos (div_pos (by norm_num) Real.pi_pos) (abs_pos.mpr (div_ne_zero ht0 (by norm_num)))).trans_le hs
  have hne : (Real.sin (t / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (abs_pos.mp hspos)
  rw [← dirichletKernel_mul_sin N t]
  field_simp

/-- The pointwise convergence assertion of PMA 8.14, with the local bound exactly
at the specified point; global Lipschitz continuity is not assumed. -/
theorem riemannFourierSum_tendsto_of_local_lipschitz {f : ℝ → ℂ} {x δ M : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (hδ : 0 < δ)
    (hl : ∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) :
    Tendsto (fun N => riemannFourierSum f N x) atTop (𝓝 (f x)) := by
  have hg := fourier_lipschitz_quotient_intervalIntegrable hf hp hδ hl
  have hw : Tendsto (fun N : ℕ => (N : ℝ) + 1 / 2) atTop atTop :=
    tendsto_atTop_mono (fun N => le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
  have hlim := (interval_integral_mul_sin_tendsto_zero hg hw).const_mul (2 * Real.pi : ℂ)⁻¹
  have he (N : ℕ) := riemannFourierSum_sub_value_eq_sine_integral hf hp N x
  have hz : Tendsto (fun N => riemannFourierSum f N x - f x) atTop (𝓝 0) := by
    simpa only [← he, mul_zero] using hlim
  simpa only [sub_add_cancel, zero_add] using hz.add_const (f x)

theorem fourier_native_integrable_sub {f g : ℝ → ℂ} {a b : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id a b)
    (hg : Chapter06.ComplexRSIntegrable g id a b) :
    Chapter06.ComplexRSIntegrable (fun x => f x - g x) id a b := by
  simpa only [sub_eq_add_neg, neg_one_mul] using
    (Chapter06.complexRSIntegrable_add hf (Chapter06.complexRSIntegrable_const_mul hg (-1)).1).1

theorem riemannFourierCoeff_sub {f g : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hg : Chapter06.ComplexRSIntegrable g id (-Real.pi) Real.pi) (n : ℤ) :
    riemannFourierCoeff (fun x => f x - g x) n =
      riemannFourierCoeff f n - riemannFourierCoeff g n := by
  have hfg := fourier_native_integrable_sub hf hg
  rw [riemannFourierCoeff_eq_integral hfg, riemannFourierCoeff_eq_integral hf,
    riemannFourierCoeff_eq_integral hg]
  simp_rw [sub_mul]
  rw [intervalIntegral.integral_sub
    ((native_complex_intervalIntegrable hf).mul_continuousOn
      (fourierMonomial_continuous (-n)).continuousOn)
    ((native_complex_intervalIntegrable hg).mul_continuousOn
      (fourierMonomial_continuous (-n)).continuousOn), mul_sub]

theorem riemannFourierSum_sub {f g : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hg : Chapter06.ComplexRSIntegrable g id (-Real.pi) Real.pi) (N : ℕ) (x : ℝ) :
    riemannFourierSum (fun t => f t - g t) N x =
      riemannFourierSum f N x - riemannFourierSum g N x := by
  unfold riemannFourierSum trigonometricPartialSum
  simp_rw [riemannFourierCoeff_sub hf hg, sub_mul, Finset.sum_sub_distrib]

/-- The localization corollary: only equality in some neighborhood of the point
is needed. Both original functions retain native Riemann-integrability. -/
theorem fourier_localization {f g : ℝ → ℂ} {x δ : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hg : Chapter06.ComplexRSIntegrable g id (-Real.pi) Real.pi)
    (hpf : Function.Periodic f (2 * Real.pi))
    (hpg : Function.Periodic g (2 * Real.pi)) (hδ : 0 < δ)
    (he : ∀ t : ℝ, |t - x| < δ → f t = g t) :
    Tendsto (fun N => riemannFourierSum f N x - riemannFourierSum g N x) atTop (𝓝 0) := by
  have hx : f x = g x := he x (by simpa using hδ)
  have hh := riemannFourierSum_tendsto_of_local_lipschitz
    (f := fun t => f t - g t) (x := x) (M := 0)
    (fourier_native_integrable_sub hf hg) (fun t => by dsimp only; rw [hpf t, hpg t]) hδ
    (fun t ht => by simp [he (x + t) (by simpa using ht), hx])
  simpa only [riemannFourierSum_sub hf hg, hx, sub_self] using hh

theorem fourier_tendsto_zero_on_open_interval {f : ℝ → ℂ} {a b x : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi)
    (hp : Function.Periodic f (2 * Real.pi)) (hx : x ∈ Ioo a b)
    (hz : ∀ t ∈ Ioo a b, f t = 0) :
    Tendsto (fun N => riemannFourierSum f N x) atTop (𝓝 0) := by
  have hδ : 0 < min (x - a) (b - x) := lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hh := riemannFourierSum_tendsto_of_local_lipschitz (x := x) (M := 0)
    hf hp hδ (fun t ht => ?_)
  · simpa only [hz x hx] using hh
  · have ht' := abs_lt.mp ht
    have hxt : x + t ∈ Ioo a b := by
      have h₁ := min_le_left (x - a) (b - x)
      have h₂ := min_le_right (x - a) (b - x)
      constructor <;> linarith
    simp only [hz (x + t) hxt, hz x hx, sub_self, norm_zero, zero_mul, le_refl]

def pma8_14_contract : Prop :=
  (∀ (f : ℝ → ℂ) (x δ M : ℝ),
    Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi →
    Function.Periodic f (2 * Real.pi) → 0 < δ →
    (∀ t : ℝ, |t| < δ → ‖f (x + t) - f x‖ ≤ M * |t|) →
    Tendsto (fun N => riemannFourierSum f N x) atTop (𝓝 (f x))) ∧
  (∀ (f g : ℝ → ℂ) (x δ : ℝ),
    Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi →
    Chapter06.ComplexRSIntegrable g id (-Real.pi) Real.pi →
    Function.Periodic f (2 * Real.pi) → Function.Periodic g (2 * Real.pi) → 0 < δ →
    (∀ t : ℝ, |t - x| < δ → f t = g t) →
    Tendsto (fun N => riemannFourierSum f N x - riemannFourierSum g N x) atTop (𝓝 0))

theorem pma8_14 : pma8_14_contract :=
  ⟨fun _ _ _ _ hf hp hδ hl => riemannFourierSum_tendsto_of_local_lipschitz hf hp hδ hl,
    fun _ _ _ _ hf hg hpf hpg hδ he => fourier_localization hf hg hpf hpg hδ he⟩

end Rudin.PMA.Chapter08
