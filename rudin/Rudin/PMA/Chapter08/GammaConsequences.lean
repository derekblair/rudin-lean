import Rudin.PMA.Chapter08.Gamma

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter08

def trigonometricBetaIntegrand (x y t : ℝ) : ℝ :=
  Real.sin t ^ (2 * x - 1) * Real.cos t ^ (2 * y - 1)

private theorem sin_sq_strictMono :
    StrictMonoOn (fun t => Real.sin t ^ 2) (Icc 0 (Real.pi / 2)) := by
  intro a ha b hb hab
  have hsin := Real.strictMonoOn_sin
    (show a ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      exact ⟨(by linarith [Real.pi_pos, ha.1]), ha.2⟩)
    (show b ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by
      exact ⟨(by linarith [Real.pi_pos, hb.1]), hb.2⟩) hab
  exact pow_lt_pow_left₀ hsin (Real.sin_nonneg_of_nonneg_of_le_pi ha.1
    (ha.2.trans (by linarith [Real.pi_pos]))) (by decide)

private theorem sin_sq_image :
    (fun t => Real.sin t ^ 2) '' Ioo 0 (Real.pi / 2) = Ioo 0 1 := by
  simpa using ContinuousOn.image_Ioo_of_strictMonoOn
    (show (0 : ℝ) ≤ Real.pi / 2 by positivity)
    (show ContinuousOn (fun t => Real.sin t ^ 2) (Icc 0 (Real.pi / 2)) by fun_prop)
    sin_sq_strictMono

private theorem sin_sq_deriv (t : ℝ) :
    HasDerivAt (fun t => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t) t := by
  simpa using! (Real.hasDerivAt_sin t).pow 2

private theorem trigonometricBeta_change (x y t : ℝ) (ht : t ∈ Ioo 0 (Real.pi / 2)) :
    |2 * Real.sin t * Real.cos t| • betaIntegrand x y (Real.sin t ^ 2) =
      2 * trigonometricBetaIntegrand x y t := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
    (ht.2.trans (by linarith [Real.pi_pos]))
  have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
  rw [abs_of_pos (by positivity), smul_eq_mul, betaIntegrand, trigonometricBetaIntegrand,
    show 1 - Real.sin t ^ 2 = Real.cos t ^ 2 by nlinarith [Real.sin_sq_add_cos_sq t]]
  rw [← Real.rpow_natCast (Real.sin t) 2, ← Real.rpow_natCast (Real.cos t) 2,
    ← Real.rpow_mul hs.le, ← Real.rpow_mul hc.le]
  have h1 : Real.sin t * Real.sin t ^ ((2 : ℝ) * (x - 1)) = Real.sin t ^ (2 * x - 1) := by
    nth_rw 1 [← Real.rpow_one (Real.sin t)]
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have h2 : Real.cos t * Real.cos t ^ ((2 : ℝ) * (y - 1)) = Real.cos t ^ (2 * y - 1) := by
    nth_rw 1 [← Real.rpow_one (Real.cos t)]
    rw [← Real.rpow_add hc]
    congr 1
    ring
  calc
    _ = 2 * ((Real.sin t * Real.sin t ^ (2 * (x - 1))) *
      (Real.cos t * Real.cos t ^ (2 * (y - 1)))) := by ring
    _ = _ := by rw [h1, h2]

/-- PMA 8.21, equation (98); the endpoint singularities are integrable. -/
theorem trigonometric_beta {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (trigonometricBetaIntegrand x y) volume 0 (Real.pi / 2) ∧
    2 * (∫ t in 0..(Real.pi / 2), trigonometricBetaIntegrand x y t) =
      gamma x * gamma y / gamma (x + y) := by
  have hd : ∀ t ∈ Ioo 0 (Real.pi / 2),
      HasDerivWithinAt (fun t => Real.sin t ^ 2) (2 * Real.sin t * Real.cos t)
        (Ioo 0 (Real.pi / 2)) t := fun t _ => (sin_sq_deriv t).hasDerivWithinAt
  have hinj := (sin_sq_strictMono.mono Ioo_subset_Icc_self).injOn
  have hi := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo hd hinj
    (betaIntegrand x y)).mp (by
      rw [sin_sq_image]
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (betaIntegrand_integrable hx hy))
  have hi2 : IntegrableOn (fun t => 2 * trigonometricBetaIntegrand x y t)
      (Ioo 0 (Real.pi / 2)) :=
    IntegrableOn.congr_fun hi (trigonometricBeta_change x y) measurableSet_Ioo
  constructor
  · apply (intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)).mpr
    have hi3 := hi2.const_mul (1 / 2 : ℝ)
    have heq : (fun t => (1 / 2 : ℝ) * (2 * trigonometricBetaIntegrand x y t)) =
        trigonometricBetaIntegrand x y := by funext t; ring
    rw [heq] at hi3
    exact hi3
  · have he := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hd hinj
      (betaIntegrand x y)
    rw [sin_sq_image] at he
    rw [setIntegral_congr_fun measurableSet_Ioo (trigonometricBeta_change x y),
      integral_const_mul] at he
    rw [intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
    rw [← he, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le zero_le_one]
    exact betaIntegral_eq hx hy

/-- The substitution in PMA 8.21, equation (100), including convergence. -/
theorem gamma_square_substitution {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => s ^ (2 * x - 1) * Real.exp (-(s ^ 2))) (Ioi 0) ∧
    gamma x = 2 * ∫ s in Ioi 0, s ^ (2 * x - 1) * Real.exp (-(s ^ 2)) := by
  have heq (s : ℝ) (hs : s ∈ Ioi (0 : ℝ)) :
      s ^ ((2 : ℝ) - 1) • gammaIntegrand x (s ^ (2 : ℝ)) =
        s ^ (2 * x - 1) * Real.exp (-(s ^ 2)) := by
    simp only [gammaIntegrand, smul_eq_mul, ← mul_assoc]
    rw [← Real.rpow_mul hs.le, ← Real.rpow_add hs]
    norm_num
    congr 1
    ring
  constructor
  · exact ((integrableOn_Ioi_comp_rpow_iff' (gammaIntegrand x)
      (by norm_num : (2 : ℝ) ≠ 0)).mpr (gammaIntegrand_integrable hx)).congr_fun heq
      measurableSet_Ioi
  · have h := integral_rpow_mul_exp_neg_rpow (show (0 : ℝ) < 2 by norm_num)
      (show -1 < 2 * x - 1 by linarith)
    have hc : (2 * x - 1 + 1) / 2 = x := by ring
    rw [hc] at h
    norm_num at h
    rw [gamma_eq_realGamma hx, h]
    ring

theorem gamma_half : gamma (1 / 2) = Real.sqrt Real.pi := by
  rw [gamma_eq_realGamma (by norm_num), Real.Gamma_one_half_eq]

theorem gamma_gaussian :
    Integrable (fun s : ℝ => Real.exp (-(s ^ 2))) ∧
    (∫ s : ℝ, Real.exp (-(s ^ 2))) = Real.sqrt Real.pi := by
  constructor
  · simpa only [neg_mul, one_mul] using integrable_exp_neg_mul_sq (show (0 : ℝ) < 1 by norm_num)
  · simpa only [neg_mul, one_mul, div_one] using integral_gaussian 1

theorem gamma_duplication {x : ℝ} (hx : 0 < x) :
    gamma x = 2 ^ (x - 1) / Real.sqrt Real.pi * gamma (x / 2) * gamma ((x + 1) / 2) := by
  rw [gamma_eq_realGamma hx, gamma_eq_realGamma (by positivity),
    gamma_eq_realGamma (by positivity)]
  have h := Real.doublingGamma_eq_Gamma hx
  rw [Real.doublingGamma] at h
  rw [show (x + 1) / 2 = x / 2 + 1 / 2 by ring]
  calc
    Real.Gamma x = _ := h.symm
    _ = _ := by ring

/-- The beta substitution also holds as an improper limit of the native
Chapter 6 integrals, with independent truncations at the two endpoints. -/
theorem trigonometric_beta_native_limit {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0))
    (hv : Tendsto v atTop (𝓝 (Real.pi / 2)))
    (huv : ∀ n, 0 < u n ∧ u n ≤ v n ∧ v n < Real.pi / 2) :
    Tendsto (fun n => 2 * Chapter06.RSIntegral
      (trigonometricBetaIntegrand x y) id (u n) (v n)) atTop
      (𝓝 (gamma x * gamma y / gamma (x + y))) := by
  have hc : ContinuousOn (trigonometricBetaIntegrand x y) (Ioo 0 (Real.pi / 2)) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1
      (ht.2.trans (by linarith [Real.pi_pos]))
    have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1], ht.2⟩
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hs.ne')).comp
      Real.continuous_sin.continuousAt).mul
      ((Real.continuousAt_rpow_const _ _ (Or.inl hcos.ne')).comp
        Real.continuous_cos.continuousAt)
  have h := (native_improper_interval_limit (by positivity)
    (trigonometric_beta hx hy).1 hc u v hu hv huv).const_mul 2
  simpa only [(trigonometric_beta hx hy).2] using h

theorem gamma_square_native_limit {x : ℝ} (hx : 0 < x)
    (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop atTop)
    (huv : ∀ n, 0 < u n ∧ u n ≤ v n) :
    Tendsto (fun n => 2 * Chapter06.RSIntegral
      (fun s : ℝ => s ^ (2 * x - 1) * Real.exp (-(s ^ 2))) id (u n) (v n)) atTop
      (𝓝 (gamma x)) := by
  have hc : ContinuousOn (fun s : ℝ => s ^ (2 * x - 1) * Real.exp (-(s ^ 2))) (Ioi 0) := by
    apply ContinuousOn.mul _ (by fun_prop)
    exact continuousOn_of_forall_continuousAt (fun t ht =>
      Real.continuousAt_rpow_const _ _ (Or.inl ht.ne'))
  have h := (native_improper_Ioi_limit (gamma_square_substitution hx).1 hc u v hu hv huv).const_mul 2
  simpa only [← (gamma_square_substitution hx).2] using h

theorem gamma_gaussian_native_limit (u v : ℕ → ℝ)
    (hu : Tendsto u atTop atBot) (hv : Tendsto v atTop atTop)
    (huv : ∀ n, u n ≤ v n) :
    Tendsto (fun n => Chapter06.RSIntegral (fun s : ℝ => Real.exp (-(s ^ 2)))
      id (u n) (v n)) atTop (𝓝 (Real.sqrt Real.pi)) := by
  have h := intervalIntegral_tendsto_integral gamma_gaussian.1 hu hv
  rw [gamma_gaussian.2] at h
  apply h.congr
  intro n
  exact (continuous_native_integral_eq (huv n) (by fun_prop)).symm

/-- PMA 8.21: all five displayed consequences, including convergence of the
integrals which may have endpoint singularities. -/
def pma8_21_contract : Prop :=
  (∀ x y : ℝ, 0 < x → 0 < y →
    IntervalIntegrable (trigonometricBetaIntegrand x y) volume 0 (Real.pi / 2) ∧
    2 * (∫ t in 0..(Real.pi / 2), trigonometricBetaIntegrand x y t) =
      gamma x * gamma y / gamma (x + y)) ∧
  gamma (1 / 2) = Real.sqrt Real.pi ∧
  (∀ x : ℝ, 0 < x →
    IntegrableOn (fun s : ℝ => s ^ (2 * x - 1) * Real.exp (-(s ^ 2))) (Ioi 0) ∧
    gamma x = 2 * ∫ s in Ioi 0, s ^ (2 * x - 1) * Real.exp (-(s ^ 2))) ∧
  (Integrable (fun s : ℝ => Real.exp (-(s ^ 2))) ∧
    (∫ s : ℝ, Real.exp (-(s ^ 2))) = Real.sqrt Real.pi) ∧
  (∀ x : ℝ, 0 < x → gamma x =
    2 ^ (x - 1) / Real.sqrt Real.pi * gamma (x / 2) * gamma ((x + 1) / 2))

theorem pma8_21 : pma8_21_contract :=
  ⟨fun _ _ hx hy => trigonometric_beta hx hy, gamma_half,
    fun _ hx => gamma_square_substitution hx, gamma_gaussian,
    fun _ hx => gamma_duplication hx⟩

end Rudin.PMA.Chapter08
