import Rudin.PMA.Chapter06.Calculus
import Rudin.PMA.Chapter06.Endpoint
import Mathlib

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter08

/-- The native Chapter 6 integral agrees with the library integral on compact
intervals for continuous real functions. The proof uses both versions of FTC. -/
theorem continuous_native_integral_eq {f : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Chapter06.RSIntegral f id a b = ∫ t in a..b, f t := by
  rcases hab.eq_or_lt with rfl | hab
  · simp only [(Chapter06.calculus_singleton_integrals f id a).2,
      intervalIntegral.integral_same]
  let g : ℝ → ℝ := IccExtend hab.le (fun t : Icc a b => f t)
  have hg : Continuous g :=
    continuous_IccExtend_iff.mpr (continuousOn_iff_continuous_domRestrict.mp hf)
  have heq (t : ℝ) (ht : t ∈ Icc a b) : g t = f t := by
    exact IccExtend_of_mem _ _ ht
  have hi := Chapter06.rsIntegrable_of_continuousOn hab.le hf
    (show MonotoneOn id (Icc a b) from fun _ _ _ _ h => h)
  have hftc := Chapter06.pma6_21 (fun u => ∫ t in a..u, g t) f a b hab
    (fun t ht => by
      rw [← heq t ht]
      exact (intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable a t)
        hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt).hasDerivWithinAt) hi
  rw [intervalIntegral.integral_same, sub_zero] at hftc
  exact hftc.trans (intervalIntegral.integral_congr (fun t ht =>
    heq t (by simpa only [uIcc_of_le hab.le] using ht)))

/-- A convergent library integral of a function continuous on the open interval
is the improper limit of native compact Riemann integrals. Either endpoint may
be singular; the two truncations approach independently. -/
theorem native_improper_interval_limit {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hi : IntervalIntegrable f volume a b)
    (hc : ContinuousOn f (Ioo a b)) (u v : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 a)) (hv : Tendsto v atTop (𝓝 b))
    (huv : ∀ n, a < u n ∧ u n ≤ v n ∧ v n < b) :
    Tendsto (fun n => Chapter06.RSIntegral f id (u n) (v n)) atTop
      (𝓝 (∫ t in a..b, f t)) := by
  have hF := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hu' : Tendsto u atTop (𝓝[uIcc a b] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu, Eventually.of_forall (fun n => by
      rw [uIcc_of_le hab.le]
      exact ⟨(huv n).1.le, ((huv n).2.1.trans (huv n).2.2.le)⟩)⟩
  have hv' : Tendsto v atTop (𝓝[uIcc a b] b) :=
    tendsto_nhdsWithin_iff.mpr ⟨hv, Eventually.of_forall (fun n => by
      rw [uIcc_of_le hab.le]
      exact ⟨(huv n).1.le.trans (huv n).2.1, (huv n).2.2.le⟩)⟩
  have h := ((hF b right_mem_uIcc).tendsto.comp hv').sub
    ((hF a left_mem_uIcc).tendsto.comp hu')
  simp only [intervalIntegral.integral_same, sub_zero] at h
  apply h.congr
  intro n
  have hun : u n ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨(huv n).1.le, (huv n).2.1.trans (huv n).2.2.le⟩
  have hvn : v n ∈ uIcc a b := by
    rw [uIcc_of_le hab.le]
    exact ⟨(huv n).1.le.trans (huv n).2.1, (huv n).2.2.le⟩
  simp only [Function.comp_apply]
  rw [intervalIntegral.integral_interval_sub_left
    (hi.mono_set (uIcc_subset_uIcc left_mem_uIcc hvn))
    (hi.mono_set (uIcc_subset_uIcc left_mem_uIcc hun))]
  exact (continuous_native_integral_eq (huv n).2.1 (hc.mono (fun t ht =>
    ⟨(huv n).1.trans_le ht.1, ht.2.trans_lt (huv n).2.2⟩))).symm

/-- Both improper endpoints on the positive half-line, expressed with native
compact truncations. This applies also to the square substitution in 8.21. -/
theorem native_improper_Ioi_limit {f : ℝ → ℝ}
    (hi : IntegrableOn f (Ioi 0)) (hc : ContinuousOn f (Ioi 0))
    (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop atTop)
    (huv : ∀ n, 0 < u n ∧ u n ≤ v n) :
    Tendsto (fun n => Chapter06.RSIntegral f id (u n) (v n)) atTop
      (𝓝 (∫ t in Ioi 0, f t)) := by
  have hi01 : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  have hF := intervalIntegral.continuousOn_primitive_interval' hi01 left_mem_uIcc
  have hu' : Tendsto u atTop (𝓝[uIcc (0 : ℝ) 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hu, ?_⟩
    filter_upwards [hu.eventually (Iio_mem_nhds zero_lt_one)] with n hn
    rw [uIcc_of_le zero_le_one]
    exact ⟨(huv n).1.le, hn.le⟩
  have hlow := (hF 0 left_mem_uIcc).tendsto.comp hu'
  have hup := intervalIntegral_tendsto_integral_Ioi 0 hi hv
  have h := hup.sub hlow
  simp only [intervalIntegral.integral_same, sub_zero] at h
  apply h.congr
  intro n
  have hiu : IntervalIntegrable f volume 0 (u n) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (huv n).1.le).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  have hiv : IntervalIntegrable f volume 0 (v n) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le ((huv n).1.le.trans (huv n).2)).mpr
      (hi.mono_set Ioc_subset_Ioi_self)
  simp only [Function.comp_apply]
  rw [intervalIntegral.integral_interval_sub_left hiv hiu]
  exact (continuous_native_integral_eq (huv n).2 (hc.mono (fun t ht =>
    (huv n).1.trans_le ht.1))).symm

/-! Gamma-function nodes PMA 8.17–8.20, printed pp.192–194.
The integrals below include integrability and endpoint limit assertions. The
library's integral is used to construct the improper integral; finite compact
truncations are related to the native Chapter 6 integral below.
-/

/-- PMA 8.17 integrand, with real powers on the positive half-line. -/
def gammaIntegrand (x t : ℝ) : ℝ := t ^ (x - 1) * Real.exp (-t)

/-- PMA 8.17. Only positive arguments are used in the source-facing results. -/
def gamma (x : ℝ) : ℝ := ∫ t in Ioi 0, gammaIntegrand x t

theorem gammaIntegrand_integrable {x : ℝ} (hx : 0 < x) :
    IntegrableOn (gammaIntegrand x) (Ioi 0) := by
  change IntegrableOn (fun t : ℝ => t ^ (x - 1) * Real.exp (-t)) (Ioi 0)
  simpa only [mul_comm] using Real.GammaIntegral_convergent hx

theorem gamma_eq_realGamma {x : ℝ} (hx : 0 < x) : gamma x = Real.Gamma x := by
  simpa [gamma, gammaIntegrand, mul_comm] using (Real.Gamma_eq_integral hx).symm

/-- Explicit convergence at infinity, including the integrable singularity at zero. -/
theorem gamma_upper_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun b : ℝ => ∫ t in 0..b, gammaIntegrand x t) atTop (𝓝 (gamma x)) :=
  intervalIntegral_tendsto_integral_Ioi 0 (gammaIntegrand_integrable hx) tendsto_id

theorem gammaIntegrand_continuousOn {x a b : ℝ} (ha : 0 < a) :
    ContinuousOn (gammaIntegrand x) (Icc a b) := by
  apply ContinuousOn.mul _ (by fun_prop)
  exact continuousOn_of_forall_continuousAt (fun t ht =>
    Real.continuousAt_rpow_const _ _ (Or.inl (ha.trans_le ht.1).ne'))

/-- Lower-endpoint convergence in the native Riemann theory: each compact
truncation starts strictly to the right of the possible singularity. -/
theorem gamma_lower_native_limit {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    Tendsto (fun a => Chapter06.RSIntegral (gammaIntegrand x) id a b)
      (𝓝[>] 0) (𝓝 (∫ t in 0..b, gammaIntegrand x t)) := by
  have hi : IntervalIntegrable (gammaIntegrand x) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).mpr
      ((gammaIntegrand_integrable hx).mono_set Ioc_subset_Ioi_self)
  have hc := (intervalIntegral.continuousOn_primitive_interval_left
    ((intervalIntegrable_iff').mp hi)) 0 (show (0 : ℝ) ∈ uIcc 0 b by simp)
  rw [uIcc_of_le hb.le, ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE hb] at hc
  apply (hc.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)).congr'
  filter_upwards [self_mem_nhdsWithin,
    (nhdsWithin_le_nhds (Iio_mem_nhds hb) : ∀ᶠ a : ℝ in 𝓝[>] 0, a < b)] with a ha hab
  exact (continuous_native_integral_eq hab.le (gammaIntegrand_continuousOn ha)).symm

theorem gamma_native_improper_limit {x : ℝ} (hx : 0 < x)
    (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop atTop)
    (huv : ∀ n, 0 < u n ∧ u n ≤ v n) :
    Tendsto (fun n => Chapter06.RSIntegral (gammaIntegrand x) id (u n) (v n)) atTop
      (𝓝 (gamma x)) := by
  apply native_improper_Ioi_limit (gammaIntegrand_integrable hx) _ u v hu hv huv
  apply ContinuousOn.mul _ (by fun_prop)
  exact continuousOn_of_forall_continuousAt (fun t ht =>
    Real.continuousAt_rpow_const _ _ (Or.inl ht.ne'))

def pma8_17_contract : Prop := ∀ x : ℝ, 0 < x →
  IntegrableOn (gammaIntegrand x) (Ioi 0) ∧
  gamma x = ∫ t in Ioi 0, t ^ (x - 1) * Real.exp (-t) ∧
  Tendsto (fun b : ℝ => ∫ t in 0..b, gammaIntegrand x t) atTop (𝓝 (gamma x)) ∧
  (∀ b : ℝ, 0 < b → Tendsto
    (fun a => Chapter06.RSIntegral (gammaIntegrand x) id a b)
    (𝓝[>] 0) (𝓝 (∫ t in 0..b, gammaIntegrand x t))) ∧
  (∀ u v : ℕ → ℝ, Tendsto u atTop (𝓝 0) → Tendsto v atTop atTop →
    (∀ n, 0 < u n ∧ u n ≤ v n) →
    Tendsto (fun n => Chapter06.RSIntegral (gammaIntegrand x) id (u n) (v n)) atTop
      (𝓝 (gamma x)))

theorem pma8_17 : pma8_17_contract :=
  fun _ hx => ⟨gammaIntegrand_integrable hx, rfl, gamma_upper_limit hx,
    fun _ hb => gamma_lower_native_limit hx hb,
    fun u v hu hv huv => gamma_native_improper_limit hx u v hu hv huv⟩

def pma8_18_contract : Prop :=
  (∀ x : ℝ, 0 < x → gamma (x + 1) = x * gamma x) ∧
  (∀ n : ℕ, gamma (n + 1) = n.factorial) ∧
  ConvexOn ℝ (Ioi 0) (Real.log ∘ gamma) ∧ gamma 1 = 1

theorem pma8_18 : pma8_18_contract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [gamma_eq_realGamma (by linarith), gamma_eq_realGamma hx]
    exact Real.Gamma_add_one hx.ne'
  · intro n
    rw [gamma_eq_realGamma (by positivity)]
    exact Real.Gamma_nat_eq_factorial n
  · exact Real.convexOn_log_Gamma.congr (fun x hx => by
      simp only [Function.comp_apply, gamma_eq_realGamma hx])
  · rw [gamma_eq_realGamma zero_lt_one, Real.Gamma_one]

/-- PMA 8.19, with the attached Euler limit formula for every positive argument. -/
def pma8_19_contract : Prop :=
  (∀ f : ℝ → ℝ, (∀ x, 0 < x → 0 < f x) →
    (∀ x, 0 < x → f (x + 1) = x * f x) → f 1 = 1 →
    ConvexOn ℝ (Ioi 0) (Real.log ∘ f) → EqOn f gamma (Ioi 0)) ∧
  (∀ x : ℝ, 0 < x → Tendsto
    (fun n : ℕ => (n.factorial : ℝ) * (n : ℝ) ^ x /
      ∏ j ∈ Finset.range (n + 1), (x + j)) atTop (𝓝 (gamma x)))

theorem pma8_19 : pma8_19_contract := by
  constructor
  · intro f hp hr h1 hc x hx
    rw [gamma_eq_realGamma hx]
    exact Real.eq_Gamma_of_log_convex hc (fun hy => hr _ hy) (fun hy => hp _ hy) h1 hx
  · intro x hx
    rw [gamma_eq_realGamma hx]
    convert Real.GammaSeq_tendsto_Gamma x using 1
    funext n
    simp only [Real.GammaSeq, mul_comm]

/-- The beta integrand can have an integrable singularity at either endpoint. -/
def betaIntegrand (x y t : ℝ) : ℝ := t ^ (x - 1) * (1 - t) ^ (y - 1)

theorem betaIntegrand_complex {x y t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (betaIntegrand x y t : ℂ) =
      (t : ℂ) ^ ((x : ℂ) - 1) * (1 - (t : ℂ)) ^ ((y : ℂ) - 1) := by
  rw [betaIntegrand, Complex.ofReal_mul]
  rw [Complex.ofReal_cpow ht.1, Complex.ofReal_cpow (sub_nonneg.mpr ht.2)]
  push_cast
  rfl

theorem betaIntegrand_integrable {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable (betaIntegrand x y) volume 0 1 := by
  have h := Complex.betaIntegral_convergent
    (show 0 < (x : ℂ).re by simpa using hx) (show 0 < (y : ℂ).re by simpa using hy)
  have h := Complex.reCLM.integrable_comp h.1
  rw [intervalIntegrable_iff] at ⊢
  rw [uIoc_of_le zero_le_one]
  exact IntegrableOn.congr_fun h (fun t ht => congrArg Complex.re (betaIntegrand_complex
    ⟨le_of_lt ht.1, ht.2⟩).symm) measurableSet_Ioc

theorem betaIntegral_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t in 0..1, betaIntegrand x y t) = gamma x * gamma y / gamma (x + y) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have h := Complex.betaIntegral_eq_Gamma_mul_div (x : ℂ) (y : ℂ)
    (by simpa using hx) (by simpa using hy)
  rw [Complex.betaIntegral] at h
  rw [intervalIntegral.integral_congr (fun t ht => betaIntegrand_complex
    (by simpa only [uIcc_of_le zero_le_one] using ht)), h]
  simp only [gamma_eq_realGamma hx, gamma_eq_realGamma hy,
    gamma_eq_realGamma (add_pos hx hy), Complex.ofReal_div, Complex.ofReal_mul,
    ← Complex.Gamma_ofReal, Complex.ofReal_add]

theorem betaIntegrand_continuousOn (x y : ℝ) :
    ContinuousOn (betaIntegrand x y) (Ioo 0 1) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  apply ContinuousAt.mul
  · exact Real.continuousAt_rpow_const _ _ (Or.inl ht.1.ne')
  · exact (Real.continuousAt_rpow_const _ _
      (Or.inl (sub_pos.mpr ht.2).ne')).comp (by fun_prop)

theorem beta_native_improper_limit {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (u v : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 0)) (hv : Tendsto v atTop (𝓝 1))
    (huv : ∀ n, 0 < u n ∧ u n ≤ v n ∧ v n < 1) :
    Tendsto (fun n => Chapter06.RSIntegral (betaIntegrand x y) id (u n) (v n)) atTop
      (𝓝 (gamma x * gamma y / gamma (x + y))) := by
  rw [← betaIntegral_eq hx hy]
  exact native_improper_interval_limit zero_lt_one (betaIntegrand_integrable hx hy)
    (betaIntegrand_continuousOn x y) u v hu hv huv

def pma8_20_contract : Prop := ∀ x y : ℝ, 0 < x → 0 < y →
  IntervalIntegrable (betaIntegrand x y) volume 0 1 ∧
  (∫ t in 0..1, betaIntegrand x y t) = gamma x * gamma y / gamma (x + y) ∧
  (∀ u v : ℕ → ℝ, Tendsto u atTop (𝓝 0) → Tendsto v atTop (𝓝 1) →
    (∀ n, 0 < u n ∧ u n ≤ v n ∧ v n < 1) →
    Tendsto (fun n => Chapter06.RSIntegral (betaIntegrand x y) id (u n) (v n)) atTop
      (𝓝 (gamma x * gamma y / gamma (x + y))))

theorem pma8_20 : pma8_20_contract :=
  fun _ _ hx hy => ⟨betaIntegrand_integrable hx hy, betaIntegral_eq hx hy,
    fun u v hu hv huv => beta_native_improper_limit hx hy u v hu hv huv⟩

end Rudin.PMA.Chapter08
