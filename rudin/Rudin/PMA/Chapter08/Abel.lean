import Rudin.PMA.Chapter03

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter08

/-!
## PMA 8.2: Abel's endpoint theorem

The coefficient and endpoint series use Chapter 3's ordered partial-sum limit.
In particular, no absolute convergence is required at the endpoint. The `tsum`
below is used only together with explicit interior summability. At the endpoint
the extension takes the ordered sum, which need not equal the unordered `tsum`.

The proof uses Mathlib's Abel limit theorem. The attached Cauchy-product
application is exactly the previously verified PMA 3.51, whose proof already
declares the same forward Mathlib dependency.
-/

/-- A scalar power series with complex coefficients and real argument. -/
def abelPowerSeries (a : ℕ → ℂ) (x : ℝ) : ℂ :=
  ∑' n, a n * (x : ℂ) ^ n

/-- At a convergent endpoint use the ordered sum, including conditional sums. -/
def abelEndpointExtension (a : ℕ → ℂ) (R : ℝ) (A : ℂ) (x : ℝ) : ℂ :=
  if x = R then A else abelPowerSeries a x

theorem abel_interior_hasSum (a : ℕ → ℂ) (R : ℝ) (A : ℂ)
    (hR : 0 < R) (ha : Chapter03.SeriesHasSum (fun n => a n * (R : ℂ) ^ n) A)
    {x : ℝ} (hx : |x| < R) :
    HasSum (fun n => a n * (x : ℂ) ^ n) (abelPowerSeries a x) := by
  apply Summable.hasSum
  apply summable_powerSeries_of_norm_lt ha.cauchySeq
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using hx

theorem abel_limit_one (a : ℕ → ℂ) (A : ℂ)
    (ha : Chapter03.SeriesHasSum a A) :
    Tendsto (abelPowerSeries a) (𝓝[<] (1 : ℝ)) (𝓝 A) := by
  have h := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt ha
  rw [tendsto_map'_iff] at h
  exact h

theorem abel_limit_scaled (a : ℕ → ℂ) (R : ℝ) (A : ℂ)
    (hR : 0 < R) (ha : Chapter03.SeriesHasSum (fun n => a n * (R : ℂ) ^ n) A) :
    Tendsto (abelPowerSeries a) (𝓝[<] R) (𝓝 A) := by
  have hdiv : Tendsto (fun x : ℝ => x / R) (𝓝[<] R) (𝓝[<] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun x : ℝ => x / R) := continuous_id.div_const R
      have hlimit : Tendsto (fun x : ℝ => x / R) (𝓝 R) (𝓝 (1 : ℝ)) := by
        simpa only [div_self hR.ne'] using hcont.tendsto R
      exact hlimit.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (div_lt_one hR).mpr hx
  have h := (abel_limit_one (fun n => a n * (R : ℂ) ^ n) A ha).comp hdiv
  convert h using 1
  ext x
  apply tsum_congr
  intro n
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [Complex.ofReal_div]
  rw [mul_assoc, ← mul_pow, mul_div_cancel₀ _ hRc]

theorem abel_endpoint_continuous (a : ℕ → ℂ) (R : ℝ) (A : ℂ)
    (hR : 0 < R) (ha : Chapter03.SeriesHasSum (fun n => a n * (R : ℂ) ^ n) A) :
    ContinuousWithinAt (abelEndpointExtension a R A) (Iic R) R := by
  apply continuousWithinAt_Iio_iff_Iic.mp
  change Tendsto (abelEndpointExtension a R A) (𝓝[<] R)
    (𝓝 (abelEndpointExtension a R A R))
  have he : abelEndpointExtension a R A R = A := by simp [abelEndpointExtension]
  rw [he]
  apply (abel_limit_scaled a R A hR ha).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [abelEndpointExtension, ne_of_lt (mem_Iio.mp hx)]

theorem abel_negative_interior_hasSum (a : ℕ → ℂ) (R : ℝ) (A : ℂ)
    (hR : 0 < R)
    (ha : Chapter03.SeriesHasSum (fun n => a n * ((-R : ℝ) : ℂ) ^ n) A)
    {x : ℝ} (hx : |x| < R) :
    HasSum (fun n => a n * (x : ℂ) ^ n) (abelPowerSeries a x) := by
  apply Summable.hasSum
  apply summable_powerSeries_of_norm_lt ha.cauchySeq
  simpa only [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hR] using hx

/-- Reflection turns convergence at a negative endpoint into positive-endpoint
convergence of the alternating coefficient series. -/
theorem abel_reflection (a : ℕ → ℂ) (x : ℝ) :
    abelPowerSeries (fun n => a n * (-1 : ℂ) ^ n) (-x) = abelPowerSeries a x := by
  apply tsum_congr
  intro n
  rw [Complex.ofReal_neg, mul_assoc, ← mul_pow]
  simp

theorem abel_limit_negative (a : ℕ → ℂ) (R : ℝ) (A : ℂ)
    (hR : 0 < R)
    (ha : Chapter03.SeriesHasSum (fun n => a n * ((-R : ℝ) : ℂ) ^ n) A) :
    Tendsto (abelPowerSeries a) (𝓝[>] (-R)) (𝓝 A) := by
  have hb : Chapter03.SeriesHasSum
      (fun n => (a n * (-1 : ℂ) ^ n) * (R : ℂ) ^ n) A := by
    convert ha using 1
    ext n
    rw [mul_assoc, ← mul_pow]
    simp
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[>] (-R)) (𝓝[<] R) :=
    tendsto_neg_nhdsGT_neg
  simpa only [Function.comp_def, abel_reflection] using
    (abel_limit_scaled (fun n => a n * (-1 : ℂ) ^ n) R A hR hb).comp hneg

theorem abel_negative_endpoint_continuous (a : ℕ → ℂ) (R : ℝ) (A : ℂ)
    (hR : 0 < R)
    (ha : Chapter03.SeriesHasSum (fun n => a n * ((-R : ℝ) : ℂ) ^ n) A) :
    ContinuousWithinAt (abelEndpointExtension a (-R) A) (Ici (-R)) (-R) := by
  apply continuousWithinAt_Ioi_iff_Ici.mp
  change Tendsto (abelEndpointExtension a (-R) A) (𝓝[>] (-R))
    (𝓝 (abelEndpointExtension a (-R) A (-R)))
  have he : abelEndpointExtension a (-R) A (-R) = A := by simp [abelEndpointExtension]
  rw [he]
  apply (abel_limit_negative a R A hR ha).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp [abelEndpointExtension, ne_of_gt (mem_Ioi.mp hx)]

/-- Abel's unit-endpoint theorem, scaling to positive endpoints, the attached
conditional Cauchy-product consequence, and reflected negative endpoints. -/
def pma8_2_contract : Prop :=
  (∀ (a : ℕ → ℂ) (A : ℂ), Chapter03.SeriesHasSum a A →
    (∀ x : ℝ, |x| < 1 →
      HasSum (fun n => a n * (x : ℂ) ^ n) (abelPowerSeries a x)) ∧
    Tendsto (abelPowerSeries a) (𝓝[<] (1 : ℝ)) (𝓝 A) ∧
    ContinuousWithinAt (abelEndpointExtension a 1 A) (Iic 1) 1) ∧
  (∀ (a : ℕ → ℂ) (R : ℝ) (A : ℂ), 0 < R →
    Chapter03.SeriesHasSum (fun n => a n * (R : ℂ) ^ n) A →
    (∀ x : ℝ, |x| < R →
      HasSum (fun n => a n * (x : ℂ) ^ n) (abelPowerSeries a x)) ∧
    Tendsto (abelPowerSeries a) (𝓝[<] R) (𝓝 A) ∧
    ContinuousWithinAt (abelEndpointExtension a R A) (Iic R) R) ∧
  Chapter03.pma3_51_contract ∧
  (∀ (a : ℕ → ℂ) (R : ℝ) (A : ℂ), 0 < R →
    Chapter03.SeriesHasSum (fun n => a n * ((-R : ℝ) : ℂ) ^ n) A →
    (∀ x : ℝ, |x| < R →
      HasSum (fun n => a n * (x : ℂ) ^ n) (abelPowerSeries a x)) ∧
    Tendsto (abelPowerSeries a) (𝓝[>] (-R)) (𝓝 A) ∧
    ContinuousWithinAt (abelEndpointExtension a (-R) A) (Ici (-R)) (-R))

theorem pma8_2 : pma8_2_contract := by
  refine ⟨?_, ?_, Chapter03.pma3_51, ?_⟩
  · intro a A ha
    have ha' : Chapter03.SeriesHasSum (fun n => a n * ((1 : ℝ) : ℂ) ^ n) A := by
      simpa using ha
    exact ⟨fun x hx => abel_interior_hasSum a 1 A zero_lt_one ha' hx,
      abel_limit_one a A ha, abel_endpoint_continuous a 1 A zero_lt_one ha'⟩
  · intro a R A hR ha
    exact ⟨fun x hx => abel_interior_hasSum a R A hR ha hx,
      abel_limit_scaled a R A hR ha, abel_endpoint_continuous a R A hR ha⟩
  · intro a R A hR ha
    exact ⟨fun x hx => abel_negative_interior_hasSum a R A hR ha hx,
      abel_limit_negative a R A hR ha, abel_negative_endpoint_continuous a R A hR ha⟩

end Rudin.PMA.Chapter08
