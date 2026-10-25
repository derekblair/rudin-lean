import Rudin.PMA.Chapter11.L2
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Order.Filter.AtTopBot.Interval

/-!
# PMA 11.40: trigonometric Fourier series in L²

We use symmetric partial sums indexed by integers from `-n` through `n`.
The interval and additive-circle presentations below are related explicitly;
the normalized Haar measure has total mass one, so the ordinary integral has
the factor `2 * π` in Parseval's identity. The endpoint chosen in the half-open
interval makes no difference to Lebesgue integrals or L² norms.
-/

noncomputable section
open Set Filter MeasureTheory AddCircle
open scoped Topology BigOperators ComplexConjugate

namespace Rudin.PMA.Chapter11.SecondHalf

private theorem fourier_interval_pos : -Real.pi < Real.pi := by
  linarith [Real.pi_pos]

/-- The coefficients used in 11.40, initially expressed via the interval API. -/
def trigCoefficient (f : ℝ → ℂ) (k : ℤ) : ℂ :=
  fourierCoeffOn fourier_interval_pos f k

/-- The source's symmetric trigonometric partial sums. -/
def trigPartialSum (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (- (n : ℤ)) n,
    trigCoefficient f k * Complex.exp (Complex.I * k * x)

/-- The coefficient definition has the source's exact normalization. -/
theorem trigCoefficient_eq_integral (f : ℝ → ℂ) (k : ℤ) :
    trigCoefficient f k = ((2 * Real.pi : ℝ)⁻¹ : ℂ) *
      ∫ x in (-Real.pi)..Real.pi,
        Complex.exp (-(Complex.I * k * x)) * f x := by
  rw [trigCoefficient, fourierCoeffOn_eq_integral]
  rw [show Real.pi - -Real.pi = 2 * Real.pi by ring]
  simp only [one_div, Complex.real_smul, fourier_coe_apply, Int.cast_neg, smul_eq_mul]
  congr 1
  · simp
  apply intervalIntegral.integral_congr
  intro x hx
  push_cast
  field_simp

/-- 11.40, Parseval: convergence and the value of the nonnegative coefficient
series. `MemLp` allows a.e. measurable representatives, slightly more generally
than the measurable representatives in the book. -/
theorem pma11_40_parseval {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    HasSum (fun k : ℤ => ‖trigCoefficient f k‖ ^ 2)
      ((2 * Real.pi)⁻¹ * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2) := by
  have hfi : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    hf.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  simpa [trigCoefficient, sub_neg_eq_add, two_mul] using
    hasSum_sq_fourierCoeffOn fourier_interval_pos hfi

/-- The same identity as an equality of a convergent series. -/
theorem pma11_40_parseval_sum {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    (∑' k : ℤ, ‖trigCoefficient f k‖ ^ 2) =
      (2 * Real.pi)⁻¹ * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2 :=
  (pma11_40_parseval hf).tsum_eq

private theorem norm_sq_eq_integral {Y : Type*} [MeasurableSpace Y] {ν : Measure Y}
    (g : Lp ℂ 2 ν) : ‖g‖ ^ 2 = ∫ y, ‖g y‖ ^ 2 ∂ν := by
  have h := norm_toL2 (Lp.memLp g)
  rw [Lp.toLp_coeFn] at h
  rw [h, l2Norm, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]

private theorem fourier_sum_ae {T : ℝ} [Fact (0 < T)]
    (s : Finset ℤ) (c : ℤ → ℂ) :
    (∑ k ∈ s, c k • fourierLp 2 k : Lp ℂ 2 haarAddCircle) =ᵐ[haarAddCircle]
      (fun t : AddCircle T => ∑ k ∈ s, c k * fourier k t) := by
  refine (Lp.coeFn_fun_finsetSum s (fun k => c k • fourierLp 2 k)).trans ?_
  have ht (k : ℤ) :
      (c k • fourierLp 2 k : Lp ℂ 2 (@haarAddCircle T _)) =ᵐ[haarAddCircle]
        (fun t : AddCircle T => c k * fourier k t) := by
    refine (Lp.coeFn_smul (c k) (fourierLp 2 k)).trans ?_
    filter_upwards [coeFn_fourierLp 2 k] with t ht
    change c k * (fourierLp 2 k : Lp ℂ 2 (@haarAddCircle T _)) t = _
    rw [ht]
  filter_upwards [eventuallyEq_sum (fun k (_ : k ∈ s) => ht k)] with t h
  simpa using h

/-- The circle version, with every symmetric partial sum and an explicit L²
limit. This is also used to transfer the convergence to arbitrary interval
representatives; periodicity of the original function is not required. -/
theorem pma11_40_circle {T : ℝ} [Fact (0 < T)]
    (f : Lp ℂ 2 (@haarAddCircle T _)) :
    Tendsto (fun n : ℕ =>
      ∑ k ∈ Finset.Icc (-(n : ℤ)) n, fourierCoeff f k • fourierLp 2 k)
      atTop (𝓝 f) :=
  (hasSum_fourier_series_L2 f).comp Finset.tendsto_Icc_neg

private theorem circle_integral_error {T : ℝ} [hT : Fact (0 < T)]
    {F : AddCircle T → ℂ} (hF : MemLp F 2 haarAddCircle)
    (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ t : AddCircle T, ‖F t - ∑ k ∈ s, c k * fourier k t‖ ^ 2) =
      T * ‖hF.toLp F - ∑ k ∈ s, c k • fourierLp 2 k‖ ^ 2 := by
  rw [volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hT.out.le, smul_eq_mul, norm_sq_eq_integral]
  congr 1
  apply integral_congr_ae
  filter_upwards [hF.coeFn_toLp,
    fourier_sum_ae s c,
    Lp.coeFn_sub (hF.toLp F) (∑ k ∈ s, c k • fourierLp 2 k)] with t h₁ h₂ h₃
  simp only [Pi.sub_apply] at h₃
  rw [h₃, h₁, h₂]

private theorem fourier_pi (k : ℤ) (x : ℝ) :
    fourier k (x : AddCircle (2 * Real.pi)) = Complex.exp (Complex.I * k * x) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp

/-- 11.40: the symmetric Fourier partial sums converge in the ordinary,
unnormalized interval L² norm. No endpoint matching or periodicity assumption
is imposed on the given interval function. -/
theorem pma11_40_convergence {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    Tendsto (fun n => l2Norm (volume.restrict (Icc (-Real.pi) Real.pi))
      (fun x => f x - trigPartialSum f n x)) atTop (𝓝 0) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  let F : AddCircle (2 * Real.pi) → ℂ := liftIoc (2 * Real.pi) (-Real.pi) f
  have hfi : MemLp f 2 (volume.restrict (Ioc (-Real.pi) (-Real.pi + 2 * Real.pi))) := by
    simpa only [show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      hf.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
  have hF : MemLp F 2 haarAddCircle := hfi.memLp_liftIoc.haarAddCircle
  let g := hF.toLp F
  have hc (k : ℤ) : fourierCoeff g k = trigCoefficient f k := by
    rw [show fourierCoeff g k = fourierCoeff F k from
      congrFun (fourierCoeff_congr_ae hF.coeFn_toLp) k]
    change fourierCoeff (liftIoc (2 * Real.pi) (-Real.pi) f) k = trigCoefficient f k
    simpa only [trigCoefficient, show -Real.pi + 2 * Real.pi = Real.pi by ring] using
      fourierCoeff_liftIoc_eq (T := 2 * Real.pi) (a := -Real.pi) f k
  have hi (n : ℕ) :
      ∫ x in Icc (-Real.pi) Real.pi, ‖f x - trigPartialSum f n x‖ ^ 2 =
      (2 * Real.pi) * ‖g - ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
        fourierCoeff g k • fourierLp 2 k‖ ^ 2 := by
    rw [← circle_integral_error hF]
    rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi),
      show -Real.pi + 2 * Real.pi = Real.pi by ring,
      intervalIntegral.integral_of_le fourier_interval_pos.le,
      integral_Icc_eq_integral_Ioc]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only [F]
    rw [liftIoc_coe_apply (by simpa [show -Real.pi + 2 * Real.pi = Real.pi by ring] using hx)]
    congr 3
    simp only [trigPartialSum, hc, fourier_pi]
  have h := ((tendsto_const_nhds (x := g)).sub (pma11_40_circle g)).norm.pow 2
  have ht := ((tendsto_const_nhds (x := 2 * Real.pi)).mul h).sqrt
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, Real.sqrt_zero] at ht
  simpa only [l2Norm, hi] using ht

/-- 11.40, with both conclusions in a single declaration. As in the separate
statements, a.e. measurable square-integrable representatives are allowed;
this includes every measurable interval function in the source. -/
theorem pma11_40 {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi))) :
    Tendsto (fun n => l2Norm (volume.restrict (Icc (-Real.pi) Real.pi))
      (fun x => f x - trigPartialSum f n x)) atTop (𝓝 0) ∧
    HasSum (fun k : ℤ => ‖trigCoefficient f k‖ ^ 2)
      ((2 * Real.pi)⁻¹ * ∫ x in (-Real.pi)..Real.pi, ‖f x‖ ^ 2) :=
  ⟨pma11_40_convergence hf, pma11_40_parseval hf⟩

/-- The uniqueness corollary: vanishing coefficients imply zero norm and
vanishing almost everywhere on the original interval. -/
theorem pma11_40_zero_coefficients {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hc : ∀ k, trigCoefficient f k = 0) :
    l2Norm (volume.restrict (Icc (-Real.pi) Real.pi)) f = 0 ∧
      f =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] 0 := by
  have hn : l2Norm (volume.restrict (Icc (-Real.pi) Real.pi)) f = 0 := by
    have h : Tendsto (fun _ : ℕ => l2Norm (volume.restrict (Icc (-Real.pi) Real.pi)) f)
        atTop (𝓝 0) := by
      simpa [trigPartialSum, hc] using pma11_40_convergence hf
    exact tendsto_nhds_unique tendsto_const_nhds h
  refine ⟨hn, ?_⟩
  have hz : hf.toLp f = 0 := norm_eq_zero.mp ((norm_toL2 hf).trans hn)
  exact hf.coeFn_toLp.symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 _)

/-- The printed integral formulation of the corollary. -/
theorem pma11_40_corollary {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hc : ∀ k : ℤ, (∫ x in (-Real.pi)..Real.pi,
      Complex.exp (-(Complex.I * k * x)) * f x) = 0) :
    l2Norm (volume.restrict (Icc (-Real.pi) Real.pi)) f = 0 ∧
      f =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] 0 :=
  pma11_40_zero_coefficients hf (by simp [trigCoefficient_eq_integral, hc])

private theorem coefficient_sub {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hg : MemLp g 2 (volume.restrict (Icc (-Real.pi) Real.pi))) (k : ℤ) :
    trigCoefficient (f - g) k = trigCoefficient f k - trigCoefficient g k := by
  have hfi : IntervalIntegrable f volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le fourier_interval_pos.le).mpr
      (hf.integrable (by norm_num))
  have hgi : IntervalIntegrable g volume (-Real.pi) Real.pi :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le fourier_interval_pos.le).mpr
      (hg.integrable (by norm_num))
  have he : Continuous (fun x : ℝ => Complex.exp (-(Complex.I * k * x))) := by
    fun_prop
  simp only [trigCoefficient_eq_integral, Pi.sub_apply, mul_sub]
  rw [intervalIntegral.integral_sub (hfi.continuousOn_mul he.continuousOn)
    (hgi.continuousOn_mul he.continuousOn), mul_sub]

/-- The final assertion of the corollary: equal Fourier coefficients determine
the function up to equality almost everywhere. -/
theorem pma11_40_uniqueness {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hg : MemLp g 2 (volume.restrict (Icc (-Real.pi) Real.pi)))
    (hc : ∀ k, trigCoefficient f k = trigCoefficient g k) :
    f =ᵐ[volume.restrict (Icc (-Real.pi) Real.pi)] g := by
  have hz := (pma11_40_zero_coefficients (hf.sub hg) (fun k => by
    rw [coefficient_sub hf hg, hc, sub_self])).2
  filter_upwards [hz] with x hx
  exact sub_eq_zero.mp hx

end Rudin.PMA.Chapter11.SecondHalf
