import Rudin.PMA.Chapter09.HigherDerivatives
import Rudin.PMA.Chapter07.Calculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section
open Set Filter Topology MeasureTheory

namespace Rudin.PMA.Chapter09
open Chapter06 Chapter07

/-- The native Riemann–Stieltjes uniform limit theorem for a general nontrivial
filter. This is the filter version of the sequential theorem PMA 7.16. -/
theorem rsIntegrable_uniformLimit_filter {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ᶠ i in l, RSIntegrable (F i) α a b)
    (hlim : TendstoUniformlyOn F f l (Icc a b)) : RSIntegrable f α a b := by
  obtain ⟨i, hi, hnear⟩ := (hF.and
    (Metric.tendstoUniformlyOn_iff.mp hlim 1 (by norm_num))).exists
  have hab := hi.1
  have hα := hi.2.2.1
  obtain ⟨M, hM⟩ := hi.2.1
  have hb : BoundedOn f a b := by
    refine ⟨1 + M, fun x hx => ?_⟩
    have hnx : |f x - F i x| < 1 := by simpa only [Real.dist_eq] using hnear x hx
    calc
      |f x| = |(f x - F i x) + F i x| := by congr 1; ring
      _ ≤ |f x - F i x| + |F i x| := abs_add_le _ _
      _ ≤ 1 + M := add_le_add hnx.le (hM x hx)
  apply (rsIntegrable_iff_gap hab hb hα).mpr
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let δ := ε / (4 * (A + 1))
  have hden : 0 < 4 * (A + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (4 * (A + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  obtain ⟨i, hi, hn⟩ := (hF.and (Metric.tendstoUniformlyOn_iff.mp hlim δ hδ)).exists
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hab hi.2.1 hα).mp hi (ε / 2) (by positivity)
  refine ⟨P, ?_⟩
  have hgap := gap_le_of_cell_affine_gaps (f := F i) (h := f) (η := 2 * δ)
    (C := 1) hα P (fun i => by
      simpa only [one_mul] using
        cell_gap_le_of_uniform_dist hi.2.1 (fun x hx => (hn x hx).le) P i)
  dsimp only [A] at heq
  nlinarith

/-- Uniform convergence through native integrable functions commutes with the
native Riemann–Stieltjes integral, also for punctured-neighborhood limits. -/
theorem rsIntegral_uniformLimit_filter {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ᶠ i in l, RSIntegrable (F i) α a b)
    (hlim : TendstoUniformlyOn F f l (Icc a b)) :
    RSIntegrable f α a b ∧
      Tendsto (fun i => RSIntegral (F i) α a b) l (𝓝 (RSIntegral f α a b)) := by
  have hf := rsIntegrable_uniformLimit_filter hF hlim
  refine ⟨hf, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hf.2.2.1 ⟨le_rfl, hf.1⟩ ⟨hf.1, le_rfl⟩ hf.1)
  let δ := ε / (A + 1)
  have hden : 0 < A + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (A + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with i hi hn
  rw [Real.dist_eq]
  have hb := rsIntegral_sub_bound hi hf (fun x hx =>
    show |F i x - f x| ≤ δ by
      simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).le)
  dsimp only [A] at heq
  nlinarith

/-- PMA 9.42: differentiating a native Riemann–Stieltjes integral.

The derivative is needed only on some neighborhood of `s`. Its continuity in
the parameter is uniform in the integration variable, exactly as in the book.
The derivative function is supplied as data together with `HasDerivAt` evidence;
no continuity in the integration variable is assumed. -/
theorem pma9_42 (φ D : ℝ → ℝ → ℝ) (α : ℝ → ℝ) (a b c d s : ℝ)
    (_hab : a ≤ b) (_hα : MonotoneOn α (Icc a b)) (hcs : c < s) (hsd : s < d)
    (hI : ∀ t ∈ Icc c d, RSIntegrable (fun x => φ x t) α a b)
    (hD : ∃ r > 0, ∀ x ∈ Icc a b, ∀ t, |t-s| < r → HasDerivAt (φ x) (D x t) t)
    (hU : ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Icc a b, ∀ t, |t-s| < δ →
      |D x t - D x s| < ε) :
    RSIntegrable (fun x => D x s) α a b ∧
      HasDerivAt (fun t => RSIntegral (fun x => φ x t) α a b)
        (RSIntegral (fun x => D x s) α a b) s := by
  obtain ⟨r, hr, hD⟩ := hD
  let Q : ℝ → ℝ → ℝ := fun h x => (φ x (s+h) - φ x s) / h
  have hQlim : TendstoUniformlyOn Q (fun x => D x s) (𝓝[≠] 0) (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδD⟩ := hU ε hε
    have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| < min r δ := by
      exact (show ∀ᶠ h : ℝ in 𝓝 0, |h| < min r δ from by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (lt_min hr hδ)] with h hh
        simpa [Metric.mem_ball, Real.dist_eq] using hh).filter_mono nhdsWithin_le_nhds
    filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hh0
    have hne : h ≠ 0 := by simpa using hh0
    intro x hx
    have hst : s ≠ s+h := by intro he; apply hne; linarith
    obtain ⟨t, ht, he⟩ := exists_deriv_unordered (f := φ x) (f' := D x) hst
      (fun t ht => hD x hx t ((show |t-s| ≤ |h| by
        simpa only [add_sub_cancel_left] using abs_sub_left_of_mem_uIcc ht).trans_lt
          (hh.trans_le (min_le_left _ _))))
    have htd : |t-s| < δ := (show |t-s| ≤ |h| by
      simpa only [add_sub_cancel_left] using
        abs_sub_left_of_mem_uIcc (Ioo_subset_Icc_self ht)).trans_lt
      (hh.trans_le (min_le_right _ _))
    have heq : Q h x = D x t := by
      dsimp [Q]
      rw [he, show s+h-s=h by ring, mul_div_cancel_left₀ _ hne]
    simpa only [Real.dist_eq, heq, abs_sub_comm] using hδD x hx t htd
  have hsI : RSIntegrable (fun x => φ x s) α a b := hI s ⟨hcs.le, hsd.le⟩
  have hQ : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      RSIntegrable (Q h) α a b ∧
      RSIntegral (Q h) α a b =
        (RSIntegral (fun x => φ x (s+h)) α a b - RSIntegral (fun x => φ x s) α a b)/h := by
    have ht : ∀ᶠ h : ℝ in 𝓝[≠] 0, s+h ∈ Icc c d := by
      have hpos : 0 < min (s-c) (d-s) := lt_min (sub_pos.mpr hcs) (sub_pos.mpr hsd)
      have ht₀ : ∀ᶠ h : ℝ in 𝓝 0, s+h ∈ Icc c d := by
        filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
        have hh' : |h| < min (s-c) (d-s) := by simpa [Metric.mem_ball, Real.dist_eq] using hh
        have h₁ := (abs_lt.mp (hh'.trans_le (min_le_left _ _))).1
        have h₂ := (abs_lt.mp (hh'.trans_le (min_le_right _ _))).2
        exact ⟨by linarith, by linarith⟩
      exact ht₀.filter_mono nhdsWithin_le_nhds
    filter_upwards [ht] with h hh
    have hn := rsIntegrable_const_mul hsI (-1)
    have hsub := rsIntegrable_add (hI (s+h) hh) hn.1
    have hscale := rsIntegrable_const_mul hsub.1 h⁻¹
    rw [hsub.2, hn.2] at hscale
    refine ⟨?_, ?_⟩
    · simpa [Q, div_eq_mul_inv, mul_comm, sub_eq_add_neg] using hscale.1
    · simpa [Q, div_eq_mul_inv, mul_comm, sub_eq_add_neg] using hscale.2
  have hlimit := rsIntegral_uniformLimit_filter (hQ.mono fun _ h => h.1) hQlim
  refine ⟨hlimit.1, hasDerivAt_iff_tendsto_slope_zero.mpr ?_⟩
  have heq : (fun h => RSIntegral (Q h) α a b) =ᶠ[𝓝[≠] 0]
      (fun h => (RSIntegral (fun x => φ x (s+h)) α a b -
        RSIntegral (fun x => φ x s) α a b)/h) := hQ.mono fun _ h => h.2
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hlimit.2.congr' heq

/-- PMA 9.43: the Gaussian cosine transform. The absolutely convergent improper
integral is represented by the Bochner integral, with the improper-limit bridge
proved below. -/
def gaussianCosine (t : ℝ) : ℝ := ∫ x : ℝ, Real.exp (-x^2) * Real.cos (x*t)

/-- PMA 9.43: the integral obtained by differentiation in the parameter. -/
def gaussianSineDerivative (t : ℝ) : ℝ :=
  ∫ x : ℝ, -(x * Real.exp (-x^2) * Real.sin (x*t))

/-- Absolute convergence of the cosine integral in PMA 9.43. -/
theorem gaussianCosine_integrable (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (-x^2) * Real.cos (x*t)) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-x^2)) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  exact hg.mul_bdd (by fun_prop) (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x*t))

/-- Absolute convergence of the sine derivative integral in PMA 9.43. -/
theorem gaussianSineDerivative_integrable (t : ℝ) :
    Integrable (fun x : ℝ => -(x * Real.exp (-x^2) * Real.sin (x*t))) := by
  have hg : Integrable (fun x : ℝ => x * Real.exp (-x^2)) := by
    simpa using integrable_mul_exp_neg_mul_sq (b := 1) (by norm_num)
  exact (hg.mul_bdd (by fun_prop) (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (x*t))).neg

/-- Evaluation (111) of the Gaussian cosine transform. -/
theorem pma9_43_value (t : ℝ) :
    gaussianCosine t = Real.sqrt Real.pi * Real.exp (-t^2/4) := by
  have hi : Integrable (fun x : ℝ =>
      Complex.exp ((-1 : ℂ) * (x : ℂ)^2 + (Complex.I * t) * x + 0)) :=
    integrable_cexp_quadratic' (b := -1) (by norm_num) (Complex.I * t) 0
  have he := integral_cexp_quadratic (b := -1) (by norm_num : (-1 : ℂ).re < 0)
    (Complex.I * t) 0
  have hre := (integral_re hi).trans (congrArg Complex.re he)
  have hsqrt : (Real.pi : ℂ) ^ (1/2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
    norm_num
  have hexp : (0 : ℂ) - (Complex.I * t)^2 / (4 * (-1)) = ((-t^2/4 : ℝ) : ℂ) := by
    push_cast
    simp only [mul_pow, Complex.I_sq]
    ring
  simp only [neg_neg, div_one, hsqrt, hexp, ← Complex.ofReal_exp,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hre
  convert hre using 1
  unfold gaussianCosine
  congr 1
  ext x
  simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow, mul_comm]

/-- The elementary cosine difference-quotient bound (108), with the book's
explicit zero-increment convention. -/
theorem pma9_43_cosine_quotient_bound (a b : ℝ) :
    |if b = 0 then 0 else (Real.cos (a+b) - Real.cos a)/b + Real.sin a| ≤ |b| := by
  split_ifs with hb
  · simp [hb]
  have hab : a ≠ a+b := by intro he; apply hb; linarith
  obtain ⟨u, hu, he⟩ := exists_deriv_unordered (f := Real.cos)
    (f' := fun x => -Real.sin x) hab (fun x _ => Real.hasDerivAt_cos x)
  have hbound : |a-u| ≤ |b| := by
    simpa only [add_sub_cancel_left, abs_sub_comm a u] using
      abs_sub_left_of_mem_uIcc (Ioo_subset_Icc_self hu)
  have heq : (Real.cos (a+b) - Real.cos a)/b + Real.sin a = Real.sin a - Real.sin u := by
    rw [he, show a+b-a=b by ring, mul_div_cancel_left₀ _ hb]
    ring
  rw [heq]
  exact (Real.abs_sin_sub_sin_le a u).trans hbound

/-- Differentiating the Gaussian cosine integral gives the sine integral (106). -/
theorem pma9_43_derivative (t : ℝ) :
    HasDerivAt gaussianCosine (gaussianSineDerivative t) t := by
  have hbound : Integrable (fun x : ℝ => ‖x * Real.exp (-x^2)‖) := by
    apply Integrable.norm
    simpa using integrable_mul_exp_neg_mul_sq (b := 1) (by norm_num)
  have hd (x t : ℝ) : HasDerivAt (fun t => Real.exp (-x^2) * Real.cos (x*t))
      (-(x * Real.exp (-x^2) * Real.sin (x*t))) t := by
    convert (((hasDerivAt_id t).const_mul x).cos).const_mul (Real.exp (-x^2)) using 1 <;> simp only [id_eq] <;> ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun t x : ℝ => Real.exp (-x^2) * Real.cos (x*t))
    (F' := fun t x : ℝ => -(x * Real.exp (-x^2) * Real.sin (x*t)))
    (bound := fun x : ℝ => ‖x * Real.exp (-x^2)‖) (s := Set.univ)
    (x₀ := t) (μ := volume) (Filter.univ_mem)
    (Eventually.of_forall fun _ => by fun_prop) (gaussianCosine_integrable t)
    (by fun_prop) (ae_of_all _ fun x t _ => by
      rw [norm_neg, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (by
        simpa only [Real.norm_eq_abs] using Real.abs_sin_le_one (x*t))) hbound
    (ae_of_all _ fun x t _ => hd x t)
  exact h.2

/-- The differential equation (110), together with the explicit solution (111),
for the Gaussian transform in PMA 9.43. -/
theorem pma9_43 (t : ℝ) :
    HasDerivAt gaussianCosine (gaussianSineDerivative t) t ∧
      2 * gaussianSineDerivative t + t * gaussianCosine t = 0 ∧
      gaussianCosine t = Real.sqrt Real.pi * Real.exp (-t^2/4) := by
  have hd : HasDerivAt (fun t : ℝ => Real.sqrt Real.pi * Real.exp (-t^2/4))
      (Real.sqrt Real.pi * Real.exp (-t^2/4) * (-t/2)) t := by
    convert ((((hasDerivAt_id t).pow 2).neg.div_const 4).exp).const_mul
      (Real.sqrt Real.pi) using 1 <;> simp only [id_eq, Pi.neg_apply, Pi.pow_apply] <;> ring
  have heq : gaussianCosine = (fun t : ℝ => Real.sqrt Real.pi * Real.exp (-t^2/4)) :=
    funext pma9_43_value
  have hg : gaussianSineDerivative t =
      Real.sqrt Real.pi * Real.exp (-t^2/4) * (-t/2) := by
    exact (pma9_43_derivative t).unique (heq ▸ hd)
  refine ⟨pma9_43_derivative t, ?_, pma9_43_value t⟩
  rw [hg, pma9_43_value]
  ring

/-- The initial value used to solve the differential equation in PMA 9.43. -/
theorem pma9_43_initial_value : gaussianCosine 0 = Real.sqrt Real.pi := by
  simp [pma9_43_value]

/-- Formula (109). Domain clarification: its divided expression is asserted for
`t ≠ 0`; the value at zero is supplied by `pma9_43_initial_value`. -/
theorem pma9_43_integration_by_parts (t : ℝ) (ht : t ≠ 0) :
    gaussianCosine t = 2 * ∫ x : ℝ, x * Real.exp (-x^2) * (Real.sin (x*t)/t) := by
  have hode := (pma9_43 t).2.1
  have hg : gaussianSineDerivative t =
      -(∫ x : ℝ, x * Real.exp (-x^2) * Real.sin (x*t)) := integral_neg _
  have hi : (∫ x : ℝ, x * Real.exp (-x^2) * (Real.sin (x*t)/t)) =
      (∫ x : ℝ, x * Real.exp (-x^2) * Real.sin (x*t))/t := by
    simp only [← mul_div_assoc, integral_div]
  rw [hi]
  rw [hg] at hode
  rw [← mul_div_assoc]
  apply (eq_div_iff ht).mpr
  linarith

/-- Absolute convergence identifies the Gaussian integrals with improper limits
for arbitrary independently diverging endpoints. -/
theorem pma9_43_improper_limits {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (a b : ι → ℝ) (ha : Tendsto a l atBot) (hb : Tendsto b l atTop) (t : ℝ) :
    Tendsto (fun i => ∫ x : ℝ in a i..b i, Real.exp (-x^2) * Real.cos (x*t))
      l (𝓝 (gaussianCosine t)) ∧
    Tendsto (fun i => ∫ x : ℝ in a i..b i, -(x * Real.exp (-x^2) * Real.sin (x*t)))
      l (𝓝 (gaussianSineDerivative t)) := by
  exact ⟨intervalIntegral_tendsto_integral (gaussianCosine_integrable t) ha hb,
    intervalIntegral_tendsto_integral (gaussianSineDerivative_integrable t) ha hb⟩

/-- The full-line Gaussian integrals agree with their symmetric improper limits.
The preceding absolute-integrability theorems also give convergence for
independently diverging lower and upper endpoints. -/
theorem pma9_43_improper (t : ℝ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, Real.exp (-x^2) * Real.cos (x*t))
      atTop (𝓝 (gaussianCosine t)) ∧
    Tendsto (fun R : ℝ => ∫ x : ℝ in -R..R, -(x * Real.exp (-x^2) * Real.sin (x*t)))
      atTop (𝓝 (gaussianSineDerivative t)) := by
  exact ⟨intervalIntegral_tendsto_integral (gaussianCosine_integrable t)
    tendsto_neg_atTop_atBot tendsto_id,
    intervalIntegral_tendsto_integral (gaussianSineDerivative_integrable t)
      tendsto_neg_atTop_atBot tendsto_id⟩

end Rudin.PMA.Chapter09
