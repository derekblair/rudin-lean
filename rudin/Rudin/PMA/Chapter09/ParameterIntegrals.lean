import Rudin.PMA.Chapter09.HigherDerivatives
import Rudin.PMA.Chapter08.Exponential
import Rudin.PMA.Chapter07.Calculus

/-! # PMA 9.42–9.43: differentiation of native integrals.

The finite-interval theorem uses Chapter 6's Riemann–Stieltjes integral for
arbitrary increasing integrators, including discontinuous ones. Improper
whole-line convergence is expressed as a two-endpoint limit of native oriented
Riemann integrals, and includes absolute convergence.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology

namespace Rudin.PMA.Chapter09

open Chapter06

def HasImproperWholeLineIntegral (f : ℝ → ℝ) (I : ℝ) : Prop :=
  (∀ a b, a ≤ b → Chapter06.RIntegrable f a b) ∧
    Tendsto (fun p : ℝ × ℝ => Chapter08.orientedRIntegral f p.1 p.2)
      (atBot ×ˢ atTop) (𝓝 I)

def ImproperAbsolutelyIntegrable (f : ℝ → ℝ) : Prop :=
  ∃ I, HasImproperWholeLineIntegral (fun x => |f x|) I

def gaussianCosIntegrand (t x : ℝ) : ℝ := Real.exp (-(x ^ 2)) * Real.cos (x * t)

def gaussianSinIntegrand (t x : ℝ) : ℝ :=
  -(x * Real.exp (-(x ^ 2)) * Real.sin (x * t))

def gaussianCosTransform (t : ℝ) : ℝ := ∫ x : ℝ, gaussianCosIntegrand t x

def gaussianSinTransform (t : ℝ) : ℝ := ∫ x : ℝ, gaussianSinIntegrand t x

def pma9_42_contract : Prop :=
  (∀ (φ D : ℝ → ℝ → ℝ) (α : ℝ → ℝ) a b c d s,
    a ≤ b → s ∈ Ioo c d → MonotoneOn α (Icc a b) →
    (∀ t ∈ Icc c d, Chapter06.RSIntegrable (fun x => φ x t) α a b) →
    (∀ᶠ t in 𝓝 s, ∀ x ∈ Icc a b, HasDerivAt (φ x) (D x t) t) →
    TendstoUniformlyOn (fun t x => D x t) (fun x => D x s) (𝓝 s) (Icc a b) →
    Chapter06.RSIntegrable (fun x => D x s) α a b ∧
    HasDerivAt (fun t => Chapter06.RSIntegral (fun x => φ x t) α a b)
      (Chapter06.RSIntegral (fun x => D x s) α a b) s) ∧
  (∀ (φ D : ℝ → ℝ → ℝ) (α : ℝ → ℝ) a b c d s,
    a ≤ b → s ∈ Ioo c d → MonotoneOn α (Icc a b) →
    (∀ t ∈ Icc c d, Chapter06.RSIntegrable (fun x => φ x t) α a b) →
    (∀ x ∈ Icc a b, ∀ t ∈ Ioo c d, HasDerivAt (φ x) (D x t) t) →
    ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc a b ×ˢ Icc c d) →
    Chapter06.RSIntegrable (fun x => D x s) α a b ∧
    HasDerivAt (fun t => Chapter06.RSIntegral (fun x => φ x t) α a b)
      (Chapter06.RSIntegral (fun x => D x s) α a b) s)

def pma9_43_contract : Prop :=
  (∀ t, ImproperAbsolutelyIntegrable (gaussianCosIntegrand t) ∧
    ImproperAbsolutelyIntegrable (gaussianSinIntegrand t)) ∧
  (∀ t, HasImproperWholeLineIntegral (gaussianCosIntegrand t) (gaussianCosTransform t) ∧
    HasImproperWholeLineIntegral (gaussianSinIntegrand t) (gaussianSinTransform t)) ∧
  (∀ t, HasDerivAt gaussianCosTransform (gaussianSinTransform t) t) ∧
  (∀ t, 2 * gaussianSinTransform t + t * gaussianCosTransform t = 0) ∧
  (∀ t, gaussianCosTransform t = Real.sqrt Real.pi * Real.exp (-(t ^ 2) / 4))

/-- Chapter 7's native uniform-limit theorem with an arbitrary nontrivial
index filter; eventual integrability suffices. -/
theorem rsIntegrable_of_uniformFilterLimit {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ᶠ i in L, RSIntegrable (F i) α a b)
    (hlim : TendstoUniformlyOn F f L (Icc a b)) : RSIntegrable f α a b := by
  obtain ⟨i, hi⟩ := hF.exists
  have hab := hi.1
  have hα := hi.2.2.1
  obtain ⟨N, hFN, hN⟩ := (hF.and (Metric.tendstoUniformlyOn_iff.mp hlim 1 (by norm_num))).exists
  obtain ⟨M, hM⟩ := hFN.2.1
  have hb : BoundedOn f a b := by
    refine ⟨1 + M, fun x hx => ?_⟩
    have hnx : |f x - F N x| < 1 := by simpa only [Real.dist_eq] using hN x hx
    calc
      |f x| = |(f x - F N x) + F N x| := by congr 1; ring
      _ ≤ |f x - F N x| + |F N x| := abs_add_le _ _
      _ ≤ 1 + M := add_le_add hnx.le (hM x hx)
  apply (rsIntegrable_iff_gap hab hb hα).mpr
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let δ := ε / (4 * (A + 1))
  have hden : 0 < 4 * (A + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (4 * (A + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  obtain ⟨n, hFn, hn⟩ := (hF.and (Metric.tendstoUniformlyOn_iff.mp hlim δ hδ)).exists
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hab hFn.2.1 hα).mp hFn
    (ε / 2) (by positivity)
  refine ⟨P, ?_⟩
  have hgap := gap_le_of_cell_affine_gaps (f := F n) (h := f) (η := 2 * δ)
    (C := 1) hα P (fun i => by
      simpa only [one_mul] using Chapter07.cell_gap_le_of_uniform_dist hFn.2.1
        (fun x hx => (hn x hx).le) P i)
  dsimp only [A] at heq
  nlinarith

theorem rsIntegral_tendsto_of_uniformFilterLimit {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ᶠ i in L, RSIntegrable (F i) α a b)
    (hlim : TendstoUniformlyOn F f L (Icc a b)) :
    RSIntegrable f α a b ∧
      Tendsto (fun i => RSIntegral (F i) α a b) L (𝓝 (RSIntegral f α a b)) := by
  have hf := rsIntegrable_of_uniformFilterLimit hF hlim
  refine ⟨hf, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hf.2.2.1 ⟨le_rfl, hf.1⟩ ⟨hf.1, le_rfl⟩ hf.1)
  let δ := ε / (A + 1)
  have hden : 0 < A + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (A + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with i hi hlimi
  rw [Real.dist_eq]
  have hb := Chapter07.rsIntegral_sub_bound hi hf (fun x hx =>
    show |F i x - f x| ≤ δ by
      simpa only [Real.dist_eq, abs_sub_comm] using (hlimi x hx).le)
  dsimp only [A] at heq
  nlinarith

theorem parameterQuotients_tendstoUniformly {φ D : ℝ → ℝ → ℝ}
    {a b s : ℝ}
    (hder : ∀ᶠ t in 𝓝 s, ∀ x ∈ Icc a b, HasDerivAt (φ x) (D x t) t)
    (hD : TendstoUniformlyOn (fun t x => D x t) (fun x => D x s) (𝓝 s) (Icc a b)) :
    TendstoUniformlyOn (fun t x => (φ x t - φ x s) / (t - s))
      (fun x => D x s) (𝓝[≠] s) (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := Metric.tendstoUniformlyOn_iff.mp hD ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hder.and he)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds s hδ), self_mem_nhdsWithin]
    with t ht hts
  intro x hx
  have hsub : uIcc s t ⊆ Metric.ball s δ := by
    intro u hu
    have hle : dist u s ≤ dist t s := by
      simpa only [dist_comm u s, dist_comm t s] using Real.dist_left_le_of_mem_uIcc hu
    exact lt_of_le_of_lt hle ht
  have hder' : ∀ u ∈ uIcc s t, HasDerivAt (φ x) (D x u) u :=
    fun u hu => (hball (hsub hu)).1 x hx
  obtain ⟨u, hu, heq⟩ := exists_increment_eq_deriv_mul (Ne.symm hts) hder'
  have heq' : (φ x t - φ x s) / (t - s) = D x u := by
    rw [heq, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hts)]
  rw [heq']
  exact (hball (hsub (uIoo_subset_uIcc_self hu))).2 x hx

theorem parameterIntegral_hasDerivAt {φ D : ℝ → ℝ → ℝ} {α : ℝ → ℝ}
    {a b c d s : ℝ} (hs : s ∈ Ioo c d)
    (hint : ∀ t ∈ Icc c d, RSIntegrable (fun x => φ x t) α a b)
    (hder : ∀ᶠ t in 𝓝 s, ∀ x ∈ Icc a b, HasDerivAt (φ x) (D x t) t)
    (hD : TendstoUniformlyOn (fun t x => D x t) (fun x => D x s) (𝓝 s) (Icc a b)) :
    RSIntegrable (fun x => D x s) α a b ∧
    HasDerivAt (fun t => RSIntegral (fun x => φ x t) α a b)
      (RSIntegral (fun x => D x s) α a b) s := by
  have hsint := hint s (Ioo_subset_Icc_self hs)
  have htmem : ∀ᶠ t in 𝓝[≠] s, t ∈ Icc c d :=
    nhdsWithin_le_nhds (Icc_mem_nhds hs.1 hs.2)
  have hquot : ∀ᶠ t in 𝓝[≠] s,
      RSIntegrable (fun x => (φ x t - φ x s) / (t - s)) α a b ∧
      RSIntegral (fun x => (φ x t - φ x s) / (t - s)) α a b =
        (RSIntegral (fun x => φ x t) α a b - RSIntegral (fun x => φ x s) α a b) / (t - s) := by
    filter_upwards [htmem] with t ht
    have hn := rsIntegrable_const_mul hsint (-1)
    have ha := rsIntegrable_add (hint t ht) hn.1
    have hm := rsIntegrable_const_mul ha.1 ((t - s)⁻¹)
    rw [ha.2, hn.2] at hm
    simpa only [div_eq_inv_mul, neg_one_mul, ← sub_eq_add_neg] using hm
  have hlim := rsIntegral_tendsto_of_uniformFilterLimit
    (hquot.mono fun _ h => h.1) (parameterQuotients_tendstoUniformly hder hD)
  refine ⟨hlim.1, hasDerivAt_iff_tendsto_slope.mpr ?_⟩
  have hslope : slope (fun t => RSIntegral (fun x => φ x t) α a b) s =
      (fun t => (RSIntegral (fun x => φ x t) α a b -
        RSIntegral (fun x => φ x s) α a b) / (t - s)) := by
    funext t
    exact slope_def_field _ s t
  rw [hslope]
  exact hlim.2.congr' (hquot.mono fun _ h => h.2)

theorem parameterDerivatives_uniform_of_continuous {D : ℝ → ℝ → ℝ} {a b c d s : ℝ}
    (hs : s ∈ Ioo c d)
    (hD : ContinuousOn (fun p : ℝ × ℝ => D p.1 p.2) (Icc a b ×ˢ Icc c d)) :
    TendstoUniformlyOn (fun t x => D x t) (fun x => D x s) (𝓝 s) (Icc a b) := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => D p.2 p.1) (Icc c d ×ˢ Icc a b) :=
    hD.comp continuous_swap.continuousOn (fun _ h => ⟨h.2, h.1⟩)
  have hu := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc
  simpa only [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hs.1 hs.2)] using
    hu.tendstoUniformlyOn (Ioo_subset_Icc_self hs)

theorem pma9_42 : pma9_42_contract := by
  constructor
  · intro φ D α a b c d s _ hs _ hint hder hD
    exact parameterIntegral_hasDerivAt hs hint hder hD
  · intro φ D α a b c d s _ hs _ hint hder hD
    apply parameterIntegral_hasDerivAt hs hint
    · filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
      exact fun x hx => hder x hx t ht
    · exact parameterDerivatives_uniform_of_continuous hs hD

/-- The native and measure-theoretic ordinary integrals agree for continuous
functions, by applying the two fundamental theorems to the same primitive. -/
theorem orientedRIntegral_eq_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    Chapter08.orientedRIntegral f a b = ∫ x in a..b, f x := by
  have hi : ∀ u v, u ≤ v → RIntegrable f u v :=
    fun u v huv => pma6_8 f id u v huv hf.continuousOn (monotone_id.monotoneOn _)
  have he : ∀ u v, u < v → RIntegral f u v = ∫ x in u..v, f x := by
    intro u v huv
    have hd : ∀ x : ℝ, HasDerivAt (fun y => ∫ t in u..y, f t) (f x) x := by
      intro x
      exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable u x)
        (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt
    have hFTC : RIntegral f u v = (∫ t in u..v, f t) - (∫ t in u..u, f t) :=
      pma6_21 (fun y => ∫ t in u..y, f t) f u v huv
        (fun x _ => (hd x).hasDerivWithinAt) (hi u v huv.le)
    simpa only [intervalIntegral.integral_same, sub_zero] using hFTC
  rcases lt_trichotomy a b with hab | hab | hab
  · simp only [Chapter08.orientedRIntegral, ite_eq_left hab.le, he a b hab]
  · subst b
    simp only [Chapter08.orientedRIntegral, le_refl, ite_true, intervalIntegral.integral_same]
    exact (calculus_singleton_integrals f id a).2
  · rw [Chapter08.orientedRIntegral, ite_eq_right (not_le.mpr hab), he b a hab,
      intervalIntegral.integral_symm]
    simp

theorem hasImproperWholeLineIntegral_of_continuous_integrable {f : ℝ → ℝ}
    (hc : Continuous f) (hi : Integrable f) : HasImproperWholeLineIntegral f (∫ x, f x) := by
  refine ⟨fun a b hab => pma6_8 f id a b hab hc.continuousOn (monotone_id.monotoneOn _), ?_⟩
  have ht := intervalIntegral_tendsto_integral hi
    (tendsto_fst : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atBot ×ˢ atTop) atBot)
    (tendsto_snd : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (atBot ×ˢ atTop) atTop)
  simpa only [orientedRIntegral_eq_intervalIntegral hc] using ht

theorem gaussianCosIntegrand_continuous (t : ℝ) : Continuous (gaussianCosIntegrand t) := by
  unfold gaussianCosIntegrand
  fun_prop

theorem gaussianSinIntegrand_continuous (t : ℝ) : Continuous (gaussianSinIntegrand t) := by
  unfold gaussianSinIntegrand
  fun_prop

theorem gaussianCosIntegrand_integrable (t : ℝ) : Integrable (gaussianCosIntegrand t) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  exact hg.mul_bdd (by fun_prop) (Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (x * t))

theorem gaussianSinIntegrand_bound (t x : ℝ) :
    ‖gaussianSinIntegrand t x‖ ≤ |x * Real.exp (-(x ^ 2))| := by
  rw [gaussianSinIntegrand, norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (x * t)) (abs_nonneg _)).trans_eq (mul_one _)

theorem gaussianSinBound_integrable : Integrable (fun x : ℝ => |x * Real.exp (-(x ^ 2))|) := by
  simpa only [neg_one_mul, Real.norm_eq_abs] using
    (integrable_mul_exp_neg_mul_sq (b := 1) (by norm_num)).norm

theorem gaussianSinIntegrand_integrable (t : ℝ) : Integrable (gaussianSinIntegrand t) :=
  gaussianSinBound_integrable.mono' (gaussianSinIntegrand_continuous t).aestronglyMeasurable
    (Eventually.of_forall (gaussianSinIntegrand_bound t))

theorem gaussianCosIntegrand_hasDerivAt (x t : ℝ) :
    HasDerivAt (fun s => gaussianCosIntegrand s x) (gaussianSinIntegrand t x) t := by
  convert ((Real.hasDerivAt_cos (x * t)).comp t
    ((hasDerivAt_id t).const_mul x)).const_mul (Real.exp (-(x ^ 2))) using 1
  · ext s
    simp only [gaussianCosIntegrand, Function.comp_apply]
  · simp only [gaussianSinIntegrand, mul_one]
    ring

theorem gaussianCosTransform_hasDerivAt (t : ℝ) :
    HasDerivAt gaussianCosTransform (gaussianSinTransform t) t := by
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := gaussianCosIntegrand) (F' := gaussianSinIntegrand) (s := univ)
    (bound := fun x => |x * Real.exp (-(x ^ 2))|) univ_mem
    (Eventually.of_forall fun s => (gaussianCosIntegrand_continuous s).aestronglyMeasurable)
    (gaussianCosIntegrand_integrable t)
    (gaussianSinIntegrand_continuous t).aestronglyMeasurable
    (Eventually.of_forall fun x s _ => gaussianSinIntegrand_bound s x)
    gaussianSinBound_integrable
    (Eventually.of_forall fun x s _ => gaussianCosIntegrand_hasDerivAt x s)).2

def gaussianComplexIntegrand (t x : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) * Complex.exp (-((x : ℂ) ^ 2))

theorem gaussianComplexIntegrand_re (t x : ℝ) :
    (gaussianComplexIntegrand t x).re = gaussianCosIntegrand t x := by
  have hp : Complex.I * (t : ℂ) * (x : ℂ) = ((x * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have he : -((x : ℂ) ^ 2) = ((-(x ^ 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussianComplexIntegrand, hp, he, ← Complex.ofReal_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re, gaussianCosIntegrand]
  ring

theorem gaussianComplexIntegrand_norm (t x : ℝ) :
    ‖gaussianComplexIntegrand t x‖ = Real.exp (-(x ^ 2)) := by
  have hp : Complex.I * (t : ℂ) * (x : ℂ) = ((x * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have he : -((x : ℂ) ^ 2) = ((-(x ^ 2) : ℝ) : ℂ) := by push_cast; rfl
  rw [gaussianComplexIntegrand, norm_mul, hp, Complex.norm_exp_ofReal_mul_I,
    one_mul, he, ← Complex.ofReal_exp]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem gaussianComplexIntegrand_integrable (t : ℝ) : Integrable (gaussianComplexIntegrand t) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-(x ^ 2))) := by
    simpa using integrable_exp_neg_mul_sq (b := 1) (by norm_num)
  apply hg.mono'
  · unfold gaussianComplexIntegrand
    fun_prop
  · exact Eventually.of_forall fun x => (gaussianComplexIntegrand_norm t x).le

theorem gaussianCosTransform_formula (t : ℝ) :
    gaussianCosTransform t = Real.sqrt Real.pi * Real.exp (-(t ^ 2) / 4) := by
  have hf := fourierIntegral_gaussian (b := (1 : ℂ)) (by norm_num) (t : ℂ)
  have hp : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa using (Complex.ofReal_cpow Real.pi_pos.le (1 / 2 : ℝ)).symm
  have he : Complex.exp (-((t : ℂ) ^ 2) / 4) = (Real.exp (-(t ^ 2) / 4) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rfl
  have hfc : (∫ x : ℝ, gaussianComplexIntegrand t x) =
      (Real.sqrt Real.pi * Real.exp (-(t ^ 2) / 4) : ℝ) := by
    simpa only [gaussianComplexIntegrand, neg_one_mul, div_one, mul_one,
      hp, he, Complex.ofReal_mul] using hf
  have hre := congrArg Complex.re hfc
  have hi := integral_re (gaussianComplexIntegrand_integrable t)
  change (∫ x : ℝ, (gaussianComplexIntegrand t x).re) =
    (∫ x : ℝ, gaussianComplexIntegrand t x).re at hi
  rw [← hi] at hre
  simpa only [gaussianComplexIntegrand_re, Complex.ofReal_re, gaussianCosTransform] using hre

theorem gaussianCosTransform_differential_equation (t : ℝ) :
    2 * gaussianSinTransform t + t * gaussianCosTransform t = 0 := by
  have hf : HasDerivAt gaussianCosTransform
      (-(t / 2) * gaussianCosTransform t) t := by
    have hd := (((hasDerivAt_pow 2 t).neg.div_const 4).exp).const_mul (Real.sqrt Real.pi)
    have he : gaussianCosTransform = fun s => Real.sqrt Real.pi * Real.exp (-(s ^ 2) / 4) :=
      funext gaussianCosTransform_formula
    rw [he]
    convert hd using 1
    simp only [Nat.reduceSub, pow_one, Pi.neg_apply]
    ring
  have he := (gaussianCosTransform_hasDerivAt t).unique hf
  rw [he]
  ring

theorem pma9_43 : pma9_43_contract := by
  refine ⟨?_, ?_, gaussianCosTransform_hasDerivAt,
    gaussianCosTransform_differential_equation, gaussianCosTransform_formula⟩
  · intro t
    constructor
    · exact ⟨_, hasImproperWholeLineIntegral_of_continuous_integrable
        (gaussianCosIntegrand_continuous t).abs (by
          simpa only [Real.norm_eq_abs] using (gaussianCosIntegrand_integrable t).norm)⟩
    · exact ⟨_, hasImproperWholeLineIntegral_of_continuous_integrable
        (gaussianSinIntegrand_continuous t).abs (by
          simpa only [Real.norm_eq_abs] using (gaussianSinIntegrand_integrable t).norm)⟩
  · intro t
    exact ⟨hasImproperWholeLineIntegral_of_continuous_integrable
      (gaussianCosIntegrand_continuous t) (gaussianCosIntegrand_integrable t),
      hasImproperWholeLineIntegral_of_continuous_integrable
      (gaussianSinIntegrand_continuous t) (gaussianSinIntegrand_integrable t)⟩

end Rudin.PMA.Chapter09
