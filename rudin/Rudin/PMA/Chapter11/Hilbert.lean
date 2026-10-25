import Rudin.PMA.Chapter11.L2

/-!
# PMA 11.39 and 11.41–11.45: orthonormal systems and completeness

After 11.37 the functions are identified modulo equality almost everywhere.
The integral formula below relates the Hilbert-space inner product to the
book's coefficients; no abstract inner product is silently substituted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate InnerProductSpace

namespace Rudin.PMA.Chapter11.SecondHalf

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Every quotient class has a pointwise measurable square-integrable representative. -/
theorem squareIntegrable_L2 (f : L2Space μ) : SquareIntegrable μ (fun x => f x) :=
  squareIntegrable_iff.mpr ⟨(Lp.stronglyMeasurable f).measurable, Lp.memLp f⟩

/-- The quotient norm of a representative is its square-integral norm. -/
theorem l2Norm_coe (f : L2Space μ) : l2Norm μ (fun x => f x) = ‖f‖ := by
  rw [← norm_toL2 (Lp.memLp f)]
  congr 1
  exact Lp.ext (Lp.memLp f).coeFn_toLp

/-- 11.39: an orthonormal sequence of equivalence classes of complex functions. -/
def OrthonormalFunctions (φ : ℕ → L2Space μ) : Prop := Orthonormal ℂ φ

/-- 11.39: the coefficient of `f` along `φ`. -/
def fourierCoefficient (φ f : L2Space μ) : ℂ := inner ℂ φ f

/-- The coefficient is precisely the book's integral, with the conjugate on `φ`. -/
theorem fourierCoefficient_eq_integral (φ f : L2Space μ) :
    fourierCoefficient φ f = ∫ x, f x * conj (φ x) ∂μ := by
  simp [fourierCoefficient, MeasureTheory.L2.inner_def, RCLike.inner_apply]

/-- The same formula on given square-integrable functions, before quotienting. -/
theorem fourierCoefficient_toLp {φ f : X → ℂ}
    (hφ : SquareIntegrable μ φ) (hf : SquareIntegrable μ f) :
    fourierCoefficient (hφ.memLp.toLp φ) (hf.memLp.toLp f) =
      ∫ x, f x * conj (φ x) ∂μ := by
  rw [fourierCoefficient_eq_integral]
  apply integral_congr_ae
  filter_upwards [hφ.memLp.coeFn_toLp, hf.memLp.coeFn_toLp] with x hφx hfx
  rw [hφx, hfx]

/-- 11.39: orthonormality is equivalent to the displayed integral equations. -/
theorem pma11_39 (φ : ℕ → L2Space μ) :
    OrthonormalFunctions φ ↔
      ∀ i j, (∫ x, φ j x * conj (φ i x) ∂μ) = if i = j then 1 else 0 := by
  simp only [OrthonormalFunctions, orthonormal_iff_ite, ← fourierCoefficient_eq_integral,
    fourierCoefficient]

/-- 11.39's attached Bessel inequality, including convergence of the numerical series. -/
theorem pma11_39_bessel {φ : ℕ → L2Space μ} (hφ : OrthonormalFunctions φ)
    (f : L2Space μ) :
    Summable (fun n => ‖fourierCoefficient (φ n) f‖ ^ 2) ∧
      ∑' n, ‖fourierCoefficient (φ n) f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
  ⟨hφ.inner_products_summable f, hφ.tsum_inner_products_le f⟩

/-- 11.39's extension of 8.11: the Fourier sum is the unique best approximation
among combinations using the same finite orthonormal family. -/
theorem pma11_39_bestApproximation {φ : ℕ → L2Space μ}
    (hφ : OrthonormalFunctions φ) (f : L2Space μ) (s : Finset ℕ) (c : ℕ → ℂ) :
    let p := ∑ k ∈ s, fourierCoefficient (φ k) f • φ k
    let t := ∑ k ∈ s, c k • φ k
    ‖f - p‖ ≤ ‖f - t‖ ∧
      (‖f - p‖ = ‖f - t‖ ↔ ∀ k ∈ s, c k = fourierCoefficient (φ k) f) := by
  let p := ∑ k ∈ s, fourierCoefficient (φ k) f • φ k
  let t := ∑ k ∈ s, c k • φ k
  have hor : ∀ k ∈ s, inner ℂ (f - p) (φ k) = 0 := by
    intro k hk
    apply inner_eq_zero_symm.mpr
    rw [inner_sub_right, show inner ℂ (φ k) p = fourierCoefficient (φ k) f from
      hφ.inner_right_sum _ hk]
    simp [fourierCoefficient]
  have hsum : ∀ d : ℕ → ℂ, inner ℂ (f - p) (∑ k ∈ s, d k • φ k) = 0 := by
    intro d
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro k hk
    rw [inner_smul_right, hor k hk, mul_zero]
  have hot : inner ℂ (f - p) (p - t) = 0 := by
    rw [inner_sub_right, hsum _, hsum _, sub_self]
  have heq : ‖f - t‖ ^ 2 = ‖f - p‖ ^ 2 + ‖p - t‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (f - p) (p - t) hot
    simpa only [sub_add_sub_cancel, pow_two] using h
  change ‖f - p‖ ≤ ‖f - t‖ ∧ (‖f - p‖ = ‖f - t‖ ↔ _)
  refine ⟨by nlinarith [norm_nonneg (f - p), norm_nonneg (f - t), sq_nonneg ‖p - t‖], ?_⟩
  constructor
  · intro h k hk
    have hz : ‖p - t‖ ^ 2 = 0 := by
      rw [h] at heq
      linarith
    have he : p = t := sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
    have hc : inner ℂ (φ k) t = c k := hφ.inner_right_sum c hk
    rw [← he] at hc
    exact hc.symm.trans (hφ.inner_right_sum _ hk)
  · intro h
    have he : t = p := Finset.sum_congr rfl fun k hk => by rw [h k hk]
    rw [he]

/-- 11.41: convergence is convergence of the norm of the difference to zero. -/
def L2Converges (f : ℕ → L2Space μ) (g : L2Space μ) : Prop :=
  Tendsto (fun n => ‖f n - g‖) atTop (𝓝 0)

/-- 11.41: the Cauchy condition with one index for all pairs in the tail.
Using `≥ N` rather than `> N` gives the same condition by shifting `N`. -/
def L2Cauchy (f : ℕ → L2Space μ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ‖f m - f n‖ < ε

/-- 11.41 agrees with the metric-space convergence notion. -/
theorem pma11_41_converges (f : ℕ → L2Space μ) (g : L2Space μ) :
    L2Converges f g ↔ Tendsto f atTop (𝓝 g) :=
  tendsto_iff_norm_sub_tendsto_zero.symm

/-- 11.41 agrees with the metric-space Cauchy notion. -/
theorem pma11_41_cauchy (f : ℕ → L2Space μ) : L2Cauchy f ↔ CauchySeq f := by
  simp only [L2Cauchy, Metric.cauchySeq_iff, dist_eq_norm]

/-- 11.42: square-integrable functions modulo null equality form a complete space. -/
theorem pma11_42 {f : ℕ → L2Space μ} (hf : L2Cauchy f) :
    ∃ g : L2Space μ, L2Converges f g := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete ((pma11_41_cauchy f).mp hf)
  exact ⟨g, (pma11_41_converges f g).mpr hg⟩

/-- The quotient distance also computes differences between its chosen representatives. -/
theorem l2Norm_sub_coe (f g : L2Space μ) :
    l2Norm μ (fun x => f x - g x) = ‖f - g‖ := by
  change l2Norm μ ((f : X → ℂ) - (g : X → ℂ)) = ‖f - g‖
  rw [← norm_toL2 ((Lp.memLp f).sub (Lp.memLp g))]
  congr 1
  apply Lp.ext
  exact ((Lp.memLp f).sub (Lp.memLp g)).coeFn_toLp.trans (Lp.coeFn_sub f g).symm

/-- 11.42 explicitly produces a measurable function representative of the limit. -/
theorem pma11_42_representative {f : ℕ → L2Space μ} (hf : L2Cauchy f) :
    ∃ g : X → ℂ, SquareIntegrable μ g ∧
      Tendsto (fun n => l2Norm μ (fun x => f n x - g x)) atTop (𝓝 0) := by
  obtain ⟨g, hg⟩ := pma11_42 hf
  refine ⟨g, squareIntegrable_L2 g, ?_⟩
  simpa only [l2Norm_sub_coe, L2Converges] using hg

/-- 11.42 for a sequence of the book's unquotiented measurable functions. -/
theorem pma11_42_functions {f : ℕ → X → ℂ} (hf : ∀ n, SquareIntegrable μ (f n))
    (hc : ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      l2Norm μ (f m - f n) < ε) :
    ∃ g : X → ℂ, SquareIntegrable μ g ∧
      Tendsto (fun n => l2Norm μ (f n - g)) atTop (𝓝 0) := by
  let F : ℕ → L2Space μ := fun n => (hf n).memLp.toLp (f n)
  have hF : L2Cauchy F := by
    intro ε hε
    obtain ⟨N, hN⟩ := hc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have he : ‖F m - F n‖ = l2Norm μ (f m - f n) := by
      rw [← MemLp.toLp_sub, norm_toL2]
    rw [he]
    exact hN m hm n hn
  obtain ⟨g, hg⟩ := pma11_42 hF
  refine ⟨g, squareIntegrable_L2 g, ?_⟩
  have hn : ∀ n, l2Norm μ (f n - g) = ‖F n - g‖ := by
    intro n
    rw [← norm_toL2 ((hf n).memLp.sub (Lp.memLp g))]
    congr 1
    apply Lp.ext
    exact ((hf n).memLp.sub (Lp.memLp g)).coeFn_toLp.trans
      (((hf n).memLp.coeFn_toLp.symm.sub ae_eq_rfl).trans (Lp.coeFn_sub (F n) g).symm)
  simpa only [hn, L2Converges] using hg

/-- 11.43: Riesz–Fischer, with both convergence of partial sums and the prescribed coefficients. -/
theorem pma11_43 {φ : ℕ → L2Space μ} (hφ : OrthonormalFunctions φ)
    {c : ℕ → ℂ} (hc : Summable (fun n => ‖c n‖ ^ 2)) :
    ∃ f : L2Space μ,
      L2Converges (fun n => ∑ k ∈ Finset.range n, c k • φ k) f ∧
      ∀ k, fourierCoefficient (φ k) f = c k := by
  have hs : Summable (fun n => c n • φ n) := by
    simpa only [LinearIsometry.toSpanSingleton_apply] using
      hφ.orthogonalFamily.summable_iff_norm_sq_summable c |>.mpr hc
  refine ⟨∑' n, c n • φ n,
    (pma11_41_converges _ _).mpr hs.hasSum.tendsto_sum_nat, ?_⟩
  intro k
  change (innerSL ℂ (φ k)) (∑' n, c n • φ n) = c k
  rw [ContinuousLinearMap.map_tsum _ hs]
  simp only [innerSL_apply_apply, inner_smul_right, orthonormal_iff_ite.mp hφ]
  simp

/-- 11.43 for the book's unquotiented measurable functions, producing a measurable
limit, norm convergence of the actual partial sums, and the specified integral coefficients. -/
theorem pma11_43_functions {φ : ℕ → X → ℂ}
    (hφ : ∀ n, SquareIntegrable μ (φ n))
    (ho : ∀ i j, (∫ x, φ j x * conj (φ i x) ∂μ) = if i = j then 1 else 0)
    {c : ℕ → ℂ} (hc : Summable (fun n => ‖c n‖ ^ 2)) :
    ∃ f : X → ℂ, SquareIntegrable μ f ∧
      Tendsto (fun n => l2Norm μ (fun x => (∑ k ∈ Finset.range n, c k * φ k x) - f x))
        atTop (𝓝 0) ∧
      ∀ k, (∫ x, f x * conj (φ k x) ∂μ) = c k := by
  let Φ : ℕ → L2Space μ := fun n => (hφ n).memLp.toLp (φ n)
  have hΦ : OrthonormalFunctions Φ := by
    apply orthonormal_iff_ite.mpr
    intro i j
    change fourierCoefficient (Φ i) (Φ j) = _
    rw [fourierCoefficient_toLp (hφ i) (hφ j)]
    exact ho i j
  obtain ⟨f, hf, hfc⟩ := pma11_43 hΦ hc
  let s : ℕ → L2Space μ := fun n => ∑ k ∈ Finset.range n, c k • Φ k
  have hsum : ∀ n, (fun x => s n x) =ᵐ[μ] (fun x => ∑ k ∈ Finset.range n, c k * φ k x) := by
    intro n
    have h := (Lp.coeFn_finsetSum (Finset.range n) (fun k => c k • Φ k)).trans
      (eventuallyEq_sum (fun k _ => (Lp.coeFn_smul (c k) (Φ k)).trans
        ((hφ k).memLp.coeFn_toLp.fun_comp (fun z => c k * z))))
    filter_upwards [h] with x hx
    simpa only [Finset.sum_apply, Function.comp_apply] using hx
  refine ⟨f, squareIntegrable_L2 f, ?_, ?_⟩
  · have hn : ∀ n,
        l2Norm μ (fun x => (∑ k ∈ Finset.range n, c k * φ k x) - f x) = ‖s n - f‖ := by
      intro n
      exact (l2Norm_congr_ae ((hsum n).symm.sub ae_eq_rfl)).trans (l2Norm_sub_coe (s n) f)
    simpa only [hn, L2Converges] using hf
  · intro k
    have h := fourierCoefficient_toLp (hφ k) (squareIntegrable_L2 f)
    rw [Lp.toLp_coeFn] at h
    exact h.symm.trans (hfc k)

/-- 11.44: completeness means that zero coefficients force zero norm. -/
def CompleteOrthonormal (φ : ℕ → L2Space μ) : Prop :=
  OrthonormalFunctions φ ∧
    ∀ f : L2Space μ, (∀ n, fourierCoefficient (φ n) f = 0) → ‖f‖ = 0

/-- 11.44's condition makes the orthonormal sequence a Hilbert basis. -/
def completeOrthonormalBasis {φ : ℕ → L2Space μ} (hφ : CompleteOrthonormal φ) :
    HilbertBasis ℕ ℂ (L2Space μ) :=
  HilbertBasis.mkOfOrthogonalEqBot hφ.1 (by
    apply le_antisymm
    · intro f hf
      change f = 0
      apply norm_eq_zero.mp
      apply hφ.2 f
      intro n
      exact (Submodule.mem_orthogonal _ _).mp hf (φ n)
        (Submodule.subset_span ⟨n, rfl⟩)
    · exact bot_le)

/-- 11.45: Parseval's identity for every complete orthonormal sequence. -/
theorem pma11_45 {φ : ℕ → L2Space μ} (hφ : CompleteOrthonormal φ)
    (f : L2Space μ) :
    HasSum (fun n => ‖fourierCoefficient (φ n) f‖ ^ 2) (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  let b := completeOrthonormalBasis hφ
  have hb : ∀ n, b n = φ n := by
    intro n
    exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n
  have hs := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (b.repr f)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, HilbertBasis.repr_apply_apply, hb,
    LinearIsometryEquiv.norm_map] at hs
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [← l2Norm_coe, l2Norm, Real.sq_sqrt]
    exact integral_nonneg fun x => sq_nonneg _
  simpa only [fourierCoefficient, hn] using hs

/-- The representation statement attached to 11.45: a complete orthonormal
system yields the Fourier expansion of every square-integrable function. -/
theorem pma11_45_expansion {φ : ℕ → L2Space μ} (hφ : CompleteOrthonormal φ)
    (f : L2Space μ) : HasSum (fun n => fourierCoefficient (φ n) f • φ n) f := by
  let b := completeOrthonormalBasis hφ
  have hb : ∀ n, b n = φ n := fun n =>
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n
  simpa only [HilbertBasis.repr_apply_apply, hb, fourierCoefficient] using b.hasSum_repr f

/-- The one-to-one coordinate correspondence attached to 11.45, preserving
linear structure and the norm. -/
def l2Coordinates {φ : ℕ → L2Space μ} (hφ : CompleteOrthonormal φ) :
    L2Space μ ≃ₗᵢ[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  (completeOrthonormalBasis hφ).repr

theorem l2Coordinates_apply {φ : ℕ → L2Space μ} (hφ : CompleteOrthonormal φ)
    (f : L2Space μ) (n : ℕ) :
    l2Coordinates hφ f n = fourierCoefficient (φ n) f := by
  rw [l2Coordinates, HilbertBasis.repr_apply_apply]
  change inner ℂ ((completeOrthonormalBasis hφ) n) f = inner ℂ (φ n) f
  congr 1
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

end Rudin.PMA.Chapter11.SecondHalf
