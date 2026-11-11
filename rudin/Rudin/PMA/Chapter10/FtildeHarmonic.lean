import Rudin.PMA.Chapter10.FtildeDisproofStatement
import Rudin.PMA.AxiomAudit

/-!
# Stage 3 harmonic and gauge analysis for `ftildeField` (rudin-lean #29 / PR #30)

This module evaluates the Stage 3 target clause of `ftilde_witness`:
`¬ SymmetricCurlSystem ftildeBall ftildeField`.

## Summary of findings

1. **Pointwise Fourier orthogonality (L6) holds at each fixed frequency `ξ`:**
   `l6_pointwise_fourier_orthogonality` proves that any symmetrized transverse
   symbol `Sym(ξ ⊗ ξ ⊗ v)` with `ξ · v = 0` is Frobenius-orthogonal to any
   symmetrized trace-free Hessian symbol `c ξ^{⊗ 3} + d Sym(δ ⊗ ξ)`.

2. **Exact blocking lemma in the G1–G6 / L1–L10 hand-analysis chain:**
   Step G6 inferred from L6's pointwise-in-`ξ` Fourier orthogonality that no
   `C²` scalar gauge `φ` on `ftildeBall` can cancel the physical-space blow-up
   `ftildeC i j k * log |log ‖x‖|` of `Sym(∂ S⁽⁰⁾)`. Because the orthogonal
   subspaces rotate with `ξ / ‖ξ‖` and `log |log ‖x‖| ∈ L²(ftildeBall)`,
   Plancherel orthogonality does not prevent pointwise cancellation. Indeed,
   `ftildeC` is the exact third-derivative tensor `∇³ ftildeCubicGaugePoly` of a
   harmonic cubic polynomial (`Δ ftildeCubicGaugePoly = 0`), so the `C²` gauge
   `ftildeLocalGauge(x) = -ftildeCubicGaugePoly(x) * log |log ‖x‖|` produces
   `∂_k (Hess₀ ftildeLocalGauge)_{i,j}(x) = -ftildeC i j k * log |log ‖x‖| + o(1)`
   as `x → 0`.

3. **Clause 3 of `ftilde_witness` is false on `ftildeBall`:**
   By spherical-harmonic Hodge inversion on `S²`, `ftildePotentialG` provides an
   explicit global `C²` vector potential on `ftildeBall` satisfying
   `EqOn (curl ftildePotentialG) ftildeField ftildeBall`. Consequently,
   `ContDiffOn ℝ 1 ftildeField ftildeBall` (clause 1) and
   `EqOn (divergence ftildeField) 0 ftildeBall` (clause 2) both hold, while
   `SymmetricCurlSystem ftildeBall ftildeField` ALSO holds (`symmetricCurlSystem_ftilde`),
   refuting clause 3 (`not_ftilde_clause3`).
-/

noncomputable section
set_option autoImplicit false

open Set Filter Function Metric
open scoped Topology BigOperators ContDiff

namespace Rudin.PMA.Chapter10
open Chapter09

/-! ## Section 1: Polynomial evaluator and radial-homogeneous `C¹`/`C²` engine -/

/-- A single three-variable monomial `c * x₀^a * x₁^b * x₂^d`. -/
def ftildeMonomial (c : ℝ) (a b d : ℕ) (x : Euclidean 3) : ℝ :=
  c * x 0 ^ a * x 1 ^ b * x 2 ^ d

/-- Evaluation of a formal sum of three-variable monomials. -/
def evalPoly3 (L : List (ℝ × ℕ × ℕ × ℕ)) (x : Euclidean 3) : ℝ :=
  (L.map fun t => ftildeMonomial t.1 t.2.1 t.2.2.1 t.2.2.2 x).sum

/-- Formal coordinate partial derivative of a three-variable polynomial list. -/
def derivPoly3 (j : Fin 3) (L : List (ℝ × ℕ × ℕ × ℕ)) : List (ℝ × ℕ × ℕ × ℕ) :=
  L.map fun (c, a, b, d) =>
    match j with
    | ⟨0, _⟩ => (c * (a : ℝ), a - 1, b, d)
    | ⟨1, _⟩ => (c * (b : ℝ), a, b - 1, d)
    | ⟨2, _⟩ => (c * (d : ℝ), a, b, d - 1)

lemma contDiff_ftildeMonomial (c : ℝ) (a b d : ℕ) :
    ContDiff ℝ ∞ (ftildeMonomial c a b d) := by
  have hc (i : Fin 3) : ContDiff ℝ ∞ (fun x : Euclidean 3 => x i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  unfold ftildeMonomial
  exact ((contDiff_const.mul ((hc 0).pow a)).mul ((hc 1).pow b)).mul ((hc 2).pow d)

lemma contDiff_evalPoly3 (L : List (ℝ × ℕ × ℕ × ℕ)) :
    ContDiff ℝ ∞ (evalPoly3 L) := by
  induction L with
  | nil =>
    change ContDiff ℝ ∞ (fun _ : Euclidean 3 => (0 : ℝ))
    exact contDiff_const
  | cons hd tl ih =>
    have hfun : evalPoly3 (hd :: tl) =
        fun x => ftildeMonomial hd.1 hd.2.1 hd.2.2.1 hd.2.2.2 x + evalPoly3 tl x := by
      funext x
      simp [evalPoly3]
    rw [hfun]
    exact (contDiff_ftildeMonomial hd.1 hd.2.1 hd.2.2.1 hd.2.2.2).add ih

lemma evalPoly3_homog {L : List (ℝ × ℕ × ℕ × ℕ)} {deg : ℕ}
    (hL : List.Forall (fun t => t.2.1 + t.2.2.1 + t.2.2.2 = deg) L)
    (s : ℝ) (x : Euclidean 3) :
    evalPoly3 L (s • x) = s ^ deg * evalPoly3 L x := by
  induction L with
  | nil => simp [evalPoly3]
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b, d⟩
    rw [List.forall_cons] at hL
    rcases hL with ⟨hdeg, htl⟩
    dsimp only at hdeg
    have hstep1 : evalPoly3 ((c, a, b, d) :: tl) (s • x) =
        ftildeMonomial c a b d (s • x) + evalPoly3 tl (s • x) := by
      simp [evalPoly3]
    have hstep2 : evalPoly3 ((c, a, b, d) :: tl) x =
        ftildeMonomial c a b d x + evalPoly3 tl x := by
      simp [evalPoly3]
    rw [hstep1, hstep2, ih htl, ← hdeg, pow_add, pow_add]
    simp only [ftildeMonomial, PiLp.smul_apply, smul_eq_mul]
    ring

lemma hasDerivAt_add_pow_zero (u : ℝ) (n : ℕ) :
    HasDerivAt (fun t : ℝ => (u + t) ^ n) ((n : ℝ) * u ^ (n - 1)) 0 := by
  cases n with
  | zero =>
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ))
  | succ k =>
    have h : HasDerivAt (fun t : ℝ => (u + t) ^ (k + 1))
        (((k + 1 : ℕ) : ℝ) * (u + 0) ^ k * 1) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add u).pow (k + 1)
    simpa using h

lemma coordinateVector_apply_three (j k : Fin 3) :
    coordinateVector 3 j k = if k = j then 1 else 0 := by
  simp [coordinateVector, EuclideanSpace.basisFun_apply]

lemma coordinatePartial_ftildeMonomial (c : ℝ) (a b d : ℕ) (x : Euclidean 3) (j : Fin 3) :
    coordinatePartial (ftildeMonomial c a b d) x j =
      match j with
      | ⟨0, _⟩ => ftildeMonomial (c * (a : ℝ)) (a - 1) b d x
      | ⟨1, _⟩ => ftildeMonomial (c * (b : ℝ)) a (b - 1) d x
      | ⟨2, _⟩ => ftildeMonomial (c * (d : ℝ)) a b (d - 1) x := by
  fin_cases j <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · have hline : (fun t : ℝ => ftildeMonomial c a b d (x + t • coordinateVector 3 0)) =
        fun t : ℝ => (c * x 1 ^ b * x 2 ^ d) * (x 0 + t) ^ a := by
      funext t
      simp only [ftildeMonomial, PiLp.add_apply, PiLp.smul_apply,
        coordinateVector_apply_three, smul_eq_mul]
      norm_num
      ring
    have hd := (hasDerivAt_add_pow_zero (x 0) a).const_mul (c * x 1 ^ b * x 2 ^ d)
    rw [coordinatePartial, hline, hd.deriv]
    simp only [ftildeMonomial]
    ring
  · have hline : (fun t : ℝ => ftildeMonomial c a b d (x + t • coordinateVector 3 1)) =
        fun t : ℝ => (c * x 0 ^ a * x 2 ^ d) * (x 1 + t) ^ b := by
      funext t
      simp only [ftildeMonomial, PiLp.add_apply, PiLp.smul_apply,
        coordinateVector_apply_three, smul_eq_mul]
      norm_num
      ring
    have hd := (hasDerivAt_add_pow_zero (x 1) b).const_mul (c * x 0 ^ a * x 2 ^ d)
    rw [coordinatePartial, hline, hd.deriv]
    simp only [ftildeMonomial]
    ring
  · have hline : (fun t : ℝ => ftildeMonomial c a b d (x + t • coordinateVector 3 2)) =
        fun t : ℝ => (c * x 0 ^ a * x 1 ^ b) * (x 2 + t) ^ d := by
      funext t
      simp only [ftildeMonomial, PiLp.add_apply, PiLp.smul_apply,
        coordinateVector_apply_three, smul_eq_mul]
      norm_num
    have hd := (hasDerivAt_add_pow_zero (x 2) d).const_mul (c * x 0 ^ a * x 1 ^ b)
    rw [coordinatePartial, hline, hd.deriv]
    simp only [ftildeMonomial]
    ring

lemma coordinatePartial_evalPoly3 (L : List (ℝ × ℕ × ℕ × ℕ)) (x : Euclidean 3) (j : Fin 3) :
    coordinatePartial (evalPoly3 L) x j = evalPoly3 (derivPoly3 j L) x := by
  induction L with
  | nil =>
    change coordinatePartial (fun _ => (0 : ℝ)) x j = 0
    exact coordinatePartial_const 0 x j
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b, d⟩
    have hfun : evalPoly3 ((c, a, b, d) :: tl) =
        fun y => ftildeMonomial c a b d y + evalPoly3 tl y := by
      funext y
      simp [evalPoly3]
    have hd1 : DifferentiableAt ℝ (ftildeMonomial c a b d) x :=
      ((contDiff_ftildeMonomial c a b d).differentiable (by simp)).differentiableAt
    have hd2 : DifferentiableAt ℝ (evalPoly3 tl) x :=
      ((contDiff_evalPoly3 tl).differentiable (by simp)).differentiableAt
    rw [hfun, coordinatePartial_add hd1 hd2 j, coordinatePartial_ftildeMonomial, ih]
    fin_cases j <;> simp [evalPoly3, derivPoly3]

lemma contDiff_coordinatePartial_smooth {P : Euclidean 3 → ℝ}
    (hP : ContDiff ℝ ∞ P) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => coordinatePartial P x j) := by
  have hPdiff : ∀ x, DifferentiableAt ℝ P x :=
    fun x => (hP.differentiable (by simp)).differentiableAt
  have hU : ContDiffOn ℝ ∞ P univ := contDiffOn_univ.mpr hP
  have hf : ContDiffOn ℝ ∞
      (fun x => fderiv ℝ P x (coordinateVector 3 j)) univ :=
    (hU.fderiv_of_isOpen isOpen_univ (by simp)).clm_apply contDiffOn_const
  exact contDiffOn_univ.mp
    (hf.congr fun x _ => coordinatePartial_eq_fderiv (hPdiff x) j)

lemma coordinatePartial_homog_smooth {k : ℕ} {P : Euclidean 3 → ℝ}
    (hP : ContDiff ℝ ∞ P)
    (hhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ (k + 1) * P x)
    (t : ℝ) (x : Euclidean 3) (j : Fin 3) :
    coordinatePartial P (t • x) j = t ^ k * coordinatePartial P x j := by
  have hPdiff : ∀ y, DifferentiableAt ℝ P y :=
    fun y => (hP.differentiable (by simp)).differentiableAt
  have hmul : ∀ s : ℝ, coordinatePartial P (s • x) j * s =
      s ^ (k + 1) * coordinatePartial P x j := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => P (s • (x + u • coordinateVector 3 j)))
        (s ^ (k + 1) * coordinatePartial P x j) 0 := by
      have heq : (fun u : ℝ => P (s • (x + u • coordinateVector 3 j))) =
          fun u : ℝ => s ^ (k + 1) * P (x + u • coordinateVector 3 j) := by
        funext u
        exact hhom s _
      rw [heq]
      have hl : HasDerivAt (fun u : ℝ => P (x + u • coordinateVector 3 j))
          (fderiv ℝ P x (coordinateVector 3 j)) 0 :=
        hasCoordinatePartial_of_hasFDerivAt (hPdiff x).hasFDerivAt j
      rw [← coordinatePartial_eq_fderiv (hPdiff x) j] at hl
      exact hl.const_mul (s ^ (k + 1))
    have h2 : HasDerivAt (fun u : ℝ => P (s • (x + u • coordinateVector 3 j)))
        (coordinatePartial P (s • x) j * s) 0 := by
      have heq : (fun u : ℝ => P (s • (x + u • coordinateVector 3 j))) =
          (fun v : ℝ => P (s • x + v • coordinateVector 3 j)) ∘ (fun u : ℝ => s * u) := by
        funext u
        simp [smul_add, smul_smul]
      rw [heq]
      have hl : HasDerivAt (fun v : ℝ => P (s • x + v • coordinateVector 3 j))
          (fderiv ℝ P (s • x) (coordinateVector 3 j)) 0 :=
        hasCoordinatePartial_of_hasFDerivAt (hPdiff (s • x)).hasFDerivAt j
      rw [← coordinatePartial_eq_fderiv (hPdiff (s • x)) j] at hl
      have hl' : HasDerivAt (fun v : ℝ => P (s • x + v • coordinateVector 3 j))
          (coordinatePartial P (s • x) j) (s * 0) := by
        simpa only [mul_zero] using hl
      have hmul_s : HasDerivAt (fun u : ℝ => s * u) s 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).const_mul s
      exact hl'.comp 0 hmul_s
    exact h2.unique h1
  have hne : ∀ s : ℝ, s ≠ 0 → coordinatePartial P (s • x) j = s ^ k * coordinatePartial P x j := by
    intro s hs
    apply mul_right_cancel₀ hs
    calc
      coordinatePartial P (s • x) j * s = s ^ (k + 1) * coordinatePartial P x j := hmul s
      _ = (s ^ k * coordinatePartial P x j) * s := by ring
  by_cases ht : t = 0
  · subst ht
    have hc1 : Continuous (fun s : ℝ => coordinatePartial P (s • x) j) :=
      (contDiff_coordinatePartial_smooth hP j).continuous.comp (continuous_id.smul continuous_const)
    have hc2 : Continuous (fun s : ℝ => s ^ k * coordinatePartial P x j) :=
      (continuous_id.pow k).mul continuous_const
    have ht1 : Tendsto (fun s : ℝ => coordinatePartial P (s • x) j) (𝓝[≠] 0)
        (𝓝 (coordinatePartial P ((0 : ℝ) • x) j)) :=
      hc1.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun s : ℝ => s ^ k * coordinatePartial P x j) (𝓝[≠] 0)
        (𝓝 ((0 : ℝ) ^ k * coordinatePartial P x j)) :=
      hc2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hev : (fun s : ℝ => coordinatePartial P (s • x) j) =ᶠ[𝓝[≠] (0 : ℝ)]
        (fun s : ℝ => s ^ k * coordinatePartial P x j) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hne s hs
    exact tendsto_nhds_unique (ht1.congr' hev) ht2
  · exact hne t ht

lemma norm_le_of_homogeneous {d : ℕ} {P : Euclidean 3 → ℝ}
    (hP : Continuous P)
    (hhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ d * P x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euclidean 3, x ≠ 0 → |P x| ≤ C * ‖x‖ ^ d := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Euclidean 3) 1).exists_bound_of_continuousOn
    hP.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := norm_smul_inv_norm hx
  have hmem : (‖x‖⁻¹ : ℝ) • x ∈ Metric.sphere (0 : Euclidean 3) 1 := by
    simp [hnorm]
  have hx_eq : x = ‖x‖ • ((‖x‖⁻¹ : ℝ) • x) := by
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
  have hb : |P ((‖x‖⁻¹ : ℝ) • x)| ≤ max M 0 := by
    have h1 := hM ((‖x‖⁻¹ : ℝ) • x) hmem
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (le_max_left _ _)
  calc
    |P x| = |P (‖x‖ • ((‖x‖⁻¹ : ℝ) • x))| := congrArg (fun z => |P z|) hx_eq
    _ = |‖x‖ ^ d * P ((‖x‖⁻¹ : ℝ) • x)| := by rw [hhom]
    _ = ‖x‖ ^ d * |P ((‖x‖⁻¹ : ℝ) • x)| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) d)]
    _ ≤ ‖x‖ ^ d * max M 0 := mul_le_mul_of_nonneg_left hb (pow_nonneg (norm_nonneg x) d)
    _ = max M 0 * ‖x‖ ^ d := mul_comm _ _

/-- A radial multiplier `h ‖x‖` times `P x / ‖x‖ ^ (2 * m)`, extended by `0` at the origin. -/
def radialHomogTerm (m : ℕ) (h : ℝ → ℝ) (P : Euclidean 3 → ℝ) (x : Euclidean 3) : ℝ :=
  if x = 0 then 0 else h ‖x‖ * (P x / ‖x‖ ^ (2 * m))

lemma norm_sq_eq_sum_three (x : Euclidean 3) :
    ‖x‖ ^ 2 = ∑ i : Fin 3, x i ^ 2 := by
  simpa [Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq x

lemma tendsto_norm_nhdsGT_of_nhdsNE_zero :
    Tendsto (fun x : Euclidean 3 => ‖x‖) (𝓝[≠] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_norm.tendsto 0).mono_left nhdsWithin_le_nhds |>.trans (by simp)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact norm_pos_iff.mpr hx

lemma hasFDerivAt_radialHomogTerm_ne_zero
    {m : ℕ} {h h₁ : ℝ → ℝ}
    (hdh : ∀ r ∈ Ioo 0 1, HasDerivAt h (h₁ r / r) r)
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    {x : Euclidean 3} (hx : x ∈ ftildeBall) (hx0 : x ≠ 0) :
    DifferentiableAt ℝ (radialHomogTerm m h P) x ∧
      ∀ j : Fin 3, coordinatePartial (radialHomogTerm m h P) x j =
        h₁ ‖x‖ * ((x j * P x) / ‖x‖ ^ (2 * (m + 1))) +
        h ‖x‖ * (((∑ i : Fin 3, x i ^ 2) * coordinatePartial P x j -
          (2 * m : ℝ) * (x j * P x)) / ‖x‖ ^ (2 * (m + 1))) := by
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hr1 : ‖x‖ < 1 := by simpa [ftildeBall, mem_ball_zero_iff] using hx
  have hN : HasFDerivAt (fun y : Euclidean 3 => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x :=
    hasFDerivAt_norm_euclidean hx0
  have hh : HasFDerivAt (fun y : Euclidean 3 => h ‖y‖)
      ((h₁ ‖x‖ / ‖x‖) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
    (hdh ‖x‖ ⟨hr0, hr1⟩).comp_hasFDerivAt x hN
  have hPdiff : DifferentiableAt ℝ P x :=
    (hPsmooth.differentiable (by simp)).differentiableAt
  have hP : HasFDerivAt P (fderiv ℝ P x) x := hPdiff.hasFDerivAt
  have hpow := hN.pow (2 * m)
  have hinv := ((hasDerivAt_id (‖x‖ ^ (2 * m))).inv
    (pow_ne_zero (2 * m) hr0.ne')).comp_hasFDerivAt x hpow
  have hquot : HasFDerivAt (fun y : Euclidean 3 => P y * (‖y‖ ^ (2 * m))⁻¹) _ x :=
    hP.mul hinv
  have hprod := hh.mul hquot
  have heq : radialHomogTerm m h P =ᶠ[𝓝 x]
      fun y : Euclidean 3 => h ‖y‖ * (P y * (‖y‖ ^ (2 * m))⁻¹) := by
    filter_upwards [eventually_ne_nhds hx0] with y hy
    simp [radialHomogTerm, hy, div_eq_mul_inv]
  have hfd := hprod.congr_of_eventuallyEq heq
  refine ⟨hfd.differentiableAt, fun j => ?_⟩
  rw [coordinatePartial_eq_fderiv hfd.differentiableAt j, hfd.fderiv]
  have hin : (innerSL ℝ x) (coordinateVector 3 j) = x j := by
    simp [innerSL_apply_apply, coordinateVector, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_right]
  have hPf : fderiv ℝ P x (coordinateVector 3 j) = coordinatePartial P x j :=
    (coordinatePartial_eq_fderiv hPdiff j).symm
  have hsq : ∑ i : Fin 3, x i ^ 2 = ‖x‖ ^ 2 := (norm_sq_eq_sum_three x).symm
  simp only [add_apply, smul_apply, smul_eq_mul, id_eq, hin, hPf, hsq, nsmul_eq_mul]
  cases m with
  | zero =>
    simp only [Nat.mul_zero, pow_zero, Nat.cast_zero, zero_mul, inv_one, one_mul,
      Nat.zero_add, Nat.mul_one]
    field_simp [hr0.ne']
    ring
  | succ m' =>
    have hsub : 2 * (m' + 1) - 1 = 2 * m' + 1 := by omega
    have hadd : 2 * (m' + 1 + 1) = 2 * m' + 4 := by omega
    have hmul2 : 2 * (m' + 1) = 2 * m' + 2 := by omega
    rw [hsub, hadd, hmul2]
    push_cast
    field_simp [hr0.ne']
    ring

lemma hasFDerivAt_radialHomogTerm_zero
    {m d : ℕ} (hmd : 2 * m + 1 ≤ d)
    {h : ℝ → ℝ}
    (hh0 : Tendsto (fun r => h r * r ^ (d - (2 * m + 1))) (𝓝[>] 0) (𝓝 0))
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ d * P x) :
    HasFDerivAt (radialHomogTerm m h P) (0 : Euclidean 3 →L[ℝ] ℝ) 0 := by
  obtain ⟨C, hC0, hC⟩ := norm_le_of_homogeneous hPsmooth.continuous hPhom
  rw [hasFDerivAt_iff_tendsto]
  let g : Euclidean 3 → ℝ := fun x =>
    ‖x - 0‖⁻¹ * ‖radialHomogTerm m h P x - radialHomogTerm m h P 0 -
      (0 : Euclidean 3 →L[ℝ] ℝ) (x - 0)‖
  change Tendsto g (𝓝 0) (𝓝 0)
  have hlim : Tendsto (fun x : Euclidean 3 => C * (|h ‖x‖| * ‖x‖ ^ (d - (2 * m + 1))))
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => C * |h r * r ^ (d - (2 * m + 1))|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hh0.abs.const_mul C)
    refine (h1.comp tendsto_norm_nhdsGT_of_nhdsNE_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x _
    simp only [Function.comp_def, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) _)]
  have hpunc : Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := by
    have hg0 : g 0 = 0 := by simp [g]
    rw [hg0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards with x
      dsimp only [g]
      positivity
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := hx
      have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hPx := hC x hx0
      have hpow : ‖x‖ ^ d = ‖x‖ * ‖x‖ ^ (2 * m) * ‖x‖ ^ (d - (2 * m + 1)) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      dsimp only [g]
      simp only [sub_zero, zero_apply, radialHomogTerm, hx0, ↓reduceIte,
        Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (pow_nonneg (norm_nonneg x) _)]
      calc
        ‖x‖⁻¹ * (|h ‖x‖| * (|P x| / ‖x‖ ^ (2 * m)))
            ≤ ‖x‖⁻¹ * (|h ‖x‖| * ((C * ‖x‖ ^ d) / ‖x‖ ^ (2 * m))) := by
              gcongr
        _ = C * (|h ‖x‖| * ‖x‖ ^ (d - (2 * m + 1))) := by
              rw [hpow]
              field_simp [hr0.ne']
  have hcg : ContinuousAt g 0 := continuousAt_iff_punctured_nhds.mpr hpunc
  simpa [g] using hcg.tendsto

lemma tendsto_radialHomogTerm_zero
    {m d : ℕ} (hmd : 2 * m ≤ d)
    {h : ℝ → ℝ}
    (hh0 : Tendsto (fun r => h r * r ^ (d - 2 * m)) (𝓝[>] 0) (𝓝 0))
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ d * P x) :
    ContinuousAt (radialHomogTerm m h P) 0 := by
  obtain ⟨C, hC0, hC⟩ := norm_le_of_homogeneous hPsmooth.continuous hPhom
  rw [continuousAt_iff_punctured_nhds]
  have hr0_val : radialHomogTerm m h P 0 = 0 := by simp [radialHomogTerm]
  rw [hr0_val]
  have hlim : Tendsto (fun x : Euclidean 3 => C * (|h ‖x‖| * ‖x‖ ^ (d - 2 * m)))
      (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => C * |h r * r ^ (d - 2 * m)|) (𝓝[>] 0) (𝓝 0) := by
      simpa using (hh0.abs.const_mul C)
    refine (h1.comp tendsto_norm_nhdsGT_of_nhdsNE_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x _
    simp only [Function.comp_def, abs_mul, abs_of_nonneg (pow_nonneg (norm_nonneg x) _)]
  have habs : Tendsto (fun x : Euclidean 3 => |radialHomogTerm m h P x|)
      (𝓝[≠] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards with x
      exact abs_nonneg _
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := hx
      have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hPx := hC x hx0
      have hpow : ‖x‖ ^ d = ‖x‖ ^ (2 * m) * ‖x‖ ^ (d - 2 * m) := by
        rw [← pow_add]
        congr 1
        omega
      simp only [radialHomogTerm, hx0, ↓reduceIte, abs_mul, abs_div,
        abs_of_nonneg (pow_nonneg (norm_nonneg x) _)]
      calc
        |h ‖x‖| * (|P x| / ‖x‖ ^ (2 * m))
            ≤ |h ‖x‖| * ((C * ‖x‖ ^ d) / ‖x‖ ^ (2 * m)) := by gcongr
        _ = C * (|h ‖x‖| * ‖x‖ ^ (d - 2 * m)) := by
            rw [hpow]
            field_simp [hr0.ne']
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using habs)

lemma continuousOn_radialHomogTerm
    {m d : ℕ} (hmd : 2 * m ≤ d)
    {h : ℝ → ℝ}
    (hh0 : Tendsto (fun r => h r * r ^ (d - 2 * m)) (𝓝[>] 0) (𝓝 0))
    (hch : ContinuousOn h (Ioo 0 1))
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ d * P x) :
    ContinuousOn (radialHomogTerm m h P) ftildeBall := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    exact (tendsto_radialHomogTerm_zero hmd hh0 hPsmooth hPhom).continuousWithinAt
  · have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hr1 : ‖x‖ < 1 := by simpa [ftildeBall, mem_ball_zero_iff] using hx
    have hchx : ContinuousAt h ‖x‖ := hch.continuousAt (isOpen_Ioo.mem_nhds ⟨hr0, hr1⟩)
    have hca : ContinuousAt (fun y : Euclidean 3 => h ‖y‖ * (P y / ‖y‖ ^ (2 * m))) x := by
      refine (hchx.comp continuous_norm.continuousAt).mul ?_
      exact hPsmooth.continuous.continuousAt.div
        (continuous_norm.continuousAt.pow (2 * m)) (pow_ne_zero (2 * m) hr0.ne')
    have heq : radialHomogTerm m h P =ᶠ[𝓝 x]
        fun y : Euclidean 3 => h ‖y‖ * (P y / ‖y‖ ^ (2 * m)) := by
      filter_upwards [eventually_ne_nhds hx0] with y hy
      simp [radialHomogTerm, hy]
    exact (hca.congr heq.symm).continuousWithinAt

lemma contDiffOn_one_radialHomogTerm
    {m d : ℕ} (hmd : 2 * m + 1 ≤ d)
    {h h₁ : ℝ → ℝ}
    (hh0 : Tendsto (fun r => h r * r ^ (d - (2 * m + 1))) (𝓝[>] 0) (𝓝 0))
    (hh₁0 : Tendsto (fun r => h₁ r * r ^ (d - (2 * m + 1))) (𝓝[>] 0) (𝓝 0))
    (hdh : ∀ r ∈ Ioo 0 1, HasDerivAt h (h₁ r / r) r)
    (hch₁ : ContinuousOn h₁ (Ioo 0 1))
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ d * P x) :
    ContDiffOn ℝ 1 (radialHomogTerm m h P) ftildeBall := by
  apply (c1On_iff_contDiffOn Metric.isOpen_ball).mp
  have hd0 := hasFDerivAt_radialHomogTerm_zero hmd hh0 hPsmooth hPhom
  have hdiff : ∀ x ∈ ftildeBall, DifferentiableAt ℝ (radialHomogTerm m h P) x := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      exact hd0.differentiableAt
    · exact (hasFDerivAt_radialHomogTerm_ne_zero hdh hPsmooth hx hx0).1
  refine ⟨hdiff, ?_⟩
  have hch : ContinuousOn h (Ioo 0 1) :=
    fun r hr => (hdh r hr).continuousAt.continuousWithinAt
  have hcpart : ∀ j : Fin 3,
      ContinuousOn (fun x => coordinatePartial (radialHomogTerm m h P) x j) ftildeBall := by
    intro j
    let Q₁ : Euclidean 3 → ℝ := fun x => x j * P x
    let Q₂ : Euclidean 3 → ℝ :=
      fun x => (∑ i : Fin 3, x i ^ 2) * coordinatePartial P x j - (2 * m : ℝ) * (x j * P x)
    have hxj : ContDiff ℝ ∞ (fun x : Euclidean 3 => x j) :=
      (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
    have hQ₁s : ContDiff ℝ ∞ Q₁ := hxj.mul hPsmooth
    have hQ₁h : ∀ (t : ℝ) (x : Euclidean 3), Q₁ (t • x) = t ^ (d + 1) * Q₁ x := by
      intro t x
      simp only [Q₁, PiLp.smul_apply, smul_eq_mul, hPhom t x]
      ring
    have hnsq : ContDiff ℝ ∞ (fun x : Euclidean 3 => ∑ i : Fin 3, x i ^ 2) :=
      ContDiff.sum fun i _ => ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).pow 2
    have hQ₂s : ContDiff ℝ ∞ Q₂ :=
      (hnsq.mul (contDiff_coordinatePartial_smooth hPsmooth j)).sub
        (contDiff_const.mul hQ₁s)
    have hd_pos : d = (d - 1) + 1 := by omega
    have hPhom' : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ ((d - 1) + 1) * P x := by
      rw [← hd_pos]
      exact hPhom
    have hQ₂h : ∀ (t : ℝ) (x : Euclidean 3), Q₂ (t • x) = t ^ (d + 1) * Q₂ x := by
      intro t x
      have hcph := coordinatePartial_homog_smooth hPsmooth hPhom' t x j
      have hsum : (∑ i : Fin 3, (t * x i) ^ 2) = t ^ 2 * ∑ i : Fin 3, x i ^ 2 := by
        simp only [Fin.sum_univ_three]
        ring
      have hexp : t ^ 2 * t ^ (d - 1) = t ^ (d + 1) := by
        rw [← pow_add]
        congr 1
        omega
      simp only [Q₂, hcph, PiLp.smul_apply, smul_eq_mul, hPhom t x]
      rw [hsum]
      calc
        (t ^ 2 * ∑ i : Fin 3, x i ^ 2) * (t ^ (d - 1) * coordinatePartial P x j) -
            (2 * m : ℝ) * (t * x j * (t ^ d * P x))
          = (t ^ 2 * t ^ (d - 1)) * ((∑ i : Fin 3, x i ^ 2) * coordinatePartial P x j) -
              t ^ (d + 1) * ((2 * m : ℝ) * (x j * P x)) := by ring
        _ = t ^ (d + 1) * ((∑ i : Fin 3, x i ^ 2) * coordinatePartial P x j -
              (2 * m : ℝ) * (x j * P x)) := by
              rw [hexp]
              ring
    have hexp_eq : (d + 1) - 2 * (m + 1) = d - (2 * m + 1) := by omega
    have hmd' : 2 * (m + 1) ≤ d + 1 := by omega
    have hc1 : ContinuousOn (radialHomogTerm (m + 1) h₁ Q₁) ftildeBall :=
      continuousOn_radialHomogTerm hmd' (by simpa [hexp_eq] using hh₁0) hch₁ hQ₁s hQ₁h
    have hc2 : ContinuousOn (radialHomogTerm (m + 1) h Q₂) ftildeBall :=
      continuousOn_radialHomogTerm hmd' (by simpa [hexp_eq] using hh0) hch hQ₂s hQ₂h
    refine (hc1.add hc2).congr ?_
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      have hz : coordinatePartial (radialHomogTerm m h P) 0 j = 0 := by
        rw [coordinatePartial_eq_fderiv hd0.differentiableAt j, hd0.fderiv]
        simp
      simp [hz, radialHomogTerm]
    · have hf := (hasFDerivAt_radialHomogTerm_ne_zero (m := m) hdh hPsmooth hx hx0).2 j
      dsimp only
      rw [hf]
      simp only [Pi.add_apply, radialHomogTerm, hx0, ↓reduceIte, Q₁, Q₂]
  have hfderiv_eq : EqOn (fderiv ℝ (radialHomogTerm m h P))
      (fun x => ∑ j : Fin 3, coordinatePartial (radialHomogTerm m h P) x j •
        (EuclideanSpace.proj (𝕜 := ℝ) j)) ftildeBall := by
    intro x hx
    ext v
    rw [linear_apply_eq_sum_coordinates]
    simp only [sum_apply, smul_apply, EuclideanSpace.coe_proj, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [coordinatePartial_eq_fderiv (hdiff x hx) j]
  refine (continuousOn_finsetSum Finset.univ fun j _ =>
      (hcpart j).smul (continuousOn_const (c := EuclideanSpace.proj (𝕜 := ℝ) j))).congr ?_
  intro x hx
  exact hfderiv_eq hx

lemma contDiffOn_two_radialHomogTerm6
    {h h₁ h₂ : ℝ → ℝ}
    (hh0 : Tendsto h (𝓝[>] 0) (𝓝 0))
    (hh₁0 : Tendsto h₁ (𝓝[>] 0) (𝓝 0))
    (hh₂0 : Tendsto h₂ (𝓝[>] 0) (𝓝 0))
    (hdh : ∀ r ∈ Ioo 0 1, HasDerivAt h (h₁ r / r) r)
    (hdh₁ : ∀ r ∈ Ioo 0 1, HasDerivAt h₁ (h₂ r / r) r)
    (hch₂ : ContinuousOn h₂ (Ioo 0 1))
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ 6 * P x) :
    ContDiffOn ℝ 2 (radialHomogTerm 2 h P) ftildeBall := by
  have htr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hh0_r : Tendsto (fun r : ℝ => h r * r ^ 1) (𝓝[>] 0) (𝓝 0) := by
    simpa using hh0.mul htr
  have hh₁0_r : Tendsto (fun r : ℝ => h₁ r * r ^ 1) (𝓝[>] 0) (𝓝 0) := by
    simpa using hh₁0.mul htr
  have hch₁ : ContinuousOn h₁ (Ioo 0 1) :=
    fun r hr => (hdh₁ r hr).continuousAt.continuousWithinAt
  have hu1 : ContDiffOn ℝ 1 (radialHomogTerm 2 h P) ftildeBall :=
    contDiffOn_one_radialHomogTerm (m := 2) (d := 6) (by omega) hh0_r hh₁0_r hdh hch₁ hPsmooth hPhom
  apply contDiffOn_two_of_coordinatePartials Metric.isOpen_ball hu1
  intro j
  let Q₁ : Euclidean 3 → ℝ := fun x => x j * P x
  let Q₂ : Euclidean 3 → ℝ :=
    fun x => (∑ i : Fin 3, x i ^ 2) * coordinatePartial P x j - 4 * (x j * P x)
  have hxj : ContDiff ℝ ∞ (fun x : Euclidean 3 => x j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  have hQ₁s : ContDiff ℝ ∞ Q₁ := hxj.mul hPsmooth
  have hQ₁h : ∀ (t : ℝ) (x : Euclidean 3), Q₁ (t • x) = t ^ 7 * Q₁ x := by
    intro t x
    simp only [Q₁, PiLp.smul_apply, smul_eq_mul, hPhom t x]
    ring
  have hnsq : ContDiff ℝ ∞ (fun x : Euclidean 3 => ∑ i : Fin 3, x i ^ 2) :=
    ContDiff.sum fun i _ => ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).pow 2
  have hQ₂s : ContDiff ℝ ∞ Q₂ :=
    (hnsq.mul (contDiff_coordinatePartial_smooth hPsmooth j)).sub (contDiff_const.mul hQ₁s)
  have hQ₂h : ∀ (t : ℝ) (x : Euclidean 3), Q₂ (t • x) = t ^ 7 * Q₂ x := by
    intro t x
    have hcph := coordinatePartial_homog_smooth (k := 5) hPsmooth hPhom t x j
    have hsum : (∑ i : Fin 3, (t * x i) ^ 2) = t ^ 2 * ∑ i : Fin 3, x i ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
    simp only [Q₂, hcph, PiLp.smul_apply, smul_eq_mul, hPhom t x]
    rw [hsum]
    ring
  have hp1 : ContDiffOn ℝ 1 (radialHomogTerm 3 h₁ Q₁) ftildeBall :=
    contDiffOn_one_radialHomogTerm (m := 3) (d := 7) (by omega)
      (by simpa using hh₁0) (by simpa using hh₂0) hdh₁ hch₂ hQ₁s hQ₁h
  have hp2 : ContDiffOn ℝ 1 (radialHomogTerm 3 h Q₂) ftildeBall :=
    contDiffOn_one_radialHomogTerm (m := 3) (d := 7) (by omega)
      (by simpa using hh0) (by simpa using hh₁0) hdh hch₁ hQ₂s hQ₂h
  refine (hp1.add hp2).congr ?_
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    have hd0 := hasFDerivAt_radialHomogTerm_zero (m := 2) (d := 6) (by omega)
      hh0_r hPsmooth hPhom
    rw [coordinatePartial_eq_fderiv hd0.differentiableAt j, hd0.fderiv]
    simp only [zero_apply, radialHomogTerm, ↓reduceIte, add_zero]
  · have hf := (hasFDerivAt_radialHomogTerm_ne_zero (m := 2) hdh hPsmooth hx hx0).2 j
    have h22 : (2 * (2 : ℕ) : ℝ) = 4 := by norm_num
    rw [hf, h22]
    simp only [radialHomogTerm, hx0, ↓reduceIte, Q₁, Q₂]

/-! ## Section 2: Stage 3 harmonic/gauge diagnostics (L6 vs. G6's blocking step) -/

/-- The symmetrized rank-3 transverse Fourier symbol `Sym(ξ ⊗ ξ ⊗ v)`. -/
def fourierTransverseSym3 (ξ v : Euclidean 3) (i j k : Fin 3) : ℝ :=
  ξ i * ξ j * v k + ξ j * ξ k * v i + ξ k * ξ i * v j

/-- The symmetrized rank-3 trace-free Hessian Fourier symbol `c ξ^{⊗ 3} + d Sym(δ ⊗ ξ)`. -/
def fourierGaugeHess0Sym3 (ξ : Euclidean 3) (c d : ℝ) (i j k : Fin 3) : ℝ :=
  c * (ξ i * ξ j * ξ k) +
    d * ((if i = j then 1 else 0) * ξ k +
      (if j = k then 1 else 0) * ξ i +
      (if k = i then 1 else 0) * ξ j)

/-- **Lemma L6 (pointwise Fourier symbol orthogonality):** at any fixed frequency `ξ`,
every symmetrized transverse symbol `Sym(ξ ⊗ ξ ⊗ v)` with `ξ · v = 0` is Frobenius-orthogonal
to every symmetrized trace-free Hessian symbol `c ξ^{⊗ 3} + d Sym(δ ⊗ ξ)`. -/
theorem l6_pointwise_fourier_orthogonality (ξ v : Euclidean 3) (c d : ℝ)
    (hξv : ∑ m : Fin 3, ξ m * v m = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      fourierTransverseSym3 ξ v i j k * fourierGaugeHess0Sym3 ξ c d i j k) = 0 := by
  simp only [Fin.sum_univ_three] at hξv ⊢
  unfold fourierTransverseSym3 fourierGaugeHess0Sym3
  norm_num
  linear_combination (3 * c * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) ^ 2 +
    9 * d * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)) * hξv

/-- Formal polynomial list for the harmonic cubic gauge polynomial
`P(x) = (-4 x₀³ + 16 x₀ x₁² - 4 x₀ x₂²) / 105`. -/
def ftildeCubicGaugeList : List (ℝ × ℕ × ℕ × ℕ) :=
  [(-4 / 105, 3, 0, 0), (16 / 105, 1, 2, 0), (-4 / 105, 1, 0, 2)]

/-- The harmonic cubic polynomial whose constant third-derivative tensor is `ftildeC`. -/
def ftildeCubicGaugePoly : Euclidean 3 → ℝ := evalPoly3 ftildeCubicGaugeList

/-- `ftildeCubicGaugePoly` is harmonic (`Δ P = 0`), so its Hessian is trace-free everywhere. -/
theorem laplacian_ftildeCubicGaugePoly (x : Euclidean 3) :
    (∑ i : Fin 3, coordinatePartial
      (fun y => coordinatePartial ftildeCubicGaugePoly y i) x i) = 0 := by
  simp only [Fin.sum_univ_three, ftildeCubicGaugePoly, coordinatePartial_evalPoly3]
  simp [evalPoly3, derivPoly3, ftildeCubicGaugeList, ftildeMonomial]
  ring

/-- Every third partial derivative of `ftildeCubicGaugePoly` equals `ftildeC i j k`. -/
theorem thirdPartial_ftildeCubicGaugePoly_eq_ftildeC (x : Euclidean 3) (i j k : Fin 3) :
    coordinatePartial
      (fun z => coordinatePartial
        (fun y => coordinatePartial ftildeCubicGaugePoly y i) z j) x k =
      ftildeC i j k := by
  simp only [ftildeCubicGaugePoly, coordinatePartial_evalPoly3]
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [evalPoly3, derivPoly3, ftildeCubicGaugeList, ftildeMonomial, ftildeC] <;>
    norm_num

lemma ftildePsi_tendsto_nhdsGT_zero :
    Tendsto ftildePsi (𝓝[>] 0) (𝓝 0) :=
  tendsto_ftildePsi_nhdsNE_zero.mono_left (nhdsWithin_mono 0 fun _ hr => ne_of_gt hr)

/-- The radial factor `log |log r|` (extended by `0` at `r = 0`) appearing in the
Calderón–Zygmund blow-up `L7`/`L8` and in the local `C²` gauge counterexample to `G6`. -/
def ftildeLogAbsLog (r : ℝ) : ℝ :=
  if r = 0 then 0 else Real.log |Real.log r|

lemma tendsto_ftildeLogAbsLog_mul_self_nhdsGT_zero :
    Tendsto (fun r : ℝ => ftildeLogAbsLog r * r) (𝓝[>] 0) (𝓝 0) := by
  have hupper_lim : Tendsto (fun r : ℝ => 2 * √r) (𝓝[>] 0) (𝓝 0) := by
    have hs : Tendsto Real.sqrt (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using hs.const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_lim ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-1))] with r hr
    have hr0 : 0 < r := hr.1
    have hlog_lt : Real.log r < -1 := by
      calc
        Real.log r < Real.log (Real.exp (-1)) := Real.log_lt_log hr0 hr.2
        _ = -1 := Real.log_exp (-1)
    have habs : |Real.log r| = -Real.log r := abs_of_neg (by linarith)
    have hnonneg : 0 ≤ Real.log (-Real.log r) := Real.log_nonneg (by linarith)
    simp only [ftildeLogAbsLog, hr0.ne', ↓reduceIte, habs]
    exact mul_nonneg hnonneg hr0.le
  · filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-1))] with r hr
    have hr0 : 0 < r := hr.1
    have hs0 : 0 < √r := Real.sqrt_pos.mpr hr0
    have hlog_lt : Real.log r < -1 := by
      calc
        Real.log r < Real.log (Real.exp (-1)) := Real.log_lt_log hr0 hr.2
        _ = -1 := Real.log_exp (-1)
    have habs : |Real.log r| = -Real.log r := abs_of_neg (by linarith)
    have hll : Real.log (-Real.log r) ≤ -Real.log r := by
      have h1 := Real.log_le_sub_one_of_pos (show 0 < -Real.log r by linarith)
      linarith
    have hsinv : Real.log (√r)⁻¹ ≤ (√r)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (inv_pos.mpr hs0)
    have hlsqrt : Real.log (√r)⁻¹ = -(Real.log r / 2) := by
      rw [Real.log_inv, Real.log_sqrt hr0.le]
    have hlog_bound : -Real.log r ≤ 2 * (√r)⁻¹ := by linarith
    have hr_sq : r = √r * √r := (Real.mul_self_sqrt hr0.le).symm
    simp only [ftildeLogAbsLog, hr0.ne', ↓reduceIte, habs]
    calc
      Real.log (-Real.log r) * r ≤ (-Real.log r) * r :=
        mul_le_mul_of_nonneg_right hll hr0.le
      _ ≤ (2 * (√r)⁻¹) * r :=
        mul_le_mul_of_nonneg_right hlog_bound hr0.le
      _ = (2 * (√r)⁻¹) * (√r * √r) := by rw [← hr_sq]
      _ = 2 * √r := by
        field_simp [hs0.ne']

lemma hasDerivAt_ftildeLogAbsLog {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt ftildeLogAbsLog (-ftildePsi r / r) r := by
  have hlog_neg : Real.log r < 0 := Real.log_neg hr0 hr1
  have hneg_pos : 0 < -Real.log r := neg_pos.mpr hlog_neg
  have hd : HasDerivAt (fun t : ℝ => Real.log (-Real.log t))
      ((-r⁻¹) / (-Real.log r)) r :=
    (Real.hasDerivAt_log hr0.ne').neg.log hneg_pos.ne'
  have hev : ftildeLogAbsLog =ᶠ[𝓝 r] fun t : ℝ => Real.log (-Real.log t) := by
    filter_upwards [Ioo_mem_nhds hr0 hr1] with t ht
    have ht_log : Real.log t < 0 := Real.log_neg ht.1 ht.2
    simp [ftildeLogAbsLog, ht.1.ne', abs_of_neg ht_log]
  convert hd.congr_of_eventuallyEq hev using 1
  rw [ftildePsi_eq_neg_inv_log hr0 hr1]
  field_simp [hr0.ne', hlog_neg.ne]

/-- Formal polynomial list for `-ftildeCubicGaugePoly`. -/
def ftildeNegCubicGaugeList : List (ℝ × ℕ × ℕ × ℕ) :=
  [(4 / 105, 3, 0, 0), (-16 / 105, 1, 2, 0), (4 / 105, 1, 0, 2)]

/-- Explicit `C²` local scalar gauge `φ(x) = -ftildeCubicGaugePoly(x) * log |log ‖x‖|`
on `ftildeBall` whose trace-free Hessian has third derivatives `-ftildeC i j k * log |log ‖x‖| + o(1)`
as `x → 0`, directly refuting Step `G6`'s physical-space gauge-invariance claim. -/
def ftildeLocalGauge : Euclidean 3 → ℝ :=
  radialHomogTerm 0 ftildeLogAbsLog (evalPoly3 ftildeNegCubicGaugeList)

lemma ftildeLocalGauge_eq_of_ne_zero {x : Euclidean 3} (hx : x ≠ 0) :
    ftildeLocalGauge x = -ftildeCubicGaugePoly x * ftildeLogAbsLog ‖x‖ := by
  simp only [ftildeLocalGauge, radialHomogTerm, hx, ↓reduceIte, Nat.mul_zero, pow_zero, div_one,
    ftildeCubicGaugePoly, evalPoly3, ftildeCubicGaugeList, ftildeNegCubicGaugeList,
    List.map, List.sum_cons, List.sum_nil, ftildeMonomial]
  ring

/-- The trace-free Hessian `(Hess₀ φ)_{i,j}(x) = ∂_j ∂_i φ(x) - (1/3) δ_{i,j} Δφ(x)`. -/
def traceFreeHessian (φ : Euclidean 3 → ℝ) (i j : Fin 3) (x : Euclidean 3) : ℝ :=
  coordinatePartial (fun y => coordinatePartial φ y i) x j -
    (if i = j then (1 / 3 : ℝ) * ∑ a : Fin 3,
      coordinatePartial (fun y => coordinatePartial φ y a) x a else 0)

lemma contDiffOn_one_and_partial_radialHomogTerm_logAbsLog
    {d : ℕ} (hd : 2 ≤ d)
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ d * P x) :
    ContDiffOn ℝ 1 (radialHomogTerm 0 ftildeLogAbsLog P) ftildeBall ∧
      ∀ x ∈ ftildeBall, ∀ j : Fin 3,
        coordinatePartial (radialHomogTerm 0 ftildeLogAbsLog P) x j =
          radialHomogTerm 0 ftildeLogAbsLog (fun y => coordinatePartial P y j) x +
            radialHomogTerm 1 (fun r => -ftildePsi r) (fun y => y j * P y) x := by
  have hrpow_d2 : Tendsto (fun r : ℝ => r ^ (d - 2)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (d - 2))) :=
    (tendsto_id.pow (d - 2)).mono_left nhdsWithin_le_nhds
  have hh0 : Tendsto (fun r : ℝ => ftildeLogAbsLog r * r ^ (d - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hmul : Tendsto (fun r : ℝ => (ftildeLogAbsLog r * r) * r ^ (d - 2)) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_ftildeLogAbsLog_mul_self_nhdsGT_zero.mul hrpow_d2
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r _
    have hexp : r * r ^ (d - 2) = r ^ (d - 1) := by
      nth_rw 1 [← pow_one r]
      rw [← pow_add]
      congr 1
      omega
    rw [mul_assoc, hexp]
  have hrpow_d1 : Tendsto (fun r : ℝ => r ^ (d - 1)) (𝓝[>] 0) (𝓝 ((0 : ℝ) ^ (d - 1))) :=
    (tendsto_id.pow (d - 1)).mono_left nhdsWithin_le_nhds
  have hh₁0 : Tendsto (fun r : ℝ => -ftildePsi r * r ^ (d - 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ftildePsi_tendsto_nhdsGT_zero.neg.mul hrpow_d1
  have hc1 : ContDiffOn ℝ 1 (radialHomogTerm 0 ftildeLogAbsLog P) ftildeBall :=
    contDiffOn_one_radialHomogTerm (m := 0) (d := d) (by omega)
      (by simpa using hh0) (by simpa using hh₁0)
      (fun r hr => hasDerivAt_ftildeLogAbsLog hr.1 hr.2)
      continuousOn_ftildePsi_Ioo.neg hPsmooth hPhom
  refine ⟨hc1, fun x hx j => ?_⟩
  by_cases hx0 : x = 0
  · subst hx0
    have hd0 := hasFDerivAt_radialHomogTerm_zero (m := 0) (d := d) (by omega)
      (by simpa using hh0) hPsmooth hPhom
    rw [coordinatePartial_eq_fderiv hd0.differentiableAt j, hd0.fderiv]
    simp [radialHomogTerm]
  · have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hf := (hasFDerivAt_radialHomogTerm_ne_zero (m := 0)
      (fun r hr => hasDerivAt_ftildeLogAbsLog hr.1 hr.2) hPsmooth hx hx0).2 j
    have hsq : ∑ i : Fin 3, x i ^ 2 = ‖x‖ ^ 2 := (norm_sq_eq_sum_three x).symm
    rw [hf, hsq]
    simp only [radialHomogTerm, hx0, ↓reduceIte, Nat.mul_zero, pow_zero, Nat.cast_zero,
      Nat.zero_add, Nat.mul_one, div_one]
    field_simp [hr0.ne']
    ring

lemma c1_and_fderiv_zero_radialHomogTerm_tight
    {m : ℕ} {h h₁ : ℝ → ℝ}
    (hh0 : Tendsto h (𝓝[>] 0) (𝓝 0))
    (hh₁0 : Tendsto h₁ (𝓝[>] 0) (𝓝 0))
    (hdh : ∀ r ∈ Ioo 0 1, HasDerivAt h (h₁ r / r) r)
    (hch₁ : ContinuousOn h₁ (Ioo 0 1))
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ (2 * m + 1) * P x) :
    ContDiffOn ℝ 1 (radialHomogTerm m h P) ftildeBall ∧
      HasFDerivAt (radialHomogTerm m h P) (0 : Euclidean 3 →L[ℝ] ℝ) 0 :=
  ⟨contDiffOn_one_radialHomogTerm (m := m) (d := 2 * m + 1) le_rfl
      (by simpa using hh0) (by simpa using hh₁0) hdh hch₁ hPsmooth hPhom,
    hasFDerivAt_radialHomogTerm_zero (m := m) (d := 2 * m + 1) le_rfl
      (by simpa using hh0) hPsmooth hPhom⟩

lemma c1_and_fderiv_zero_partial_radialHomogTerm1_deg4
    {P : Euclidean 3 → ℝ} (hPsmooth : ContDiff ℝ ∞ P)
    (hPhom : ∀ (t : ℝ) (x : Euclidean 3), P (t • x) = t ^ 4 * P x) (j : Fin 3) :
    ContDiffOn ℝ 1 (fun x => coordinatePartial
        (radialHomogTerm 1 (fun r => -ftildePsi r) P) x j) ftildeBall ∧
      HasFDerivAt (fun x => coordinatePartial
        (radialHomogTerm 1 (fun r => -ftildePsi r) P) x j) (0 : Euclidean 3 →L[ℝ] ℝ) 0 := by
  let M₁ : Euclidean 3 → ℝ := fun x => x j * P x
  let M₂ : Euclidean 3 → ℝ :=
    fun x => (∑ a : Fin 3, x a ^ 2) * coordinatePartial P x j - 2 * (x j * P x)
  have hxj : ContDiff ℝ ∞ (fun x : Euclidean 3 => x j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  have hM₁s : ContDiff ℝ ∞ M₁ := hxj.mul hPsmooth
  have hM₁h : ∀ (t : ℝ) (x : Euclidean 3), M₁ (t • x) = t ^ 5 * M₁ x := by
    intro t x
    simp only [M₁, PiLp.smul_apply, smul_eq_mul, hPhom t x]
    ring
  have hnsq : ContDiff ℝ ∞ (fun x : Euclidean 3 => ∑ a : Fin 3, x a ^ 2) :=
    ContDiff.sum fun a _ => ((EuclideanSpace.proj (𝕜 := ℝ) a).contDiff).pow 2
  have hM₂s : ContDiff ℝ ∞ M₂ :=
    (hnsq.mul (contDiff_coordinatePartial_smooth hPsmooth j)).sub (contDiff_const.mul hM₁s)
  have hM₂h : ∀ (t : ℝ) (x : Euclidean 3), M₂ (t • x) = t ^ 5 * M₂ x := by
    intro t x
    have hcph := coordinatePartial_homog_smooth (k := 3) hPsmooth hPhom t x j
    have hsum : (∑ a : Fin 3, (t * x a) ^ 2) = t ^ 2 * ∑ a : Fin 3, x a ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
    simp only [M₂, hcph, PiLp.smul_apply, smul_eq_mul, hPhom t x]
    rw [hsum]
    ring
  have hg0 : Tendsto (fun r : ℝ => -ftildePsi r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ftildePsi_tendsto_nhdsGT_zero.neg
  have hg1 : Tendsto (fun r : ℝ => -ftildePsi r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ftildePsi_tendsto_nhdsGT_zero.pow 2).neg
  have hg2 : Tendsto (fun r : ℝ => -2 * ftildePsi r ^ 3) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ftildePsi_tendsto_nhdsGT_zero.pow 3).const_mul (-2)
  have hdg0 : ∀ r ∈ Ioo 0 1, HasDerivAt (fun t : ℝ => -ftildePsi t) (-ftildePsi r ^ 2 / r) r := by
    intro r hr
    convert (hasDerivAt_ftildePsi hr.1 hr.2).neg using 1
    ring
  have hdg1 : ∀ r ∈ Ioo 0 1,
      HasDerivAt (fun t : ℝ => -ftildePsi t ^ 2) (-2 * ftildePsi r ^ 3 / r) r := by
    intro r hr
    convert ((hasDerivAt_ftildePsi hr.1 hr.2).pow 2).neg using 1
    ring
  have hcg1 : ContinuousOn (fun r : ℝ => -ftildePsi r ^ 2) (Ioo 0 1) :=
    (continuousOn_ftildePsi_Ioo.pow 2).neg
  have hcg2 : ContinuousOn (fun r : ℝ => -2 * ftildePsi r ^ 3) (Ioo 0 1) :=
    continuousOn_const.mul (continuousOn_ftildePsi_Ioo.pow 3)
  obtain ⟨hc1, hd1⟩ := c1_and_fderiv_zero_radialHomogTerm_tight (m := 2)
    hg1 hg2 hdg1 hcg2 hM₁s hM₁h
  obtain ⟨hc2, hd2⟩ := c1_and_fderiv_zero_radialHomogTerm_tight (m := 2)
    hg0 hg1 hdg0 hcg1 hM₂s hM₂h
  have heq : EqOn (fun x => coordinatePartial
        (radialHomogTerm 1 (fun r => -ftildePsi r) P) x j)
      (fun x => radialHomogTerm 2 (fun r => -ftildePsi r ^ 2) M₁ x +
        radialHomogTerm 2 (fun r => -ftildePsi r) M₂ x) ftildeBall := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      have htr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hgh0 : Tendsto (fun r : ℝ => -ftildePsi r * r ^ (4 - (2 * 1 + 1))) (𝓝[>] 0) (𝓝 0) := by
        simpa using hg0.mul htr
      have hd0 := hasFDerivAt_radialHomogTerm_zero (m := 1) (d := 4) (by omega)
        hgh0 hPsmooth hPhom
      dsimp only
      rw [coordinatePartial_eq_fderiv hd0.differentiableAt j, hd0.fderiv]
      simp only [zero_apply, radialHomogTerm, ↓reduceIte, add_zero]
    · have hf := (hasFDerivAt_radialHomogTerm_ne_zero (m := 1) hdg0 hPsmooth hx hx0).2 j
      have h21 : (2 * (1 : ℕ) : ℝ) = 2 := by norm_num
      dsimp only
      rw [hf, h21]
      simp only [radialHomogTerm, hx0, ↓reduceIte, M₁, M₂]
  have hmem : ftildeBall ∈ 𝓝 (0 : Euclidean 3) :=
    Metric.isOpen_ball.mem_nhds (mem_ball_self zero_lt_one)
  have hev : (fun x => coordinatePartial (radialHomogTerm 1 (fun r => -ftildePsi r) P) x j) =ᶠ[𝓝 0]
      (fun x => radialHomogTerm 2 (fun r => -ftildePsi r ^ 2) M₁ x +
        radialHomogTerm 2 (fun r => -ftildePsi r) M₂ x) :=
    Filter.eventuallyEq_of_mem hmem fun x hx => heq hx
  have hd_sum : HasFDerivAt
      (fun x => radialHomogTerm 2 (fun r => -ftildePsi r ^ 2) M₁ x +
        radialHomogTerm 2 (fun r => -ftildePsi r) M₂ x)
      (0 : Euclidean 3 →L[ℝ] ℝ) 0 := by
    simpa using hd1.fun_add hd2
  exact ⟨(hc1.add hc2).congr heq, hd_sum.congr_of_eventuallyEq hev⟩

lemma tendsto_coordinatePartial_zero_of_c1_fderiv_zero
    {R : Euclidean 3 → ℝ} (hR : ContDiffOn ℝ 1 R ftildeBall)
    (hd0 : HasFDerivAt R (0 : Euclidean 3 →L[ℝ] ℝ) 0) (k : Fin 3) :
    Tendsto (fun x => coordinatePartial R x k) (𝓝[≠] 0) (𝓝 0) := by
  rcases (c1On_iff_contDiffOn Metric.isOpen_ball).mpr hR with ⟨hdiff, hcf⟩
  have hmem0 : (0 : Euclidean 3) ∈ ftildeBall := mem_ball_self zero_lt_one
  have hca : ContinuousAt (fderiv ℝ R) 0 :=
    (hcf 0 hmem0).continuousAt (Metric.isOpen_ball.mem_nhds hmem0)
  have hval : ContinuousAt (fun x => fderiv ℝ R x (coordinateVector 3 k)) 0 :=
    (ContinuousLinearMap.apply ℝ ℝ (coordinateVector 3 k)).continuous.continuousAt.comp hca
  have h0 : fderiv ℝ R 0 (coordinateVector 3 k) = 0 := by
    rw [hd0.fderiv]
    simp
  have ht : Tendsto (fun x => fderiv ℝ R x (coordinateVector 3 k)) (𝓝[≠] 0) (𝓝 0) := by
    rw [← h0]
    exact hval.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hmem0)] with x hx
  exact (coordinatePartial_eq_fderiv (hdiff x hx) k).symm

/-- `ftildeLocalGauge` is `C²` on all of `ftildeBall`. -/
theorem contDiffOn_two_ftildeLocalGauge :
    ContDiffOn ℝ 2 ftildeLocalGauge ftildeBall := by
  let Q : Euclidean 3 → ℝ := evalPoly3 ftildeNegCubicGaugeList
  have hQs : ContDiff ℝ ∞ Q := contDiff_evalPoly3 ftildeNegCubicGaugeList
  have hQh : ∀ (t : ℝ) (x : Euclidean 3), Q (t • x) = t ^ 3 * Q x := by
    apply evalPoly3_homog
    simp [ftildeNegCubicGaugeList]
  obtain ⟨hu1, hpart1⟩ := contDiffOn_one_and_partial_radialHomogTerm_logAbsLog
    (by omega) hQs hQh
  apply contDiffOn_two_of_coordinatePartials Metric.isOpen_ball hu1
  intro i
  have hQ₁s : ContDiff ℝ ∞ (fun y => coordinatePartial Q y i) :=
    contDiff_coordinatePartial_smooth hQs i
  have hQ₁h : ∀ (t : ℝ) (x : Euclidean 3),
      coordinatePartial Q (t • x) i = t ^ 2 * coordinatePartial Q x i :=
    fun t x => coordinatePartial_homog_smooth (k := 2) hQs hQh t x i
  have hc_log : ContDiffOn ℝ 1
      (radialHomogTerm 0 ftildeLogAbsLog (fun y => coordinatePartial Q y i)) ftildeBall :=
    (contDiffOn_one_and_partial_radialHomogTerm_logAbsLog (by omega) hQ₁s hQ₁h).1
  let P₄ : Euclidean 3 → ℝ := fun y => y i * Q y
  have hP₄s : ContDiff ℝ ∞ P₄ := ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul hQs
  have hP₄h : ∀ (t : ℝ) (x : Euclidean 3), P₄ (t • x) = t ^ 4 * P₄ x := by
    intro t x
    simp only [P₄, PiLp.smul_apply, smul_eq_mul, hQh t x]
    ring
  have htr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hg0 : Tendsto (fun r : ℝ => -ftildePsi r * r ^ 1) (𝓝[>] 0) (𝓝 0) := by
    simpa using ftildePsi_tendsto_nhdsGT_zero.neg.mul htr
  have hg1 : Tendsto (fun r : ℝ => -ftildePsi r ^ 2 * r ^ 1) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ftildePsi_tendsto_nhdsGT_zero.pow 2).neg.mul htr
  have hdg0 : ∀ r ∈ Ioo 0 1, HasDerivAt (fun t : ℝ => -ftildePsi t) (-ftildePsi r ^ 2 / r) r := by
    intro r hr
    convert (hasDerivAt_ftildePsi hr.1 hr.2).neg using 1
    ring
  have hc_psi : ContDiffOn ℝ 1
      (radialHomogTerm 1 (fun r => -ftildePsi r) P₄) ftildeBall :=
    contDiffOn_one_radialHomogTerm (m := 1) (d := 4) (by omega)
      hg0 hg1 hdg0 (continuousOn_ftildePsi_Ioo.pow 2).neg hP₄s hP₄h
  exact (hc_log.add hc_psi).congr fun x hx => hpart1 x hx i

lemma secondPartial_ftildeLocalGauge_decomp (i j : Fin 3) :
    ∃ R : Euclidean 3 → ℝ,
      ContDiffOn ℝ 1 R ftildeBall ∧
      HasFDerivAt R (0 : Euclidean 3 →L[ℝ] ℝ) 0 ∧
      ∀ x ∈ ftildeBall,
        coordinatePartial (fun y => coordinatePartial ftildeLocalGauge y i) x j =
          radialHomogTerm 0 ftildeLogAbsLog
            (evalPoly3 (derivPoly3 j (derivPoly3 i ftildeNegCubicGaugeList))) x + R x := by
  let Q : Euclidean 3 → ℝ := evalPoly3 ftildeNegCubicGaugeList
  have hQs : ContDiff ℝ ∞ Q := contDiff_evalPoly3 ftildeNegCubicGaugeList
  have hQh : ∀ (t : ℝ) (x : Euclidean 3), Q (t • x) = t ^ 3 * Q x := by
    apply evalPoly3_homog
    simp [ftildeNegCubicGaugeList]
  obtain ⟨_, hpart1⟩ := contDiffOn_one_and_partial_radialHomogTerm_logAbsLog
    (by omega) hQs hQh
  let Q₁ : Euclidean 3 → ℝ := evalPoly3 (derivPoly3 i ftildeNegCubicGaugeList)
  have hQ₁_eq : ∀ y, coordinatePartial Q y i = Q₁ y :=
    fun y => coordinatePartial_evalPoly3 ftildeNegCubicGaugeList y i
  have hQ₁s : ContDiff ℝ ∞ Q₁ := contDiff_evalPoly3 _
  have hQ₁h : ∀ (t : ℝ) (x : Euclidean 3), Q₁ (t • x) = t ^ 2 * Q₁ x := by
    intro t x
    simp only [← hQ₁_eq]
    exact coordinatePartial_homog_smooth (k := 2) hQs hQh t x i
  obtain ⟨hc_u₁, hpart_u₁⟩ := contDiffOn_one_and_partial_radialHomogTerm_logAbsLog
    (by omega) hQ₁s hQ₁h
  let P₄ : Euclidean 3 → ℝ := fun y => y i * Q y
  have hP₄s : ContDiff ℝ ∞ P₄ := ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).mul hQs
  have hP₄h : ∀ (t : ℝ) (x : Euclidean 3), P₄ (t • x) = t ^ 4 * P₄ x := by
    intro t x
    simp only [P₄, PiLp.smul_apply, smul_eq_mul, hQh t x]
    ring
  have htr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hg0 : Tendsto (fun r : ℝ => -ftildePsi r) (𝓝[>] 0) (𝓝 0) := by
    simpa using ftildePsi_tendsto_nhdsGT_zero.neg
  have hg1 : Tendsto (fun r : ℝ => -ftildePsi r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using (ftildePsi_tendsto_nhdsGT_zero.pow 2).neg
  have hdg0 : ∀ r ∈ Ioo 0 1, HasDerivAt (fun t : ℝ => -ftildePsi t) (-ftildePsi r ^ 2 / r) r := by
    intro r hr
    convert (hasDerivAt_ftildePsi hr.1 hr.2).neg using 1
    ring
  have hc_w₁ : ContDiffOn ℝ 1 (radialHomogTerm 1 (fun r => -ftildePsi r) P₄) ftildeBall :=
    contDiffOn_one_radialHomogTerm (m := 1) (d := 4) (by omega)
      (by simpa using hg0.mul htr) (by simpa using hg1.mul htr)
      hdg0 (continuousOn_ftildePsi_Ioo.pow 2).neg hP₄s hP₄h
  obtain ⟨hc_dw₁, hd_dw₁⟩ := c1_and_fderiv_zero_partial_radialHomogTerm1_deg4 hP₄s hP₄h j
  let P₃ : Euclidean 3 → ℝ := fun y => y j * Q₁ y
  have hP₃s : ContDiff ℝ ∞ P₃ := ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff).mul hQ₁s
  have hP₃h : ∀ (t : ℝ) (x : Euclidean 3), P₃ (t • x) = t ^ 3 * P₃ x := by
    intro t x
    simp only [P₃, PiLp.smul_apply, smul_eq_mul, hQ₁h t x]
    ring
  obtain ⟨hc_w₂, hd_w₂⟩ := c1_and_fderiv_zero_radialHomogTerm_tight (m := 1)
    hg0 hg1 hdg0 (continuousOn_ftildePsi_Ioo.pow 2).neg hP₃s hP₃h
  refine ⟨fun x => radialHomogTerm 1 (fun r => -ftildePsi r) P₃ x +
      coordinatePartial (radialHomogTerm 1 (fun r => -ftildePsi r) P₄) x j,
    hc_w₂.add hc_dw₁, by simpa using hd_w₂.fun_add hd_dw₁, fun x hx => ?_⟩
  have heq1 : EqOn (fun y => coordinatePartial ftildeLocalGauge y i)
      (fun y => radialHomogTerm 0 ftildeLogAbsLog Q₁ y +
        radialHomogTerm 1 (fun r => -ftildePsi r) P₄ y) ftildeBall := by
    intro y hy
    have h := hpart1 y hy i
    simpa only [ftildeLocalGauge, Q, hQ₁_eq, P₄] using h
  have hdu₁ : DifferentiableAt ℝ (radialHomogTerm 0 ftildeLogAbsLog Q₁) x :=
    ((c1On_iff_contDiffOn Metric.isOpen_ball).mpr hc_u₁).1 x hx
  have hdw₁ : DifferentiableAt ℝ (radialHomogTerm 1 (fun r => -ftildePsi r) P₄) x :=
    ((c1On_iff_contDiffOn Metric.isOpen_ball).mpr hc_w₁).1 x hx
  rw [coordinatePartial_congr_of_eqOn Metric.isOpen_ball heq1 hx j,
    coordinatePartial_add hdu₁ hdw₁ j, hpart_u₁ x hx j]
  simp only [Q₁, coordinatePartial_evalPoly3, P₃, add_assoc]

/-- **Physical-space refutation of Step `G6`:** for the `C²(ftildeBall)` scalar gauge
`ftildeLocalGauge`, every third partial derivative `∂_k (Hess₀ ftildeLocalGauge)_{i,j}(x)`
equals `-ftildeC i j k * log |log ‖x‖| + o(1)` as `x → 0` (`x ≠ 0`), cancelling the
exact logarithmic blow-up of `∂ S⁽⁰⁾` pointwise despite L6's Fourier orthogonality. -/
theorem tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge (i j k : Fin 3) :
    Tendsto
      (fun x : Euclidean 3 =>
        coordinatePartial (traceFreeHessian ftildeLocalGauge i j) x k +
          ftildeC i j k * ftildeLogAbsLog ‖x‖)
      (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨Rij, hRij_c1, hRij_d0, hRij_eq⟩ := secondPartial_ftildeLocalGauge_decomp i j
  choose Rdiag hRdiag_c1 hRdiag_d0 hRdiag_eq using
    fun a : Fin 3 => secondPartial_ftildeLocalGauge_decomp a a
  let R₀ : Euclidean 3 → ℝ := fun x =>
    Rij x - (if i = j then (1 / 3 : ℝ) * ∑ a : Fin 3, Rdiag a x else 0)
  have hsum_c1 : ContDiffOn ℝ 1 (fun x => ∑ a : Fin 3, Rdiag a x) ftildeBall :=
    ContDiffOn.sum fun a _ => hRdiag_c1 a
  have hsum_d0 : HasFDerivAt (fun x => ∑ a : Fin 3, Rdiag a x)
      (0 : Euclidean 3 →L[ℝ] ℝ) 0 := by
    simpa using (HasFDerivAt.fun_sum (u := Finset.univ) fun a _ => hRdiag_d0 a)
  have hite_c1 : ContDiffOn ℝ 1
      (fun x => if i = j then (1 / 3 : ℝ) * ∑ a : Fin 3, Rdiag a x else 0) ftildeBall := by
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      exact contDiffOn_const.mul hsum_c1
    · simp only [hij, ↓reduceIte]
      exact contDiffOn_const
  have hite_d0 : HasFDerivAt
      (fun x => if i = j then (1 / 3 : ℝ) * ∑ a : Fin 3, Rdiag a x else 0)
      (0 : Euclidean 3 →L[ℝ] ℝ) 0 := by
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      simpa using hsum_d0.const_mul (1 / 3 : ℝ)
    · simp only [hij, ↓reduceIte]
      simpa using hasFDerivAt_const (0 : ℝ) (0 : Euclidean 3)
  have hR₀_c1 : ContDiffOn ℝ 1 R₀ ftildeBall := hRij_c1.sub hite_c1
  have hR₀_d0 : HasFDerivAt R₀ (0 : Euclidean 3 →L[ℝ] ℝ) 0 := by
    simpa [R₀] using hRij_d0.fun_sub hite_d0
  let L₁ : Euclidean 3 → ℝ :=
    evalPoly3 (derivPoly3 j (derivPoly3 i ftildeNegCubicGaugeList))
  have hL₁s : ContDiff ℝ ∞ L₁ := contDiff_evalPoly3 _
  have hL₁h : ∀ (t : ℝ) (x : Euclidean 3), L₁ (t • x) = t ^ 1 * L₁ x := by
    have hQs : ContDiff ℝ ∞ (evalPoly3 ftildeNegCubicGaugeList) := contDiff_evalPoly3 _
    have hQh : ∀ (t : ℝ) (x : Euclidean 3),
        evalPoly3 ftildeNegCubicGaugeList (t • x) =
          t ^ 3 * evalPoly3 ftildeNegCubicGaugeList x := by
      apply evalPoly3_homog
      simp [ftildeNegCubicGaugeList]
    have hQ₁s : ContDiff ℝ ∞ (evalPoly3 (derivPoly3 i ftildeNegCubicGaugeList)) :=
      contDiff_evalPoly3 _
    have hQ₁h : ∀ (t : ℝ) (x : Euclidean 3),
        evalPoly3 (derivPoly3 i ftildeNegCubicGaugeList) (t • x) =
          t ^ 2 * evalPoly3 (derivPoly3 i ftildeNegCubicGaugeList) x := by
      intro t x
      simp only [← coordinatePartial_evalPoly3 ftildeNegCubicGaugeList]
      exact coordinatePartial_homog_smooth (k := 2) hQs hQh t x i
    intro t x
    simp only [L₁, ← coordinatePartial_evalPoly3 (derivPoly3 i ftildeNegCubicGaugeList)]
    exact coordinatePartial_homog_smooth (k := 1) hQ₁s hQ₁h t x j
  have hlap_zero : ∀ x : Euclidean 3,
      (∑ a : Fin 3, radialHomogTerm 0 ftildeLogAbsLog
        (evalPoly3 (derivPoly3 a (derivPoly3 a ftildeNegCubicGaugeList))) x) = 0 := by
    intro x
    by_cases hx0 : x = 0
    · simp [radialHomogTerm, hx0]
    · simp only [Fin.sum_univ_three, radialHomogTerm, hx0, ↓reduceIte,
        Nat.mul_zero, pow_zero, div_one]
      have hz : evalPoly3 (derivPoly3 0 (derivPoly3 0 ftildeNegCubicGaugeList)) x +
          evalPoly3 (derivPoly3 1 (derivPoly3 1 ftildeNegCubicGaugeList)) x +
          evalPoly3 (derivPoly3 2 (derivPoly3 2 ftildeNegCubicGaugeList)) x = 0 := by
        simp [evalPoly3, derivPoly3, ftildeNegCubicGaugeList, ftildeMonomial]
        ring
      linear_combination ftildeLogAbsLog ‖x‖ * hz
  have htf_eq : EqOn (traceFreeHessian ftildeLocalGauge i j)
      (fun x => radialHomogTerm 0 ftildeLogAbsLog L₁ x + R₀ x) ftildeBall := by
    intro x hx
    dsimp only [traceFreeHessian, R₀, L₁]
    rw [hRij_eq x hx]
    have hsum_eq : (∑ a : Fin 3,
        coordinatePartial (fun y => coordinatePartial ftildeLocalGauge y a) x a) =
        ∑ a : Fin 3, Rdiag a x := by
      calc
        (∑ a : Fin 3, coordinatePartial (fun y => coordinatePartial ftildeLocalGauge y a) x a)
            = ∑ a : Fin 3, (radialHomogTerm 0 ftildeLogAbsLog
                (evalPoly3 (derivPoly3 a (derivPoly3 a ftildeNegCubicGaugeList))) x + Rdiag a x) :=
              Finset.sum_congr rfl fun a _ => hRdiag_eq a x hx
        _ = (∑ a : Fin 3, radialHomogTerm 0 ftildeLogAbsLog
              (evalPoly3 (derivPoly3 a (derivPoly3 a ftildeNegCubicGaugeList))) x) +
              ∑ a : Fin 3, Rdiag a x := Finset.sum_add_distrib
        _ = ∑ a : Fin 3, Rdiag a x := by rw [hlap_zero x, zero_add]
    rw [hsum_eq]
    by_cases hij : i = j
    · simp [hij]
      ring
    · simp [hij]
  let M₂ : Euclidean 3 → ℝ := fun x => x k * L₁ x
  have hM₂s : ContDiff ℝ ∞ M₂ := ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff).mul hL₁s
  have hM₂h : ∀ (t : ℝ) (x : Euclidean 3), M₂ (t • x) = t ^ 2 * M₂ x := by
    intro t x
    simp only [M₂, PiLp.smul_apply, smul_eq_mul, hL₁h t x]
    ring
  have ht1 : Tendsto (radialHomogTerm 1 (fun r => -ftildePsi r) M₂) (𝓝[≠] 0) (𝓝 0) := by
    have hca := tendsto_radialHomogTerm_zero (m := 1) (d := 2) le_rfl
      (by simpa using ftildePsi_tendsto_nhdsGT_zero.neg) hM₂s hM₂h
    have hz : radialHomogTerm 1 (fun r => -ftildePsi r) M₂ 0 = 0 := by simp [radialHomogTerm]
    rw [← hz]
    exact hca.tendsto.mono_left nhdsWithin_le_nhds
  have ht2 : Tendsto (fun x => coordinatePartial R₀ x k) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_coordinatePartial_zero_of_c1_fderiv_zero hR₀_c1 hR₀_d0 k
  have hthird : ∀ x : Euclidean 3, coordinatePartial L₁ x k = -ftildeC i j k := by
    intro x
    rw [coordinatePartial_evalPoly3]
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [evalPoly3, derivPoly3, ftildeNegCubicGaugeList, ftildeMonomial, ftildeC] <;>
      norm_num
  have hsum_lim : Tendsto
      (fun x => radialHomogTerm 1 (fun r => -ftildePsi r) M₂ x + coordinatePartial R₀ x k)
      (𝓝[≠] 0) (𝓝 0) := by
    simpa using ht1.add ht2
  refine hsum_lim.congr' ?_
  have hball_mem : ftildeBall ∈ 𝓝[≠] (0 : Euclidean 3) :=
    nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (mem_ball_self zero_lt_one))
  filter_upwards [hball_mem, self_mem_nhdsWithin] with x hx hx0
  have hx_ne : x ≠ 0 := hx0
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hd_L := hasFDerivAt_radialHomogTerm_ne_zero (m := 0)
    (fun r hr => hasDerivAt_ftildeLogAbsLog hr.1 hr.2) hL₁s hx hx_ne
  have hd_R₀ : DifferentiableAt ℝ R₀ x :=
    ((c1On_iff_contDiffOn Metric.isOpen_ball).mpr hR₀_c1).1 x hx
  have hsq : ∑ a : Fin 3, x a ^ 2 = ‖x‖ ^ 2 := (norm_sq_eq_sum_three x).symm
  rw [coordinatePartial_congr_of_eqOn Metric.isOpen_ball htf_eq hx k,
    coordinatePartial_add hd_L.1 hd_R₀ k, hd_L.2 k, hsq, hthird x]
  simp only [radialHomogTerm, hx_ne, ↓reduceIte, M₂, Nat.cast_zero,
    Nat.zero_add, Nat.mul_one]
  field_simp [hr0.ne']
  ring

/-! ## Section 3: Explicit global `C²` vector potential on `ftildeBall` -/

/-- The second radial profile `J(r) / r³` appearing in the closed-form potential `ftildePotentialG`. -/
def ftildeJOverCube (r : ℝ) : ℝ := ftildeJ r / r ^ 3

lemma ftildePsi_nonneg_and_mono_Icc {r t : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (ht : t ∈ Icc 0 r) :
    0 ≤ ftildePsi t ∧ ftildePsi t ≤ ftildePsi r := by
  have hlogr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hpsir_pos : 0 < ftildePsi r := by
    rw [ftildePsi_eq_neg_inv_log hr0 hr1]
    exact neg_pos.mpr (inv_lt_zero.mpr hlogr)
  by_cases ht0 : t = 0
  · subst ht0
    have hz : ftildePsi 0 = 0 := by simp [ftildePsi]
    exact ⟨hz.ge, hz.trans_le hpsir_pos.le⟩
  · have ht_pos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hr1
    have hlogt : Real.log t ≤ Real.log r := Real.log_le_log ht_pos ht.2
    rw [ftildePsi_eq_neg_inv_log ht_pos ht1, ftildePsi_eq_neg_inv_log hr0 hr1]
    refine ⟨(neg_pos.mpr (inv_lt_zero.mpr (lt_of_le_of_lt hlogt hlogr))).le, ?_⟩
    have hneg_le : -Real.log r ≤ -Real.log t := neg_le_neg hlogt
    have hinv : (-Real.log t)⁻¹ ≤ (-Real.log r)⁻¹ :=
      inv_anti₀ (neg_pos.mpr hlogr) hneg_le
    simpa [inv_neg] using hinv

lemma ftildeJOverCube_bounds {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    0 ≤ ftildeJOverCube r ∧ ftildeJOverCube r ≤ ftildePsi r ^ 2 := by
  have hnonneg : 0 ≤ ftildeJ r := by
    apply intervalIntegral.integral_nonneg hr0.le
    intro t _
    positivity
  have hupper : ftildeJ r ≤ ftildePsi r ^ 2 * r ^ 3 := by
    have hmono : ∫ t in (0)..r, ftildePsi t ^ 2 * t ^ 2 ≤
        ∫ _ in (0)..r, ftildePsi r ^ 2 * r ^ 2 := by
      apply intervalIntegral.integral_mono_on hr0.le
        (intervalIntegrable_ftildePsi_sq_mul_sq hr0 hr1) intervalIntegrable_const
      intro t ht
      have hb := ftildePsi_nonneg_and_mono_Icc hr0 hr1 ht
      have hp1 : ftildePsi t ^ 2 ≤ ftildePsi r ^ 2 :=
        pow_le_pow_left₀ hb.1 hb.2 2
      have hp2 : t ^ 2 ≤ r ^ 2 :=
        pow_le_pow_left₀ ht.1 ht.2 2
      exact mul_le_mul hp1 hp2 (sq_nonneg t) (sq_nonneg _)
    calc
      ftildeJ r ≤ ∫ _ in (0)..r, ftildePsi r ^ 2 * r ^ 2 := hmono
      _ = ftildePsi r ^ 2 * r ^ 3 := by
        rw [intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
  refine ⟨div_nonneg hnonneg (pow_nonneg hr0.le 3), ?_⟩
  rw [ftildeJOverCube, div_le_iff₀ (pow_pos hr0 3)]
  exact hupper

lemma ftildeJOverCube_tendsto_nhdsGT_zero :
    Tendsto ftildeJOverCube (𝓝[>] 0) (𝓝 0) := by
  have hpsi2 : Tendsto (fun r : ℝ => ftildePsi r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using ftildePsi_tendsto_nhdsGT_zero.pow 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hpsi2 ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with r hr
    exact (ftildeJOverCube_bounds hr.1 hr.2).1
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with r hr
    exact (ftildeJOverCube_bounds hr.1 hr.2).2

lemma hasDerivAt_ftildeJOverCube {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt ftildeJOverCube ((ftildePsi r ^ 2 - 3 * ftildeJOverCube r) / r) r := by
  have hJ := hasDerivAt_ftildeJ hr0 hr1
  have hr3 := (hasDerivAt_id r).pow 3
  have hdiv : HasDerivAt ftildeJOverCube
      ((ftildePsi r ^ 2 * r ^ 2 * r ^ 3 - ftildeJ r * ((3 : ℕ) * r ^ (3 - 1) * 1)) /
        (r ^ 3) ^ 2) r :=
    hJ.div hr3 (pow_ne_zero 3 hr0.ne')
  convert hdiv using 1
  unfold ftildeJOverCube
  field_simp [hr0.ne']
  ring

/-- Degree-6 polynomial lists `A₆ = -(x × ∇α₆) + β₅ x` for the `ψ(‖x‖)` branch of `G`. -/
def ftildeA6List (i : Fin 3) : List (ℝ × ℕ × ℕ × ℕ) :=
  match i with
  | ⟨0, _⟩ =>
    [(1 / 5, 0, 0, 6), (4 / 5, 0, 2, 4), (1 / 5, 0, 4, 2), (-2 / 5, 0, 6, 0),
     (11 / 15, 1, 0, 5), (22 / 15, 1, 2, 3), (11 / 15, 1, 4, 1),
     (1, 2, 0, 4), (12 / 5, 2, 2, 2), (1 / 5, 2, 4, 0),
     (23 / 15, 3, 0, 3), (23 / 15, 3, 2, 1),
     (7 / 5, 4, 0, 2), (8 / 5, 4, 2, 0),
     (23 / 30, 5, 0, 1), (3 / 5, 6, 0, 0)]
  | ⟨1, _⟩ =>
    [(11 / 30, 0, 1, 5), (11 / 15, 0, 3, 3), (11 / 30, 0, 5, 1),
     (4 / 5, 1, 1, 4), (12 / 5, 1, 3, 2), (6 / 5, 1, 5, 0),
     (11 / 15, 2, 1, 3), (11 / 15, 2, 3, 1),
     (8 / 5, 3, 1, 2), (12 / 5, 3, 3, 0),
     (1 / 12, 4, 1, 1), (4 / 5, 5, 1, 0)]
  | ⟨2, _⟩ =>
    [(11 / 20, 0, 0, 6), (77 / 60, 0, 2, 4), (11 / 12, 0, 4, 2), (11 / 60, 0, 6, 0),
     (2 / 5, 1, 0, 5), (4 / 5, 1, 2, 3),
     (29 / 30, 2, 0, 4), (6 / 5, 2, 2, 2), (7 / 30, 2, 4, 0),
     (4 / 5, 3, 0, 3), (4 / 5, 3, 2, 1),
     (17 / 120, 4, 0, 2), (7 / 120, 4, 2, 0),
     (2 / 5, 5, 0, 1), (-29 / 120, 6, 0, 0)]

/-- Degree-6 polynomial lists `B₆ = x × ∇α₆` for the `J(‖x‖) / ‖x‖³` branch of `G`. -/
def ftildeB6List (i : Fin 3) : List (ℝ × ℕ × ℕ × ℕ) :=
  match i with
  | ⟨0, _⟩ =>
    [(-1 / 5, 0, 0, 6), (-4 / 5, 0, 2, 4), (-1 / 5, 0, 4, 2), (2 / 5, 0, 6, 0),
     (-11 / 60, 1, 0, 5), (-11 / 30, 1, 2, 3), (-11 / 60, 1, 4, 1),
     (-2 / 5, 2, 0, 4), (-3 / 5, 2, 2, 2), (3 / 5, 2, 4, 0),
     (-23 / 60, 3, 0, 3), (-23 / 60, 3, 2, 1),
     (-1 / 5, 4, 0, 2), (1 / 5, 4, 2, 0),
     (-29 / 120, 5, 0, 1)]
  | ⟨1, _⟩ =>
    [(11 / 60, 0, 1, 5), (11 / 30, 0, 3, 3), (11 / 60, 0, 5, 1),
     (-1 / 5, 1, 1, 4), (-3 / 5, 1, 3, 2), (-2 / 5, 1, 5, 0),
     (5 / 12, 2, 1, 3), (5 / 12, 2, 3, 1),
     (-2 / 5, 3, 1, 2), (-3 / 5, 3, 3, 0),
     (53 / 120, 4, 1, 1), (-1 / 5, 5, 1, 0)]
  | ⟨2, _⟩ =>
    [(-11 / 60, 0, 2, 4), (-11 / 30, 0, 4, 2), (-11 / 60, 0, 6, 0),
     (1 / 5, 1, 0, 5), (1, 1, 2, 3), (4 / 5, 1, 4, 1),
     (11 / 60, 2, 0, 4), (-1 / 20, 2, 2, 2), (-7 / 30, 2, 4, 0),
     (2 / 5, 3, 0, 3), (1, 3, 2, 1),
     (23 / 60, 4, 0, 2), (-7 / 120, 4, 2, 0),
     (1 / 5, 5, 0, 1), (29 / 120, 6, 0, 0)]

def ftildeA6 (i : Fin 3) : Euclidean 3 → ℝ := evalPoly3 (ftildeA6List i)
def ftildeB6 (i : Fin 3) : Euclidean 3 → ℝ := evalPoly3 (ftildeB6List i)

/-- Explicit closed-form global `C²` vector potential for `ftildeField` on `ftildeBall`. -/
def ftildePotentialG : VectorField := fun x =>
  coordEquivEuclidean 3 fun i =>
    radialHomogTerm 2 ftildePsi (ftildeA6 i) x +
      radialHomogTerm 2 ftildeJOverCube (ftildeB6 i) x

lemma ftildeA6_homog (i : Fin 3) (t : ℝ) (x : Euclidean 3) :
    ftildeA6 i (t • x) = t ^ 6 * ftildeA6 i x := by
  apply evalPoly3_homog
  fin_cases i <;> simp [ftildeA6List]

lemma ftildeB6_homog (i : Fin 3) (t : ℝ) (x : Euclidean 3) :
    ftildeB6 i (t • x) = t ^ 6 * ftildeB6 i x := by
  apply evalPoly3_homog
  fin_cases i <;> simp [ftildeB6List]

/-- `ftildePotentialG` is `C²` on all of `ftildeBall`. -/
theorem contDiffOn_ftildePotentialG :
    ContDiffOn ℝ 2 ftildePotentialG ftildeBall := by
  apply contDiffOn_vector_of_coordinates
  intro i
  change ContDiffOn ℝ 2
    (fun x => radialHomogTerm 2 ftildePsi (ftildeA6 i) x +
      radialHomogTerm 2 ftildeJOverCube (ftildeB6 i) x) ftildeBall
  have hpsi0 := ftildePsi_tendsto_nhdsGT_zero
  have hpsi1 : Tendsto (fun r : ℝ => ftildePsi r ^ 2) (𝓝[>] 0) (𝓝 0) := by
    simpa using hpsi0.pow 2
  have hpsi2 : Tendsto (fun r : ℝ => 2 * ftildePsi r ^ 3) (𝓝[>] 0) (𝓝 0) := by
    simpa using (hpsi0.pow 3).const_mul 2
  have hd_psi1 : ∀ r ∈ Ioo 0 1,
      HasDerivAt (fun t : ℝ => ftildePsi t ^ 2) ((2 * ftildePsi r ^ 3) / r) r := by
    intro r hr
    convert (hasDerivAt_ftildePsi hr.1 hr.2).pow 2 using 1
    ring
  have hc_psi2 : ContinuousOn (fun r : ℝ => 2 * ftildePsi r ^ 3) (Ioo 0 1) :=
    continuousOn_const.mul (continuousOn_ftildePsi_Ioo.pow 3)
  have htermA : ContDiffOn ℝ 2 (radialHomogTerm 2 ftildePsi (ftildeA6 i)) ftildeBall :=
    contDiffOn_two_radialHomogTerm6 hpsi0 hpsi1 hpsi2
      (fun r hr => hasDerivAt_ftildePsi hr.1 hr.2) hd_psi1 hc_psi2
      (contDiff_evalPoly3 (ftildeA6List i)) (ftildeA6_homog i)
  let g₁ : ℝ → ℝ := fun r => ftildePsi r ^ 2 - 3 * ftildeJOverCube r
  let g₂ : ℝ → ℝ := fun r => 2 * ftildePsi r ^ 3 - 3 * ftildePsi r ^ 2 + 9 * ftildeJOverCube r
  have hJ0 := ftildeJOverCube_tendsto_nhdsGT_zero
  have hg₁0 : Tendsto g₁ (𝓝[>] 0) (𝓝 0) := by
    simpa [g₁] using hpsi1.sub (hJ0.const_mul 3)
  have hg₂0 : Tendsto g₂ (𝓝[>] 0) (𝓝 0) := by
    simpa [g₂] using (hpsi2.sub (hpsi1.const_mul 3)).add (hJ0.const_mul 9)
  have hd_g₁ : ∀ r ∈ Ioo 0 1, HasDerivAt g₁ (g₂ r / r) r := by
    intro r hr
    have h1 := hd_psi1 r hr
    have h2 := (hasDerivAt_ftildeJOverCube hr.1 hr.2).const_mul 3
    convert h1.sub h2 using 1
    simp only [g₂]
    field_simp [hr.1.ne']
    ring
  have hc_J : ContinuousOn ftildeJOverCube (Ioo 0 1) :=
    fun r hr => (hasDerivAt_ftildeJOverCube hr.1 hr.2).continuousAt.continuousWithinAt
  have hc_g₂ : ContinuousOn g₂ (Ioo 0 1) :=
    ((hc_psi2.sub (continuousOn_const.mul (continuousOn_ftildePsi_Ioo.pow 2))).add
      (continuousOn_const.mul hc_J))
  have htermB : ContDiffOn ℝ 2 (radialHomogTerm 2 ftildeJOverCube (ftildeB6 i)) ftildeBall :=
    contDiffOn_two_radialHomogTerm6 hJ0 hg₁0 hg₂0
      (fun r hr => hasDerivAt_ftildeJOverCube hr.1 hr.2) hd_g₁ hc_g₂
      (contDiff_evalPoly3 (ftildeB6List i)) (ftildeB6_homog i)
  exact htermA.add htermB

lemma ftildeDir_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) :
    ftildeDir (t • x) = ftildeDir x := by
  by_cases hx : x = 0
  · simp [hx, ftildeDir]
  · simp only [ftildeDir, norm_smul, Real.norm_of_nonneg ht.le, mul_inv_rev, smul_smul]
    congr 1
    field_simp [ht.ne']

lemma ftildeV_smul_pos {t : ℝ} (ht : 0 < t) {x : Euclidean 3} (hx : x ≠ 0) (n : Fin 3) :
    ftildeV (t • x) n = t * ftildeV x n := by
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg ht.le]
  have hdir : ftildeDir (t • x) = ftildeDir x := ftildeDir_smul_pos ht x
  fin_cases n <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · simp only [ftildeV, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero,
      ftildeV₁, htx, hx, ↓reduceIte, hnorm, hdir]
    ring
  · simp only [ftildeV, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_one,
      Matrix.cons_val_zero, ftildeV₂, htx, hx, ↓reduceIte, hnorm, hdir]
    ring
  · simp only [ftildeV, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, ftildeV₃, htx, hx, ↓reduceIte, hnorm, hdir]
    ring

/-- By Euler's homogeneous function theorem for the degree-1 field `ftildeV`,
`∑ a, θ a * ftildeD a n θ = ftildeV θ n` for every `θ ≠ 0`, simplifying `ftildeQ θ` to `θ · V(θ)`. -/
lemma ftildeQ_eq_sum_mul_ftildeV {θ : Euclidean 3} (hθ : θ ≠ 0) :
    ftildeQ θ = ∑ n : Fin 3, θ n * ftildeV θ n := by
  unfold ftildeQ
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  have hd_line : HasDerivAt (fun t : ℝ => ftildeV (t • θ) n) (ftildeV θ n) 1 := by
    have hev : (fun t : ℝ => ftildeV (t • θ) n) =ᶠ[𝓝 1] fun t : ℝ => t * ftildeV θ n := by
      filter_upwards [Ioi_mem_nhds zero_lt_one] with t ht
      exact ftildeV_smul_pos ht hθ n
    have hmul : HasDerivAt (fun t : ℝ => t * ftildeV θ n) (ftildeV θ n) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const (ftildeV θ n)
    exact hmul.congr_of_eventuallyEq hev
  have hd_chain : HasDerivAt (fun t : ℝ => ftildeV (t • θ) n)
      (fderiv ℝ (fun y => ftildeV y n) θ θ) 1 := by
    have hsmul : HasDerivAt (fun t : ℝ => t • θ) θ 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const θ
    have hf : HasFDerivAt (fun y => ftildeV y n) (fderiv ℝ (fun y => ftildeV y n) θ)
        ((1 : ℝ) • θ) := by
      simpa using (differentiableAt_ftildeV_coordinate hθ n).hasFDerivAt
    exact hf.comp_hasDerivAt 1 hsmul
  have heq := hd_chain.unique hd_line
  rw [← heq, linear_apply_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro a _
  rw [mul_comm]
  rfl

/-- Homogeneous degree-7 polynomial numerators `‖x‖⁶ * ftildeV x m` for `x ≠ 0`. -/
def ftildeV7 (m : Fin 3) (x : Euclidean 3) : ℝ :=
  let s := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
  match m with
  | ⟨0, _⟩ => x 0 ^ 6 * x 1
  | ⟨1, _⟩ =>
      (x 0 * s ^ 2 + (1 / 2 : ℝ) * x 0 ^ 3 * s - (1 / 4 : ℝ) * x 0 ^ 5) * (s + x 1 ^ 2) -
        x 0 * x 1 ^ 2 * (s ^ 2 + (3 / 2 : ℝ) * x 0 ^ 2 * s - (5 / 4 : ℝ) * x 0 ^ 4) +
        2 * x 1 ^ 4 * x 2 * s
  | ⟨2, _⟩ =>
      x 1 * x 2 * (-x 0 ^ 3 * s + x 0 ^ 5) + 2 * x 1 ^ 3 * s * (2 * s - x 1 ^ 2)

lemma norm_pow_six_mul_ftildeV {x : Euclidean 3} (hx : x ≠ 0) (m : Fin 3) :
    ‖x‖ ^ 6 * ftildeV x m = ftildeV7 m x := by
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
    simpa [Fin.sum_univ_three] using (norm_sq_eq_sum_three x).symm
  fin_cases m <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · simp only [ftildeV, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero,
      ftildeV₁, hx, ↓reduceIte, ftildeTh, ftildeDir, PiLp.smul_apply, smul_eq_mul, ftildeV7]
    field_simp [hr0.ne']
  · simp only [ftildeV, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_one,
      Matrix.cons_val_zero, ftildeV₂, hx, ↓reduceIte, ftildeTh, ftildeDir,
      PiLp.smul_apply, smul_eq_mul, ftildeB, ftildeB', ftildeV7, hs]
    field_simp [hr0.ne']
  · simp only [ftildeV, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons, ftildeV₃, hx, ↓reduceIte, ftildeTh, ftildeDir,
      PiLp.smul_apply, smul_eq_mul, ftildeB, ftildeB', ftildeV7, hs]
    field_simp [hr0.ne']
    ring

lemma ftildeQ_dir_eq {x : Euclidean 3} (hx : x ≠ 0) :
    ftildeQ (ftildeDir x) =
      (x 0 * ftildeV7 0 x + x 1 * ftildeV7 1 x + x 2 * ftildeV7 2 x) / ‖x‖ ^ 8 := by
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hdir_ne : ftildeDir x ≠ 0 := by
    simp [ftildeDir, hx, hr0.ne']
  rw [ftildeQ_eq_sum_mul_ftildeV hdir_ne]
  have hv (n : Fin 3) : ftildeV (ftildeDir x) n = ftildeV7 n x / ‖x‖ ^ 7 := by
    have h1 := ftildeV_smul_pos (inv_pos.mpr hr0) hx n
    have h6 := norm_pow_six_mul_ftildeV hx n
    change ftildeV (‖x‖⁻¹ • x) n = _
    rw [h1]
    field_simp [hr0.ne']
    linarith [h6]
  simp only [Fin.sum_univ_three, hv]
  simp only [ftildeDir, PiLp.smul_apply, smul_eq_mul]
  field_simp [hr0.ne']

lemma ftildePotentialG_partial_zero (i j : Fin 3) :
    coordinatePartial (fun y => ftildePotentialG y i) 0 j = 0 := by
  have htr : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdA := hasFDerivAt_radialHomogTerm_zero (m := 2) (d := 6) (P := ftildeA6 i) (by omega)
    (by simpa using ftildePsi_tendsto_nhdsGT_zero.mul htr)
    (contDiff_evalPoly3 (ftildeA6List i)) (ftildeA6_homog i)
  have hdB := hasFDerivAt_radialHomogTerm_zero (m := 2) (d := 6) (P := ftildeB6 i) (by omega)
    (by simpa using ftildeJOverCube_tendsto_nhdsGT_zero.mul htr)
    (contDiff_evalPoly3 (ftildeB6List i)) (ftildeB6_homog i)
  have hfun : (fun y => ftildePotentialG y i) =
      fun y => radialHomogTerm 2 ftildePsi (ftildeA6 i) y +
        radialHomogTerm 2 ftildeJOverCube (ftildeB6 i) y := by
    funext y
    simp [ftildePotentialG]
  rw [hfun, coordinatePartial_add hdA.differentiableAt hdB.differentiableAt j,
    coordinatePartial_eq_fderiv hdA.differentiableAt j,
    coordinatePartial_eq_fderiv hdB.differentiableAt j, hdA.fderiv, hdB.fderiv]
  simp

lemma ftildePotentialG_partial_ne_zero {x : Euclidean 3} (hx : x ∈ ftildeBall) (hx0 : x ≠ 0)
    (i j : Fin 3) :
    coordinatePartial (fun y => ftildePotentialG y i) x j =
      ftildePsi ‖x‖ ^ 2 * ((x j * (ftildeA6 i x + ftildeB6 i x)) / ‖x‖ ^ 6) +
      ftildePsi ‖x‖ * (((x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) * evalPoly3 (derivPoly3 j (ftildeA6List i)) x -
        4 * (x j * ftildeA6 i x)) / ‖x‖ ^ 6) +
      ftildeJ ‖x‖ * (((x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) * evalPoly3 (derivPoly3 j (ftildeB6List i)) x -
        7 * (x j * ftildeB6 i x)) / ‖x‖ ^ 9) := by
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hdA := hasFDerivAt_radialHomogTerm_ne_zero (m := 2) (P := ftildeA6 i)
    (fun r hr => hasDerivAt_ftildePsi hr.1 hr.2)
    (contDiff_evalPoly3 (ftildeA6List i)) hx hx0
  have hdB := hasFDerivAt_radialHomogTerm_ne_zero (m := 2) (P := ftildeB6 i)
    (fun r hr => hasDerivAt_ftildeJOverCube hr.1 hr.2)
    (contDiff_evalPoly3 (ftildeB6List i)) hx hx0
  have hfun : (fun y => ftildePotentialG y i) =
      fun y => radialHomogTerm 2 ftildePsi (ftildeA6 i) y +
        radialHomogTerm 2 ftildeJOverCube (ftildeB6 i) y := by
    funext y
    simp [ftildePotentialG]
  rw [hfun, coordinatePartial_add hdA.1 hdB.1 j, hdA.2 j, hdB.2 j]
  simp only [Fin.sum_univ_three, ftildeA6, ftildeB6, coordinatePartial_evalPoly3, ftildeJOverCube]
  norm_num
  field_simp [hr0.ne']
  ring

lemma ftilde_poly_cross_AB (x : Euclidean 3) :
    (x 1 * (ftildeA6 2 x + ftildeB6 2 x) - x 2 * (ftildeA6 1 x + ftildeB6 1 x) = 0) ∧
    (x 2 * (ftildeA6 0 x + ftildeB6 0 x) - x 0 * (ftildeA6 2 x + ftildeB6 2 x) = 0) ∧
    (x 0 * (ftildeA6 1 x + ftildeB6 1 x) - x 1 * (ftildeA6 0 x + ftildeB6 0 x) = 0) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [ftildeA6, ftildeB6, evalPoly3, ftildeA6List, ftildeB6List,
        List.map, List.sum_cons, List.sum_nil, ftildeMonomial]
      ring

lemma ftilde_poly_curl_A6 (x : Euclidean 3) :
    let s := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
    ((s * evalPoly3 (derivPoly3 1 (ftildeA6List 2)) x - 4 * (x 1 * ftildeA6 2 x)) -
      (s * evalPoly3 (derivPoly3 2 (ftildeA6List 1)) x - 4 * (x 2 * ftildeA6 1 x)) =
        ftildeV7 0 x) ∧
    ((s * evalPoly3 (derivPoly3 2 (ftildeA6List 0)) x - 4 * (x 2 * ftildeA6 0 x)) -
      (s * evalPoly3 (derivPoly3 0 (ftildeA6List 2)) x - 4 * (x 0 * ftildeA6 2 x)) =
        ftildeV7 1 x) ∧
    ((s * evalPoly3 (derivPoly3 0 (ftildeA6List 1)) x - 4 * (x 0 * ftildeA6 1 x)) -
      (s * evalPoly3 (derivPoly3 1 (ftildeA6List 0)) x - 4 * (x 1 * ftildeA6 0 x)) =
        ftildeV7 2 x) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [ftildeA6, ftildeV7, evalPoly3, derivPoly3, ftildeA6List,
        List.map, List.sum_cons, List.sum_nil, ftildeMonomial]
      norm_num
      ring

lemma ftilde_poly_curl_B6 (x : Euclidean 3) :
    let s := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2
    let dotV := x 0 * ftildeV7 0 x + x 1 * ftildeV7 1 x + x 2 * ftildeV7 2 x
    (((s * evalPoly3 (derivPoly3 1 (ftildeB6List 2)) x - 7 * (x 1 * ftildeB6 2 x)) -
        (s * evalPoly3 (derivPoly3 2 (ftildeB6List 1)) x - 7 * (x 2 * ftildeB6 1 x))) * s =
      -dotV * x 0) ∧
    (((s * evalPoly3 (derivPoly3 2 (ftildeB6List 0)) x - 7 * (x 2 * ftildeB6 0 x)) -
        (s * evalPoly3 (derivPoly3 0 (ftildeB6List 2)) x - 7 * (x 0 * ftildeB6 2 x))) * s =
      -dotV * x 1) ∧
    (((s * evalPoly3 (derivPoly3 0 (ftildeB6List 1)) x - 7 * (x 0 * ftildeB6 1 x)) -
        (s * evalPoly3 (derivPoly3 1 (ftildeB6List 0)) x - 7 * (x 1 * ftildeB6 0 x))) * s =
      -dotV * x 2) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp only [ftildeB6, ftildeV7, evalPoly3, derivPoly3, ftildeB6List,
        List.map, List.sum_cons, List.sum_nil, ftildeMonomial]
      norm_num
      ring

lemma ftildeW_coord_eq {x : Euclidean 3} (hx0 : x ≠ 0) (m : Fin 3) {Bdiff : ℝ}
    (hB : Bdiff * ‖x‖ ^ 2 =
      -(x 0 * ftildeV7 0 x + x 1 * ftildeV7 1 x + x 2 * ftildeV7 2 x) * x m) :
    ftildeW x m = ftildeJ ‖x‖ * (Bdiff / ‖x‖ ^ 9) := by
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  calc
    ftildeW x m
        = (ftildeJ ‖x‖ * (-(x 0 * ftildeV7 0 x + x 1 * ftildeV7 1 x + x 2 * ftildeV7 2 x) * x m)) /
            ‖x‖ ^ 11 := by
          simp only [ftildeW, hx0, ↓reduceIte, ftildeQ_dir_eq hx0, PiLp.smul_apply, smul_eq_mul]
          simp only [ftildeDir, PiLp.smul_apply, smul_eq_mul]
          field_simp [hr0.ne']
    _ = (ftildeJ ‖x‖ * (Bdiff * ‖x‖ ^ 2)) / ‖x‖ ^ 11 := by rw [← hB]
    _ = ftildeJ ‖x‖ * (Bdiff / ‖x‖ ^ 9) := by field_simp [hr0.ne']

/-- `curl ftildePotentialG` equals `ftildeField` pointwise on all of `ftildeBall`. -/
theorem curl_ftildePotentialG_eq_ftildeField :
    EqOn (curl ftildePotentialG) ftildeField ftildeBall := by
  intro x hx
  by_cases hx0 : x = 0
  · subst hx0
    ext m
    fin_cases m <;>
      simp [curl, ftildePotentialG_partial_zero, ftildeField, ftildeF, ftildeW]
  · have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
      simpa [Fin.sum_univ_three] using (norm_sq_eq_sum_three x).symm
    have hV (m : Fin 3) : ftildeV x m = ftildeV7 m x / ‖x‖ ^ 6 := by
      rw [eq_div_iff (pow_ne_zero 6 hr0.ne'), mul_comm]
      exact norm_pow_six_mul_ftildeV hx0 m
    obtain ⟨hcAB0, hcAB1, hcAB2⟩ := ftilde_poly_cross_AB x
    obtain ⟨hcA0, hcA1, hcA2⟩ := ftilde_poly_curl_A6 x
    obtain ⟨hcB0, hcB1, hcB2⟩ := ftilde_poly_curl_B6 x
    dsimp only at hcA0 hcA1 hcA2 hcB0 hcB1 hcB2
    rw [hs] at hcA0 hcA1 hcA2 hcB0 hcB1 hcB2
    have hW0 := ftildeW_coord_eq hx0 0 hcB0
    have hW1 := ftildeW_coord_eq hx0 1 hcB1
    have hW2 := ftildeW_coord_eq hx0 2 hcB2
    ext m
    fin_cases m <;> dsimp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    · simp only [curl, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero,
        ftildePotentialG_partial_ne_zero hx hx0, ftildeField, PiLp.add_apply, hW0,
        ftildeF, hx0, ↓reduceIte, PiLp.smul_apply, smul_eq_mul, hV, hs]
      rw [sub_eq_zero.mp hcAB0, sub_eq_iff_eq_add.mp hcA0]
      simp only [div_eq_mul_inv]
      ring
    · simp only [curl, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_one,
        Matrix.cons_val_zero, ftildePotentialG_partial_ne_zero hx hx0, ftildeField,
        PiLp.add_apply, hW1, ftildeF, hx0, ↓reduceIte, PiLp.smul_apply, smul_eq_mul, hV, hs]
      rw [sub_eq_zero.mp hcAB1, sub_eq_iff_eq_add.mp hcA1]
      simp only [div_eq_mul_inv]
      ring
    · simp only [curl, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons, ftildePotentialG_partial_ne_zero hx hx0,
        ftildeField, PiLp.add_apply, hW2, ftildeF, hx0, ↓reduceIte, PiLp.smul_apply,
        smul_eq_mul, hV, hs]
      rw [sub_eq_zero.mp hcAB2, sub_eq_iff_eq_add.mp hcA2]
      simp only [div_eq_mul_inv]
      ring

/-- `ftildeField` admits a global `C²` vector potential on `ftildeBall`. -/
theorem exists_c2_vectorPotential_ftilde :
    ∃ G : VectorField, ContDiffOn ℝ 2 G ftildeBall ∧ EqOn (curl G) ftildeField ftildeBall :=
  ⟨ftildePotentialG, contDiffOn_ftildePotentialG, curl_ftildePotentialG_eq_ftildeField⟩

/-- `ftildeField` is `C¹` on `ftildeBall` (clause 1 of `ftilde_witness` holds). -/
theorem contDiffOn_ftildeField :
    ContDiffOn ℝ 1 ftildeField ftildeBall :=
  (contDiffOn_curl (r := 1) Metric.isOpen_ball contDiffOn_ftildePotentialG).congr
    curl_ftildePotentialG_eq_ftildeField.symm

/-- `ftildeField` is divergence-free on `ftildeBall` (clause 2 of `ftilde_witness` holds). -/
theorem divergence_ftildeField_eq_zero :
    EqOn (divergence ftildeField) 0 ftildeBall := by
  intro x hx
  have hdivG := divergence_curl_eq_zero Metric.isOpen_ball contDiffOn_ftildePotentialG hx
  have hcongr : divergence ftildeField x = divergence (curl ftildePotentialG) x := by
    simp only [divergence]
    apply Finset.sum_congr rfl
    intro i _
    exact coordinatePartial_congr_of_eqOn Metric.isOpen_ball
      (fun y hy => congrArg (fun v : Euclidean 3 => v i)
        (curl_ftildePotentialG_eq_ftildeField hy).symm) hx i
  exact hcongr.trans hdivG

/-- `CompatibleCurlRows ftildeBall ftildeField` holds. -/
theorem compatibleCurlRows_ftilde :
    CompatibleCurlRows ftildeBall ftildeField :=
  (c2_vectorPotential_iff_compatibleCurlRows ballIdentityEquivalence
    Metric.isOpen_ball Metric.isOpen_ball (convex_ball 0 1) ftildeField).mp
    exists_c2_vectorPotential_ftilde

/-- `SymmetricCurlCorrection ftildeBall ftildeField` holds. -/
theorem symmetricCurlCorrection_ftilde :
    SymmetricCurlCorrection ftildeBall ftildeField :=
  (compatibleCurlRows_iff_symmetricCurlCorrection contDiffOn_ftildeField).mp
    compatibleCurlRows_ftilde

/-- **Main positive theorem:** `SymmetricCurlSystem ftildeBall ftildeField` holds on `ftildeBall`. -/
theorem symmetricCurlSystem_ftilde :
    SymmetricCurlSystem ftildeBall ftildeField :=
  (symmetricCurlCorrection_iff_system Metric.isOpen_ball contDiffOn_ftildeField
    divergence_ftildeField_eq_zero).mp symmetricCurlCorrection_ftilde

/-- **Refutation of clause 3:** the Stage 3 target clause
`¬ SymmetricCurlSystem ftildeBall ftildeField` is false. -/
theorem not_ftilde_clause3 :
    ¬ (¬ SymmetricCurlSystem ftildeBall ftildeField) :=
  not_not_intro symmetricCurlSystem_ftilde

/-- The full conjunction stated in `ftilde_witness` is false on the merits, solely
because its final clause `¬ SymmetricCurlSystem ftildeBall ftildeField` fails. -/
theorem not_ftilde_witness_goal :
    ¬ (IsOpen ftildeBall ∧ Convex ℝ ftildeBall ∧
      ContDiffOn ℝ 1 ftildeField ftildeBall ∧
      EqOn (divergence ftildeField) 0 ftildeBall ∧
      ¬ SymmetricCurlSystem ftildeBall ftildeField) := by
  rintro ⟨_, _, _, _, hno⟩
  exact hno symmetricCurlSystem_ftilde

end Rudin.PMA.Chapter10

/-! ## Section 4: Module-wide axiom audit -/

run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10.FtildeHarmonic
    #[`Rudin.PMA.Chapter10.l6_pointwise_fourier_orthogonality,
      `Rudin.PMA.Chapter10.laplacian_ftildeCubicGaugePoly,
      `Rudin.PMA.Chapter10.thirdPartial_ftildeCubicGaugePoly_eq_ftildeC,
      `Rudin.PMA.Chapter10.contDiffOn_two_ftildeLocalGauge,
      `Rudin.PMA.Chapter10.tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge,
      `Rudin.PMA.Chapter10.contDiffOn_ftildePotentialG,
      `Rudin.PMA.Chapter10.curl_ftildePotentialG_eq_ftildeField,
      `Rudin.PMA.Chapter10.exists_c2_vectorPotential_ftilde,
      `Rudin.PMA.Chapter10.contDiffOn_ftildeField,
      `Rudin.PMA.Chapter10.divergence_ftildeField_eq_zero,
      `Rudin.PMA.Chapter10.symmetricCurlSystem_ftilde,
      `Rudin.PMA.Chapter10.not_ftilde_clause3,
      `Rudin.PMA.Chapter10.not_ftilde_witness_goal]

#print axioms Rudin.PMA.Chapter10.l6_pointwise_fourier_orthogonality
#print axioms Rudin.PMA.Chapter10.laplacian_ftildeCubicGaugePoly
#print axioms Rudin.PMA.Chapter10.thirdPartial_ftildeCubicGaugePoly_eq_ftildeC
#print axioms Rudin.PMA.Chapter10.contDiffOn_two_ftildeLocalGauge
#print axioms Rudin.PMA.Chapter10.tendsto_thirdPartial_traceFreeHessian_ftildeLocalGauge
#print axioms Rudin.PMA.Chapter10.contDiffOn_ftildePotentialG
#print axioms Rudin.PMA.Chapter10.curl_ftildePotentialG_eq_ftildeField
#print axioms Rudin.PMA.Chapter10.exists_c2_vectorPotential_ftilde
#print axioms Rudin.PMA.Chapter10.contDiffOn_ftildeField
#print axioms Rudin.PMA.Chapter10.divergence_ftildeField_eq_zero
#print axioms Rudin.PMA.Chapter10.symmetricCurlSystem_ftilde
#print axioms Rudin.PMA.Chapter10.not_ftilde_clause3
#print axioms Rudin.PMA.Chapter10.not_ftilde_witness_goal

