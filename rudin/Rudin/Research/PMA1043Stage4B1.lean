import Rudin.PMA.Chapter10.FtildeCZPrep

/-!
# Stage 4 Branch B1 — Full All-Gauge Planar Duality, Spin-3 Obstruction, and Gliding-Hump Counterexample Scaffold

Following the Stage A verdict for Rudin PMA Theorem 10.43 (`#29`), where the
four-component all-gauge planar duality inequality `(⋆)` fails via the spin-3
harmonic-cubic specialization and a 3-ray stopped-martingale staircase, this
module formalizes the complete kernel-checked Stage B1 functional-analytic and
rectangular integration-by-parts reduction in Lean:

1. **Full 4-Component All-Gauge Planar Duality (`planar_c2_div_allGauge_duality`,
   `planar_c2_div_allGauge_bound`):**
   For *any* `C²` planar vector field `V` (with NO `C³` hypothesis on `V`) and
   any `C²` test triple `(φ₁, φ₂, φ₃)` whose tangential first partials vanish on
   `∂([a, b] × [c, d])`,
   `∫_c^d ∫_a^b planarDivergence V · (∂_x ∂_y φ₂)`
   `  = -∫_c^d ∫_a^b ((∂_x² V₁)(∂_y φ₁) - (∂_x∂_y V₁)(∂_x φ₁ - ∂_y φ₂)`
   `                 + (∂_x∂_y V₀)(∂_x φ₂ - ∂_y φ₃) + (∂_y² V₀)(∂_x φ₃))`,
   yielding the exact `L∞–L¹` bound `(⋆)` on `[a, b] × [c, d]`.

2. **Spin-3 Harmonic-Cubic Specialization (`planar_c2_div_spin3_duality`,
   `planar_c2_div_spin3_bound`):**
   Substituting `(φ₁, φ₂, φ₃) = (3∂_x² U - ∂_y² U, 8∂_x∂_y U, -∂_x² U + 3∂_y² U)`
   for any `C⁴` test function `U` collapses all four gauge components into
   multiples of the two spin-3 Cauchy–Riemann cubic operators
   `spin3A1 U = (∂_x³ - 3∂_x∂_y²) U` and `spin3A2 U = (3∂_x²∂_y - ∂_y³) U`,
   giving
   `2 |∫_c^d ∫_a^b planarDivergence V · (∂_x² ∂_y² U)|`
   `  ≤ M ∫_c^d ∫_a^b (|spin3A1 U| + |spin3A2 U|)`.
   We also prove `vanishesThirdPartialsOnRectBdry_of_zero_outside_subrect`, so any
   compactly supported `U` inside `(a, b) × (c, d)` discharges the boundary
   hypothesis automatically.

3. **Compact-Box Uniform Bound & Gliding-Hump Disproof Scaffolds
   (`not_pma10_43_contract_of_allGauge_blowup`,
    `not_pma10_43_contract_of_spin3_blowup`,
    `not_pma10_43_contract_of_spin3_gliding_hump`,
    `not_pma10_43_contract_of_fourth_order_blowup`):**
   Using compactness of `[A, B] × [C, D]` to bound the continuous second partials
   of any `C²` solution `V` and `PMA1043Planar.pma10_43_contract_implies_planarDivergence`,
   any `C¹` planar datum `f` (including a disjoint-box gliding-hump sum
   `f = Σ ε_k h_k` on sub-rectangles `[a_k, b_k] × [c_k, d_k] ⊆ [A, B] × [C, D]`)
   whose local test ratios diverge refutes `pma10_43_contract` with zero
   singular-integral or Fourier prerequisites.

4. **3-Ray Spin-3 Coincidence & Quantitative Haar-Shift Equidistribution
   (`spin3_planeWave_identities`, `spin3_three_ray_obstruction`,
    `antiperiodic_haar_shift_bound_1d`):**
   Kernel-checks the two analytic/algebraic pillars of the 3-ray staircase:
   (a) the exact 3-to-1 symbol coincidence `(spin3A1, spin3A2) = (Λ³ g''', 0)` on
   all three `120°` zero-sum unit rays `(1, 0), (-1/2, ±√3/2)`, and
   (b) the sharp quantitative 1D Haar-shift equidistribution bound
   `|∫_0^1 F(x) g(N x) dx| ≤ (L / (4 N)) ∫_0^1 |g(t)| dt` for any Lipschitz `F`
   and `(1/2)`-antiperiodic wave `g` without requiring `F` to be periodic.
-/

noncomputable section
set_option autoImplicit false

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators Interval

namespace Rudin.PMA.Chapter10

/-! ### Section 1: Planar Partial Interface and Linearity Lemmas -/

private lemma planarPt_eq_linComb (x y : ℝ) :
    planarPt x y = x • coordinateVector 2 0 + y • coordinateVector 2 1 := by
  ext i
  fin_cases i <;> simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planarPt_apply_zero (x y : ℝ) : planarPt x y 0 = x := by
  rw [planarPt_eq_linComb]
  simp [coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] lemma planarPt_apply_one (x y : ℝ) : planarPt x y 1 = y := by
  rw [planarPt_eq_linComb]
  simp [coordinateVector, EuclideanSpace.basisFun_apply]

private lemma diff_of_contDiff_succ_b1 {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) : Differentiable ℝ f :=
  hf.differentiable (by norm_cast)

lemma contDiff_planarDx_b1 {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) : ContDiff ℝ (r : ℕ) (planarDx f) := by
  unfold planarDx
  exact contDiffOn_univ.mp (contDiffOn_coordinatePartial (r := r) isOpen_univ hf.contDiffOn 0)

lemma contDiff_planarDy_b1 {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) : ContDiff ℝ (r : ℕ) (planarDy f) := by
  unfold planarDy
  exact contDiffOn_univ.mp (contDiffOn_coordinatePartial (r := r) isOpen_univ hf.contDiffOn 1)

lemma planarDx_planarDy_comm_b1 {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 2 : ℕ) f) (q : Euclidean 2) :
    planarDx (planarDy f) q = planarDy (planarDx f) q := by
  unfold planarDx planarDy
  exact coordinatePartial_commute isOpen_univ
    (hf.contDiffOn.of_le (by norm_cast; omega)) (mem_univ q) 1 0

lemma planarDivergence_eq_planarDx_add_planarDy_b1
    (V : PlanarVectorField) (q : Euclidean 2) :
    planarDivergence V q =
      planarDx (fun p => V p 0) q + planarDy (fun p => V p 1) q := by
  unfold planarDivergence planarDx planarDy
  rfl

private lemma hasDerivAt_planarPt_x_b1 {f : Euclidean 2 → ℝ}
    (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun s : ℝ => f (planarPt s y)) (planarDx f (planarPt x y)) x := by
  have hpt : HasDerivAt (fun s : ℝ => planarPt s y) (coordinateVector 2 0) x := by
    have hrew : (fun s : ℝ => planarPt s y) =
        fun s : ℝ => y • coordinateVector 2 1 + s • coordinateVector 2 0 := by
      funext s; rw [planarPt_eq_linComb, add_comm]
    rw [hrew]
    simpa [one_smul] using
      ((hasDerivAt_id x).smul_const (coordinateVector 2 0)).const_add (y • coordinateVector 2 1)
  have hcomp := (hf (planarPt x y)).hasFDerivAt.comp_hasDerivAt x hpt
  unfold planarDx
  rwa [coordinatePartial_eq_fderiv (hf (planarPt x y))]

private lemma hasDerivAt_planarPt_y_b1 {f : Euclidean 2 → ℝ}
    (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f (planarPt x t)) (planarDy f (planarPt x y)) y := by
  have hpt : HasDerivAt (fun t : ℝ => planarPt x t) (coordinateVector 2 1) y := by
    have hrew : (fun t : ℝ => planarPt x t) =
        fun t : ℝ => x • coordinateVector 2 0 + t • coordinateVector 2 1 := by
      funext t; rw [planarPt_eq_linComb]
    rw [hrew]
    simpa [one_smul] using
      ((hasDerivAt_id y).smul_const (coordinateVector 2 1)).const_add (x • coordinateVector 2 0)
  have hcomp := (hf (planarPt x y)).hasFDerivAt.comp_hasDerivAt y hpt
  unfold planarDy
  rwa [coordinatePartial_eq_fderiv (hf (planarPt x y))]

private lemma continuous_planarPt_uncurry :
    Continuous (fun q : ℝ × ℝ => planarPt q.1 q.2) := by
  have hrew : (fun q : ℝ × ℝ => planarPt q.1 q.2) =
      fun q : ℝ × ℝ => q.1 • coordinateVector 2 0 + q.2 • coordinateVector 2 1 := by
    funext q; exact planarPt_eq_linComb q.1 q.2
  rw [hrew]
  exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

private lemma cont_planarPt_uncurry_b1 {f : Euclidean 2 → ℝ} (hf : Continuous f) :
    Continuous (Function.uncurry fun x y : ℝ => f (planarPt x y)) :=
  hf.comp continuous_planarPt_uncurry

private lemma cont_planarPt_mul_b1 {f g : Euclidean 2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (Function.uncurry fun x y : ℝ => f (planarPt x y) * g (planarPt x y)) :=
  cont_planarPt_uncurry_b1 (hf.mul hg)

private lemma planar_prod_integrableOn_b1 {a b c d : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : Continuous (Function.uncurry G)) :
    IntegrableOn (Function.uncurry G) (uIoc a b ×ˢ uIoc c d) :=
  (hG.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

private lemma ibp_1d_zero_boundary_b1 {a b : ℝ} {u v u' v' : ℝ → ℝ}
    (hu : ∀ s ∈ uIcc a b, HasDerivAt u (u' s) s)
    (hv : ∀ s ∈ uIcc a b, HasDerivAt v (v' s) s)
    (hcu : Continuous u) (hcv : Continuous v)
    (hcu' : Continuous u') (hcv' : Continuous v')
    (hva : v a = 0) (hvb : v b = 0) :
    (∫ s in a..b, u' s * v s) = -(∫ s in a..b, u s * v' s) := by
  have hprod : ∀ s ∈ uIcc a b, HasDerivAt (fun t => u t * v t) (u' s * v s + u s * v' s) s :=
    fun s hs => (hu s hs).mul (hv s hs)
  have hi1 : IntervalIntegrable (fun s => u' s * v s) volume a b :=
    (hcu'.mul hcv).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun s => u s * v' s) volume a b :=
    (hcu.mul hcv').intervalIntegrable a b
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2, hva, hvb, mul_zero, mul_zero, sub_self] at hftc
  linarith

private lemma ibp_1d_zero_boundary_right_b1 {a b : ℝ} {u v u' v' : ℝ → ℝ}
    (hu : ∀ s ∈ uIcc a b, HasDerivAt u (u' s) s)
    (hv : ∀ s ∈ uIcc a b, HasDerivAt v (v' s) s)
    (hcu : Continuous u) (hcv : Continuous v)
    (hcu' : Continuous u') (hcv' : Continuous v')
    (hva : v a = 0) (hvb : v b = 0) :
    (∫ s in a..b, u s * v' s) = -(∫ s in a..b, u' s * v s) := by
  have h := ibp_1d_zero_boundary_b1 hu hv hcu hcv hcu' hcv' hva hvb
  linarith

private lemma planarDx_add {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDx (fun q => f q + g q) p = planarDx f p + planarDx g p := by
  unfold planarDx
  change coordinatePartial (f + g) p 0 = _
  rw [coordinatePartial_eq_fderiv (hf.add hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [add_apply] using
    congrArg (fun A : Euclidean 2 →L[ℝ] ℝ => A (coordinateVector 2 0)) (fderiv_add hf hg)

private lemma planarDy_add {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDy (fun q => f q + g q) p = planarDy f p + planarDy g p := by
  unfold planarDy
  change coordinatePartial (f + g) p 1 = _
  rw [coordinatePartial_eq_fderiv (hf.add hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [add_apply] using
    congrArg (fun A : Euclidean 2 →L[ℝ] ℝ => A (coordinateVector 2 1)) (fderiv_add hf hg)

private lemma planarDx_sub {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDx (fun q => f q - g q) p = planarDx f p - planarDx g p := by
  unfold planarDx
  change coordinatePartial (f - g) p 0 = _
  rw [coordinatePartial_eq_fderiv (hf.sub hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [sub_apply] using
    congrArg (fun A : Euclidean 2 →L[ℝ] ℝ => A (coordinateVector 2 0)) (fderiv_sub hf hg)

private lemma planarDy_sub {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDy (fun q => f q - g q) p = planarDy f p - planarDy g p := by
  unfold planarDy
  change coordinatePartial (f - g) p 1 = _
  rw [coordinatePartial_eq_fderiv (hf.sub hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [sub_apply] using
    congrArg (fun A : Euclidean 2 →L[ℝ] ℝ => A (coordinateVector 2 1)) (fderiv_sub hf hg)

private lemma planarDx_const_mul (c : ℝ) {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    planarDx (fun q => c * f q) p = c * planarDx f p := by
  unfold planarDx
  change coordinatePartial (c • f) p 0 = _
  rw [coordinatePartial_eq_fderiv (hf.const_smul c), coordinatePartial_eq_fderiv hf]
  simpa only [smul_apply, smul_eq_mul] using
    congrArg (fun A : Euclidean 2 →L[ℝ] ℝ => A (coordinateVector 2 0)) (fderiv_const_smul hf c)

private lemma planarDy_const_mul (c : ℝ) {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    planarDy (fun q => c * f q) p = c * planarDy f p := by
  unfold planarDy
  change coordinatePartial (c • f) p 1 = _
  rw [coordinatePartial_eq_fderiv (hf.const_smul c), coordinatePartial_eq_fderiv hf]
  simpa only [smul_apply, smul_eq_mul] using
    congrArg (fun A : Euclidean 2 →L[ℝ] ℝ => A (coordinateVector 2 1)) (fderiv_const_smul hf c)

private lemma planarDx_neg {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    planarDx (fun q => -f q) p = -planarDx f p := by
  simpa using planarDx_const_mul (-1) hf

private lemma planarDy_neg {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    planarDy (fun q => -f q) p = -planarDy f p := by
  simpa using planarDy_const_mul (-1) hf

private lemma planarDx_eq_zero_of_eqOn_zero {O : Set (Euclidean 2)} (hO : IsOpen O)
    {f : Euclidean 2 → ℝ} (hf : EqOn f 0 O) {p : Euclidean 2} (hp : p ∈ O) :
    planarDx f p = 0 := by
  unfold planarDx
  rw [coordinatePartial_congr_of_eqOn hO hf hp 0]
  simp [coordinatePartial]

private lemma planarDy_eq_zero_of_eqOn_zero {O : Set (Euclidean 2)} (hO : IsOpen O)
    {f : Euclidean 2 → ℝ} (hf : EqOn f 0 O) {p : Euclidean 2} (hp : p ∈ O) :
    planarDy f p = 0 := by
  unfold planarDy
  rw [coordinatePartial_congr_of_eqOn hO hf hp 1]
  simp [coordinatePartial]

/-! ### Section 2: Full 4-Component All-Gauge Planar Duality `(⋆)` -/

private lemma allGauge_ibp_pieceA {a b c d : ℝ}
    {v₀ φ₂ φ₃ : Euclidean 2 → ℝ}
    (hV0 : ContDiff ℝ (2 : ℕ) v₀)
    (hφ₂ : ContDiff ℝ (2 : ℕ) φ₂)
    (hφ₃ : ContDiff ℝ (2 : ℕ) φ₃)
    (hx_φ₃ : ∀ y : ℝ, planarDy φ₃ (planarPt a y) = 0 ∧ planarDy φ₃ (planarPt b y) = 0)
    (hy_φ₂ : ∀ x : ℝ, planarDx φ₂ (planarPt x c) = 0 ∧ planarDx φ₂ (planarPt x d) = 0)
    (hy_φ₃ : ∀ x : ℝ, planarDx φ₃ (planarPt x c) = 0 ∧ planarDx φ₃ (planarPt x d) = 0) :
    (∫ y in c..d, ∫ x in a..b,
      planarDx v₀ (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
    -((∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₀) (planarPt x y) *
          (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y))) +
      (∫ y in c..d, ∫ x in a..b,
        planarDy (planarDy v₀) (planarPt x y) * planarDx φ₃ (planarPt x y))) := by
  have hv₀_x : ContDiff ℝ (1 : ℕ) (planarDx v₀) := contDiff_planarDx_b1 (r := 1) hV0
  have hv₀_y : ContDiff ℝ (1 : ℕ) (planarDy v₀) := contDiff_planarDy_b1 (r := 1) hV0
  have hv₀_yx : ContDiff ℝ (0 : ℕ) (planarDy (planarDx v₀)) := contDiff_planarDy_b1 (r := 0) hv₀_x
  have hv₀_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy v₀)) := contDiff_planarDx_b1 (r := 0) hv₀_y
  have hv₀_yy : ContDiff ℝ (0 : ℕ) (planarDy (planarDy v₀)) := contDiff_planarDy_b1 (r := 0) hv₀_y
  have hφ₂_x : ContDiff ℝ (1 : ℕ) (planarDx φ₂) := contDiff_planarDx_b1 (r := 1) hφ₂
  have hφ₂_y : ContDiff ℝ (1 : ℕ) (planarDy φ₂) := contDiff_planarDy_b1 (r := 1) hφ₂
  have hφ₂_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy φ₂)) := contDiff_planarDx_b1 (r := 0) hφ₂_y
  have hφ₂_yx : ContDiff ℝ (0 : ℕ) (planarDy (planarDx φ₂)) := contDiff_planarDy_b1 (r := 0) hφ₂_x
  have hφ₃_x : ContDiff ℝ (1 : ℕ) (planarDx φ₃) := contDiff_planarDx_b1 (r := 1) hφ₃
  have hφ₃_y : ContDiff ℝ (1 : ℕ) (planarDy φ₃) := contDiff_planarDy_b1 (r := 1) hφ₃
  have hφ₃_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy φ₃)) := contDiff_planarDx_b1 (r := 0) hφ₃_y
  have hφ₃_yx : ContDiff ℝ (0 : ℕ) (planarDy (planarDx φ₃)) := contDiff_planarDy_b1 (r := 0) hφ₃_x
  have hcomm_φ₂ : planarDx (planarDy φ₂) = planarDy (planarDx φ₂) :=
    funext fun q => planarDx_planarDy_comm_b1 (r := 0) hφ₂ q
  have hcomm_v₀ : planarDy (planarDx v₀) = planarDx (planarDy v₀) :=
    funext fun q => (planarDx_planarDy_comm_b1 (r := 0) hV0 q).symm
  have hcomm_φ₃ : planarDx (planarDy φ₃) = planarDy (planarDx φ₃) :=
    funext fun q => planarDx_planarDy_comm_b1 (r := 0) hφ₃ q
  have hc_int : ∀ F : ℝ → ℝ → ℝ, Continuous (Function.uncurry F) →
      Continuous (fun y : ℝ => ∫ x in a..b, F x y) := fun F hF =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => F x y) (hF.comp continuous_swap) a b
  -- Step 1: Swap x/y and integrate by parts in y on `planarDx v₀ * planarDy (planarDx φ₂)`.
  have hstep1 :
      (∫ y in c..d, ∫ x in a..b,
        planarDx v₀ (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
      -(∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₀) (planarPt x y) * planarDx φ₂ (planarPt x y)) := by
    rw [← MeasureTheory.intervalIntegral_intervalIntegral_swap
      (planar_prod_integrableOn_b1 (cont_planarPt_mul_b1 hv₀_x.continuous hφ₂_xy.continuous))]
    have hibp_y : ∀ x : ℝ,
        (∫ y in c..d,
          planarDx v₀ (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
        -(∫ y in c..d,
          planarDx (planarDy v₀) (planarPt x y) * planarDx φ₂ (planarPt x y)) := by
      intro x
      rw [hcomm_φ₂, ← hcomm_v₀]
      exact ibp_1d_zero_boundary_right_b1
        (fun y _ => hasDerivAt_planarPt_y_b1 (diff_of_contDiff_succ_b1 (r := 0) hv₀_x) x y)
        (fun y _ => hasDerivAt_planarPt_y_b1 (diff_of_contDiff_succ_b1 (r := 0) hφ₂_x) x y)
        ((cont_planarPt_uncurry_b1 hv₀_x.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hφ₂_x.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hv₀_yx.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hφ₂_yx.continuous).comp (continuous_const.prodMk continuous_id))
        (hy_φ₂ x).1 (hy_φ₂ x).2
    simp_rw [hibp_y, intervalIntegral.integral_neg]
    congr 1
    exact MeasureTheory.intervalIntegral_intervalIntegral_swap
      (planar_prod_integrableOn_b1 (cont_planarPt_mul_b1 hv₀_xy.continuous hφ₂_x.continuous))
  -- Step 2: Split `planarDx φ₂ = (planarDx φ₂ - planarDy φ₃) + planarDy φ₃`.
  have hstep2 :
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₀) (planarPt x y) * planarDx φ₂ (planarPt x y)) =
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₀) (planarPt x y) *
          (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y))) +
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₀) (planarPt x y) * planarDy φ₃ (planarPt x y)) := by
    have hdiff_cont : Continuous (fun q : Euclidean 2 => planarDx φ₂ q - planarDy φ₃ q) :=
      hφ₂_x.continuous.sub hφ₃_y.continuous
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          planarDx (planarDy v₀) (planarPt x y) * planarDx φ₂ (planarPt x y)) =
        (∫ x in a..b,
          planarDx (planarDy v₀) (planarPt x y) *
            (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y))) +
        (∫ x in a..b,
          planarDx (planarDy v₀) (planarPt x y) * planarDy φ₃ (planarPt x y)) := by
      intro y
      have hrew : (fun x : ℝ =>
          planarDx (planarDy v₀) (planarPt x y) * planarDx φ₂ (planarPt x y)) =
          fun x : ℝ =>
            planarDx (planarDy v₀) (planarPt x y) *
              (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
            planarDx (planarDy v₀) (planarPt x y) * planarDy φ₃ (planarPt x y) := by
        funext x; ring
      rw [hrew]
      exact intervalIntegral.integral_add
        (((cont_planarPt_mul_b1 hv₀_xy.continuous hdiff_cont).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
        (((cont_planarPt_mul_b1 hv₀_xy.continuous hφ₃_y.continuous).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    simp_rw [hinner]
    exact intervalIntegral.integral_add
      ((hc_int _ (cont_planarPt_mul_b1 hv₀_xy.continuous hdiff_cont)).intervalIntegrable c d)
      ((hc_int _ (cont_planarPt_mul_b1 hv₀_xy.continuous hφ₃_y.continuous)).intervalIntegrable c d)
  -- Step 3: Transform `∫∫ (∂_x ∂_y v₀)(∂_y φ₃)` into `∫∫ (∂_y² v₀)(∂_x φ₃)`.
  have hstep3 :
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₀) (planarPt x y) * planarDy φ₃ (planarPt x y)) =
      (∫ y in c..d, ∫ x in a..b,
        planarDy (planarDy v₀) (planarPt x y) * planarDx φ₃ (planarPt x y)) := by
    have hibp_x : ∀ y : ℝ,
        (∫ x in a..b,
          planarDx (planarDy v₀) (planarPt x y) * planarDy φ₃ (planarPt x y)) =
        -(∫ x in a..b,
          planarDy v₀ (planarPt x y) * planarDx (planarDy φ₃) (planarPt x y)) := by
      intro y
      exact ibp_1d_zero_boundary_b1
        (fun x _ => hasDerivAt_planarPt_x_b1 (diff_of_contDiff_succ_b1 (r := 0) hv₀_y) x y)
        (fun x _ => hasDerivAt_planarPt_x_b1 (diff_of_contDiff_succ_b1 (r := 0) hφ₃_y) x y)
        ((cont_planarPt_uncurry_b1 hv₀_y.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hφ₃_y.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hv₀_xy.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hφ₃_xy.continuous).comp (continuous_id.prodMk continuous_const))
        (hx_φ₃ y).1 (hx_φ₃ y).2
    simp_rw [hibp_x, intervalIntegral.integral_neg]
    rw [← MeasureTheory.intervalIntegral_intervalIntegral_swap
      (planar_prod_integrableOn_b1 (cont_planarPt_mul_b1 hv₀_y.continuous hφ₃_xy.continuous))]
    have hibp_y2 : ∀ x : ℝ,
        (∫ y in c..d,
          planarDy v₀ (planarPt x y) * planarDx (planarDy φ₃) (planarPt x y)) =
        -(∫ y in c..d,
          planarDy (planarDy v₀) (planarPt x y) * planarDx φ₃ (planarPt x y)) := by
      intro x
      rw [hcomm_φ₃]
      exact ibp_1d_zero_boundary_right_b1
        (fun y _ => hasDerivAt_planarPt_y_b1 (diff_of_contDiff_succ_b1 (r := 0) hv₀_y) x y)
        (fun y _ => hasDerivAt_planarPt_y_b1 (diff_of_contDiff_succ_b1 (r := 0) hφ₃_x) x y)
        ((cont_planarPt_uncurry_b1 hv₀_y.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hφ₃_x.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hv₀_yy.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hφ₃_yx.continuous).comp (continuous_const.prodMk continuous_id))
        (hy_φ₃ x).1 (hy_φ₃ x).2
    simp_rw [hibp_y2, intervalIntegral.integral_neg, neg_neg]
    exact MeasureTheory.intervalIntegral_intervalIntegral_swap
      (planar_prod_integrableOn_b1 (cont_planarPt_mul_b1 hv₀_yy.continuous hφ₃_x.continuous))
  rw [hstep1, hstep2, hstep3]

private lemma allGauge_ibp_pieceB {a b c d : ℝ}
    {v₁ φ₁ φ₂ : Euclidean 2 → ℝ}
    (hV1 : ContDiff ℝ (2 : ℕ) v₁)
    (hφ₁ : ContDiff ℝ (2 : ℕ) φ₁)
    (hφ₂ : ContDiff ℝ (2 : ℕ) φ₂)
    (hx_φ₁ : ∀ y : ℝ, planarDy φ₁ (planarPt a y) = 0 ∧ planarDy φ₁ (planarPt b y) = 0)
    (hx_φ₂ : ∀ y : ℝ, planarDy φ₂ (planarPt a y) = 0 ∧ planarDy φ₂ (planarPt b y) = 0)
    (hy_φ₁ : ∀ x : ℝ, planarDx φ₁ (planarPt x c) = 0 ∧ planarDx φ₁ (planarPt x d) = 0) :
    (∫ y in c..d, ∫ x in a..b,
      planarDy v₁ (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
    -((∫ y in c..d, ∫ x in a..b,
        planarDx (planarDx v₁) (planarPt x y) * planarDy φ₁ (planarPt x y)) -
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₁) (planarPt x y) *
          (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)))) := by
  have hv₁_x : ContDiff ℝ (1 : ℕ) (planarDx v₁) := contDiff_planarDx_b1 (r := 1) hV1
  have hv₁_y : ContDiff ℝ (1 : ℕ) (planarDy v₁) := contDiff_planarDy_b1 (r := 1) hV1
  have hv₁_xx : ContDiff ℝ (0 : ℕ) (planarDx (planarDx v₁)) := contDiff_planarDx_b1 (r := 0) hv₁_x
  have hv₁_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy v₁)) := contDiff_planarDx_b1 (r := 0) hv₁_y
  have hv₁_yx : ContDiff ℝ (0 : ℕ) (planarDy (planarDx v₁)) := contDiff_planarDy_b1 (r := 0) hv₁_x
  have hφ₁_x : ContDiff ℝ (1 : ℕ) (planarDx φ₁) := contDiff_planarDx_b1 (r := 1) hφ₁
  have hφ₁_y : ContDiff ℝ (1 : ℕ) (planarDy φ₁) := contDiff_planarDy_b1 (r := 1) hφ₁
  have hφ₁_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy φ₁)) := contDiff_planarDx_b1 (r := 0) hφ₁_y
  have hφ₁_yx : ContDiff ℝ (0 : ℕ) (planarDy (planarDx φ₁)) := contDiff_planarDy_b1 (r := 0) hφ₁_x
  have hφ₂_y : ContDiff ℝ (1 : ℕ) (planarDy φ₂) := contDiff_planarDy_b1 (r := 1) hφ₂
  have hφ₂_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy φ₂)) := contDiff_planarDx_b1 (r := 0) hφ₂_y
  have hcomm_v₁ : planarDx (planarDy v₁) = planarDy (planarDx v₁) :=
    funext fun q => planarDx_planarDy_comm_b1 (r := 0) hV1 q
  have hcomm_φ₁ : planarDy (planarDx φ₁) = planarDx (planarDy φ₁) :=
    funext fun q => (planarDx_planarDy_comm_b1 (r := 0) hφ₁ q).symm
  have hc_int : ∀ F : ℝ → ℝ → ℝ, Continuous (Function.uncurry F) →
      Continuous (fun y : ℝ => ∫ x in a..b, F x y) := fun F hF =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => F x y) (hF.comp continuous_swap) a b
  -- Step 1: Integrate by parts in x on `planarDy v₁ * planarDx (planarDy φ₂)`.
  have hstep1 :
      (∫ y in c..d, ∫ x in a..b,
        planarDy v₁ (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
      -(∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₁) (planarPt x y) * planarDy φ₂ (planarPt x y)) := by
    have hibp_x : ∀ y : ℝ,
        (∫ x in a..b,
          planarDy v₁ (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
        -(∫ x in a..b,
          planarDx (planarDy v₁) (planarPt x y) * planarDy φ₂ (planarPt x y)) := by
      intro y
      exact ibp_1d_zero_boundary_right_b1
        (fun x _ => hasDerivAt_planarPt_x_b1 (diff_of_contDiff_succ_b1 (r := 0) hv₁_y) x y)
        (fun x _ => hasDerivAt_planarPt_x_b1 (diff_of_contDiff_succ_b1 (r := 0) hφ₂_y) x y)
        ((cont_planarPt_uncurry_b1 hv₁_y.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hφ₂_y.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hv₁_xy.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hφ₂_xy.continuous).comp (continuous_id.prodMk continuous_const))
        (hx_φ₂ y).1 (hx_φ₂ y).2
    simp_rw [hibp_x, intervalIntegral.integral_neg]
  -- Step 2: Split `planarDy φ₂ = planarDx φ₁ - (planarDx φ₁ - planarDy φ₂)`.
  have hstep2 :
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₁) (planarPt x y) * planarDy φ₂ (planarPt x y)) =
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₁) (planarPt x y) * planarDx φ₁ (planarPt x y)) -
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₁) (planarPt x y) *
          (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y))) := by
    have hdiff_cont : Continuous (fun q : Euclidean 2 => planarDx φ₁ q - planarDy φ₂ q) :=
      hφ₁_x.continuous.sub hφ₂_y.continuous
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          planarDx (planarDy v₁) (planarPt x y) * planarDy φ₂ (planarPt x y)) =
        (∫ x in a..b,
          planarDx (planarDy v₁) (planarPt x y) * planarDx φ₁ (planarPt x y)) -
        (∫ x in a..b,
          planarDx (planarDy v₁) (planarPt x y) *
            (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y))) := by
      intro y
      have hrew : (fun x : ℝ =>
          planarDx (planarDy v₁) (planarPt x y) * planarDy φ₂ (planarPt x y)) =
          fun x : ℝ =>
            planarDx (planarDy v₁) (planarPt x y) * planarDx φ₁ (planarPt x y) -
            planarDx (planarDy v₁) (planarPt x y) *
              (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)) := by
        funext x; ring
      rw [hrew]
      exact intervalIntegral.integral_sub
        (((cont_planarPt_mul_b1 hv₁_xy.continuous hφ₁_x.continuous).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
        (((cont_planarPt_mul_b1 hv₁_xy.continuous hdiff_cont).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    simp_rw [hinner]
    exact intervalIntegral.integral_sub
      ((hc_int _ (cont_planarPt_mul_b1 hv₁_xy.continuous hφ₁_x.continuous)).intervalIntegrable c d)
      ((hc_int _ (cont_planarPt_mul_b1 hv₁_xy.continuous hdiff_cont)).intervalIntegrable c d)
  -- Step 3: Transform `∫∫ (∂_x ∂_y v₁)(∂_x φ₁)` into `∫∫ (∂_x² v₁)(∂_y φ₁)`.
  have hstep3 :
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDy v₁) (planarPt x y) * planarDx φ₁ (planarPt x y)) =
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDx v₁) (planarPt x y) * planarDy φ₁ (planarPt x y)) := by
    rw [← MeasureTheory.intervalIntegral_intervalIntegral_swap
      (planar_prod_integrableOn_b1 (cont_planarPt_mul_b1 hv₁_xy.continuous hφ₁_x.continuous))]
    have hibp_y : ∀ x : ℝ,
        (∫ y in c..d,
          planarDx (planarDy v₁) (planarPt x y) * planarDx φ₁ (planarPt x y)) =
        -(∫ y in c..d,
          planarDx v₁ (planarPt x y) * planarDx (planarDy φ₁) (planarPt x y)) := by
      intro x
      rw [hcomm_v₁, ← hcomm_φ₁]
      exact ibp_1d_zero_boundary_b1
        (fun y _ => hasDerivAt_planarPt_y_b1 (diff_of_contDiff_succ_b1 (r := 0) hv₁_x) x y)
        (fun y _ => hasDerivAt_planarPt_y_b1 (diff_of_contDiff_succ_b1 (r := 0) hφ₁_x) x y)
        ((cont_planarPt_uncurry_b1 hv₁_x.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hφ₁_x.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hv₁_yx.continuous).comp (continuous_const.prodMk continuous_id))
        ((cont_planarPt_uncurry_b1 hφ₁_yx.continuous).comp (continuous_const.prodMk continuous_id))
        (hy_φ₁ x).1 (hy_φ₁ x).2
    simp_rw [hibp_y, intervalIntegral.integral_neg]
    rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
      (planar_prod_integrableOn_b1 (cont_planarPt_mul_b1 hv₁_x.continuous hφ₁_xy.continuous))]
    have hibp_x2 : ∀ y : ℝ,
        (∫ x in a..b,
          planarDx v₁ (planarPt x y) * planarDx (planarDy φ₁) (planarPt x y)) =
        -(∫ x in a..b,
          planarDx (planarDx v₁) (planarPt x y) * planarDy φ₁ (planarPt x y)) := by
      intro y
      exact ibp_1d_zero_boundary_right_b1
        (fun x _ => hasDerivAt_planarPt_x_b1 (diff_of_contDiff_succ_b1 (r := 0) hv₁_x) x y)
        (fun x _ => hasDerivAt_planarPt_x_b1 (diff_of_contDiff_succ_b1 (r := 0) hφ₁_y) x y)
        ((cont_planarPt_uncurry_b1 hv₁_x.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hφ₁_y.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hv₁_xx.continuous).comp (continuous_id.prodMk continuous_const))
        ((cont_planarPt_uncurry_b1 hφ₁_xy.continuous).comp (continuous_id.prodMk continuous_const))
        (hx_φ₁ y).1 (hx_φ₁ y).2
    simp_rw [hibp_x2, intervalIntegral.integral_neg, neg_neg]
  rw [hstep1, hstep2, hstep3]

/-- **Full 4-Component All-Gauge Planar Duality Identity (`(⋆)` on `[a, b] × [c, d]`):**
For *any* `C²` planar vector field `V` (with NO `C³` hypothesis on `V`) and any `C²` test triple
`(φ₁, φ₂, φ₃)` whose tangential first partials vanish on `∂([a, b] × [c, d])`,
`∫_c^d ∫_a^b planarDivergence V (x,y) · (∂_x ∂_y φ₂)(x,y) dx dy`
`  = -∫_c^d ∫_a^b ((∂_x² V₁)(∂_y φ₁) - (∂_x∂_y V₁)(∂_x φ₁ - ∂_y φ₂)`
`                 + (∂_x∂_y V₀)(∂_x φ₂ - ∂_y φ₃) + (∂_y² V₀)(∂_x φ₃)) dx dy`. -/
theorem planar_c2_div_allGauge_duality
    {a b c d : ℝ} {V : PlanarVectorField} (hV : ContDiff ℝ (2 : ℕ) V)
    {φ₁ φ₂ φ₃ : Euclidean 2 → ℝ}
    (hφ₁ : ContDiff ℝ (2 : ℕ) φ₁)
    (hφ₂ : ContDiff ℝ (2 : ℕ) φ₂)
    (hφ₃ : ContDiff ℝ (2 : ℕ) φ₃)
    (hx_bdry : ∀ y : ℝ,
      planarDy φ₁ (planarPt a y) = 0 ∧ planarDy φ₁ (planarPt b y) = 0 ∧
      planarDy φ₂ (planarPt a y) = 0 ∧ planarDy φ₂ (planarPt b y) = 0 ∧
      planarDy φ₃ (planarPt a y) = 0 ∧ planarDy φ₃ (planarPt b y) = 0)
    (hy_bdry : ∀ x : ℝ,
      planarDx φ₁ (planarPt x c) = 0 ∧ planarDx φ₁ (planarPt x d) = 0 ∧
      planarDx φ₂ (planarPt x c) = 0 ∧ planarDx φ₂ (planarPt x d) = 0 ∧
      planarDx φ₃ (planarPt x c) = 0 ∧ planarDx φ₃ (planarPt x d) = 0) :
    (∫ y in c..d, ∫ x in a..b,
      planarDivergence V (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
    -(∫ y in c..d, ∫ x in a..b,
      (planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y) -
        planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
          (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)) +
        planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
          (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
        planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y))) := by
  have hV0 : ContDiff ℝ (2 : ℕ) (fun q => V q 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hV1 : ContDiff ℝ (2 : ℕ) (fun q => V q 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hv₀_x : ContDiff ℝ (1 : ℕ) (planarDx (fun q => V q 0)) := contDiff_planarDx_b1 (r := 1) hV0
  have hv₁_y : ContDiff ℝ (1 : ℕ) (planarDy (fun q => V q 1)) := contDiff_planarDy_b1 (r := 1) hV1
  have hv₀_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy (fun q => V q 0))) :=
    contDiff_planarDx_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV0)
  have hv₀_yy : ContDiff ℝ (0 : ℕ) (planarDy (planarDy (fun q => V q 0))) :=
    contDiff_planarDy_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV0)
  have hv₁_xx : ContDiff ℝ (0 : ℕ) (planarDx (planarDx (fun q => V q 1))) :=
    contDiff_planarDx_b1 (r := 0) (contDiff_planarDx_b1 (r := 1) hV1)
  have hv₁_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy (fun q => V q 1))) :=
    contDiff_planarDx_b1 (r := 0) hv₁_y
  have hφ₁_x : ContDiff ℝ (1 : ℕ) (planarDx φ₁) := contDiff_planarDx_b1 (r := 1) hφ₁
  have hφ₁_y : ContDiff ℝ (1 : ℕ) (planarDy φ₁) := contDiff_planarDy_b1 (r := 1) hφ₁
  have hφ₂_x : ContDiff ℝ (1 : ℕ) (planarDx φ₂) := contDiff_planarDx_b1 (r := 1) hφ₂
  have hφ₂_y : ContDiff ℝ (1 : ℕ) (planarDy φ₂) := contDiff_planarDy_b1 (r := 1) hφ₂
  have hφ₂_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy φ₂)) := contDiff_planarDx_b1 (r := 0) hφ₂_y
  have hφ₃_x : ContDiff ℝ (1 : ℕ) (planarDx φ₃) := contDiff_planarDx_b1 (r := 1) hφ₃
  have hφ₃_y : ContDiff ℝ (1 : ℕ) (planarDy φ₃) := contDiff_planarDy_b1 (r := 1) hφ₃
  have hpA := allGauge_ibp_pieceA (a := a) (b := b) (c := c) (d := d) hV0 hφ₂ hφ₃
    (fun y => ⟨(hx_bdry y).2.2.2.2.1, (hx_bdry y).2.2.2.2.2⟩)
    (fun x => ⟨(hy_bdry x).2.2.1, (hy_bdry x).2.2.2.1⟩)
    (fun x => ⟨(hy_bdry x).2.2.2.2.1, (hy_bdry x).2.2.2.2.2⟩)
  have hpB := allGauge_ibp_pieceB (a := a) (b := b) (c := c) (d := d) hV1 hφ₁ hφ₂
    (fun y => ⟨(hx_bdry y).1, (hx_bdry y).2.1⟩)
    (fun y => ⟨(hx_bdry y).2.2.1, (hx_bdry y).2.2.2.1⟩)
    (fun x => ⟨(hy_bdry x).1, (hy_bdry x).2.1⟩)
  have hc_int : ∀ F : ℝ → ℝ → ℝ, Continuous (Function.uncurry F) →
      Continuous (fun y : ℝ => ∫ x in a..b, F x y) := fun F hF =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => F x y) (hF.comp continuous_swap) a b
  have hsplit_lhs :
      (∫ y in c..d, ∫ x in a..b,
        planarDivergence V (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
      (∫ y in c..d, ∫ x in a..b,
        planarDx (fun q => V q 0) (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) +
      (∫ y in c..d, ∫ x in a..b,
        planarDy (fun q => V q 1) (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) := by
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          planarDivergence V (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
        (∫ x in a..b,
          planarDx (fun q => V q 0) (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) +
        (∫ x in a..b,
          planarDy (fun q => V q 1) (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) := by
      intro y
      have hrew : (fun x : ℝ =>
          planarDivergence V (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)) =
          fun x : ℝ =>
            planarDx (fun q => V q 0) (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y) +
            planarDy (fun q => V q 1) (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y) := by
        funext x; rw [planarDivergence_eq_planarDx_add_planarDy_b1, add_mul]
      rw [hrew]
      exact intervalIntegral.integral_add
        (((cont_planarPt_mul_b1 hv₀_x.continuous hφ₂_xy.continuous).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
        (((cont_planarPt_mul_b1 hv₁_y.continuous hφ₂_xy.continuous).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    simp_rw [hinner]
    exact intervalIntegral.integral_add
      ((hc_int _ (cont_planarPt_mul_b1 hv₀_x.continuous hφ₂_xy.continuous)).intervalIntegrable c d)
      ((hc_int _ (cont_planarPt_mul_b1 hv₁_y.continuous hφ₂_xy.continuous)).intervalIntegrable c d)
  have hdiff12 : Continuous (fun q : Euclidean 2 => planarDx φ₁ q - planarDy φ₂ q) :=
    hφ₁_x.continuous.sub hφ₂_y.continuous
  have hdiff23 : Continuous (fun q : Euclidean 2 => planarDx φ₂ q - planarDy φ₃ q) :=
    hφ₂_x.continuous.sub hφ₃_y.continuous
  have hc1 := cont_planarPt_mul_b1 hv₁_xx.continuous hφ₁_y.continuous
  have hc2 := cont_planarPt_mul_b1 hv₁_xy.continuous hdiff12
  have hc3 := cont_planarPt_mul_b1 hv₀_xy.continuous hdiff23
  have hc4 := cont_planarPt_mul_b1 hv₀_yy.continuous hφ₃_x.continuous
  have hsplit_rhs :
      (∫ y in c..d, ∫ x in a..b,
        (planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y) -
          planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
            (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)) +
          planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
            (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
          planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y))) =
      ((∫ y in c..d, ∫ x in a..b,
          planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y)) -
        (∫ y in c..d, ∫ x in a..b,
          planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
            (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)))) +
      ((∫ y in c..d, ∫ x in a..b,
          planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
            (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y))) +
        (∫ y in c..d, ∫ x in a..b,
          planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y))) := by
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          (planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y) -
            planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
              (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)) +
            planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
              (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
            planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y))) =
        ((∫ x in a..b,
            planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y)) -
          (∫ x in a..b,
            planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
              (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)))) +
        ((∫ x in a..b,
            planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
              (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y))) +
          (∫ x in a..b,
            planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y))) := by
      intro y
      have hi1 := (hc1.comp (continuous_id.prodMk (continuous_const (y := y)))).intervalIntegrable (μ := volume) a b
      have hi2 := (hc2.comp (continuous_id.prodMk (continuous_const (y := y)))).intervalIntegrable (μ := volume) a b
      have hi3 := (hc3.comp (continuous_id.prodMk (continuous_const (y := y)))).intervalIntegrable (μ := volume) a b
      have hi4 := (hc4.comp (continuous_id.prodMk (continuous_const (y := y)))).intervalIntegrable (μ := volume) a b
      have hrew : (fun x : ℝ =>
          planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y) -
            planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
              (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)) +
            planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
              (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
            planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y)) =
          fun x : ℝ =>
            ((planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y) -
              planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
                (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y))) +
              (planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
                (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
              planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y))) := by
        funext x; ring
      rw [hrew]
      exact (intervalIntegral.integral_add (hi1.sub hi2) (hi3.add hi4)).trans
        (congrArg₂ (· + ·)
          (intervalIntegral.integral_sub hi1 hi2)
          (intervalIntegral.integral_add hi3 hi4))
    simp_rw [hinner]
    have ho1 := (hc_int _ hc1).intervalIntegrable (μ := volume) c d
    have ho2 := (hc_int _ hc2).intervalIntegrable (μ := volume) c d
    have ho3 := (hc_int _ hc3).intervalIntegrable (μ := volume) c d
    have ho4 := (hc_int _ hc4).intervalIntegrable (μ := volume) c d
    exact (intervalIntegral.integral_add (ho1.sub ho2) (ho3.add ho4)).trans
      (congrArg₂ (· + ·)
        (intervalIntegral.integral_sub ho1 ho2)
        (intervalIntegral.integral_add ho3 ho4))
  rw [hsplit_lhs, hpA, hpB, hsplit_rhs]
  ring

/-- **Full 4-Component All-Gauge Planar `L∞–L¹` Duality Bound `(⋆)`:**
If `V ∈ C²` has `|∂_x² V₁|, |∂_x∂_y V₁|, |∂_x∂_y V₀|, |∂_y² V₀| ≤ M` on `[a, b] × [c, d]`,
then for every `C²` test triple `(φ₁, φ₂, φ₃)` satisfying the boundary conditions of
`planar_c2_div_allGauge_duality`,
`|∫_c^d ∫_a^b planarDivergence V (x,y) · (∂_x ∂_y φ₂)(x,y) dx dy|`
`  ≤ M * ∫_c^d ∫_a^b (|∂_y φ₁| + |∂_x φ₁ - ∂_y φ₂| + |∂_x φ₂ - ∂_y φ₃| + |∂_x φ₃|) dx dy`. -/
theorem planar_c2_div_allGauge_bound
    {a b c d M : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {V : PlanarVectorField} (hV : ContDiff ℝ (2 : ℕ) V)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M)
    {φ₁ φ₂ φ₃ : Euclidean 2 → ℝ}
    (hφ₁ : ContDiff ℝ (2 : ℕ) φ₁)
    (hφ₂ : ContDiff ℝ (2 : ℕ) φ₂)
    (hφ₃ : ContDiff ℝ (2 : ℕ) φ₃)
    (hx_bdry : ∀ y : ℝ,
      planarDy φ₁ (planarPt a y) = 0 ∧ planarDy φ₁ (planarPt b y) = 0 ∧
      planarDy φ₂ (planarPt a y) = 0 ∧ planarDy φ₂ (planarPt b y) = 0 ∧
      planarDy φ₃ (planarPt a y) = 0 ∧ planarDy φ₃ (planarPt b y) = 0)
    (hy_bdry : ∀ x : ℝ,
      planarDx φ₁ (planarPt x c) = 0 ∧ planarDx φ₁ (planarPt x d) = 0 ∧
      planarDx φ₂ (planarPt x c) = 0 ∧ planarDx φ₂ (planarPt x d) = 0 ∧
      planarDx φ₃ (planarPt x c) = 0 ∧ planarDx φ₃ (planarPt x d) = 0) :
    |∫ y in c..d, ∫ x in a..b,
      planarDivergence V (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)| ≤
    M * ∫ y in c..d, ∫ x in a..b,
      (|planarDy φ₁ (planarPt x y)| +
        |planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)| +
        |planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)| +
        |planarDx φ₃ (planarPt x y)|) := by
  rw [planar_c2_div_allGauge_duality hV hφ₁ hφ₂ hφ₃ hx_bdry hy_bdry, abs_neg]
  have hV0 : ContDiff ℝ (2 : ℕ) (fun q => V q 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hV1 : ContDiff ℝ (2 : ℕ) (fun q => V q 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hv₀_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy (fun q => V q 0))) :=
    contDiff_planarDx_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV0)
  have hv₀_yy : ContDiff ℝ (0 : ℕ) (planarDy (planarDy (fun q => V q 0))) :=
    contDiff_planarDy_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV0)
  have hv₁_xx : ContDiff ℝ (0 : ℕ) (planarDx (planarDx (fun q => V q 1))) :=
    contDiff_planarDx_b1 (r := 0) (contDiff_planarDx_b1 (r := 1) hV1)
  have hv₁_xy : ContDiff ℝ (0 : ℕ) (planarDx (planarDy (fun q => V q 1))) :=
    contDiff_planarDx_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV1)
  have hφ₁_x : ContDiff ℝ (1 : ℕ) (planarDx φ₁) := contDiff_planarDx_b1 (r := 1) hφ₁
  have hφ₁_y : ContDiff ℝ (1 : ℕ) (planarDy φ₁) := contDiff_planarDy_b1 (r := 1) hφ₁
  have hφ₂_x : ContDiff ℝ (1 : ℕ) (planarDx φ₂) := contDiff_planarDx_b1 (r := 1) hφ₂
  have hφ₂_y : ContDiff ℝ (1 : ℕ) (planarDy φ₂) := contDiff_planarDy_b1 (r := 1) hφ₂
  have hφ₃_x : ContDiff ℝ (1 : ℕ) (planarDx φ₃) := contDiff_planarDx_b1 (r := 1) hφ₃
  have hφ₃_y : ContDiff ℝ (1 : ℕ) (planarDy φ₃) := contDiff_planarDy_b1 (r := 1) hφ₃
  let F : ℝ → ℝ → ℝ := fun x y =>
    planarDx (planarDx (fun q => V q 1)) (planarPt x y) * planarDy φ₁ (planarPt x y) -
      planarDx (planarDy (fun q => V q 1)) (planarPt x y) *
        (planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)) +
      planarDx (planarDy (fun q => V q 0)) (planarPt x y) *
        (planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)) +
      planarDy (planarDy (fun q => V q 0)) (planarPt x y) * planarDx φ₃ (planarPt x y)
  let W : ℝ → ℝ → ℝ := fun x y =>
    |planarDy φ₁ (planarPt x y)| +
      |planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)| +
      |planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)| +
      |planarDx φ₃ (planarPt x y)|
  have hcF : Continuous (Function.uncurry F) :=
    cont_planarPt_uncurry_b1
      ((((hv₁_xx.continuous.mul hφ₁_y.continuous).sub
          (hv₁_xy.continuous.mul (hφ₁_x.continuous.sub hφ₂_y.continuous))).add
        (hv₀_xy.continuous.mul (hφ₂_x.continuous.sub hφ₃_y.continuous))).add
        (hv₀_yy.continuous.mul hφ₃_x.continuous))
  have hcW : Continuous (Function.uncurry W) :=
    cont_planarPt_uncurry_b1
      (((hφ₁_y.continuous.abs.add (hφ₁_x.continuous.sub hφ₂_y.continuous).abs).add
        (hφ₂_x.continuous.sub hφ₃_y.continuous).abs).add hφ₃_x.continuous.abs)
  have hcF_int : Continuous (fun y : ℝ => ∫ x in a..b, F x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => F x y) (hcF.comp continuous_swap) a b
  have hcW_int : Continuous (fun y : ℝ => ∫ x in a..b, W x y) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => W x y) (hcW.comp continuous_swap) a b
  have hrow : ∀ y ∈ Icc c d, |∫ x in a..b, F x y| ≤ M * ∫ x in a..b, W x y := by
    intro y hy
    have hnorm_x : |∫ x in a..b, F x y| ≤ ∫ x in a..b, |F x y| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_integral_norm (f := fun x => F x y) hab
    have hpt_x : ∀ x ∈ Icc a b, |F x y| ≤ M * W x y := by
      intro x hx
      obtain ⟨hb1, hb2, hb3, hb4⟩ := hbound x hx y hy
      let a1 := planarDx (planarDx (fun q => V q 1)) (planarPt x y)
      let a2 := planarDx (planarDy (fun q => V q 1)) (planarPt x y)
      let a3 := planarDx (planarDy (fun q => V q 0)) (planarPt x y)
      let a4 := planarDy (planarDy (fun q => V q 0)) (planarPt x y)
      let b1 := planarDy φ₁ (planarPt x y)
      let b2 := planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)
      let b3 := planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)
      let b4 := planarDx φ₃ (planarPt x y)
      have htri : |a1 * b1 - a2 * b2 + a3 * b3 + a4 * b4| ≤
          |a1| * |b1| + |a2| * |b2| + |a3| * |b3| + |a4| * |b4| := by
        calc
          |a1 * b1 - a2 * b2 + a3 * b3 + a4 * b4|
              ≤ |a1 * b1 - a2 * b2 + a3 * b3| + |a4 * b4| := abs_add_le _ _
          _ ≤ (|a1 * b1 - a2 * b2| + |a3 * b3|) + |a4 * b4| := by
                gcongr; exact abs_add_le _ _
          _ ≤ ((|a1 * b1| + |a2 * b2|) + |a3 * b3|) + |a4 * b4| := by
                gcongr; exact abs_sub _ _
          _ = |a1| * |b1| + |a2| * |b2| + |a3| * |b3| + |a4| * |b4| := by
                simp only [abs_mul]
      have hmul : |a1| * |b1| + |a2| * |b2| + |a3| * |b3| + |a4| * |b4| ≤
          M * |b1| + M * |b2| + M * |b3| + M * |b4| := by
        gcongr
      calc
        |F x y| = |a1 * b1 - a2 * b2 + a3 * b3 + a4 * b4| := rfl
        _ ≤ M * |b1| + M * |b2| + M * |b3| + M * |b4| := htri.trans hmul
        _ = M * W x y := by dsimp [W, b1, b2, b3, b4]; ring
    have hmono_x : (∫ x in a..b, |F x y|) ≤ ∫ x in a..b, M * W x y :=
      intervalIntegral.integral_mono_on hab
        ((hcF.comp (continuous_id.prodMk continuous_const)).abs.intervalIntegrable a b)
        ((continuous_const.mul (hcW.comp (continuous_id.prodMk continuous_const))).intervalIntegrable a b)
        hpt_x
    rw [intervalIntegral.integral_const_mul] at hmono_x
    exact hnorm_x.trans hmono_x
  calc
    |∫ y in c..d, ∫ x in a..b, F x y|
        ≤ ∫ y in c..d, |∫ x in a..b, F x y| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm
              (f := fun y => ∫ x in a..b, F x y) hcd
    _ ≤ ∫ y in c..d, M * ∫ x in a..b, W x y :=
        intervalIntegral.integral_mono_on hcd
          (hcF_int.abs.intervalIntegrable c d)
          ((continuous_const.mul hcW_int).intervalIntegrable c d)
          hrow
    _ = M * ∫ y in c..d, ∫ x in a..b, W x y :=
        intervalIntegral.integral_const_mul M _

/-! ### Section 3: Spin-3 Harmonic-Cubic Specialization for the 3-Ray Staircase -/

/-- First spin-3 Cauchy–Riemann cubic operator `(∂_x³ - 3∂_x ∂_y²) U` (symbol `r³ cos 3θ`). -/
def spin3A1 (U : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  planarDx (planarDx (planarDx U)) p - 3 * planarDx (planarDy (planarDy U)) p

/-- Second spin-3 Cauchy–Riemann cubic operator `(3∂_x² ∂_y - ∂_y³) U` (symbol `r³ sin 3θ`). -/
def spin3A2 (U : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  3 * planarDx (planarDx (planarDy U)) p - planarDy (planarDy (planarDy U)) p

/-- First component `φ₁ = (3∂_x² - ∂_y²) U` of the integer-scaled spin-3 test triple. -/
def spin3Phi1 (U : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  3 * planarDx (planarDx U) p - planarDy (planarDy U) p

/-- Middle component `φ₂ = 8 ∂_x ∂_y U` of the integer-scaled spin-3 test triple. -/
def spin3Phi2 (U : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  8 * planarDx (planarDy U) p

/-- Third component `φ₃ = (-∂_x² + 3∂_y²) U` of the integer-scaled spin-3 test triple. -/
def spin3Phi3 (U : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  -planarDx (planarDx U) p + 3 * planarDy (planarDy U) p

/-- Canonical third-partial boundary vanishing condition for `U` on `∂([a, b] × [c, d])`. -/
def vanishesThirdPartialsOnRectBdry (a b c d : ℝ) (U : Euclidean 2 → ℝ) : Prop :=
  (∀ y : ℝ,
    planarDx (planarDx (planarDx U)) (planarPt a y) = 0 ∧
    planarDx (planarDx (planarDx U)) (planarPt b y) = 0 ∧
    planarDx (planarDx (planarDy U)) (planarPt a y) = 0 ∧
    planarDx (planarDx (planarDy U)) (planarPt b y) = 0 ∧
    planarDx (planarDy (planarDy U)) (planarPt a y) = 0 ∧
    planarDx (planarDy (planarDy U)) (planarPt b y) = 0 ∧
    planarDy (planarDy (planarDy U)) (planarPt a y) = 0 ∧
    planarDy (planarDy (planarDy U)) (planarPt b y) = 0) ∧
  (∀ x : ℝ,
    planarDx (planarDx (planarDx U)) (planarPt x c) = 0 ∧
    planarDx (planarDx (planarDx U)) (planarPt x d) = 0 ∧
    planarDx (planarDx (planarDy U)) (planarPt x c) = 0 ∧
    planarDx (planarDx (planarDy U)) (planarPt x d) = 0 ∧
    planarDx (planarDy (planarDy U)) (planarPt x c) = 0 ∧
    planarDx (planarDy (planarDy U)) (planarPt x d) = 0 ∧
    planarDy (planarDy (planarDy U)) (planarPt x c) = 0 ∧
    planarDy (planarDy (planarDy U)) (planarPt x d) = 0)

/-- Any function `U` that vanishes outside a strictly interior sub-rectangle
`[a', b'] × [c', d'] ⊂ (a, b) × (c, d)` automatically satisfies
`vanishesThirdPartialsOnRectBdry a b c d U`. -/
lemma vanishesThirdPartialsOnRectBdry_of_zero_outside_subrect
    {a b c d a' b' c' d' : ℝ}
    (haa' : a < a') (hb'b : b' < b) (hcc' : c < c') (hd'd : d' < d)
    {U : Euclidean 2 → ℝ}
    (hsupp : ∀ p : Euclidean 2, (p 0 < a' ∨ b' < p 0 ∨ p 1 < c' ∨ d' < p 1) → U p = 0) :
    vanishesThirdPartialsOnRectBdry a b c d U := by
  let O : Set (Euclidean 2) :=
    {p | p 0 < a'} ∪ {p | b' < p 0} ∪ {p | p 1 < c'} ∪ {p | d' < p 1}
  have hO_open : IsOpen O := by
    have hc0 : Continuous (fun p : Euclidean 2 => p 0) :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous
    have hc1 : Continuous (fun p : Euclidean 2 => p 1) :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (((isOpen_lt hc0 continuous_const).union (isOpen_lt continuous_const hc0)).union
      (isOpen_lt hc1 continuous_const)).union (isOpen_lt continuous_const hc1)
  have hU0 : EqOn U 0 O := by
    intro p hp
    rcases hp with (((h1 | h2) | h3) | h4)
    · exact hsupp p (Or.inl h1)
    · exact hsupp p (Or.inr (Or.inl h2))
    · exact hsupp p (Or.inr (Or.inr (Or.inl h3)))
    · exact hsupp p (Or.inr (Or.inr (Or.inr h4)))
  have hdx0 : EqOn (planarDx U) 0 O := fun p hp => planarDx_eq_zero_of_eqOn_zero hO_open hU0 hp
  have hdy0 : EqOn (planarDy U) 0 O := fun p hp => planarDy_eq_zero_of_eqOn_zero hO_open hU0 hp
  have hdxx0 : EqOn (planarDx (planarDx U)) 0 O :=
    fun p hp => planarDx_eq_zero_of_eqOn_zero hO_open hdx0 hp
  have hdxy0 : EqOn (planarDx (planarDy U)) 0 O :=
    fun p hp => planarDx_eq_zero_of_eqOn_zero hO_open hdy0 hp
  have hdyy0 : EqOn (planarDy (planarDy U)) 0 O :=
    fun p hp => planarDy_eq_zero_of_eqOn_zero hO_open hdy0 hp
  have hdxxx0 : ∀ p ∈ O, planarDx (planarDx (planarDx U)) p = 0 :=
    fun p hp => planarDx_eq_zero_of_eqOn_zero hO_open hdxx0 hp
  have hdxxy0 : ∀ p ∈ O, planarDx (planarDx (planarDy U)) p = 0 :=
    fun p hp => planarDx_eq_zero_of_eqOn_zero hO_open hdxy0 hp
  have hdxyy0 : ∀ p ∈ O, planarDx (planarDy (planarDy U)) p = 0 :=
    fun p hp => planarDx_eq_zero_of_eqOn_zero hO_open hdyy0 hp
  have hdyyy0 : ∀ p ∈ O, planarDy (planarDy (planarDy U)) p = 0 :=
    fun p hp => planarDy_eq_zero_of_eqOn_zero hO_open hdyy0 hp
  have hmem_a : ∀ y : ℝ, planarPt a y ∈ O := fun y =>
    Or.inl (Or.inl (Or.inl (by simp [haa'])))
  have hmem_b : ∀ y : ℝ, planarPt b y ∈ O := fun y =>
    Or.inl (Or.inl (Or.inr (by simp [hb'b])))
  have hmem_c : ∀ x : ℝ, planarPt x c ∈ O := fun x =>
    Or.inl (Or.inr (by simp [hcc']))
  have hmem_d : ∀ x : ℝ, planarPt x d ∈ O := fun x =>
    Or.inr (by simp [hd'd])
  refine ⟨fun y => ⟨hdxxx0 _ (hmem_a y), hdxxx0 _ (hmem_b y),
    hdxxy0 _ (hmem_a y), hdxxy0 _ (hmem_b y),
    hdxyy0 _ (hmem_a y), hdxyy0 _ (hmem_b y),
    hdyyy0 _ (hmem_a y), hdyyy0 _ (hmem_b y)⟩,
    fun x => ⟨hdxxx0 _ (hmem_c x), hdxxx0 _ (hmem_d x),
    hdxxy0 _ (hmem_c x), hdxxy0 _ (hmem_d x),
    hdxyy0 _ (hmem_c x), hdxyy0 _ (hmem_d x),
    hdyyy0 _ (hmem_c x), hdyyy0 _ (hmem_d x)⟩⟩

private lemma spin3_identities {U : Euclidean 2 → ℝ} (hU : ContDiff ℝ (4 : ℕ) U) :
    ContDiff ℝ (2 : ℕ) (spin3Phi1 U) ∧
    ContDiff ℝ (2 : ℕ) (spin3Phi2 U) ∧
    ContDiff ℝ (2 : ℕ) (spin3Phi3 U) ∧
    (∀ p : Euclidean 2, planarDy (spin3Phi1 U) p = spin3A2 U p) ∧
    (∀ p : Euclidean 2,
      planarDx (spin3Phi1 U) p - planarDy (spin3Phi2 U) p = 3 * spin3A1 U p) ∧
    (∀ p : Euclidean 2,
      planarDx (spin3Phi2 U) p - planarDy (spin3Phi3 U) p = 3 * spin3A2 U p) ∧
    (∀ p : Euclidean 2, planarDx (spin3Phi3 U) p = -spin3A1 U p) ∧
    (∀ p : Euclidean 2,
      planarDx (planarDy (spin3Phi2 U)) p =
        8 * planarDx (planarDx (planarDy (planarDy U))) p) := by
  have hUx : ContDiff ℝ (3 : ℕ) (planarDx U) := contDiff_planarDx_b1 (r := 3) hU
  have hUy : ContDiff ℝ (3 : ℕ) (planarDy U) := contDiff_planarDy_b1 (r := 3) hU
  have hUxx : ContDiff ℝ (2 : ℕ) (planarDx (planarDx U)) := contDiff_planarDx_b1 (r := 2) hUx
  have hUxy : ContDiff ℝ (2 : ℕ) (planarDx (planarDy U)) := contDiff_planarDx_b1 (r := 2) hUy
  have hUyy : ContDiff ℝ (2 : ℕ) (planarDy (planarDy U)) := contDiff_planarDy_b1 (r := 2) hUy
  have hUxyy : ContDiff ℝ (1 : ℕ) (planarDx (planarDy (planarDy U))) :=
    contDiff_planarDx_b1 (r := 1) hUyy
  have hUyxy : ContDiff ℝ (1 : ℕ) (planarDy (planarDx (planarDy U))) :=
    contDiff_planarDy_b1 (r := 1) hUxy
  have hcPhi1 : ContDiff ℝ (2 : ℕ) (spin3Phi1 U) := by
    unfold spin3Phi1
    exact (contDiff_const.mul hUxx).sub hUyy
  have hcPhi2 : ContDiff ℝ (2 : ℕ) (spin3Phi2 U) := by
    unfold spin3Phi2
    exact contDiff_const.mul hUxy
  have hcPhi3 : ContDiff ℝ (2 : ℕ) (spin3Phi3 U) := by
    unfold spin3Phi3
    exact hUxx.neg.add (contDiff_const.mul hUyy)
  -- Commutation of 3rd partials into canonical `∂_x^a ∂_y^b U` order:
  have comm_y_xx : ∀ p : Euclidean 2,
      planarDy (planarDx (planarDx U)) p = planarDx (planarDx (planarDy U)) p := by
    intro p
    rw [← planarDx_planarDy_comm_b1 (r := 1) hUx p]
    have h1 : planarDy (planarDx U) = planarDx (planarDy U) :=
      funext fun q => (planarDx_planarDy_comm_b1 (r := 2) hU q).symm
    rw [h1]
  have comm_y_xy : ∀ p : Euclidean 2,
      planarDy (planarDx (planarDy U)) p = planarDx (planarDy (planarDy U)) p := by
    intro p
    exact (planarDx_planarDy_comm_b1 (r := 1) hUy p).symm
  have hdxx := diff_of_contDiff_succ_b1 (r := 1) hUxx
  have hdxy := diff_of_contDiff_succ_b1 (r := 1) hUxy
  have hdyy := diff_of_contDiff_succ_b1 (r := 1) hUyy
  refine ⟨hcPhi1, hcPhi2, hcPhi3, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    unfold spin3Phi1 spin3A2
    rw [planarDy_sub (hdxx.const_mul 3 p) (hdyy p),
      planarDy_const_mul 3 (hdxx p), comm_y_xx p]
  · intro p
    unfold spin3Phi1 spin3Phi2 spin3A1
    rw [planarDx_sub (hdxx.const_mul 3 p) (hdyy p),
      planarDx_const_mul 3 (hdxx p),
      planarDy_const_mul 8 (hdxy p), comm_y_xy p]
    ring
  · intro p
    have hneg_xx : DifferentiableAt ℝ (fun q => -planarDx (planarDx U) q) p := (hdxx p).neg
    unfold spin3Phi2 spin3Phi3 spin3A2
    rw [planarDx_const_mul 8 (hdxy p),
      planarDy_add hneg_xx (hdyy.const_mul 3 p),
      planarDy_neg (hdxx p), planarDy_const_mul 3 (hdyy p), comm_y_xx p]
    ring
  · intro p
    have hneg_xx : DifferentiableAt ℝ (fun q => -planarDx (planarDx U) q) p := (hdxx p).neg
    unfold spin3Phi3 spin3A1
    rw [planarDx_add hneg_xx (hdyy.const_mul 3 p),
      planarDx_neg (hdxx p), planarDx_const_mul 3 (hdyy p)]
    ring
  · intro p
    have hdyPhi2 : planarDy (spin3Phi2 U) = fun q => 8 * planarDx (planarDy (planarDy U)) q := by
      funext q
      unfold spin3Phi2
      rw [planarDy_const_mul 8 (hdxy q), comm_y_xy q]
    rw [hdyPhi2, planarDx_const_mul 8 (diff_of_contDiff_succ_b1 (r := 0) hUxyy p)]

/-- **Spin-3 Harmonic-Cubic Planar `L∞–L¹` Duality Bound:**
If `V ∈ C²` has `|∂_x² V₁|, |∂_x∂_y V₁|, |∂_x∂_y V₀|, |∂_y² V₀| ≤ M` on `[a, b] × [c, d]`,
then for every `C⁴` test function `U` satisfying `vanishesThirdPartialsOnRectBdry a b c d U`,
`2 * |∫_c^d ∫_a^b planarDivergence V (x,y) · (∂_x² ∂_y² U)(x,y) dx dy|`
`  ≤ M * ∫_c^d ∫_a^b (|spin3A1 U (x,y)| + |spin3A2 U (x,y)|) dx dy`. -/
theorem planar_c2_div_spin3_bound
    {a b c d M : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {V : PlanarVectorField} (hV : ContDiff ℝ (2 : ℕ) V)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M)
    {U : Euclidean 2 → ℝ} (hU : ContDiff ℝ (4 : ℕ) U)
    (hbdry : vanishesThirdPartialsOnRectBdry a b c d U) :
    2 * |∫ y in c..d, ∫ x in a..b,
      planarDivergence V (planarPt x y) *
        planarDx (planarDx (planarDy (planarDy U))) (planarPt x y)| ≤
    M * ∫ y in c..d, ∫ x in a..b,
      (|spin3A1 U (planarPt x y)| + |spin3A2 U (planarPt x y)|) := by
  obtain ⟨hc1, hc2, hc3, hid1, hid2, hid3, hid4, hid_lhs⟩ := spin3_identities hU
  have hUx : ContDiff ℝ (3 : ℕ) (planarDx U) := contDiff_planarDx_b1 (r := 3) hU
  have hUy : ContDiff ℝ (3 : ℕ) (planarDy U) := contDiff_planarDy_b1 (r := 3) hU
  have hUxy : ContDiff ℝ (2 : ℕ) (planarDx (planarDy U)) := contDiff_planarDx_b1 (r := 2) hUy
  have hUyy : ContDiff ℝ (2 : ℕ) (planarDy (planarDy U)) := contDiff_planarDy_b1 (r := 2) hUy
  have comm_y_xy : ∀ p : Euclidean 2,
      planarDy (planarDx (planarDy U)) p = planarDx (planarDy (planarDy U)) p :=
    fun p => (planarDx_planarDy_comm_b1 (r := 1) hUy p).symm
  have hdyPhi2 : ∀ p : Euclidean 2,
      planarDy (spin3Phi2 U) p = 8 * planarDx (planarDy (planarDy U)) p := by
    intro p; unfold spin3Phi2
    rw [planarDy_const_mul 8 (diff_of_contDiff_succ_b1 (r := 1) hUxy p), comm_y_xy p]
  have hdxPhi2 : ∀ p : Euclidean 2,
      planarDx (spin3Phi2 U) p = 8 * planarDx (planarDx (planarDy U)) p := by
    intro p; unfold spin3Phi2
    rw [planarDx_const_mul 8 (diff_of_contDiff_succ_b1 (r := 1) hUxy p)]
  have hx_phi : ∀ y : ℝ,
      planarDy (spin3Phi1 U) (planarPt a y) = 0 ∧
      planarDy (spin3Phi1 U) (planarPt b y) = 0 ∧
      planarDy (spin3Phi2 U) (planarPt a y) = 0 ∧
      planarDy (spin3Phi2 U) (planarPt b y) = 0 ∧
      planarDy (spin3Phi3 U) (planarPt a y) = 0 ∧
      planarDy (spin3Phi3 U) (planarPt b y) = 0 := by
    intro y
    obtain ⟨h1a, h1b, h2a, h2b, h3a, h3b, h4a, h4b⟩ := hbdry.1 y
    have hA2a : spin3A2 U (planarPt a y) = 0 := by unfold spin3A2; rw [h2a, h4a]; ring
    have hA2b : spin3A2 U (planarPt b y) = 0 := by unfold spin3A2; rw [h2b, h4b]; ring
    have hP2a : planarDy (spin3Phi2 U) (planarPt a y) = 0 := by rw [hdyPhi2, h3a]; ring
    have hP2b : planarDy (spin3Phi2 U) (planarPt b y) = 0 := by rw [hdyPhi2, h3b]; ring
    have hP3a : planarDy (spin3Phi3 U) (planarPt a y) = 0 := by
      have := hid3 (planarPt a y); rw [hdxPhi2, h2a, hA2a] at this; linarith
    have hP3b : planarDy (spin3Phi3 U) (planarPt b y) = 0 := by
      have := hid3 (planarPt b y); rw [hdxPhi2, h2b, hA2b] at this; linarith
    exact ⟨by rw [hid1, hA2a], by rw [hid1, hA2b], hP2a, hP2b, hP3a, hP3b⟩
  have hy_phi : ∀ x : ℝ,
      planarDx (spin3Phi1 U) (planarPt x c) = 0 ∧
      planarDx (spin3Phi1 U) (planarPt x d) = 0 ∧
      planarDx (spin3Phi2 U) (planarPt x c) = 0 ∧
      planarDx (spin3Phi2 U) (planarPt x d) = 0 ∧
      planarDx (spin3Phi3 U) (planarPt x c) = 0 ∧
      planarDx (spin3Phi3 U) (planarPt x d) = 0 := by
    intro x
    obtain ⟨h1c, h1d, h2c, h2d, h3c, h3d, _, _⟩ := hbdry.2 x
    have hA1c : spin3A1 U (planarPt x c) = 0 := by unfold spin3A1; rw [h1c, h3c]; ring
    have hA1d : spin3A1 U (planarPt x d) = 0 := by unfold spin3A1; rw [h1d, h3d]; ring
    have hP2c : planarDx (spin3Phi2 U) (planarPt x c) = 0 := by rw [hdxPhi2, h2c]; ring
    have hP2d : planarDx (spin3Phi2 U) (planarPt x d) = 0 := by rw [hdxPhi2, h2d]; ring
    have hdyP2c : planarDy (spin3Phi2 U) (planarPt x c) = 0 := by rw [hdyPhi2, h3c]; ring
    have hdyP2d : planarDy (spin3Phi2 U) (planarPt x d) = 0 := by rw [hdyPhi2, h3d]; ring
    have hP1c : planarDx (spin3Phi1 U) (planarPt x c) = 0 := by
      have := hid2 (planarPt x c); rw [hdyP2c, hA1c] at this; linarith
    have hP1d : planarDx (spin3Phi1 U) (planarPt x d) = 0 := by
      have := hid2 (planarPt x d); rw [hdyP2d, hA1d] at this; linarith
    exact ⟨hP1c, hP1d, hP2c, hP2d,
      by rw [hid4, hA1c, neg_zero], by rw [hid4, hA1d, neg_zero]⟩
  have hall := planar_c2_div_allGauge_bound hab hcd hV hbound hc1 hc2 hc3 hx_phi hy_phi
  -- Simplify LHS integral (`8 * ∫∫ planarDivergence V * ∂_x²∂_y² U`)
  have hlhs :
      |∫ y in c..d, ∫ x in a..b,
        planarDivergence V (planarPt x y) *
          planarDx (planarDy (spin3Phi2 U)) (planarPt x y)| =
      8 * |∫ y in c..d, ∫ x in a..b,
        planarDivergence V (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy U))) (planarPt x y)| := by
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          planarDivergence V (planarPt x y) *
            planarDx (planarDy (spin3Phi2 U)) (planarPt x y)) =
        8 * ∫ x in a..b,
          planarDivergence V (planarPt x y) *
            planarDx (planarDx (planarDy (planarDy U))) (planarPt x y) := by
      intro y
      have hrew : (fun x : ℝ =>
          planarDivergence V (planarPt x y) *
            planarDx (planarDy (spin3Phi2 U)) (planarPt x y)) =
          fun x : ℝ =>
            8 * (planarDivergence V (planarPt x y) *
              planarDx (planarDx (planarDy (planarDy U))) (planarPt x y)) := by
        funext x; rw [hid_lhs]; ring
      rw [hrew, intervalIntegral.integral_const_mul]
    simp_rw [hinner, intervalIntegral.integral_const_mul]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 8)]
  -- Simplify RHS integral (`4 * ∫∫ (|spin3A1 U| + |spin3A2 U|)`)
  have hrhs :
      (∫ y in c..d, ∫ x in a..b,
        (|planarDy (spin3Phi1 U) (planarPt x y)| +
          |planarDx (spin3Phi1 U) (planarPt x y) - planarDy (spin3Phi2 U) (planarPt x y)| +
          |planarDx (spin3Phi2 U) (planarPt x y) - planarDy (spin3Phi3 U) (planarPt x y)| +
          |planarDx (spin3Phi3 U) (planarPt x y)|)) =
      4 * ∫ y in c..d, ∫ x in a..b,
        (|spin3A1 U (planarPt x y)| + |spin3A2 U (planarPt x y)|) := by
    have hpt : ∀ x y : ℝ,
        |planarDy (spin3Phi1 U) (planarPt x y)| +
          |planarDx (spin3Phi1 U) (planarPt x y) - planarDy (spin3Phi2 U) (planarPt x y)| +
          |planarDx (spin3Phi2 U) (planarPt x y) - planarDy (spin3Phi3 U) (planarPt x y)| +
          |planarDx (spin3Phi3 U) (planarPt x y)| =
        4 * (|spin3A1 U (planarPt x y)| + |spin3A2 U (planarPt x y)|) := by
      intro x y
      rw [hid1, hid2, hid3, hid4, abs_neg, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      ring
    simp_rw [hpt, intervalIntegral.integral_const_mul]
  rw [hlhs, hrhs] at hall
  linarith

/-! ### Section 4: Compact-Box Uniform Bounds and Stage B1 Disproof Scaffolds -/

/-- On any compact rectangle `[A, B] × [C, D]`, every `C²` planar vector field `V` has a
uniform nonnegative bound `M` on all four second partials entering `(⋆)`. -/
lemma exists_c2_allGauge_bound_on_rect
    (A B C D : ℝ) {V : PlanarVectorField} (hV : ContDiff ℝ (2 : ℕ) V) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Icc A B, ∀ y ∈ Icc C D,
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M := by
  have hV0 : ContDiff ℝ (2 : ℕ) (fun q => V q 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hV1 : ContDiff ℝ (2 : ℕ) (fun q => V q 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hc1 : Continuous (Function.uncurry fun x y =>
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)|) :=
    (cont_planarPt_uncurry_b1
      (contDiff_planarDx_b1 (r := 0) (contDiff_planarDx_b1 (r := 1) hV1)).continuous).abs
  have hc2 : Continuous (Function.uncurry fun x y =>
      |planarDx (planarDy (fun q => V q 1)) (planarPt x y)|) :=
    (cont_planarPt_uncurry_b1
      (contDiff_planarDx_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV1)).continuous).abs
  have hc3 : Continuous (Function.uncurry fun x y =>
      |planarDx (planarDy (fun q => V q 0)) (planarPt x y)|) :=
    (cont_planarPt_uncurry_b1
      (contDiff_planarDx_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV0)).continuous).abs
  have hc4 : Continuous (Function.uncurry fun x y =>
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)|) :=
    (cont_planarPt_uncurry_b1
      (contDiff_planarDy_b1 (r := 0) (contDiff_planarDy_b1 (r := 1) hV0)).continuous).abs
  let g : ℝ × ℝ → ℝ := fun q =>
    max (max (|planarDx (planarDx (fun p => V p 1)) (planarPt q.1 q.2)|)
             (|planarDx (planarDy (fun p => V p 1)) (planarPt q.1 q.2)|))
        (max (|planarDx (planarDy (fun p => V p 0)) (planarPt q.1 q.2)|)
             (|planarDy (planarDy (fun p => V p 0)) (planarPt q.1 q.2)|))
  have hcg : Continuous g := (hc1.max hc2).max (hc3.max hc4)
  obtain ⟨M₀, hM₀⟩ :=
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc A B ×ˢ Icc C D)).exists_bound_of_continuousOn
      hcg.continuousOn
  refine ⟨max M₀ 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have hle : g (x, y) ≤ max M₀ 0 := by
    have hnorm := hM₀ (x, y) ⟨hx, hy⟩
    rw [Real.norm_eq_abs] at hnorm
    exact (le_abs_self _).trans (hnorm.trans (le_max_left _ _))
  have h12 : max (|planarDx (planarDx (fun p => V p 1)) (planarPt x y)|)
                 (|planarDx (planarDy (fun p => V p 1)) (planarPt x y)|) ≤ max M₀ 0 :=
    (le_max_left _ _).trans hle
  have h34 : max (|planarDx (planarDy (fun p => V p 0)) (planarPt x y)|)
                 (|planarDy (planarDy (fun p => V p 0)) (planarPt x y)|) ≤ max M₀ 0 :=
    (le_max_right _ _).trans hle
  exact ⟨(le_max_left _ _).trans h12, (le_max_right _ _).trans h12,
    (le_max_left _ _).trans h34, (le_max_right _ _).trans h34⟩

/-- **All-Gauge Quantitative Blowup Refutes Planar `C²` Divergence Solvability:**
If inside a compact macro-box `[A, B] × [C, D]` a planar datum `f` possesses, for every `M ≥ 0`,
a sub-rectangle `[a, b] × [c, d] ⊆ [A, B] × [C, D]` and `C²` test triple `(φ₁, φ₂, φ₃)`
violating the `M`-bound of `(⋆)`, then `f` has NO `C²` planar divergence solution on `ℝ²`. -/
theorem not_planarDivergence_c2_of_allGauge_blowup
    {A B C D : ℝ} {f : Euclidean 2 → ℝ}
    (hblowup : ∀ M : ℝ, 0 ≤ M →
      ∃ a b c d : ℝ, A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ C ≤ c ∧ c ≤ d ∧ d ≤ D ∧
        ∃ φ₁ φ₂ φ₃ : Euclidean 2 → ℝ,
          ContDiff ℝ (2 : ℕ) φ₁ ∧ ContDiff ℝ (2 : ℕ) φ₂ ∧ ContDiff ℝ (2 : ℕ) φ₃ ∧
          (∀ y : ℝ,
            planarDy φ₁ (planarPt a y) = 0 ∧ planarDy φ₁ (planarPt b y) = 0 ∧
            planarDy φ₂ (planarPt a y) = 0 ∧ planarDy φ₂ (planarPt b y) = 0 ∧
            planarDy φ₃ (planarPt a y) = 0 ∧ planarDy φ₃ (planarPt b y) = 0) ∧
          (∀ x : ℝ,
            planarDx φ₁ (planarPt x c) = 0 ∧ planarDx φ₁ (planarPt x d) = 0 ∧
            planarDx φ₂ (planarPt x c) = 0 ∧ planarDx φ₂ (planarPt x d) = 0 ∧
            planarDx φ₃ (planarPt x c) = 0 ∧ planarDx φ₃ (planarPt x d) = 0) ∧
          M * (∫ y in c..d, ∫ x in a..b,
            (|planarDy φ₁ (planarPt x y)| +
              |planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)| +
              |planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)| +
              |planarDx φ₃ (planarPt x y)|)) <
          |∫ y in c..d, ∫ x in a..b,
            f (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)|) :
    ¬ ∃ V : PlanarVectorField, ContDiff ℝ 2 V ∧ planarDivergence V = f := by
  rintro ⟨V, hV, hdiv⟩
  obtain ⟨M, hM0, hM⟩ := exists_c2_allGauge_bound_on_rect A B C D hV
  obtain ⟨a, b, c, d, hAa, hab, hbB, hCc, hcd, hdD,
    φ₁, φ₂, φ₃, hφ₁, hφ₂, hφ₃, hx_b, hy_b, hstrict⟩ := hblowup M hM0
  have hsub : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M :=
    fun x hx y hy => hM x ⟨hAa.trans hx.1, hx.2.trans hbB⟩ y ⟨hCc.trans hy.1, hy.2.trans hdD⟩
  have hle := planar_c2_div_allGauge_bound hab hcd hV hsub hφ₁ hφ₂ hφ₃ hx_b hy_b
  rw [hdiv] at hle
  exact not_lt_of_ge hle hstrict

/-- **All-Gauge Quantitative Blowup Refutes `pma10_43_contract`:**
Combines `not_planarDivergence_c2_of_allGauge_blowup` with
`PMA1043Planar.pma10_43_contract_implies_planarDivergence`. -/
theorem not_pma10_43_contract_of_allGauge_blowup
    {A B C D : ℝ} {f : Euclidean 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hblowup : ∀ M : ℝ, 0 ≤ M →
      ∃ a b c d : ℝ, A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ C ≤ c ∧ c ≤ d ∧ d ≤ D ∧
        ∃ φ₁ φ₂ φ₃ : Euclidean 2 → ℝ,
          ContDiff ℝ (2 : ℕ) φ₁ ∧ ContDiff ℝ (2 : ℕ) φ₂ ∧ ContDiff ℝ (2 : ℕ) φ₃ ∧
          (∀ y : ℝ,
            planarDy φ₁ (planarPt a y) = 0 ∧ planarDy φ₁ (planarPt b y) = 0 ∧
            planarDy φ₂ (planarPt a y) = 0 ∧ planarDy φ₂ (planarPt b y) = 0 ∧
            planarDy φ₃ (planarPt a y) = 0 ∧ planarDy φ₃ (planarPt b y) = 0) ∧
          (∀ x : ℝ,
            planarDx φ₁ (planarPt x c) = 0 ∧ planarDx φ₁ (planarPt x d) = 0 ∧
            planarDx φ₂ (planarPt x c) = 0 ∧ planarDx φ₂ (planarPt x d) = 0 ∧
            planarDx φ₃ (planarPt x c) = 0 ∧ planarDx φ₃ (planarPt x d) = 0) ∧
          M * (∫ y in c..d, ∫ x in a..b,
            (|planarDy φ₁ (planarPt x y)| +
              |planarDx φ₁ (planarPt x y) - planarDy φ₂ (planarPt x y)| +
              |planarDx φ₂ (planarPt x y) - planarDy φ₃ (planarPt x y)| +
              |planarDx φ₃ (planarPt x y)|)) <
          |∫ y in c..d, ∫ x in a..b,
            f (planarPt x y) * planarDx (planarDy φ₂) (planarPt x y)|) :
    ¬ pma10_43_contract := fun hcontract =>
  not_planarDivergence_c2_of_allGauge_blowup hblowup
    (pma10_43_contract_implies_planarDivergence hcontract f hf)

/-- **Spin-3 Quantitative Blowup Refutes `pma10_43_contract`:**
Direct Stage B1 reduction tailored to the spin-3 harmonic-cubic test family `U`. -/
theorem not_pma10_43_contract_of_spin3_blowup
    {A B C D : ℝ} {f : Euclidean 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hblowup : ∀ M : ℝ, 0 ≤ M →
      ∃ a b c d : ℝ, A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ C ≤ c ∧ c ≤ d ∧ d ≤ D ∧
        ∃ U : Euclidean 2 → ℝ, ContDiff ℝ (4 : ℕ) U ∧
          vanishesThirdPartialsOnRectBdry a b c d U ∧
          M * (∫ y in c..d, ∫ x in a..b,
            (|spin3A1 U (planarPt x y)| + |spin3A2 U (planarPt x y)|)) <
          2 * |∫ y in c..d, ∫ x in a..b,
            f (planarPt x y) *
              planarDx (planarDx (planarDy (planarDy U))) (planarPt x y)|) :
    ¬ pma10_43_contract := by
  intro hcontract
  obtain ⟨V, hV, hdiv⟩ := pma10_43_contract_implies_planarDivergence hcontract f hf
  obtain ⟨M, hM0, hM⟩ := exists_c2_allGauge_bound_on_rect A B C D hV
  obtain ⟨a, b, c, d, hAa, hab, hbB, hCc, hcd, hdD, U, hU, hbdry, hstrict⟩ := hblowup M hM0
  have hsub : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 1)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M :=
    fun x hx y hy => hM x ⟨hAa.trans hx.1, hx.2.trans hbB⟩ y ⟨hCc.trans hy.1, hy.2.trans hdD⟩
  have hle := planar_c2_div_spin3_bound hab hcd hV hsub hU hbdry
  rw [hdiv] at hle
  exact not_lt_of_ge hle hstrict

/-- **Disjoint-Box Gliding-Hump Stage B1 Counterexample Scaffold (`f = Σ ε_k h_k`):**
Given a sequence of sub-rectangles `[a_k, b_k] × [c_k, d_k] ⊆ [A, B] × [C, D]`, local data
`h_k`, positive weights `ε_k > 0`, `C⁴` spin-3 witnesses `U_k`, and a global `C¹` datum `f`
agreeing with `ε_k * h_k` on each `[a_k, b_k] × [c_k, d_k]` (as holds for any disjointly
supported sum `f = Σ ε_k h_k` with `supp h_k ⊆ [a_k, b_k] × [c_k, d_k]`), if the weighted
spin-3 ratios diverge, then `¬ pma10_43_contract`. -/
theorem not_pma10_43_contract_of_spin3_gliding_hump
    {A B C D : ℝ}
    {a b c d ε : ℕ → ℝ}
    {h U : ℕ → Euclidean 2 → ℝ}
    {f : Euclidean 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hboxes : ∀ k : ℕ, A ≤ a k ∧ a k ≤ b k ∧ b k ≤ B ∧ C ≤ c k ∧ c k ≤ d k ∧ d k ≤ D)
    (hε : ∀ k : ℕ, 0 < ε k)
    (hU_reg : ∀ k : ℕ, ContDiff ℝ (4 : ℕ) (U k))
    (hU_bdry : ∀ k : ℕ, vanishesThirdPartialsOnRectBdry (a k) (b k) (c k) (d k) (U k))
    (hlocal : ∀ k : ℕ, ∀ x ∈ Icc (a k) (b k), ∀ y ∈ Icc (c k) (d k),
      f (planarPt x y) = ε k * h k (planarPt x y))
    (hdiverge : ∀ M : ℝ, 0 ≤ M → ∃ k : ℕ,
      M * (∫ y in c k..d k, ∫ x in a k..b k,
        (|spin3A1 (U k) (planarPt x y)| + |spin3A2 (U k) (planarPt x y)|)) <
      2 * ε k * |∫ y in c k..d k, ∫ x in a k..b k,
        h k (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y)|) :
    ¬ pma10_43_contract := by
  apply not_pma10_43_contract_of_spin3_blowup (A := A) (B := B) (C := C) (D := D) hf
  intro M hM0
  obtain ⟨k, hk⟩ := hdiverge M hM0
  obtain ⟨hAa, hab, hbB, hCc, hcd, hdD⟩ := hboxes k
  refine ⟨a k, b k, c k, d k, hAa, hab, hbB, hCc, hcd, hdD, U k, hU_reg k, hU_bdry k, ?_⟩
  have hint_eq :
      (∫ y in c k..d k, ∫ x in a k..b k,
        f (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y)) =
      ε k * (∫ y in c k..d k, ∫ x in a k..b k,
        h k (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y)) := by
    have hcd_u : uIcc (c k) (d k) = Icc (c k) (d k) := uIcc_of_le hcd
    have hab_u : uIcc (a k) (b k) = Icc (a k) (b k) := uIcc_of_le hab
    have hinner : ∀ y ∈ uIcc (c k) (d k),
        (∫ x in a k..b k,
          f (planarPt x y) *
            planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y)) =
        ε k * (∫ x in a k..b k,
          h k (planarPt x y) *
            planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y)) := by
      intro y hy
      rw [hcd_u] at hy
      have hcongr : (∫ x in a k..b k,
          f (planarPt x y) *
            planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y)) =
          (∫ x in a k..b k,
            ε k * (h k (planarPt x y) *
              planarDx (planarDx (planarDy (planarDy (U k)))) (planarPt x y))) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [hab_u] at hx
        dsimp only
        rw [hlocal k x hx y hy, mul_assoc]
      rw [hcongr, intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_congr hinner, intervalIntegral.integral_const_mul]
  rw [hint_eq, abs_mul, abs_of_pos (hε k)]
  linarith

/-- **Diagonal `(⋆⋆)` Companion Reduction (`not_pma10_43_contract_of_fourth_order_blowup`):**
Direct bridge from `FtildeCZPrep.planar_c2_div_fourth_order_bound` to `¬ pma10_43_contract`. -/
theorem not_pma10_43_contract_of_fourth_order_blowup
    {A B C D : ℝ} {f : Euclidean 2 → ℝ} (hf : ContDiff ℝ 1 f)
    (hblowup : ∀ M : ℝ, 0 ≤ M →
      ∃ a b c d : ℝ, A ≤ a ∧ a ≤ b ∧ b ≤ B ∧ C ≤ c ∧ c ≤ d ∧ d ≤ D ∧
        ∃ w : Euclidean 2 → ℝ, ContDiff ℝ (5 : ℕ) w ∧
          (∀ y : ℝ,
            planarDy (planarDy (planarDx (planarDx w))) (planarPt a y) = 0 ∧
            planarDy (planarDy (planarDx (planarDx w))) (planarPt b y) = 0 ∧
            planarDy (planarDy (planarDy w)) (planarPt a y) = 0 ∧
            planarDy (planarDy (planarDy w)) (planarPt b y) = 0 ∧
            planarDx (planarDy (planarDy (planarDy w))) (planarPt a y) = 0 ∧
            planarDx (planarDy (planarDy (planarDy w))) (planarPt b y) = 0) ∧
          (∀ x : ℝ,
            planarDy (planarDy (planarDx (planarDx w))) (planarPt x c) = 0 ∧
            planarDy (planarDy (planarDx (planarDx w))) (planarPt x d) = 0 ∧
            planarDy (planarDx (planarDx (planarDx w))) (planarPt x c) = 0 ∧
            planarDy (planarDx (planarDx (planarDx w))) (planarPt x d) = 0 ∧
            planarDx (planarDx (planarDx w)) (planarPt x c) = 0 ∧
            planarDx (planarDx (planarDx w)) (planarPt x d) = 0) ∧
          M * (∫ y in c..d, ∫ x in a..b,
            (|planarDx (planarDx (planarDx w)) (planarPt x y)| +
              |planarDy (planarDy (planarDy w)) (planarPt x y)|)) <
          |∫ y in c..d, ∫ x in a..b,
            f (planarPt x y) *
              planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)|) :
    ¬ pma10_43_contract := by
  intro hcontract
  obtain ⟨V, hV, hdiv⟩ := pma10_43_contract_implies_planarDivergence hcontract f hf
  obtain ⟨M, hM0, hM⟩ := exists_c2_allGauge_bound_on_rect A B C D hV
  obtain ⟨a, b, c, d, hAa, hab, hbB, hCc, hcd, hdD, w, hw, hx_b, hy_b, hstrict⟩ :=
    hblowup M hM0
  have hsub : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M := by
    intro x hx y hy
    obtain ⟨hb1, _, _, hb4⟩ :=
      hM x ⟨hAa.trans hx.1, hx.2.trans hbB⟩ y ⟨hCc.trans hy.1, hy.2.trans hdD⟩
    exact ⟨hb4, hb1⟩
  have hle := planar_c2_div_fourth_order_bound hab hcd hV hsub hw hx_b hy_b
  rw [hdiv] at hle
  exact not_lt_of_ge hle hstrict

/-! ### Section 5: 3-Ray Spin-3 Coincidence and Quantitative Haar-Shift Equidistribution -/

/-- Planar rank-one wave `p ↦ g(α p₀ + β p₁)` along wavevector `(α, β) ∈ ℝ²`. -/
def planarPlaneWave (α β : ℝ) (g : ℝ → ℝ) (p : Euclidean 2) : ℝ :=
  g (α * p 0 + β * p 1)

private lemma planarDx_planarPlaneWave (α β : ℝ) {g g' : ℝ → ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t) :
    planarDx (planarPlaneWave α β g) =
      planarPlaneWave α β (fun t => α * g' t) := by
  funext p
  unfold planarDx coordinatePartial planarPlaneWave
  have hline : (fun t : ℝ =>
      g (α * (p + t • coordinateVector 2 0) 0 + β * (p + t • coordinateVector 2 0) 1)) =
      fun t : ℝ => g ((α * p 0 + β * p 1) + α * t) := by
    funext t
    congr 1
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
    ring
  rw [hline]
  have hinner : HasDerivAt (fun t : ℝ => (α * p 0 + β * p 1) + α * t) α 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul α).const_add (α * p 0 + β * p 1)
  have hg_at : HasDerivAt g (g' (α * p 0 + β * p 1)) ((α * p 0 + β * p 1) + α * 0) := by
    simpa [mul_zero, add_zero] using hg (α * p 0 + β * p 1)
  have hcomp : HasDerivAt (fun t : ℝ => g ((α * p 0 + β * p 1) + α * t))
      (g' (α * p 0 + β * p 1) * α) 0 :=
    hg_at.comp (0 : ℝ) hinner
  rw [hcomp.deriv]
  ring

private lemma planarDy_planarPlaneWave (α β : ℝ) {g g' : ℝ → ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t) :
    planarDy (planarPlaneWave α β g) =
      planarPlaneWave α β (fun t => β * g' t) := by
  funext p
  unfold planarDy coordinatePartial planarPlaneWave
  have hline : (fun t : ℝ =>
      g (α * (p + t • coordinateVector 2 1) 0 + β * (p + t • coordinateVector 2 1) 1)) =
      fun t : ℝ => g ((α * p 0 + β * p 1) + β * t) := by
    funext t
    congr 1
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
    ring
  rw [hline]
  have hinner : HasDerivAt (fun t : ℝ => (α * p 0 + β * p 1) + β * t) β 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul β).const_add (α * p 0 + β * p 1)
  have hg_at : HasDerivAt g (g' (α * p 0 + β * p 1)) ((α * p 0 + β * p 1) + β * 0) := by
    simpa [mul_zero, add_zero] using hg (α * p 0 + β * p 1)
  have hcomp : HasDerivAt (fun t : ℝ => g ((α * p 0 + β * p 1) + β * t))
      (g' (α * p 0 + β * p 1) * β) 0 :=
    hg_at.comp (0 : ℝ) hinner
  rw [hcomp.deriv]
  ring

/-- **Exact Action of `(spin3A1, spin3A2)` on Arbitrary Planar Rank-One Waves:**
For any wavevector `(α, β) ∈ ℝ²` and any three-times differentiable 1D profile
`(g₀, g₁, g₂, g₃)`,
`spin3A1 (p ↦ g₀(α p₀ + β p₁)) p = (α³ - 3 α β²) g₃(α p₀ + β p₁)` and
`spin3A2 (p ↦ g₀(α p₀ + β p₁)) p = (3 α² β - β³) g₃(α p₀ + β p₁)`. -/
theorem spin3_planeWave_identities (α β : ℝ) {g₀ g₁ g₂ g₃ : ℝ → ℝ}
    (hg₀ : ∀ t : ℝ, HasDerivAt g₀ (g₁ t) t)
    (hg₁ : ∀ t : ℝ, HasDerivAt g₁ (g₂ t) t)
    (hg₂ : ∀ t : ℝ, HasDerivAt g₂ (g₃ t) t)
    (p : Euclidean 2) :
    spin3A1 (planarPlaneWave α β g₀) p =
      (α ^ 3 - 3 * α * β ^ 2) * g₃ (α * p 0 + β * p 1) ∧
    spin3A2 (planarPlaneWave α β g₀) p =
      (3 * α ^ 2 * β - β ^ 3) * g₃ (α * p 0 + β * p 1) := by
  have hdx1 := planarDx_planarPlaneWave α β hg₀
  have hdy1 := planarDy_planarPlaneWave α β hg₀
  have hdx2 : planarDx (planarDx (planarPlaneWave α β g₀)) =
      planarPlaneWave α β (fun t => α * (α * g₂ t)) := by
    rw [hdx1]
    exact planarDx_planarPlaneWave α β (fun t => (hg₁ t).const_mul α)
  have hdyy2 : planarDy (planarDy (planarPlaneWave α β g₀)) =
      planarPlaneWave α β (fun t => β * (β * g₂ t)) := by
    rw [hdy1]
    exact planarDy_planarPlaneWave α β (fun t => (hg₁ t).const_mul β)
  have hdxy2 : planarDx (planarDy (planarPlaneWave α β g₀)) =
      planarPlaneWave α β (fun t => α * (β * g₂ t)) := by
    rw [hdy1]
    exact planarDx_planarPlaneWave α β (fun t => (hg₁ t).const_mul β)
  have hdxxx3 : planarDx (planarDx (planarDx (planarPlaneWave α β g₀))) =
      planarPlaneWave α β (fun t => α * (α * (α * g₃ t))) := by
    rw [hdx2]
    exact planarDx_planarPlaneWave α β (fun t => ((hg₂ t).const_mul α).const_mul α)
  have hdxxy3 : planarDx (planarDx (planarDy (planarPlaneWave α β g₀))) =
      planarPlaneWave α β (fun t => α * (α * (β * g₃ t))) := by
    rw [hdxy2]
    exact planarDx_planarPlaneWave α β (fun t => ((hg₂ t).const_mul β).const_mul α)
  have hdxyy3 : planarDx (planarDy (planarDy (planarPlaneWave α β g₀))) =
      planarPlaneWave α β (fun t => α * (β * (β * g₃ t))) := by
    rw [hdyy2]
    exact planarDx_planarPlaneWave α β (fun t => ((hg₂ t).const_mul β).const_mul β)
  have hdyyy3 : planarDy (planarDy (planarDy (planarPlaneWave α β g₀))) =
      planarPlaneWave α β (fun t => β * (β * (β * g₃ t))) := by
    rw [hdyy2]
    exact planarDy_planarPlaneWave α β (fun t => ((hg₂ t).const_mul β).const_mul β)
  unfold spin3A1 spin3A2
  rw [hdxxx3, hdxxy3, hdxyy3, hdyyy3]
  unfold planarPlaneWave
  constructor <;> ring

/-- First `120°` unit ray `v₀ = (1, 0)`. -/
def spin3Ray0 : ℝ × ℝ := (1, 0)

/-- Second `120°` unit ray `v₁ = (-1/2, √3/2)`. -/
def spin3Ray1 : ℝ × ℝ := (-1 / 2, Real.sqrt 3 / 2)

/-- Third `120°` unit ray `v₂ = (-1/2, -√3/2)`. -/
def spin3Ray2 : ℝ × ℝ := (-1 / 2, -Real.sqrt 3 / 2)

/-- **3-Ray Zero-Sum & Spin-3 3-to-1 Coincidence Theorem:**
The three `120°` unit vectors `v₀ = (1, 0)`, `v₁ = (-1/2, √3/2)`, `v₂ = (-1/2, -√3/2)`
satisfy:
1. `v₀ + v₁ + v₂ = (0, 0)` (exact 3-step gradient cancellation),
2. `‖v₀‖² = ‖v₁‖² = ‖v₂‖² = 1`, and
3. for every frequency `Λ ∈ ℝ` and 3-times differentiable 1D profile `(g₀, g₁, g₂, g₃)`,
   **all three** plane waves `W_r(p) = g₀(Λ (v_r · p))` satisfy identically
   `spin3A1 W_r p = Λ³ g₃(Λ (v_r · p))` and `spin3A2 W_r p = 0`. -/
theorem spin3_three_ray_obstruction (Λ : ℝ) {g₀ g₁ g₂ g₃ : ℝ → ℝ}
    (hg₀ : ∀ t : ℝ, HasDerivAt g₀ (g₁ t) t)
    (hg₁ : ∀ t : ℝ, HasDerivAt g₁ (g₂ t) t)
    (hg₂ : ∀ t : ℝ, HasDerivAt g₂ (g₃ t) t)
    (p : Euclidean 2) :
    (spin3Ray0.1 + spin3Ray1.1 + spin3Ray2.1 = 0 ∧
      spin3Ray0.2 + spin3Ray1.2 + spin3Ray2.2 = 0) ∧
    (spin3Ray0.1 ^ 2 + spin3Ray0.2 ^ 2 = 1 ∧
      spin3Ray1.1 ^ 2 + spin3Ray1.2 ^ 2 = 1 ∧
      spin3Ray2.1 ^ 2 + spin3Ray2.2 ^ 2 = 1) ∧
    (spin3A1 (planarPlaneWave (Λ * spin3Ray0.1) (Λ * spin3Ray0.2) g₀) p =
        Λ ^ 3 * g₃ (Λ * (spin3Ray0.1 * p 0 + spin3Ray0.2 * p 1)) ∧
      spin3A2 (planarPlaneWave (Λ * spin3Ray0.1) (Λ * spin3Ray0.2) g₀) p = 0) ∧
    (spin3A1 (planarPlaneWave (Λ * spin3Ray1.1) (Λ * spin3Ray1.2) g₀) p =
        Λ ^ 3 * g₃ (Λ * (spin3Ray1.1 * p 0 + spin3Ray1.2 * p 1)) ∧
      spin3A2 (planarPlaneWave (Λ * spin3Ray1.1) (Λ * spin3Ray1.2) g₀) p = 0) ∧
    (spin3A1 (planarPlaneWave (Λ * spin3Ray2.1) (Λ * spin3Ray2.2) g₀) p =
        Λ ^ 3 * g₃ (Λ * (spin3Ray2.1 * p 0 + spin3Ray2.2 * p 1)) ∧
      spin3A2 (planarPlaneWave (Λ * spin3Ray2.1) (Λ * spin3Ray2.2) g₀) p = 0) := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcube3 : Real.sqrt 3 ^ 3 = 3 * Real.sqrt 3 := by
    calc
      Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 := by ring
      _ = 3 * Real.sqrt 3 := by rw [hsq3]
  have hid0 := spin3_planeWave_identities (Λ * spin3Ray0.1) (Λ * spin3Ray0.2) hg₀ hg₁ hg₂ p
  have hid1 := spin3_planeWave_identities (Λ * spin3Ray1.1) (Λ * spin3Ray1.2) hg₀ hg₁ hg₂ p
  have hid2 := spin3_planeWave_identities (Λ * spin3Ray2.1) (Λ * spin3Ray2.2) hg₀ hg₁ hg₂ p
  have harg : ∀ r : ℝ × ℝ,
      (Λ * r.1) * p 0 + (Λ * r.2) * p 1 = Λ * (r.1 * p 0 + r.2 * p 1) :=
    fun _ => by ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [spin3Ray0, spin3Ray1, spin3Ray2]; constructor <;> ring
  · simp only [spin3Ray0, spin3Ray1, spin3Ray2]
    refine ⟨by norm_num, ?_, ?_⟩
    · calc
        (-1 / 2 : ℝ) ^ 2 + (Real.sqrt 3 / 2) ^ 2
            = 1 / 4 + Real.sqrt 3 ^ 2 / 4 := by ring
        _ = 1 := by rw [hsq3]; norm_num
    · calc
        (-1 / 2 : ℝ) ^ 2 + (-Real.sqrt 3 / 2) ^ 2
            = 1 / 4 + Real.sqrt 3 ^ 2 / 4 := by ring
        _ = 1 := by rw [hsq3]; norm_num
  · rw [hid0.1, hid0.2, harg spin3Ray0]
    simp only [spin3Ray0]; constructor <;> ring
  · rw [hid1.1, hid1.2, harg spin3Ray1]
    simp only [spin3Ray1]
    constructor
    · have hc : (Λ * (-1 / 2)) ^ 3 - 3 * (Λ * (-1 / 2)) * (Λ * (Real.sqrt 3 / 2)) ^ 2 =
          Λ ^ 3 * (-1 / 8 + 3 / 8 * Real.sqrt 3 ^ 2) := by ring
      rw [hc, hsq3]; ring
    · have hs : 3 * (Λ * (-1 / 2)) ^ 2 * (Λ * (Real.sqrt 3 / 2)) -
          (Λ * (Real.sqrt 3 / 2)) ^ 3 =
          Λ ^ 3 / 8 * (3 * Real.sqrt 3 - Real.sqrt 3 ^ 3) := by ring
      rw [hs, hcube3]; ring
  · rw [hid2.1, hid2.2, harg spin3Ray2]
    simp only [spin3Ray2]
    constructor
    · have hc : (Λ * (-1 / 2)) ^ 3 - 3 * (Λ * (-1 / 2)) * (Λ * (-Real.sqrt 3 / 2)) ^ 2 =
          Λ ^ 3 * (-1 / 8 + 3 / 8 * Real.sqrt 3 ^ 2) := by ring
      rw [hc, hsq3]; ring
    · have hs : 3 * (Λ * (-1 / 2)) ^ 2 * (Λ * (-Real.sqrt 3 / 2)) -
          (Λ * (-Real.sqrt 3 / 2)) ^ 3 =
          Λ ^ 3 / 8 * (-3 * Real.sqrt 3 + Real.sqrt 3 ^ 3) := by ring
      rw [hs, hcube3]; ring

/-- **Sharp Quantitative 1D Antiperiodic Haar-Shift Equidistribution Bound:**
For any continuous `(1/2)`-antiperiodic wave `g : ℝ → ℝ` (`g(t + 1/2) = -g(t)`),
any continuous function `F : ℝ → ℝ` that is `L`-Lipschitz on `[0, 1]` (without
assuming `F` is periodic!), and any frequency `N ≥ 1`,
`|∫_0^1 F(x) g(N x) dx| ≤ (L / (4 N)) * ∫_0^1 |g(t)| dt`. -/
theorem antiperiodic_haar_shift_bound_1d
    {F g : ℝ → ℝ} {L : ℝ} {N : ℕ}
    (hN : 1 ≤ N)
    (hF_cont : Continuous F) (hg_cont : Continuous g)
    (hF_lip : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, |F x - F y| ≤ L * |x - y|)
    (hanti : ∀ t : ℝ, g (t + 1 / 2) = -g t) :
    |∫ x in (0 : ℝ)..1, F x * g ((N : ℝ) * x)| ≤
      (L / (4 * (N : ℝ))) * ∫ t in (0 : ℝ)..1, |g t| := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have habs_half : ∀ t : ℝ, |g (t + 1 / 2)| = |g t| := fun t => by
    rw [hanti t, abs_neg]
  have habs_one : ∀ t : ℝ, |g (t + 1)| = |g t| := fun t => by
    have h1 : t + 1 = (t + 1 / 2) + 1 / 2 := by ring
    rw [h1, habs_half, habs_half]
  have habs_nat : ∀ (k : ℕ) (t : ℝ), |g (t + (k : ℝ))| = |g t| := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
        intro t
        push_cast
        rw [← add_assoc, habs_one, ih]
  have hg_full : (∫ t in (0 : ℝ)..1, |g t|) = 2 * ∫ t in (0 : ℝ)..(1 / 2), |g t| := by
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.abs.intervalIntegrable (μ := volume) (0 : ℝ) (1 / 2))
      (hg_cont.abs.intervalIntegrable (μ := volume) (1 / 2 : ℝ) 1)).symm
    have hshift : (∫ t in (1 / 2 : ℝ)..1, |g t|) = ∫ t in (0 : ℝ)..(1 / 2), |g t| := by
      calc
        (∫ t in (1 / 2 : ℝ)..1, |g t|)
            = ∫ t in ((0 : ℝ) + 1 / 2)..((1 / 2 : ℝ) + 1 / 2), |g t| := by norm_num
        _ = ∫ t in (0 : ℝ)..(1 / 2), |g (t + 1 / 2)| :=
            (intervalIntegral.integral_comp_add_right (fun t => |g t|) (1 / 2)).symm
        _ = ∫ t in (0 : ℝ)..(1 / 2), |g t| := by simp_rw [habs_half]
    linarith
  have hFg_cont : Continuous (fun x : ℝ => F x * g ((N : ℝ) * x)) :=
    hF_cont.mul (hg_cont.comp (continuous_const.mul continuous_id))
  let d : ℝ := 1 / (2 * (N : ℝ))
  have hd_pos : 0 < d := by dsimp [d]; positivity
  have hsub_bound : ∀ k < N,
      |∫ x in ((k : ℝ) / (N : ℝ))..(((k + 1 : ℕ) : ℝ) / (N : ℝ)),
        F x * g ((N : ℝ) * x)| ≤
      (L / (4 * (N : ℝ) ^ 2)) * ∫ t in (0 : ℝ)..1, |g t| := by
    intro k hk
    let a_k : ℝ := (k : ℝ) / (N : ℝ)
    let m_k : ℝ := ((k : ℝ) + 1 / 2) / (N : ℝ)
    let b_k : ℝ := (((k + 1 : ℕ) : ℝ) / (N : ℝ))
    have ha_le_m : a_k ≤ m_k := by
      dsimp [a_k, m_k]; gcongr; linarith
    have hm_eq : m_k = a_k + d := by
      dsimp [a_k, m_k, d]; field_simp [hN_ne]
    have hb_eq : b_k = m_k + d := by
      dsimp [m_k, b_k, d]; push_cast; field_simp [hN_ne]; ring
    have hcell_eq :
        (∫ x in a_k..b_k, F x * g ((N : ℝ) * x)) =
        ∫ x in a_k..m_k, (F x - F (x + d)) * g ((N : ℝ) * x) := by
      have hiA := hFg_cont.intervalIntegrable (μ := volume) a_k m_k
      have hFg_shift_cont : Continuous (fun x : ℝ => -(F (x + d) * g ((N : ℝ) * x))) :=
        ((hF_cont.comp (continuous_id.add (continuous_const (y := d)))).mul
          (hg_cont.comp (continuous_const.mul continuous_id))).neg
      have hiB := hFg_shift_cont.intervalIntegrable (μ := volume) a_k m_k
      calc
        (∫ x in a_k..b_k, F x * g ((N : ℝ) * x))
            = (∫ x in a_k..m_k, F x * g ((N : ℝ) * x)) +
                ∫ x in m_k..b_k, F x * g ((N : ℝ) * x) :=
              (intervalIntegral.integral_add_adjacent_intervals
                (hFg_cont.intervalIntegrable (μ := volume) a_k m_k)
                (hFg_cont.intervalIntegrable (μ := volume) m_k b_k)).symm
        _ = (∫ x in a_k..m_k, F x * g ((N : ℝ) * x)) +
              ∫ x in (a_k + d)..(m_k + d), F x * g ((N : ℝ) * x) := by
            rw [← hm_eq, ← hb_eq]
        _ = (∫ x in a_k..m_k, F x * g ((N : ℝ) * x)) +
              ∫ x in a_k..m_k, F (x + d) * g ((N : ℝ) * (x + d)) := by
            rw [← intervalIntegral.integral_comp_add_right
              (fun x => F x * g ((N : ℝ) * x)) d]
        _ = (∫ x in a_k..m_k, F x * g ((N : ℝ) * x)) +
              ∫ x in a_k..m_k, -(F (x + d) * g ((N : ℝ) * x)) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro x _
            dsimp only
            have hNx : (N : ℝ) * (x + d) = (N : ℝ) * x + 1 / 2 := by
              dsimp [d]; field_simp [hN_ne]
            rw [hNx, hanti, mul_neg]
        _ = ∫ x in a_k..m_k,
              (F x * g ((N : ℝ) * x) + -(F (x + d) * g ((N : ℝ) * x))) :=
            (intervalIntegral.integral_add hiA hiB).symm
        _ = ∫ x in a_k..m_k, (F x - F (x + d)) * g ((N : ℝ) * x) := by
            apply intervalIntegral.integral_congr
            intro x _; dsimp only; ring
    have hdiff_cont : Continuous (fun x : ℝ => (F x - F (x + d)) * g ((N : ℝ) * x)) :=
      (hF_cont.sub (hF_cont.comp (continuous_id.add (continuous_const (y := d))))).mul
        (hg_cont.comp (continuous_const.mul continuous_id))
    have hgN_abs_cont : Continuous (fun x : ℝ => |g ((N : ℝ) * x)|) :=
      (hg_cont.comp (continuous_const.mul continuous_id)).abs
    have hpt_lip : ∀ x ∈ Icc a_k m_k,
        |(F x - F (x + d)) * g ((N : ℝ) * x)| ≤ (L * d) * |g ((N : ℝ) * x)| := by
      intro x hx
      have ha_nonneg : 0 ≤ a_k := div_nonneg (Nat.cast_nonneg k) hN_pos.le
      have hk_succ_le : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hk
      have hb_le_one : b_k ≤ 1 := (div_le_one hN_pos).mpr hk_succ_le
      have hx_mem : x ∈ Icc (0 : ℝ) 1 := by
        refine ⟨ha_nonneg.trans hx.1, ?_⟩
        have hxd : x ≤ m_k + d := by linarith [hx.2, hd_pos]
        rw [← hb_eq] at hxd
        exact hxd.trans hb_le_one
      have hxd_mem : x + d ∈ Icc (0 : ℝ) 1 := by
        refine ⟨by linarith [hx_mem.1, hd_pos], ?_⟩
        have hxd : x + d ≤ m_k + d := by linarith [hx.2]
        rw [← hb_eq] at hxd
        exact hxd.trans hb_le_one
      have hlip_x := hF_lip x hx_mem (x + d) hxd_mem
      have habs_d : |x - (x + d)| = d := by
        have hsub : x - (x + d) = -d := by ring
        rw [hsub, abs_neg, abs_of_pos hd_pos]
      rw [habs_d] at hlip_x
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hlip_x (abs_nonneg _)
    have hg_cell :
        (∫ x in a_k..m_k, |g ((N : ℝ) * x)|) =
          (1 / (2 * (N : ℝ))) * ∫ t in (0 : ℝ)..1, |g t| := by
      calc
        (∫ x in a_k..m_k, |g ((N : ℝ) * x)|)
            = (N : ℝ)⁻¹ • ∫ t in ((N : ℝ) * a_k)..((N : ℝ) * m_k), |g t| :=
              intervalIntegral.integral_comp_mul_left (f := fun t => |g t|) hN_ne
        _ = (N : ℝ)⁻¹ * ∫ t in ((0 : ℝ) + (k : ℝ))..((1 / 2 : ℝ) + (k : ℝ)), |g t| := by
            have hk1 : (N : ℝ) * a_k = (0 : ℝ) + (k : ℝ) := by
              dsimp [a_k]; field_simp [hN_ne]; ring
            have hk2 : (N : ℝ) * m_k = (1 / 2 : ℝ) + (k : ℝ) := by
              dsimp [m_k]; field_simp [hN_ne]; ring
            rw [hk1, hk2, smul_eq_mul]
        _ = (N : ℝ)⁻¹ * ∫ t in (0 : ℝ)..(1 / 2), |g (t + (k : ℝ))| := by
            rw [← intervalIntegral.integral_comp_add_right (fun t => |g t|) (k : ℝ)]
        _ = (N : ℝ)⁻¹ * ∫ t in (0 : ℝ)..(1 / 2), |g t| := by
            simp_rw [habs_nat k]
        _ = (1 / (2 * (N : ℝ))) * ∫ t in (0 : ℝ)..1, |g t| := by
            rw [hg_full]; ring
    rw [hcell_eq]
    calc
      |∫ x in a_k..m_k, (F x - F (x + d)) * g ((N : ℝ) * x)|
          ≤ ∫ x in a_k..m_k, |(F x - F (x + d)) * g ((N : ℝ) * x)| := by
            simpa only [Real.norm_eq_abs] using
              intervalIntegral.norm_integral_le_integral_norm
                (f := fun x => (F x - F (x + d)) * g ((N : ℝ) * x)) ha_le_m
      _ ≤ ∫ x in a_k..m_k, (L * d) * |g ((N : ℝ) * x)| :=
          intervalIntegral.integral_mono_on ha_le_m
            (hdiff_cont.abs.intervalIntegrable (μ := volume) a_k m_k)
            ((continuous_const.mul hgN_abs_cont).intervalIntegrable (μ := volume) a_k m_k)
            hpt_lip
      _ = (L * d) * ∫ x in a_k..m_k, |g ((N : ℝ) * x)| :=
          intervalIntegral.integral_const_mul (L * d) _
      _ = (L / (4 * (N : ℝ) ^ 2)) * ∫ t in (0 : ℝ)..1, |g t| := by
          rw [hg_cell]; dsimp [d]; ring
  let pts : ℕ → ℝ := fun k => (k : ℝ) / (N : ℝ)
  have hpts0 : pts 0 = 0 := by simp [pts]
  have hptsN : pts N = 1 := by simp [pts, div_self hN_ne]
  have hsum_eq :
      (∫ x in (0 : ℝ)..1, F x * g ((N : ℝ) * x)) =
        ∑ k ∈ Finset.range N,
          ∫ x in (pts k)..(pts (k + 1)), F x * g ((N : ℝ) * x) := by
    rw [← hpts0, ← hptsN]
    exact (intervalIntegral.sum_integral_adjacent_intervals
      (a := pts) (n := N)
      (fun k _ => hFg_cont.intervalIntegrable (μ := volume) _ _)).symm
  rw [hsum_eq]
  calc
    |∑ k ∈ Finset.range N, ∫ x in (pts k)..(pts (k + 1)), F x * g ((N : ℝ) * x)|
        ≤ ∑ k ∈ Finset.range N,
            |∫ x in (pts k)..(pts (k + 1)), F x * g ((N : ℝ) * x)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N,
          (L / (4 * (N : ℝ) ^ 2)) * ∫ t in (0 : ℝ)..1, |g t| := by
        apply Finset.sum_le_sum
        intro k hk
        exact hsub_bound k (Finset.mem_range.mp hk)
    _ = (L / (4 * (N : ℝ))) * ∫ t in (0 : ℝ)..1, |g t| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp [hN_ne]

end Rudin.PMA.Chapter10

/-! Verify module ownership and standard foundations for all declarations in this module. -/
run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.Research.PMA1043Stage4B1
    #[`Rudin.PMA.Chapter10.planar_c2_div_allGauge_duality,
      `Rudin.PMA.Chapter10.planar_c2_div_allGauge_bound,
      `Rudin.PMA.Chapter10.vanishesThirdPartialsOnRectBdry_of_zero_outside_subrect,
      `Rudin.PMA.Chapter10.planar_c2_div_spin3_bound,
      `Rudin.PMA.Chapter10.exists_c2_allGauge_bound_on_rect,
      `Rudin.PMA.Chapter10.not_planarDivergence_c2_of_allGauge_blowup,
      `Rudin.PMA.Chapter10.not_pma10_43_contract_of_allGauge_blowup,
      `Rudin.PMA.Chapter10.not_pma10_43_contract_of_spin3_blowup,
      `Rudin.PMA.Chapter10.not_pma10_43_contract_of_spin3_gliding_hump,
      `Rudin.PMA.Chapter10.not_pma10_43_contract_of_fourth_order_blowup,
      `Rudin.PMA.Chapter10.spin3_planeWave_identities,
      `Rudin.PMA.Chapter10.spin3_three_ray_obstruction,
      `Rudin.PMA.Chapter10.antiperiodic_haar_shift_bound_1d]
