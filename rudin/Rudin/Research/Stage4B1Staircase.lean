import Rudin.Research.Stage4B1Waves

/-!
# Stage 4 Branch B1 — Closed-Form 3-Ray Stopped-Martingale Staircase `(Ũ_K, h̃_K)` on `[0, 1]²`

This module constructs the compactly supported `C⁴` 3-ray stopped-martingale
staircase `(staircaseU K, staircaseH K)` on `[0, 1]²` from the 1D spline waves of
`Stage4B1Waves.lean` and the exact `120°` zero-sum triad `spin3Ray0..2` of
`PMA1043Stage4B1.lean`, and proves all estimates required by
`not_pma10_43_contract_of_spin3_gliding_hump`:

1. `contDiff_staircaseU`, `contDiff_staircaseH`: `ContDiff ℝ (4 : ℕ)` regularity.
2. `staircaseU_zero_outside`, `staircaseH_zero_outside`,
   `vanishesThirdPartialsOnRectBdry_staircaseU`: strict support inside
   `[1/8, 7/8]² ⊂ (0, 1)²` and vanishing of all 16 boundary third partials on `∂([0, 1]²)`.
3. `abs_staircaseH_le_one`, `norm_fderiv_staircaseH_le_one`: uniform `C¹(ℝ²)` bound on
   `staircaseH K` independent of `K` via 3-step zero-sum Abel summation and the
   pointwise stopping telescope.
4. `spin3_l1_staircaseU_le_two`: uniform `L¹([0, 1]²)` bound
   `∫_0^1 ∫_0^1 (|spin3A1 (staircaseU K)| + |spin3A2 (staircaseU K)|) ≤ 2` via
   `spin3_three_ray_obstruction` (`spin3A2 = 0` on pure waves), the pointwise
   martingale stopping identity, and `antiperiodic_haar_shift_bound_1d` in `x`.
5. `pairing_staircase_lower_bound`: linear `≳ m + 1` pairing growth
   `((m + 1 : ℝ) / 1024) ≤ ∫_0^1 ∫_0^1 staircaseH (3 * (m + 1)) · ∂_x² ∂_y² (staircaseU (3 * (m + 1)))`.
-/

noncomputable section
set_option autoImplicit false

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators Interval

namespace Rudin.PMA.Chapter10

/-! ### Section 1: Planar Calculus, 3-Jet Leibniz Commutator, and 1D Equidistribution Wrappers -/

private lemma diff_of_c1 {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) : Differentiable ℝ f :=
  hf.differentiable (by norm_cast)

private lemma planarDx_add_s {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDx (fun q => f q + g q) p = planarDx f p + planarDx g p := by
  unfold planarDx
  exact coordinatePartial_add hf hg 0

private lemma planarDy_add_s {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDy (fun q => f q + g q) p = planarDy f p + planarDy g p := by
  unfold planarDy
  exact coordinatePartial_add hf hg 1

private lemma planarDx_mul_s {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDx (fun q => f q * g q) p = planarDx f p * g p + f p * planarDx g p := by
  unfold planarDx
  exact coordinatePartial_mul hf hg 0

private lemma planarDy_mul_s {f g : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    planarDy (fun q => f q * g q) p = planarDy f p * g p + f p * planarDy g p := by
  unfold planarDy
  exact coordinatePartial_mul hf hg 1

private lemma planarDx_const_mul_s (c : ℝ) {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    planarDx (fun q => c * f q) p = c * planarDx f p := by
  unfold planarDx
  exact coordinatePartial_const_mul hf c 0

private lemma planarDy_const_mul_s (c : ℝ) {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    planarDy (fun q => c * f q) p = c * planarDy f p := by
  unfold planarDy
  exact coordinatePartial_const_mul hf c 1

private lemma planarDx_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Euclidean 2 → ℝ}
    {p : Euclidean 2} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) p) :
    planarDx (fun q => ∑ i ∈ s, f i q) p = ∑ i ∈ s, planarDx (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [planarDx, coordinatePartial]
  | @insert a s ha ih =>
      have h1 : DifferentiableAt ℝ (f a) p := hf a (Finset.mem_insert_self a s)
      have h2 : DifferentiableAt ℝ (fun q => ∑ i ∈ s, f i q) p :=
        DifferentiableAt.fun_sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simp_rw [Finset.sum_insert ha]
      rw [planarDx_add_s h1 h2, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

private lemma planarDy_finset_sum {ι : Type*} (s : Finset ι) {f : ι → Euclidean 2 → ℝ}
    {p : Euclidean 2} (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) p) :
    planarDy (fun q => ∑ i ∈ s, f i q) p = ∑ i ∈ s, planarDy (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [planarDy, coordinatePartial]
  | @insert a s ha ih =>
      have h1 : DifferentiableAt ℝ (f a) p := hf a (Finset.mem_insert_self a s)
      have h2 : DifferentiableAt ℝ (fun q => ∑ i ∈ s, f i q) p :=
        DifferentiableAt.fun_sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
      simp_rw [Finset.sum_insert ha]
      rw [planarDy_add_s h1 h2, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

lemma norm_fderiv_le_abs_planarDx_add_planarDy {f : Euclidean 2 → ℝ} {p : Euclidean 2}
    (hf : DifferentiableAt ℝ f p) :
    ‖fderiv ℝ f p‖ ≤ |planarDx f p| + |planarDy f p| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hv_eq : v = v 0 • coordinateVector 2 0 + v 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector, EuclideanSpace.basisFun_apply]
  have happly : fderiv ℝ f p v = v 0 * planarDx f p + v 1 * planarDy f p := by
    conv_lhs => rw [hv_eq]
    rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    unfold planarDx planarDy
    rw [coordinatePartial_eq_fderiv hf 0, coordinatePartial_eq_fderiv hf 1]
  rw [Real.norm_eq_abs, happly]
  have hv0 : |v 0| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 0
  have hv1 : |v 1| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v 1
  calc
    |v 0 * planarDx f p + v 1 * planarDy f p|
        ≤ |v 0 * planarDx f p| + |v 1 * planarDy f p| := abs_add_le _ _
    _ = |v 0| * |planarDx f p| + |v 1| * |planarDy f p| := by rw [abs_mul, abs_mul]
    _ ≤ ‖v‖ * |planarDx f p| + ‖v‖ * |planarDy f p| :=
        add_le_add (mul_le_mul_of_nonneg_right hv0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hv1 (abs_nonneg _))
    _ = (|planarDx f p| + |planarDy f p|) * ‖v‖ := by ring

lemma planarDx_planarPlaneWave_s (α β : ℝ) {g g' : ℝ → ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t) :
    planarDx (planarPlaneWave α β g) = planarPlaneWave α β (fun t => α * g' t) := by
  funext p
  unfold planarDx coordinatePartial planarPlaneWave
  have hline : (fun t : ℝ =>
      g (α * (p + t • coordinateVector 2 0) 0 + β * (p + t • coordinateVector 2 0) 1)) =
      fun t : ℝ => g ((α * p 0 + β * p 1) + α * t) := by
    funext t; congr 1; simp [coordinateVector, EuclideanSpace.basisFun_apply]; ring
  rw [hline]
  have hinner : HasDerivAt (fun t : ℝ => (α * p 0 + β * p 1) + α * t) α 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul α).const_add (α * p 0 + β * p 1)
  have hg_at : HasDerivAt g (g' (α * p 0 + β * p 1)) ((α * p 0 + β * p 1) + α * 0) := by
    simpa [mul_zero, add_zero] using hg (α * p 0 + β * p 1)
  have hcomp : HasDerivAt (fun t : ℝ => g ((α * p 0 + β * p 1) + α * t))
      (g' (α * p 0 + β * p 1) * α) 0 :=
    HasDerivAt.comp (h₂ := g) (h := fun t : ℝ => (α * p 0 + β * p 1) + α * t) 0 hg_at hinner
  rw [hcomp.deriv]
  ring

lemma planarDy_planarPlaneWave_s (α β : ℝ) {g g' : ℝ → ℝ}
    (hg : ∀ t : ℝ, HasDerivAt g (g' t) t) :
    planarDy (planarPlaneWave α β g) = planarPlaneWave α β (fun t => β * g' t) := by
  funext p
  unfold planarDy coordinatePartial planarPlaneWave
  have hline : (fun t : ℝ =>
      g (α * (p + t • coordinateVector 2 1) 0 + β * (p + t • coordinateVector 2 1) 1)) =
      fun t : ℝ => g ((α * p 0 + β * p 1) + β * t) := by
    funext t; congr 1; simp [coordinateVector, EuclideanSpace.basisFun_apply]; ring
  rw [hline]
  have hinner : HasDerivAt (fun t : ℝ => (α * p 0 + β * p 1) + β * t) β 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul β).const_add (α * p 0 + β * p 1)
  have hg_at : HasDerivAt g (g' (α * p 0 + β * p 1)) ((α * p 0 + β * p 1) + β * 0) := by
    simpa [mul_zero, add_zero] using hg (α * p 0 + β * p 1)
  have hcomp : HasDerivAt (fun t : ℝ => g ((α * p 0 + β * p 1) + β * t))
      (g' (α * p 0 + β * p 1) * β) 0 :=
    HasDerivAt.comp (h₂ := g) (h := fun t : ℝ => (α * p 0 + β * p 1) + β * t) 0 hg_at hinner
  rw [hcomp.deriv]
  ring

lemma contDiff_planarPlaneWave {n : ℕ} (α β : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ (n : ℕ) g) :
    ContDiff ℝ (n : ℕ) (planarPlaneWave α β g) := by
  unfold planarPlaneWave
  have hlin : ContDiff ℝ (n : ℕ) (fun p : Euclidean 2 => α * p 0 + β * p 1) :=
    (contDiff_const.mul (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff).add
      (contDiff_const.mul (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff)
  exact hg.comp hlin

/-- Sum of absolute values of all 1st, 2nd, and 3rd planar partials of `A` at `p`. -/
def jet3Norm (A : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  |planarDx A p| + |planarDy A p| +
  |planarDx (planarDx A) p| + |planarDx (planarDy A) p| +
  |planarDy (planarDx A) p| + |planarDy (planarDy A) p| +
  |planarDx (planarDx (planarDx A)) p| + |planarDx (planarDx (planarDy A)) p| +
  |planarDx (planarDy (planarDx A)) p| + |planarDx (planarDy (planarDy A)) p| +
  |planarDy (planarDx (planarDx A)) p| + |planarDy (planarDx (planarDy A)) p| +
  |planarDy (planarDy (planarDx A)) p| + |planarDy (planarDy (planarDy A)) p|

lemma continuous_jet3Norm {A : Euclidean 2 → ℝ} (hA : ContDiff ℝ (3 : ℕ) A) :
    Continuous (jet3Norm A) := by
  have hx := contDiff_planarDx_b1 (r := 2) hA
  have hy := contDiff_planarDy_b1 (r := 2) hA
  have hxx := contDiff_planarDx_b1 (r := 1) hx
  have hxy := contDiff_planarDx_b1 (r := 1) hy
  have hyx := contDiff_planarDy_b1 (r := 1) hx
  have hyy := contDiff_planarDy_b1 (r := 1) hy
  have hxxx := (contDiff_planarDx_b1 (r := 0) hxx).continuous
  have hxxy := (contDiff_planarDx_b1 (r := 0) hxy).continuous
  have hxyx := (contDiff_planarDx_b1 (r := 0) hyx).continuous
  have hxyy := (contDiff_planarDx_b1 (r := 0) hyy).continuous
  have hyxx := (contDiff_planarDy_b1 (r := 0) hxx).continuous
  have hyxy := (contDiff_planarDy_b1 (r := 0) hxy).continuous
  have hyyx := (contDiff_planarDy_b1 (r := 0) hyx).continuous
  have hyyy := (contDiff_planarDy_b1 (r := 0) hyy).continuous
  have hcx := hx.continuous
  have hcy := hy.continuous
  have hcxx := hxx.continuous
  have hcxy := hxy.continuous
  have hcyx := hyx.continuous
  have hcyy := hyy.continuous
  unfold jet3Norm
  fun_prop

private lemma leibniz3_commutator
    {D₁ D₂ D₃ : (Euclidean 2 → ℝ) → (Euclidean 2 → ℝ)}
    (hD₂_reg : ∀ {r : ℕ} {f : Euclidean 2 → ℝ},
      ContDiff ℝ (r + 1 : ℕ) f → ContDiff ℝ (r : ℕ) (D₂ f))
    (hD₃_reg : ∀ {r : ℕ} {f : Euclidean 2 → ℝ},
      ContDiff ℝ (r + 1 : ℕ) f → ContDiff ℝ (r : ℕ) (D₃ f))
    (hD₁_add : ∀ {f g : Euclidean 2 → ℝ} {p : Euclidean 2},
      DifferentiableAt ℝ f p → DifferentiableAt ℝ g p →
      D₁ (fun q => f q + g q) p = D₁ f p + D₁ g p)
    (hD₂_add : ∀ {f g : Euclidean 2 → ℝ} {p : Euclidean 2},
      DifferentiableAt ℝ f p → DifferentiableAt ℝ g p →
      D₂ (fun q => f q + g q) p = D₂ f p + D₂ g p)
    (hD₁_mul : ∀ {f g : Euclidean 2 → ℝ} {p : Euclidean 2},
      DifferentiableAt ℝ f p → DifferentiableAt ℝ g p →
      D₁ (fun q => f q * g q) p = D₁ f p * g p + f p * D₁ g p)
    (hD₂_mul : ∀ {f g : Euclidean 2 → ℝ} {p : Euclidean 2},
      DifferentiableAt ℝ f p → DifferentiableAt ℝ g p →
      D₂ (fun q => f q * g q) p = D₂ f p * g p + f p * D₂ g p)
    (hD₃_mul : ∀ {f g : Euclidean 2 → ℝ} {p : Euclidean 2},
      DifferentiableAt ℝ f p → DifferentiableAt ℝ g p →
      D₃ (fun q => f q * g q) p = D₃ f p * g p + f p * D₃ g p)
    {A W : Euclidean 2 → ℝ} (hA : ContDiff ℝ (3 : ℕ) A) (hW : ContDiff ℝ (3 : ℕ) W)
    {E : ℝ} (p : Euclidean 2)
    (hW0 : |W p| ≤ E)
    (hW1a : |D₁ W p| ≤ E) (hW1b : |D₂ W p| ≤ E) (hW1c : |D₃ W p| ≤ E)
    (hW2a : |D₁ (D₂ W) p| ≤ E) (hW2b : |D₁ (D₃ W) p| ≤ E) (hW2c : |D₂ (D₃ W) p| ≤ E) :
    |D₁ (D₂ (D₃ (fun q => A q * W q))) p - A p * D₁ (D₂ (D₃ W)) p| ≤
      (|D₁ (D₂ (D₃ A)) p| + |D₂ (D₃ A) p| + |D₁ (D₃ A) p| + |D₃ A p| +
        |D₁ (D₂ A) p| + |D₂ A p| + |D₁ A p|) * E := by
  have hA2 : ContDiff ℝ (2 : ℕ) (D₃ A) := hD₃_reg hA
  have hW2 : ContDiff ℝ (2 : ℕ) (D₃ W) := hD₃_reg hW
  have hstep1 : D₃ (fun q => A q * W q) = fun q => D₃ A q * W q + A q * D₃ W q :=
    funext fun q => hD₃_mul (diff_of_c1 (r := 2) hA q) (diff_of_c1 (r := 2) hW q)
  have hstep2 : D₂ (D₃ (fun q => A q * W q)) = fun q =>
      (D₂ (D₃ A) q * W q + D₃ A q * D₂ W q) + (D₂ A q * D₃ W q + A q * D₂ (D₃ W) q) := by
    rw [hstep1]
    funext q
    have hd1 : DifferentiableAt ℝ (fun x => D₃ A x * W x) q :=
      (diff_of_c1 (r := 1) hA2 q).fun_mul (diff_of_c1 (r := 2) hW q)
    have hd2 : DifferentiableAt ℝ (fun x => A x * D₃ W x) q :=
      (diff_of_c1 (r := 2) hA q).fun_mul (diff_of_c1 (r := 1) hW2 q)
    rw [hD₂_add hd1 hd2,
      hD₂_mul (diff_of_c1 (r := 1) hA2 q) (diff_of_c1 (r := 2) hW q),
      hD₂_mul (diff_of_c1 (r := 2) hA q) (diff_of_c1 (r := 1) hW2 q)]
  have hA1_23 : DifferentiableAt ℝ (D₂ (D₃ A)) p := diff_of_c1 (r := 0) (hD₂_reg hA2) p
  have hA1_2 : DifferentiableAt ℝ (D₂ A) p := diff_of_c1 (r := 1) (hD₂_reg hA) p
  have hW1_2 : DifferentiableAt ℝ (D₂ W) p := diff_of_c1 (r := 1) (hD₂_reg hW) p
  have hW1_23 : DifferentiableAt ℝ (D₂ (D₃ W)) p := diff_of_c1 (r := 0) (hD₂_reg hW2) p
  have hA0 : DifferentiableAt ℝ A p := diff_of_c1 (r := 2) hA p
  have hW0d : DifferentiableAt ℝ W p := diff_of_c1 (r := 2) hW p
  have hA1_3 : DifferentiableAt ℝ (D₃ A) p := diff_of_c1 (r := 1) hA2 p
  have hW1_3 : DifferentiableAt ℝ (D₃ W) p := diff_of_c1 (r := 1) hW2 p
  have hstep3 : D₁ (D₂ (D₃ (fun q => A q * W q))) p - A p * D₁ (D₂ (D₃ W)) p =
      D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p +
      D₁ (D₃ A) p * D₂ W p + D₃ A p * D₁ (D₂ W) p +
      D₁ (D₂ A) p * D₃ W p + D₂ A p * D₁ (D₃ W) p +
      D₁ A p * D₂ (D₃ W) p := by
    rw [hstep2]
    rw [hD₁_add ((hA1_23.fun_mul hW0d).fun_add (hA1_3.fun_mul hW1_2))
          ((hA1_2.fun_mul hW1_3).fun_add (hA0.fun_mul hW1_23)),
        hD₁_add (hA1_23.fun_mul hW0d) (hA1_3.fun_mul hW1_2),
        hD₁_add (hA1_2.fun_mul hW1_3) (hA0.fun_mul hW1_23),
        hD₁_mul hA1_23 hW0d, hD₁_mul hA1_3 hW1_2,
        hD₁_mul hA1_2 hW1_3, hD₁_mul hA0 hW1_23]
    ring
  rw [hstep3]
  have hterm : ∀ a b : ℝ, |b| ≤ E → |a * b| ≤ |a| * E := fun a b hb => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg a)
  calc
    |D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p +
        D₁ (D₃ A) p * D₂ W p + D₃ A p * D₁ (D₂ W) p +
        D₁ (D₂ A) p * D₃ W p + D₂ A p * D₁ (D₃ W) p +
        D₁ A p * D₂ (D₃ W) p|
        ≤ |D₁ (D₂ (D₃ A)) p * W p| + |D₂ (D₃ A) p * D₁ W p| +
          |D₁ (D₃ A) p * D₂ W p| + |D₃ A p * D₁ (D₂ W) p| +
          |D₁ (D₂ A) p * D₃ W p| + |D₂ A p * D₁ (D₃ W) p| +
          |D₁ A p * D₂ (D₃ W) p| := by
            linarith [abs_add_le (D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p +
                        D₁ (D₃ A) p * D₂ W p + D₃ A p * D₁ (D₂ W) p +
                        D₁ (D₂ A) p * D₃ W p + D₂ A p * D₁ (D₃ W) p)
                        (D₁ A p * D₂ (D₃ W) p),
                      abs_add_le (D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p +
                        D₁ (D₃ A) p * D₂ W p + D₃ A p * D₁ (D₂ W) p +
                        D₁ (D₂ A) p * D₃ W p) (D₂ A p * D₁ (D₃ W) p),
                      abs_add_le (D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p +
                        D₁ (D₃ A) p * D₂ W p + D₃ A p * D₁ (D₂ W) p)
                        (D₁ (D₂ A) p * D₃ W p),
                      abs_add_le (D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p +
                        D₁ (D₃ A) p * D₂ W p) (D₃ A p * D₁ (D₂ W) p),
                      abs_add_le (D₁ (D₂ (D₃ A)) p * W p + D₂ (D₃ A) p * D₁ W p)
                        (D₁ (D₃ A) p * D₂ W p),
                      abs_add_le (D₁ (D₂ (D₃ A)) p * W p) (D₂ (D₃ A) p * D₁ W p)]
    _ ≤ |D₁ (D₂ (D₃ A)) p| * E + |D₂ (D₃ A) p| * E +
          |D₁ (D₃ A) p| * E + |D₃ A p| * E +
          |D₁ (D₂ A) p| * E + |D₂ A p| * E +
          |D₁ A p| * E := by
            gcongr
            · exact hterm _ _ hW0
            · exact hterm _ _ hW1a
            · exact hterm _ _ hW1b
            · exact hterm _ _ hW2a
            · exact hterm _ _ hW1c
            · exact hterm _ _ hW2b
            · exact hterm _ _ hW2c
    _ = (|D₁ (D₂ (D₃ A)) p| + |D₂ (D₃ A) p| + |D₁ (D₃ A) p| + |D₃ A p| +
          |D₁ (D₂ A) p| + |D₂ A p| + |D₁ A p|) * E := by ring

/-- Concrete 3rd-order commutator bounds for `∂_x ∂_y² (A * W)`, `spin3A1 (A * W)`, and
`spin3A2 (A * W)` in terms of `jet3Norm A p`. -/
lemma third_partials_commutator_jet3Norm
    {A W : Euclidean 2 → ℝ} (hA : ContDiff ℝ (3 : ℕ) A) (hW : ContDiff ℝ (3 : ℕ) W)
    {E : ℝ} (hE : 0 ≤ E) (p : Euclidean 2)
    (hW_jet2 :
      |W p| ≤ E ∧ |planarDx W p| ≤ E ∧ |planarDy W p| ≤ E ∧
      |planarDx (planarDx W) p| ≤ E ∧ |planarDx (planarDy W) p| ≤ E ∧
      |planarDy (planarDy W) p| ≤ E) :
    |planarDx (planarDy (planarDy (fun q => A q * W q))) p -
        A p * planarDx (planarDy (planarDy W)) p| ≤ 3 * jet3Norm A p * E ∧
    |spin3A1 (fun q => A q * W q) p - A p * spin3A1 W p| ≤ 12 * jet3Norm A p * E ∧
    |spin3A2 (fun q => A q * W q) p - A p * spin3A2 W p| ≤ 12 * jet3Norm A p * E := by
  obtain ⟨h0, hx, hy, hxx, hxy, hyy⟩ := hW_jet2
  have h_xxx := leibniz3_commutator
    contDiff_planarDx_b1 contDiff_planarDx_b1
    planarDx_add_s planarDx_add_s planarDx_mul_s planarDx_mul_s planarDx_mul_s
    hA hW p h0 hx hx hx hxx hxx hxx
  have h_xxy := leibniz3_commutator
    contDiff_planarDx_b1 contDiff_planarDy_b1
    planarDx_add_s planarDx_add_s planarDx_mul_s planarDx_mul_s planarDy_mul_s
    hA hW p h0 hx hx hy hxx hxy hxy
  have h_xyy := leibniz3_commutator
    contDiff_planarDy_b1 contDiff_planarDy_b1
    planarDx_add_s planarDy_add_s planarDx_mul_s planarDy_mul_s planarDy_mul_s
    hA hW p h0 hx hy hy hxy hxy hyy
  have h_yyy := leibniz3_commutator
    contDiff_planarDy_b1 contDiff_planarDy_b1
    planarDy_add_s planarDy_add_s planarDy_mul_s planarDy_mul_s planarDy_mul_s
    hA hW p h0 hy hy hy hyy hyy hyy
  have hn1 := abs_nonneg (planarDx A p)
  have hn2 := abs_nonneg (planarDy A p)
  have hn3 := abs_nonneg (planarDx (planarDx A) p)
  have hn4 := abs_nonneg (planarDx (planarDy A) p)
  have hn5 := abs_nonneg (planarDy (planarDx A) p)
  have hn6 := abs_nonneg (planarDy (planarDy A) p)
  have hn7 := abs_nonneg (planarDx (planarDx (planarDx A)) p)
  have hn8 := abs_nonneg (planarDx (planarDx (planarDy A)) p)
  have hn9 := abs_nonneg (planarDx (planarDy (planarDx A)) p)
  have hn10 := abs_nonneg (planarDx (planarDy (planarDy A)) p)
  have hn11 := abs_nonneg (planarDy (planarDx (planarDx A)) p)
  have hn12 := abs_nonneg (planarDy (planarDx (planarDy A)) p)
  have hn13 := abs_nonneg (planarDy (planarDy (planarDx A)) p)
  have hn14 := abs_nonneg (planarDy (planarDy (planarDy A)) p)
  have hj_xxx : |planarDx (planarDx (planarDx A)) p| + |planarDx (planarDx A) p| +
      |planarDx (planarDx A) p| + |planarDx A p| + |planarDx (planarDx A) p| +
      |planarDx A p| + |planarDx A p| ≤ 3 * jet3Norm A p := by
    unfold jet3Norm; linarith
  have hj_xxy : |planarDx (planarDx (planarDy A)) p| + |planarDx (planarDy A) p| +
      |planarDx (planarDy A) p| + |planarDy A p| + |planarDx (planarDx A) p| +
      |planarDx A p| + |planarDx A p| ≤ 3 * jet3Norm A p := by
    unfold jet3Norm; linarith
  have hj_xyy : |planarDx (planarDy (planarDy A)) p| + |planarDy (planarDy A) p| +
      |planarDx (planarDy A) p| + |planarDy A p| + |planarDx (planarDy A) p| +
      |planarDy A p| + |planarDx A p| ≤ 3 * jet3Norm A p := by
    unfold jet3Norm; linarith
  have hj_yyy : |planarDy (planarDy (planarDy A)) p| + |planarDy (planarDy A) p| +
      |planarDy (planarDy A) p| + |planarDy A p| + |planarDy (planarDy A) p| +
      |planarDy A p| + |planarDy A p| ≤ 3 * jet3Norm A p := by
    unfold jet3Norm; linarith
  have hb_xxx := h_xxx.trans (mul_le_mul_of_nonneg_right hj_xxx hE)
  have hb_xxy := h_xxy.trans (mul_le_mul_of_nonneg_right hj_xxy hE)
  have hb_xyy := h_xyy.trans (mul_le_mul_of_nonneg_right hj_xyy hE)
  have hb_yyy := h_yyy.trans (mul_le_mul_of_nonneg_right hj_yyy hE)
  refine ⟨hb_xyy, ?_, ?_⟩
  · unfold spin3A1
    have hsplit : (planarDx (planarDx (planarDx (fun q => A q * W q))) p -
        3 * planarDx (planarDy (planarDy (fun q => A q * W q))) p) -
        A p * (planarDx (planarDx (planarDx W)) p - 3 * planarDx (planarDy (planarDy W)) p) =
        (planarDx (planarDx (planarDx (fun q => A q * W q))) p -
          A p * planarDx (planarDx (planarDx W)) p) -
        3 * (planarDx (planarDy (planarDy (fun q => A q * W q))) p -
          A p * planarDx (planarDy (planarDy W)) p) := by ring
    rw [hsplit]
    calc
      |_ - 3 * _| ≤ |planarDx (planarDx (planarDx (fun q => A q * W q))) p -
            A p * planarDx (planarDx (planarDx W)) p| +
          |3 * (planarDx (planarDy (planarDy (fun q => A q * W q))) p -
            A p * planarDx (planarDy (planarDy W)) p)| := abs_sub _ _
      _ = |planarDx (planarDx (planarDx (fun q => A q * W q))) p -
            A p * planarDx (planarDx (planarDx W)) p| +
          3 * |planarDx (planarDy (planarDy (fun q => A q * W q))) p -
            A p * planarDx (planarDy (planarDy W)) p| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ ≤ 3 * jet3Norm A p * E + 3 * (3 * jet3Norm A p * E) := by gcongr
      _ = 12 * jet3Norm A p * E := by ring
  · unfold spin3A2
    have hsplit : (3 * planarDx (planarDx (planarDy (fun q => A q * W q))) p -
        planarDy (planarDy (planarDy (fun q => A q * W q))) p) -
        A p * (3 * planarDx (planarDx (planarDy W)) p - planarDy (planarDy (planarDy W)) p) =
        3 * (planarDx (planarDx (planarDy (fun q => A q * W q))) p -
          A p * planarDx (planarDx (planarDy W)) p) -
        (planarDy (planarDy (planarDy (fun q => A q * W q))) p -
          A p * planarDy (planarDy (planarDy W)) p) := by ring
    rw [hsplit]
    calc
      |3 * _ - _| ≤ |3 * (planarDx (planarDx (planarDy (fun q => A q * W q))) p -
            A p * planarDx (planarDx (planarDy W)) p)| +
          |planarDy (planarDy (planarDy (fun q => A q * W q))) p -
            A p * planarDy (planarDy (planarDy W)) p| := abs_sub _ _
      _ = 3 * |planarDx (planarDx (planarDy (fun q => A q * W q))) p -
            A p * planarDx (planarDx (planarDy W)) p| +
          |planarDy (planarDy (planarDy (fun q => A q * W q))) p -
            A p * planarDy (planarDy (planarDy W)) p| := by
            rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
      _ ≤ 3 * (3 * jet3Norm A p * E) + 3 * jet3Norm A p * E := by gcongr
      _ = 12 * jet3Norm A p * E := by ring

/-- Compactness supremum bound on `[0, 1]²` for any continuous planar function. -/
lemma exists_sup_on_unitSquare {G : Euclidean 2 → ℝ} (hG : Continuous G) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |G (planarPt x y)| ≤ B := by
  have hpt_cont : Continuous (fun q : ℝ × ℝ => planarPt q.1 q.2) := by
    have hrew : (fun q : ℝ × ℝ => planarPt q.1 q.2) =
        fun q : ℝ × ℝ => q.1 • coordinateVector 2 0 + q.2 • coordinateVector 2 1 := by
      funext q; ext i; fin_cases i <;> simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    rw [hrew]
    exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)
  have hcpt : Continuous (fun q : ℝ × ℝ => G (planarPt q.1 q.2)) := hG.comp hpt_cont
  obtain ⟨B₀, hB₀⟩ :=
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).exists_bound_of_continuousOn
      hcpt.continuousOn
  refine ⟨max B₀ 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  have h := hB₀ (x, y) ⟨hx, hy⟩
  rw [Real.norm_eq_abs] at h
  exact h.trans (le_max_left _ _)

/-- Uniform `x`-Lipschitz constant on `[0, 1]²` for any `C¹` planar function. -/
lemma exists_x_lipschitz_on_unitSquare {G : Euclidean 2 → ℝ} (hG : ContDiff ℝ (1 : ℕ) G) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
      |G (planarPt x₁ y) - G (planarPt x₂ y)| ≤ L * |x₁ - x₂| := by
  have hGx_cont : Continuous (planarDx G) := (contDiff_planarDx_b1 (r := 0) hG).continuous
  obtain ⟨L, hL0, hL⟩ := exists_sup_on_unitSquare hGx_cont
  refine ⟨L, hL0, ?_⟩
  intro y hy x₁ hx₁ x₂ hx₂
  have hderiv : ∀ s : ℝ, HasDerivAt (fun t : ℝ => G (planarPt t y)) (planarDx G (planarPt s y)) s := by
    intro s
    have hpt : HasDerivAt (fun t : ℝ => planarPt t y) (coordinateVector 2 0) s := by
      have hrew : (fun t : ℝ => planarPt t y) =
          fun t : ℝ => y • coordinateVector 2 1 + t • coordinateVector 2 0 := by
        funext t; ext i; fin_cases i <;> simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply, add_comm]
      rw [hrew]
      simpa [one_smul] using
        ((hasDerivAt_id s).smul_const (coordinateVector 2 0)).const_add (y • coordinateVector 2 1)
    have hd := diff_of_c1 (r := 0) hG (planarPt s y)
    unfold planarDx
    rw [coordinatePartial_eq_fderiv hd]
    exact hd.hasFDerivAt.comp_hasDerivAt s hpt
  have hline_cont : Continuous (fun s : ℝ => planarPt s y) := by
    have hrew : (fun s : ℝ => planarPt s y) =
        fun s : ℝ => s • coordinateVector 2 0 + y • coordinateVector 2 1 := by
      funext s; ext i; fin_cases i <;> simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    rw [hrew]
    exact (continuous_id.smul continuous_const).add continuous_const
  have hGx_line_cont : Continuous (fun s : ℝ => planarDx G (planarPt s y)) :=
    hGx_cont.comp hline_cont
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hGx_line_cont.intervalIntegrable x₂ x₁)
  have hsub : |G (planarPt x₁ y) - G (planarPt x₂ y)| =
      ‖∫ s in x₂..x₁, planarDx G (planarPt s y)‖ := by
    rw [Real.norm_eq_abs, hftc]
  rw [hsub]
  have hbound : ∀ s ∈ uIoc x₂ x₁, ‖planarDx G (planarPt s y)‖ ≤ L := by
    intro s hs
    have hs_mem : s ∈ Icc (0 : ℝ) 1 := by
      have hu := uIoc_subset_uIcc hs
      exact ⟨le_trans (le_min hx₂.1 hx₁.1) hu.1, le_trans hu.2 (max_le hx₂.2 hx₁.2)⟩
    rw [Real.norm_eq_abs]
    exact hL s hs_mem y hy
  exact intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- Phase- and sign-invariant wrapper around `antiperiodic_haar_shift_bound_1d`. -/
lemma antiperiodic_phase_sign_bound_1d
    {F g : ℝ → ℝ} {L B a φ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hL0 : 0 ≤ L) (_hB0 : 0 ≤ B)
    (ha : a = (N : ℝ) ∨ a = -(N : ℝ))
    (hF_cont : Continuous F) (hg_cont : Continuous g)
    (hF_lip : ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1, |F x₁ - F x₂| ≤ L * |x₁ - x₂|)
    (hanti : ∀ t : ℝ, g (t + 1 / 2) = -g t)
    (hB : ∀ t : ℝ, |g t| ≤ B) :
    |∫ x in (0 : ℝ)..1, F x * g (a * x + φ)| ≤ (L * B) / (4 * (N : ℝ)) := by
  let g_shift : ℝ → ℝ := fun t => if a = (N : ℝ) then g (t + φ) else g (-t + φ)
  have hg_shift_cont : Continuous g_shift := by
    dsimp [g_shift]
    split_ifs <;> fun_prop
  have hg_shift_anti : ∀ t : ℝ, g_shift (t + 1 / 2) = -g_shift t := by
    intro t
    dsimp [g_shift]
    split_ifs with hpos
    · have h1 : t + 1 / 2 + φ = (t + φ) + 1 / 2 := by ring
      rw [h1, hanti]
    · have h1 : -(t + 1 / 2) + φ = (-t + φ - 1 / 2) := by ring
      have h2 := hanti (-t + φ - 1 / 2)
      have h3 : -t + φ - 1 / 2 + 1 / 2 = -t + φ := by ring
      rw [h3] at h2
      rw [h1]
      linarith
  have hmatch : ∀ x : ℝ, g (a * x + φ) = g_shift ((N : ℝ) * x) := by
    intro x
    dsimp [g_shift]
    rcases ha with rfl | rfl
    · simp
    · have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
      have hne : -(N : ℝ) ≠ (N : ℝ) := by linarith
      split_ifs with heq
      · exact absurd heq hne
      · ring_nf
  simp_rw [hmatch]
  have hhaar := antiperiodic_haar_shift_bound_1d hN hF_cont hg_shift_cont hF_lip hg_shift_anti
  have hint_B : (∫ t in (0 : ℝ)..1, |g_shift t|) ≤ B := by
    calc
      (∫ t in (0 : ℝ)..1, |g_shift t|) ≤ ∫ _t in (0 : ℝ)..1, B :=
        intervalIntegral.integral_mono_on zero_le_one
          (hg_shift_cont.abs.intervalIntegrable 0 1)
          (continuous_const.intervalIntegrable 0 1)
          (fun t _ => by dsimp [g_shift]; split_ifs <;> exact hB _)
      _ = B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  calc
    |∫ x in (0 : ℝ)..1, F x * g_shift ((N : ℝ) * x)|
        ≤ (L / (4 * (N : ℝ))) * ∫ t in (0 : ℝ)..1, |g_shift t| := hhaar
    _ ≤ (L / (4 * (N : ℝ))) * B :=
        mul_le_mul_of_nonneg_left hint_B (by positivity)
    _ = (L * B) / (4 * (N : ℝ)) := by ring

/-- Quantitative 1D periodic cell-mean equidistribution bound on `[0, 1]` (phase- and
sign-invariant). -/
lemma periodic_phase_sign_mean_bound_1d
    {F q : ℝ → ℝ} {L B a φ : ℝ} {N : ℕ}
    (hN : 1 ≤ N) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B)
    (ha : a = (N : ℝ) ∨ a = -(N : ℝ))
    (hF_cont : Continuous F) (hq_cont : Continuous q)
    (hF_lip : ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1, |F x₁ - F x₂| ≤ L * |x₁ - x₂|)
    (hper : ∀ t : ℝ, q (t + 1) = q t)
    (hB : ∀ t : ℝ, |q t| ≤ B) :
    |(∫ x in (0 : ℝ)..1, F x * q (a * x + φ)) -
        (∫ t in (0 : ℝ)..1, q t) * ∫ x in (0 : ℝ)..1, F x| ≤
      (2 * B * L) / (N : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hN)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  let μ : ℝ := ∫ t in (0 : ℝ)..1, q t
  have hμ_abs : |μ| ≤ B := by
    dsimp [μ]
    calc
      |∫ t in (0 : ℝ)..1, q t| ≤ ∫ t in (0 : ℝ)..1, |q t| := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := q) zero_le_one
      _ ≤ ∫ _t in (0 : ℝ)..1, B :=
        intervalIntegral.integral_mono_on zero_le_one
          (hq_cont.abs.intervalIntegrable 0 1) (continuous_const.intervalIntegrable 0 1)
          (fun t _ => hB t)
      _ = B := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hshift_int : ∀ ψ : ℝ, (∫ t in (0 : ℝ)..1, q (t + ψ)) = μ := by
    let Φ : ℝ → ℝ := fun ψ => (∫ u in (0 : ℝ)..(ψ + 1), q u) - ∫ u in (0 : ℝ)..ψ, q u
    have hΦ_eq : ∀ ψ : ℝ, (∫ t in (0 : ℝ)..1, q (t + ψ)) = Φ ψ := by
      intro ψ
      have h1 := intervalIntegral.integral_comp_add_right q ψ (a := 0) (b := 1)
      rw [zero_add, add_comm 1 ψ] at h1
      have h2 := intervalIntegral.integral_add_adjacent_intervals
        (hq_cont.intervalIntegrable (μ := volume) 0 ψ)
        (hq_cont.intervalIntegrable (μ := volume) ψ (ψ + 1))
      dsimp [Φ]
      linarith
    have hΦ_deriv : ∀ ψ : ℝ, HasDerivAt Φ 0 ψ := by
      intro ψ
      have hinner : HasDerivAt (fun s : ℝ => s + (1 : ℝ)) 1 ψ := (hasDerivAt_id ψ).add_const 1
      have hd1 : HasDerivAt (fun s : ℝ => ∫ u in (0 : ℝ)..(s + 1), q u) (q (ψ + 1) * 1) ψ :=
        HasDerivAt.comp (h₂ := fun x : ℝ => ∫ u in (0 : ℝ)..x, q u)
          (h := fun s : ℝ => s + (1 : ℝ)) ψ
          (intervalIntegral.integral_hasDerivAt_right
            (hq_cont.intervalIntegrable 0 (ψ + 1))
            (hq_cont.stronglyMeasurableAtFilter volume (𝓝 (ψ + 1))) hq_cont.continuousAt) hinner
      have hd2 := intervalIntegral.integral_hasDerivAt_right
        (hq_cont.intervalIntegrable 0 ψ)
        (hq_cont.stronglyMeasurableAtFilter volume (𝓝 ψ)) hq_cont.continuousAt
      convert hd1.sub hd2 using 1
      rw [hper ψ]
      ring
    intro ψ
    rw [hΦ_eq ψ]
    have hc := is_const_of_deriv_eq_zero (fun s => (hΦ_deriv s).differentiableAt)
      (fun s => (hΦ_deriv s).deriv) ψ 0
    rw [hc]
    dsimp [Φ, μ]
    simp only [zero_add, intervalIntegral.integral_same, sub_zero]
  let Q : ℝ → ℝ := fun t => if a = (N : ℝ) then q (t + φ) else q (-t + φ)
  have hQ_cont : Continuous Q := by dsimp [Q]; split_ifs <;> fun_prop
  have hQ_per : ∀ t : ℝ, Q (t + 1) = Q t := by
    intro t; dsimp [Q]
    split_ifs
    · have h1 : t + 1 + φ = (t + φ) + 1 := by ring
      rw [h1, hper]
    · have h1 : -(t + 1) + φ = (-t + φ - 1) := by ring
      have h2 := hper (-t + φ - 1)
      have h3 : -t + φ - 1 + 1 = -t + φ := by ring
      rw [h3] at h2
      rw [h1, ← h2]
  have hQ_int : (∫ t in (0 : ℝ)..1, Q t) = μ := by
    dsimp [Q]
    split_ifs
    · exact hshift_int φ
    · calc
        (∫ t in (0 : ℝ)..1, q (-t + φ))
            = ∫ t in (0 : ℝ)..1, q (-(t - φ)) := by
                apply intervalIntegral.integral_congr; intro t _; dsimp only; ring_nf
        _ = ∫ u in (0 - φ)..(1 - φ), q (-u) :=
              intervalIntegral.integral_comp_sub_right (fun u => q (-u)) φ
        _ = ∫ v in (-(1 - φ))..(-(0 - φ)), q v := intervalIntegral.integral_comp_neg q
        _ = ∫ v in ((0 : ℝ) + (φ - 1))..((1 : ℝ) + (φ - 1)), q v := by
              have h1 : -(1 - φ) = 0 + (φ - 1) := by ring
              have h2 : -(0 - φ) = 1 + (φ - 1) := by ring
              rw [h1, h2]
        _ = ∫ t in (0 : ℝ)..1, q (t + (φ - 1)) :=
              (intervalIntegral.integral_comp_add_right q (φ - 1)).symm
        _ = μ := hshift_int (φ - 1)
  have hmatch : ∀ x : ℝ, q (a * x + φ) = Q ((N : ℝ) * x) := by
    intro x; dsimp [Q]
    rcases ha with rfl | rfl
    · simp
    · have hne : -(N : ℝ) ≠ (N : ℝ) := by linarith
      split_ifs with heq
      · exact absurd heq hne
      · ring_nf
  let q₀ : ℝ → ℝ := fun t => Q t - μ
  have hq₀_cont : Continuous q₀ := hQ_cont.sub continuous_const
  have hq₀_bound : ∀ t : ℝ, |q₀ t| ≤ 2 * B := by
    intro t
    have hQt : |Q t| ≤ B := by dsimp [Q]; split_ifs <;> exact hB _
    dsimp [q₀]
    linarith [abs_sub (Q t) μ]
  have hq₀_per_nat : ∀ (k : ℕ) (t : ℝ), q₀ (t + (k : ℝ)) = q₀ t := by
    intro k; induction k with
    | zero => intro t; simp
      | succ k ih =>
          intro t; push_cast
          have h1 : t + ((k : ℝ) + 1) = (t + (k : ℝ)) + 1 := by ring
          rw [h1]; dsimp [q₀]; rw [hQ_per]; exact ih t
  have hq₀_zero_mean : (∫ t in (0 : ℝ)..1, q₀ t) = 0 := by
    dsimp [q₀]
    rw [intervalIntegral.integral_sub (hQ_cont.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1), hQ_int, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hrew_lhs : (∫ x in (0 : ℝ)..1, F x * q (a * x + φ)) - μ * ∫ x in (0 : ℝ)..1, F x =
      ∫ x in (0 : ℝ)..1, F x * q₀ ((N : ℝ) * x) := by
    simp_rw [hmatch]
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun x : ℝ => F x * Q ((N : ℝ) * x))).intervalIntegrable 0 1)
      ((by fun_prop : Continuous (fun x : ℝ => μ * F x)).intervalIntegrable 0 1)]
    apply intervalIntegral.integral_congr; intro x _; dsimp [q₀]; ring
  rw [hrew_lhs]
  have hFq₀_cont : Continuous (fun x : ℝ => F x * q₀ ((N : ℝ) * x)) := by fun_prop
  let pts : ℕ → ℝ := fun k => (k : ℝ) / (N : ℝ)
  have hpts0 : pts 0 = 0 := by simp [pts]
  have hptsN : pts N = 1 := by simp [pts, div_self hN_ne]
  have hcell : ∀ k < N,
      |∫ x in (pts k)..(pts (k + 1)), F x * q₀ ((N : ℝ) * x)| ≤ (2 * B * L) / (N : ℝ) ^ 2 := by
    intro k hk
    have hlo_le_hi : pts k ≤ pts (k + 1) := by dsimp [pts]; gcongr; linarith
    have hcell_zero : (∫ x in (pts k)..(pts (k + 1)), q₀ ((N : ℝ) * x)) = 0 := by
      calc
        (∫ x in (pts k)..(pts (k + 1)), q₀ ((N : ℝ) * x))
            = (N : ℝ)⁻¹ • ∫ t in ((N : ℝ) * pts k)..((N : ℝ) * pts (k + 1)), q₀ t :=
                intervalIntegral.integral_comp_mul_left (f := q₀) hN_ne
        _ = (N : ℝ)⁻¹ * ∫ t in ((0 : ℝ) + (k : ℝ))..((1 : ℝ) + (k : ℝ)), q₀ t := by
              have hk1 : (N : ℝ) * pts k = 0 + (k : ℝ) := by dsimp [pts]; field_simp [hN_ne]; ring
              have hk2 : (N : ℝ) * pts (k + 1) = 1 + (k : ℝ) := by
                dsimp [pts]; push_cast; field_simp [hN_ne]; ring
              rw [hk1, hk2, smul_eq_mul]
        _ = (N : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, q₀ (t + (k : ℝ)) := by
              rw [← intervalIntegral.integral_comp_add_right q₀ (k : ℝ)]
        _ = (N : ℝ)⁻¹ * ∫ t in (0 : ℝ)..1, q₀ t := by simp_rw [hq₀_per_nat k]
        _ = 0 := by rw [hq₀_zero_mean, mul_zero]
    have hsub_const : (∫ x in (pts k)..(pts (k + 1)), F x * q₀ ((N : ℝ) * x)) =
        ∫ x in (pts k)..(pts (k + 1)), (F x - F (pts k)) * q₀ ((N : ℝ) * x) := by
      have hc0 : (∫ x in (pts k)..(pts (k + 1)), F (pts k) * q₀ ((N : ℝ) * x)) = 0 := by
        rw [intervalIntegral.integral_const_mul, hcell_zero, mul_zero]
      rw [← sub_zero (∫ x in (pts k)..(pts (k + 1)), F x * q₀ ((N : ℝ) * x)), ← hc0,
        ← intervalIntegral.integral_sub
          (hFq₀_cont.intervalIntegrable _ _)
          ((by fun_prop : Continuous (fun x : ℝ => F (pts k) * q₀ ((N : ℝ) * x))).intervalIntegrable _ _)]
      apply intervalIntegral.integral_congr; intro x _; dsimp only; ring
    rw [hsub_const, ← Real.norm_eq_abs]
    have hpt_bound : ∀ x ∈ uIoc (pts k) (pts (k + 1)),
        ‖(F x - F (pts k)) * q₀ ((N : ℝ) * x)‖ ≤ (2 * B * L) / (N : ℝ) := by
      intro x hx
      rw [uIoc_of_le hlo_le_hi] at hx
      have hpk_mem : pts k ∈ Icc (0 : ℝ) 1 := by
        refine ⟨by dsimp [pts]; positivity, (div_le_one hN_pos).mpr (by exact_mod_cast le_of_lt hk)⟩
      have hpk1_le : pts (k + 1) ≤ 1 :=
        (div_le_one hN_pos).mpr (by exact_mod_cast Nat.succ_le_of_lt hk)
      have hx_mem : x ∈ Icc (0 : ℝ) 1 := ⟨hpk_mem.1.trans (le_of_lt hx.1), hx.2.trans hpk1_le⟩
      have hdx : |x - pts k| ≤ 1 / (N : ℝ) := by
        rw [abs_of_nonneg (by linarith [hx.1])]
        have hlen : pts (k + 1) - pts k = 1 / (N : ℝ) := by
          dsimp [pts]; push_cast; field_simp [hN_ne]; ring
        linarith [hx.2, hlen]
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |F x - F (pts k)| * |q₀ ((N : ℝ) * x)|
            ≤ (L * |x - pts k|) * (2 * B) :=
              mul_le_mul (hF_lip x hx_mem (pts k) hpk_mem) (hq₀_bound _) (abs_nonneg _)
                (mul_nonneg hL0 (abs_nonneg _))
        _ ≤ (L * (1 / (N : ℝ))) * (2 * B) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdx hL0) (by positivity)
        _ = (2 * B * L) / (N : ℝ) := by ring
    calc
      ‖∫ x in (pts k)..(pts (k + 1)), (F x - F (pts k)) * q₀ ((N : ℝ) * x)‖
          ≤ ((2 * B * L) / (N : ℝ)) * |pts (k + 1) - pts k| :=
              intervalIntegral.norm_integral_le_of_norm_le_const hpt_bound
      _ = (2 * B * L) / (N : ℝ) ^ 2 := by
            have hlen : pts (k + 1) - pts k = 1 / (N : ℝ) := by
              dsimp [pts]; push_cast; field_simp [hN_ne]; ring
            rw [hlen, abs_of_pos (by positivity)]; ring
  have hsum_eq : (∫ x in (0 : ℝ)..1, F x * q₀ ((N : ℝ) * x)) =
      ∑ k ∈ Finset.range N, ∫ x in (pts k)..(pts (k + 1)), F x * q₀ ((N : ℝ) * x) := by
    rw [← hpts0, ← hptsN]
    exact (intervalIntegral.sum_integral_adjacent_intervals (a := pts) (n := N)
      (fun k _ => hFq₀_cont.intervalIntegrable _ _)).symm
  rw [hsum_eq]
  calc
    |∑ k ∈ Finset.range N, ∫ x in (pts k)..(pts (k + 1)), F x * q₀ ((N : ℝ) * x)|
        ≤ ∑ k ∈ Finset.range N, |∫ x in (pts k)..(pts (k + 1)), F x * q₀ ((N : ℝ) * x)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range N, (2 * B * L) / (N : ℝ) ^ 2 :=
          Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.mp hk)
    _ = (2 * B * L) / (N : ℝ) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp [hN_ne]

/-! ### Section 2: 3-Ray Stopped-Martingale Staircase `(staircaseU K, staircaseH K)` -/

/-- Cyclic 3-ray schedule `(v₀, v₁, v₂, v₀, v₁, v₂, ...)` built from `spin3Ray0..2`. -/
def spin3Ray (k : ℕ) : ℝ × ℝ :=
  match k % 3 with
  | 0 => spin3Ray0
  | 1 => spin3Ray1
  | _ => spin3Ray2

lemma spin3Ray_norm_sq (k : ℕ) : (spin3Ray k).1 ^ 2 + (spin3Ray k).2 ^ 2 = 1 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> simp [spin3Ray, h, spin3Ray0, spin3Ray1, spin3Ray2] <;>
    nlinarith [hsq3]

lemma abs_spin3Ray_fst_le_one (k : ℕ) : |(spin3Ray k).1| ≤ 1 := by
  have h := spin3Ray_norm_sq k
  have h2 : (spin3Ray k).1 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg (spin3Ray k).2]
  exact (sq_le_sq.mp h2).trans (by norm_num)

lemma abs_spin3Ray_snd_le_one (k : ℕ) : |(spin3Ray k).2| ≤ 1 := by
  have h := spin3Ray_norm_sq k
  have h2 : (spin3Ray k).2 ^ 2 ≤ 1 ^ 2 := by nlinarith [sq_nonneg (spin3Ray k).1]
  exact (sq_le_sq.mp h2).trans (by norm_num)

lemma spin3Ray_sq_mul_sq (k : ℕ) :
    (spin3Ray k).1 ^ 2 * (spin3Ray k).2 ^ 2 = if k % 3 = 0 then 0 else 3 / 16 := by
  have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> simp [spin3Ray, h, spin3Ray0, spin3Ray1, spin3Ray2] <;>
    nlinarith [hsq3]

/-- Exact integer `x`-frequency of `(2 * M) * (spin3Ray k).1`. -/
def xFreqNat (k M : ℕ) : ℕ :=
  if k % 3 = 0 then 2 * M else M

lemma le_xFreqNat (k M : ℕ) : M ≤ xFreqNat k M := by
  unfold xFreqNat
  split_ifs <;> omega

lemma xFreqNat_ray_fst (k M : ℕ) :
    (2 * (M : ℝ)) * (spin3Ray k).1 = (xFreqNat k M : ℝ) ∨
      (2 * (M : ℝ)) * (spin3Ray k).1 = -(xFreqNat k M : ℝ) := by
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h
  · left; simp [xFreqNat, spin3Ray, h, spin3Ray0]
  · right; simp [xFreqNat, spin3Ray, h, spin3Ray1]; ring
  · right; simp [xFreqNat, spin3Ray, h, spin3Ray2]; ring

lemma spin3_ray_planeWave (k : ℕ) (Λ : ℝ) {g₀ g₁ g₂ g₃ : ℝ → ℝ}
    (hg₀ : ∀ t : ℝ, HasDerivAt g₀ (g₁ t) t)
    (hg₁ : ∀ t : ℝ, HasDerivAt g₁ (g₂ t) t)
    (hg₂ : ∀ t : ℝ, HasDerivAt g₂ (g₃ t) t)
    (p : Euclidean 2) :
    spin3A1 (planarPlaneWave (Λ * (spin3Ray k).1) (Λ * (spin3Ray k).2) g₀) p =
      Λ ^ 3 * g₃ (Λ * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) ∧
    spin3A2 (planarPlaneWave (Λ * (spin3Ray k).1) (Λ * (spin3Ray k).2) g₀) p = 0 := by
  have hobs := spin3_three_ray_obstruction Λ hg₀ hg₁ hg₂ p
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h <;> simp only [spin3Ray, h]
  · exact hobs.2.2.1
  · exact hobs.2.2.2.1
  · exact hobs.2.2.2.2

/-- Partial sums of `spin3Ray` for Abel summation of `∇ staircaseH`. -/
def rayPartialSum : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | k + 1 => ((rayPartialSum k).1 + (spin3Ray k).1, (rayPartialSum k).2 + (spin3Ray k).2)

lemma rayPartialSum_add_three (k : ℕ) : rayPartialSum (k + 3) = rayPartialSum k := by
  simp only [rayPartialSum]
  have hmod : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hmod with h | h | h
  · have h1 : (k + 1) % 3 = 1 := by omega
    have h2 : (k + 2) % 3 = 2 := by omega
    ext <;> simp [spin3Ray, h, h1, h2, spin3Ray0, spin3Ray1, spin3Ray2] <;> ring
  · have h1 : (k + 1) % 3 = 2 := by omega
    have h2 : (k + 2) % 3 = 0 := by omega
    ext <;> simp [spin3Ray, h, h1, h2, spin3Ray0, spin3Ray1, spin3Ray2] <;> ring
  · have h1 : (k + 1) % 3 = 0 := by omega
    have h2 : (k + 2) % 3 = 1 := by omega
    ext <;> simp [spin3Ray, h, h1, h2, spin3Ray0, spin3Ray1, spin3Ray2] <;> ring

lemma abs_rayPartialSum_le_one (k : ℕ) :
    |(rayPartialSum k).1| ≤ 1 ∧ |(rayPartialSum k).2| ≤ 1 := by
  induction k using Nat.strongRecOn with
  | ind n ih =>
      rcases lt_or_ge n 3 with hn | hn
      · interval_cases n
        · simp [rayPartialSum]
        · simp [rayPartialSum, spin3Ray, spin3Ray0]
        · simp only [rayPartialSum, spin3Ray, spin3Ray0, spin3Ray1]
          have hsq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
          have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
          have hs2 : Real.sqrt 3 ≤ 2 := by nlinarith
          refine ⟨by norm_num, ?_⟩
          rw [zero_add, abs_of_nonneg (by positivity)]
          linarith
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
        rw [rayPartialSum_add_three]
        exact ih m (by omega)

/-- Smooth `C⁴` 2D box cutoff supported in `[1/8, 7/8]²` and equal to `1` on `[1/4, 3/4]²`. -/
def boxCutoff2D (p : Euclidean 2) : ℝ :=
  boxCutoff1D (p 0) * boxCutoff1D (p 1)

lemma contDiff_boxCutoff2D : ContDiff ℝ (4 : ℕ) boxCutoff2D := by
  unfold boxCutoff2D
  exact (contDiff_boxCutoff1D.comp
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff).mul
    (contDiff_boxCutoff1D.comp
      (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff)

lemma boxCutoff2D_nonneg (p : Euclidean 2) : 0 ≤ boxCutoff2D p :=
  mul_nonneg (boxCutoff1D_nonneg _) (boxCutoff1D_nonneg _)

lemma boxCutoff2D_le_one (p : Euclidean 2) : boxCutoff2D p ≤ 1 := by
  calc
    boxCutoff2D p ≤ 1 * 1 :=
      mul_le_mul (boxCutoff1D_le_one _) (boxCutoff1D_le_one _) (boxCutoff1D_nonneg _) zero_le_one
    _ = 1 := mul_one 1

lemma boxCutoff2D_zero_outside {p : Euclidean 2}
    (hp : p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) :
    boxCutoff2D p = 0 := by
  unfold boxCutoff2D
  rcases hp with h | h | h | h
  · rw [boxCutoff1D_of_le h, zero_mul]
  · rw [boxCutoff1D_of_ge h, zero_mul]
  · rw [boxCutoff1D_of_le h, mul_zero]
  · rw [boxCutoff1D_of_ge h, mul_zero]

/-- Transition width parameter `δ_K = 1 / (64 * (K + 3))` satisfying `0 < δ_K ≤ 1/8` for all `K`. -/
def staircaseDelta (K : ℕ) : ℝ :=
  1 / (64 * ((K : ℝ) + 3))

lemma staircaseDelta_pos (K : ℕ) : 0 < staircaseDelta K := by
  unfold staircaseDelta; positivity

lemma staircaseDelta_le_eighth (K : ℕ) : staircaseDelta K ≤ 1 / 8 := by
  unfold staircaseDelta
  exact one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) K])

/-- Cumulative stopped-martingale weight `A_k(p) = χ(p) * ∏_{j < k} η_δ(Λ_j (v_j · p))`. -/
def ampProd (δ : ℝ) (Λ : ℕ → ℝ) : ℕ → Euclidean 2 → ℝ
  | 0 => boxCutoff2D
  | k + 1 => fun p => ampProd δ Λ k p *
      etaWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))

lemma ampProd_congr (δ : ℝ) {Λ₁ Λ₂ : ℕ → ℝ} {k : ℕ}
    (h : ∀ j < k, Λ₁ j = Λ₂ j) : ampProd δ Λ₁ k = ampProd δ Λ₂ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      funext p
      simp only [ampProd]
      rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h k (Nat.lt_succ_self k)]

lemma contDiff_ampProd {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (Λ : ℕ → ℝ) (k : ℕ) :
    ContDiff ℝ (4 : ℕ) (ampProd δ Λ k) := by
  induction k with
  | zero => exact contDiff_boxCutoff2D
  | succ k ih =>
      have heta : ContDiff ℝ (4 : ℕ)
          (fun p : Euclidean 2 => etaWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) := by
        have hrew : (fun p : Euclidean 2 =>
            etaWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) =
            planarPlaneWave (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2) (etaWave δ) := by
          funext p; unfold planarPlaneWave; ring_nf
        rw [hrew]
        exact contDiff_planarPlaneWave _ _ (contDiff_etaWave hδ0 hδ1)
      exact ih.mul heta

lemma ampProd_nonneg (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) (p : Euclidean 2) :
    0 ≤ ampProd δ Λ k p := by
  induction k with
  | zero => exact boxCutoff2D_nonneg p
  | succ k ih => exact mul_nonneg ih (etaWave_nonneg _ _)

lemma ampProd_succ_le (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) (p : Euclidean 2) :
    ampProd δ Λ (k + 1) p ≤ ampProd δ Λ k p := by
  simp only [ampProd]
  calc
    ampProd δ Λ k p * etaWave δ _ ≤ ampProd δ Λ k p * 1 :=
      mul_le_mul_of_nonneg_left (etaWave_le_one _ _) (ampProd_nonneg δ Λ k p)
    _ = ampProd δ Λ k p := mul_one _

lemma ampProd_le_one (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) (p : Euclidean 2) :
    ampProd δ Λ k p ≤ 1 := by
  induction k with
  | zero => exact boxCutoff2D_le_one p
  | succ k ih => exact (ampProd_succ_le δ Λ k p).trans ih

lemma ampProd_zero_outside (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) :
    ampProd δ Λ k p = 0 := by
  induction k with
  | zero => exact boxCutoff2D_zero_outside hp
  | succ k ih => simp [ampProd, ih]

/-- Scale-`k` building block of `staircaseU`. -/
def uTerm (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) (p : Euclidean 2) : ℝ :=
  ampProd δ Λ k p *
    (((1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3) *
      gammaWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)))

/-- Scale-`k` building block of `staircaseH` (with `-1/8` sign chosen so the post-IBP pairing
with `∂_x² ∂_y² staircaseU` is strictly positive). -/
def hTerm (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) (p : Euclidean 2) : ℝ :=
  -(1 / 8 : ℝ) * (1 / Λ k) * ampProd δ Λ k p *
    tauWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))

lemma uTerm_congr (δ : ℝ) {Λ₁ Λ₂ : ℕ → ℝ} {k : ℕ}
    (h : ∀ j ≤ k, Λ₁ j = Λ₂ j) : uTerm δ Λ₁ k = uTerm δ Λ₂ k := by
  funext p
  unfold uTerm
  rw [ampProd_congr δ (fun j hj => h j (le_of_lt hj)), h k le_rfl]

lemma hTerm_congr (δ : ℝ) {Λ₁ Λ₂ : ℕ → ℝ} {k : ℕ}
    (h : ∀ j ≤ k, Λ₁ j = Λ₂ j) : hTerm δ Λ₁ k = hTerm δ Λ₂ k := by
  funext p
  unfold hTerm
  rw [ampProd_congr δ (fun j hj => h j (le_of_lt hj)), h k le_rfl]

lemma contDiff_uTerm {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (Λ : ℕ → ℝ) (k : ℕ) :
    ContDiff ℝ (4 : ℕ) (uTerm δ Λ k) := by
  have hw : ContDiff ℝ (4 : ℕ) (fun p : Euclidean 2 =>
      ((1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3) *
        gammaWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) := by
    have hrew : (fun p : Euclidean 2 =>
        ((1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3) *
          gammaWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) =
        fun p : Euclidean 2 =>
          ((1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3) *
            planarPlaneWave (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2) (gammaWave δ) p := by
      funext p; unfold planarPlaneWave; ring_nf
    rw [hrew]
    exact contDiff_const.mul (contDiff_planarPlaneWave _ _ (contDiff_gammaWave hδ0 hδ1))
  exact (contDiff_ampProd hδ0 hδ1 Λ k).mul hw

lemma contDiff_hTerm {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (Λ : ℕ → ℝ) (k : ℕ) :
    ContDiff ℝ (4 : ℕ) (hTerm δ Λ k) := by
  have hw : ContDiff ℝ (4 : ℕ) (fun p : Euclidean 2 =>
      tauWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) := by
    have hrew : (fun p : Euclidean 2 =>
        tauWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) =
        planarPlaneWave (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2) (tauWave δ) := by
      funext p; unfold planarPlaneWave; ring_nf
    rw [hrew]
    exact contDiff_planarPlaneWave _ _ (contDiff_tauWave hδ0 hδ1)
  unfold hTerm
  exact ((contDiff_const.mul contDiff_const).mul (contDiff_ampProd hδ0 hδ1 Λ k)).mul hw

lemma uTerm_zero_outside (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) :
    uTerm δ Λ k p = 0 := by
  unfold uTerm
  rw [ampProd_zero_outside δ Λ k hp, zero_mul]

lemma hTerm_zero_outside (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) :
    hTerm δ Λ k p = 0 := by
  unfold hTerm
  rw [ampProd_zero_outside δ Λ k hp, mul_zero, zero_mul]

/-- Proof-irrelevant supremum bound on `[0, 1]²` depending only on `G` as a function. -/
def unitSqSup (G : Euclidean 2 → ℝ) : ℝ := by
  classical
  exact if h : Continuous G then Classical.choose (exists_sup_on_unitSquare h) else 0

/-- Proof-irrelevant `x`-Lipschitz constant on `[0, 1]²` depending only on `G` as a function. -/
def unitSqXLip (G : Euclidean 2 → ℝ) : ℝ := by
  classical
  exact if h : ContDiff ℝ (1 : ℕ) G then Classical.choose (exists_x_lipschitz_on_unitSquare h) else 0

lemma unitSqSup_nonneg (G : Euclidean 2 → ℝ) : 0 ≤ unitSqSup G := by
  classical
  unfold unitSqSup
  split_ifs with h
  · exact (Classical.choose_spec (exists_sup_on_unitSquare h)).1
  · exact le_rfl

lemma abs_le_unitSqSup {G : Euclidean 2 → ℝ} (hG : Continuous G)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |G (planarPt x y)| ≤ unitSqSup G := by
  classical
  unfold unitSqSup
  split_ifs
  exact (Classical.choose_spec (exists_sup_on_unitSquare hG)).2 x hx y hy

lemma unitSqXLip_nonneg (G : Euclidean 2 → ℝ) : 0 ≤ unitSqXLip G := by
  classical
  unfold unitSqXLip
  split_ifs with h
  · exact (Classical.choose_spec (exists_x_lipschitz_on_unitSquare h)).1
  · exact le_rfl

lemma sub_le_unitSqXLip {G : Euclidean 2 → ℝ} (hG : ContDiff ℝ (1 : ℕ) G)
    {y x₁ x₂ : ℝ} (hy : y ∈ Icc (0 : ℝ) 1)
    (hx₁ : x₁ ∈ Icc (0 : ℝ) 1) (hx₂ : x₂ ∈ Icc (0 : ℝ) 1) :
    |G (planarPt x₁ y) - G (planarPt x₂ y)| ≤ unitSqXLip G * |x₁ - x₂| := by
  classical
  unfold unitSqXLip
  split_ifs
  exact (Classical.choose_spec (exists_x_lipschitz_on_unitSquare hG)).2 y hy x₁ hx₁ x₂ hx₂

private lemma coordinatePartial_zero_of_eqOn_zero {F : Euclidean 2 → ℝ} {O : Set (Euclidean 2)}
    (hO : IsOpen O) (hF : EqOn F 0 O) {p : Euclidean 2} (hp : p ∈ O) (i : Fin 2) :
    coordinatePartial F p i = 0 := by
  unfold coordinatePartial
  have hcont : Continuous (fun t : ℝ => p + t • coordinateVector 2 i) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hmem : {t : ℝ | p + t • coordinateVector 2 i ∈ O} ∈ 𝓝 (0 : ℝ) :=
    hO.mem_nhds (by simpa using hp) |> hcont.continuousAt
  have hev : (fun t : ℝ => F (p + t • coordinateVector 2 i)) =ᶠ[𝓝 (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [hmem] with t ht
    exact hF ht
  exact ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev).deriv

/-- Any function vanishing outside `[1/8, 7/8]²` has its planar first partials bounded by
`unitSqSup` across the *entire* plane `ℝ²`. -/
lemma abs_planarPartial_le_unitSqSup_everywhere {F : Euclidean 2 → ℝ}
    (hsupp : ∀ p : Euclidean 2,
      (p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) → F p = 0)
    (hDx_cont : Continuous (planarDx F)) (hDy_cont : Continuous (planarDy F))
    (p : Euclidean 2) :
    |planarDx F p| ≤ unitSqSup (planarDx F) ∧
    |planarDy F p| ≤ unitSqSup (planarDy F) := by
  by_cases hp : p 0 ∈ Icc (0 : ℝ) 1 ∧ p 1 ∈ Icc (0 : ℝ) 1
  · have hpt_eq : planarPt (p 0) (p 1) = p := by
      ext i; fin_cases i <;> simp
    rw [← hpt_eq]
    exact ⟨abs_le_unitSqSup hDx_cont hp.1 hp.2, abs_le_unitSqSup hDy_cont hp.1 hp.2⟩
  · let O : Set (Euclidean 2) :=
      {q | q 0 < 1 / 8} ∪ {q | 7 / 8 < q 0} ∪ {q | q 1 < 1 / 8} ∪ {q | 7 / 8 < q 1}
    have hO_open : IsOpen O := by
      have hc0 : Continuous (fun q : Euclidean 2 => q 0) :=
        (EuclideanSpace.proj (0 : Fin 2)).continuous
      have hc1 : Continuous (fun q : Euclidean 2 => q 1) :=
        (EuclideanSpace.proj (1 : Fin 2)).continuous
      exact (((isOpen_lt hc0 continuous_const).union (isOpen_lt continuous_const hc0)).union
        (isOpen_lt hc1 continuous_const)).union (isOpen_lt continuous_const hc1)
    have hF0 : EqOn F 0 O := by
      intro q hq
      rcases hq with (((h1 | h2) | h3) | h4)
      · exact hsupp q (Or.inl (le_of_lt h1))
      · exact hsupp q (Or.inr (Or.inl (le_of_lt h2)))
      · exact hsupp q (Or.inr (Or.inr (Or.inl (le_of_lt h3))))
      · exact hsupp q (Or.inr (Or.inr (Or.inr (le_of_lt h4))))
    have hp_mem : p ∈ O := by
      by_cases hx0 : p 0 < 0
      · exact Or.inl (Or.inl (Or.inl (show p 0 < 1 / 8 by linarith)))
      · by_cases hx1 : 1 < p 0
        · exact Or.inl (Or.inl (Or.inr (show 7 / 8 < p 0 by linarith)))
        · by_cases hy0 : p 1 < 0
          · exact Or.inl (Or.inr (show p 1 < 1 / 8 by linarith))
          · by_cases hy1 : 1 < p 1
            · exact Or.inr (show 7 / 8 < p 1 by linarith)
            · exfalso
              exact hp ⟨⟨not_lt.mp hx0, not_lt.mp hx1⟩, ⟨not_lt.mp hy0, not_lt.mp hy1⟩⟩
    have hdx0 : planarDx F p = 0 := by
      unfold planarDx; exact coordinatePartial_zero_of_eqOn_zero hO_open hF0 hp_mem 0
    have hdy0 : planarDy F p = 0 := by
      unfold planarDy; exact coordinatePartial_zero_of_eqOn_zero hO_open hF0 hp_mem 1
    rw [hdx0, hdy0, abs_zero]
    exact ⟨unitSqSup_nonneg _, unitSqSup_nonneg _⟩

/-- Combined lacunary frequency threshold at step `k`, depending only on `Λ 0, ..., Λ (k - 1)`. -/
def reqBound (K k : ℕ) (Λ : ℕ → ℝ) : ℝ :=
  let δ := staircaseDelta K
  let Ak := ampProd δ Λ k
  let bGrad := unitSqSup (planarDx Ak) + unitSqSup (planarDy Ak)
  let bLip := unitSqXLip Ak
  let bJet3 := unitSqSup (jet3Norm Ak)
  let sU4 := ∑ j ∈ Finset.range k,
    unitSqSup (planarDx (planarDx (planarDy (planarDy (uTerm δ Λ j)))))
  let sPast := ∑ j ∈ Finset.range k,
    (unitSqSup (planarDx (hTerm δ Λ j)) +
      unitSqXLip (fun p => planarDx (hTerm δ Λ j) p * Ak p))
  (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) *
    (1 + bGrad + bLip + bJet3 + sU4 + (1 + bJet3) * sPast)

lemma reqBound_congr (K k : ℕ) {Λ₁ Λ₂ : ℕ → ℝ} (h : ∀ j < k, Λ₁ j = Λ₂ j) :
    reqBound K k Λ₁ = reqBound K k Λ₂ := by
  unfold reqBound
  have hAk : ampProd (staircaseDelta K) Λ₁ k = ampProd (staircaseDelta K) Λ₂ k :=
    ampProd_congr _ h
  have hsU4 : (∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy (uTerm (staircaseDelta K) Λ₁ j)))))) =
      ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy (uTerm (staircaseDelta K) Λ₂ j))))) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    rw [uTerm_congr _ (fun i hi => h i (Nat.lt_of_le_of_lt hi hj_lt))]
  have hsPast : (∑ j ∈ Finset.range k,
      (unitSqSup (planarDx (hTerm (staircaseDelta K) Λ₁ j)) +
        unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) Λ₁ j) p *
          ampProd (staircaseDelta K) Λ₁ k p))) =
      ∑ j ∈ Finset.range k,
      (unitSqSup (planarDx (hTerm (staircaseDelta K) Λ₂ j)) +
        unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) Λ₂ j) p *
          ampProd (staircaseDelta K) Λ₂ k p)) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hj_lt : j < k := Finset.mem_range.mp hj
    rw [hTerm_congr _ (fun i hi => h i (Nat.lt_of_le_of_lt hi hj_lt)), hAk]
  dsimp only
  rw [hsPast, hAk, hsU4]

/-- Inductively chosen integer lacunary schedule `M_{K, k} ≥ 1`. -/
def staircaseM (K : ℕ) (k : ℕ) : ℕ :=
  max 1 ⌈reqBound K k (fun j => if h : j < k then 2 * (staircaseM K j : ℝ) else 0)⌉₊
termination_by k

/-- Even real frequencies `Λ_{K, k} = 2 * M_{K, k}`, ensuring `Λ_{K, k} * (spin3Ray k).1 ∈ ℤ \ {0}`. -/
def staircaseLambda (K k : ℕ) : ℝ :=
  2 * (staircaseM K k : ℝ)

lemma one_le_staircaseM (K k : ℕ) : 1 ≤ staircaseM K k := by
  rw [staircaseM]
  exact le_max_left 1 _

lemma staircaseM_pos (K k : ℕ) : (0 : ℝ) < (staircaseM K k : ℝ) :=
  Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one (one_le_staircaseM K k))

lemma staircaseLambda_pos (K k : ℕ) : 0 < staircaseLambda K k := by
  unfold staircaseLambda
  linarith [staircaseM_pos K k]

lemma reqBound_le_staircaseM (K k : ℕ) :
    reqBound K k (staircaseLambda K) ≤ (staircaseM K k : ℝ) := by
  have heq : reqBound K k (staircaseLambda K) =
      reqBound K k (fun j => if h : j < k then 2 * (staircaseM K j : ℝ) else 0) := by
    apply reqBound_congr
    intro j hj
    split_ifs
    rfl
  rw [heq, staircaseM]
  exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 1 _)

lemma pow_le_staircaseM (K k : ℕ) : (2 : ℝ) ^ (3 * k + 16) ≤ (staircaseM K k : ℝ) := by
  have hreq := reqBound_le_staircaseM K k
  unfold reqBound at hreq
  dsimp only at hreq
  have hb1 : 0 ≤ unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) :=
    add_nonneg (unitSqSup_nonneg _) (unitSqSup_nonneg _)
  have hb2 : 0 ≤ unitSqXLip (ampProd (staircaseDelta K) (staircaseLambda K) k) :=
    unitSqXLip_nonneg _
  have hb3 : 0 ≤ unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k)) :=
    unitSqSup_nonneg _
  have hb4 : 0 ≤ ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) j))))) :=
    Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
  have hb5 : 0 ≤ ∑ j ∈ Finset.range k,
      (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
        unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
          ampProd (staircaseDelta K) (staircaseLambda K) k p)) :=
    Finset.sum_nonneg fun _ _ => add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _)
  have hK : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
  have hfactor : (1 : ℝ) ≤ ((K : ℝ) + 3) *
      (1 + (unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
        unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))) +
        unitSqXLip (ampProd (staircaseDelta K) (staircaseLambda K) k) +
        unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
        (∑ j ∈ Finset.range k,
          unitSqSup (planarDx (planarDx (planarDy (planarDy
            (uTerm (staircaseDelta K) (staircaseLambda K) j)))))) +
        (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
          ∑ j ∈ Finset.range k,
            (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
              unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
                ampProd (staircaseDelta K) (staircaseLambda K) k p))) := by
    have hsum1 : (1 : ℝ) ≤ 1 + (unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
        unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))) +
        unitSqXLip (ampProd (staircaseDelta K) (staircaseLambda K) k) +
        unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
        (∑ j ∈ Finset.range k,
          unitSqSup (planarDx (planarDx (planarDy (planarDy
            (uTerm (staircaseDelta K) (staircaseLambda K) j)))))) +
        (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
          ∑ j ∈ Finset.range k,
            (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
              unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
                ampProd (staircaseDelta K) (staircaseLambda K) k p)) := by
      have hmul5 : 0 ≤ (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
          ∑ j ∈ Finset.range k,
            (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
              unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
                ampProd (staircaseDelta K) (staircaseLambda K) k p)) :=
        mul_nonneg (by linarith) hb5
      linarith
    nlinarith
  calc
    (2 : ℝ) ^ (3 * k + 16) = (2 : ℝ) ^ (3 * k + 16) * 1 := (mul_one _).symm
    _ ≤ (2 : ℝ) ^ (3 * k + 16) * (((K : ℝ) + 3) * _) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = _ := by ring
    _ ≤ (staircaseM K k : ℝ) := hreq

lemma one_le_staircaseLambda (K k : ℕ) : 1 ≤ staircaseLambda K k := by
  unfold staircaseLambda
  have h := one_le_staircaseM K k
  have hcast : (1 : ℝ) ≤ (staircaseM K k : ℝ) := by exact_mod_cast h
  linarith

/-- Closed-form `K`-scale spin-3 test potential `Ũ_K` supported in `[1/8, 7/8]² ⊂ (0, 1)²`. -/
def staircaseU (K : ℕ) (p : Euclidean 2) : ℝ :=
  ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k p

/-- Closed-form `K`-scale local datum `h̃_K` supported in `[1/8, 7/8]² ⊂ (0, 1)²`. -/
def staircaseH (K : ℕ) (p : Euclidean 2) : ℝ :=
  ∑ k ∈ Finset.range K, hTerm (staircaseDelta K) (staircaseLambda K) k p

theorem contDiff_staircaseU (K : ℕ) : ContDiff ℝ (4 : ℕ) (staircaseU K) := by
  unfold staircaseU
  exact ContDiff.sum fun k _ =>
    contDiff_uTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K) (staircaseLambda K) k

theorem contDiff_staircaseH (K : ℕ) : ContDiff ℝ (4 : ℕ) (staircaseH K) := by
  unfold staircaseH
  exact ContDiff.sum fun k _ =>
    contDiff_hTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K) (staircaseLambda K) k

theorem staircaseU_zero_outside (K : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) :
    staircaseU K p = 0 := by
  unfold staircaseU
  exact Finset.sum_eq_zero fun k _ => uTerm_zero_outside _ _ k hp

theorem staircaseH_zero_outside (K : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ 1 / 8 ∨ 7 / 8 ≤ p 0 ∨ p 1 ≤ 1 / 8 ∨ 7 / 8 ≤ p 1) :
    staircaseH K p = 0 := by
  unfold staircaseH
  exact Finset.sum_eq_zero fun k _ => hTerm_zero_outside _ _ k hp

theorem vanishesThirdPartialsOnRectBdry_staircaseU (K : ℕ) :
    vanishesThirdPartialsOnRectBdry 0 1 0 1 (staircaseU K) := by
  apply vanishesThirdPartialsOnRectBdry_of_zero_outside_subrect
    (a' := 1 / 8) (b' := 7 / 8) (c' := 1 / 8) (d' := 7 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro p hp
  rcases hp with h | h | h | h
  · exact staircaseU_zero_outside K (Or.inl (le_of_lt h))
  · exact staircaseU_zero_outside K (Or.inr (Or.inl (le_of_lt h)))
  · exact staircaseU_zero_outside K (Or.inr (Or.inr (Or.inl (le_of_lt h))))
  · exact staircaseU_zero_outside K (Or.inr (Or.inr (Or.inr (le_of_lt h))))

/-! ### Section 3: Uniform `C¹(ℝ²)` Bounds on `staircaseH K` via 3-Ray Abel Summation -/

private lemma sum_half_pow_lt_two (N : ℕ) :
    (∑ k ∈ Finset.range N, (1 / 2 : ℝ) ^ k) ≤ 2 := by
  induction N with
  | zero => norm_num
  | succ n ih =>
      have hgeom : ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k =
          2 - (1 / 2 : ℝ) ^ n := by
        clear ih
        induction n with
        | zero => norm_num
        | succ m ihm =>
            rw [Finset.sum_range_succ, ihm]
            ring
      rw [hgeom]
      have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
      linarith

private lemma abel_sum_bound (N : ℕ) (a s : ℕ → ℝ)
    (ha_nonneg : ∀ k, 0 ≤ a k)
    (ha_anti : ∀ k, a (k + 1) ≤ a k)
    (hs0 : s 0 = 0)
    (hs_bound : ∀ k, |s k| ≤ 1) :
    |∑ k ∈ Finset.range N, a (k + 1) * (s (k + 1) - s k)| ≤ a 0 := by
  have hid : ∑ k ∈ Finset.range N, a (k + 1) * (s (k + 1) - s k) =
      a N * s N - a 0 * s 0 + ∑ k ∈ Finset.range N, (a k - a (k + 1)) * s k := by
    induction N with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
  rw [hid, hs0, mul_zero, sub_zero]
  have h1 : |a N * s N| ≤ a N := by
    rw [abs_mul, abs_of_nonneg (ha_nonneg N)]
    calc
      a N * |s N| ≤ a N * 1 := mul_le_mul_of_nonneg_left (hs_bound N) (ha_nonneg N)
      _ = a N := mul_one _
  have h2 : ∑ k ∈ Finset.range N, |(a k - a (k + 1)) * s k| ≤
      ∑ k ∈ Finset.range N, (a k - a (k + 1)) := by
    apply Finset.sum_le_sum
    intro k _
    have hdiff : 0 ≤ a k - a (k + 1) := sub_nonneg.mpr (ha_anti k)
    rw [abs_mul, abs_of_nonneg hdiff]
    calc
      (a k - a (k + 1)) * |s k| ≤ (a k - a (k + 1)) * 1 :=
        mul_le_mul_of_nonneg_left (hs_bound k) hdiff
      _ = a k - a (k + 1) := mul_one _
  have htel : ∑ k ∈ Finset.range N, (a k - a (k + 1)) = a 0 - a N :=
    Finset.sum_range_sub' a N
  calc
    |a N * s N + ∑ k ∈ Finset.range N, (a k - a (k + 1)) * s k|
        ≤ |a N * s N| + |∑ k ∈ Finset.range N, (a k - a (k + 1)) * s k| := abs_add_le _ _
    _ ≤ a N + ∑ k ∈ Finset.range N, |(a k - a (k + 1)) * s k| :=
        add_le_add h1 (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ a N + (a 0 - a N) := add_le_add le_rfl (h2.trans (le_of_eq htel))
    _ = a 0 := by ring

private lemma hTerm_partials (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (Λ : ℕ → ℝ) (k : ℕ) (hΛ : Λ k ≠ 0) (p : Euclidean 2) :
    planarDx (hTerm δ Λ k) p =
      -(1 / (8 * Λ k)) * planarDx (ampProd δ Λ k) p *
          tauWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) -
        (1 / 8) * ampProd δ Λ k p *
          tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
            (spin3Ray k).1 ∧
    planarDy (hTerm δ Λ k) p =
      -(1 / (8 * Λ k)) * planarDy (ampProd δ Λ k) p *
          tauWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) -
        (1 / 8) * ampProd δ Λ k p *
          tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
            (spin3Ray k).2 := by
  let W : Euclidean 2 → ℝ :=
    planarPlaneWave (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2) (tauWave δ)
  have hW_reg : ContDiff ℝ (4 : ℕ) W :=
    contDiff_planarPlaneWave _ _ (contDiff_tauWave hδ0 hδ1)
  have hW_dx : planarDx W p =
      (Λ k * (spin3Ray k).1) *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) := by
    have h := congrFun (planarDx_planarPlaneWave_s (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2)
      (hasDerivAt_tauWave hδ0 hδ1)) p
    dsimp [W]
    rw [h]
    unfold planarPlaneWave
    congr 2
    ring
  have hW_dy : planarDy W p =
      (Λ k * (spin3Ray k).2) *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) := by
    have h := congrFun (planarDy_planarPlaneWave_s (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2)
      (hasDerivAt_tauWave hδ0 hδ1)) p
    dsimp [W]
    rw [h]
    unfold planarPlaneWave
    congr 2
    ring
  have hrew : hTerm δ Λ k = fun q => (-(1 / 8 : ℝ) * (1 / Λ k)) * (ampProd δ Λ k q * W q) := by
    funext q; unfold hTerm W planarPlaneWave; ring_nf
  have hA_diff := diff_of_c1 (r := 3) (contDiff_ampProd hδ0 hδ1 Λ k) p
  have hW_diff := diff_of_c1 (r := 3) hW_reg p
  rw [hrew]
  constructor
  · rw [planarDx_const_mul_s _ (hA_diff.fun_mul hW_diff),
      planarDx_mul_s hA_diff hW_diff, hW_dx]
    unfold W planarPlaneWave
    have harg : (Λ k * (spin3Ray k).1) * p 0 + (Λ k * (spin3Ray k).2) * p 1 =
        Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1) := by ring
    rw [harg]
    field_simp [hΛ]
    ring
  · rw [planarDy_const_mul_s _ (hA_diff.fun_mul hW_diff),
      planarDy_mul_s hA_diff hW_diff, hW_dy]
    unfold W planarPlaneWave
    have harg : (Λ k * (spin3Ray k).1) * p 0 + (Λ k * (spin3Ray k).2) * p 1 =
        Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1) := by ring
    rw [harg]
    field_simp [hΛ]
    ring

private lemma bGrad_div_staircaseM_le (K k : ℕ) :
    (unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))) /
      (staircaseM K k : ℝ) ≤ (1 / 2 : ℝ) ^ k := by
  have hM_pos := staircaseM_pos K k
  rw [div_le_iff₀ hM_pos]
  have hreq := reqBound_le_staircaseM K k
  unfold reqBound at hreq
  dsimp only at hreq
  have hb2 := unitSqXLip_nonneg (ampProd (staircaseDelta K) (staircaseLambda K) k)
  have hb3 := unitSqSup_nonneg (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))
  have hb4 : 0 ≤ ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) j))))) :=
    Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
  have hb5 : 0 ≤ (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
      ∑ j ∈ Finset.range k,
        (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
          unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
            ampProd (staircaseDelta K) (staircaseLambda K) k p)) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ =>
      add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _))
  set B := unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))
  set S1 := ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) j)))))
  set S2 := (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
      ∑ j ∈ Finset.range k,
        (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
          unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
            ampProd (staircaseDelta K) (staircaseLambda K) k p))
  have hB0 : 0 ≤ B := add_nonneg (unitSqSup_nonneg _) (unitSqSup_nonneg _)
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
    have h1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k + 16) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
    calc
      (2 : ℝ) ^ k = (2 : ℝ) ^ k * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
          mul_le_mul h1 h2 zero_le_one (by positivity)
  have hstep : B ≤ (1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ k * B) := by
    have hinv : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]; norm_num
    rw [← mul_assoc, hinv, one_mul]
  calc
    B ≤ (1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ k * B) := hstep
    _ ≤ (1 / 2 : ℝ) ^ k * ((2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * B) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have : (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * B =
            ((2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3)) * B := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right hpow hB0
    _ ≤ (1 / 2 : ℝ) ^ k * (staircaseM K k : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hle_sum : B ≤ 1 + B +
            unitSqXLip (ampProd (staircaseDelta K) (staircaseLambda K) k) +
            unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k)) + S1 + S2 := by
          linarith
        exact (mul_le_mul_of_nonneg_left hle_sum (by positivity)).trans hreq

theorem abs_staircaseH_le_one (K : ℕ) (p : Euclidean 2) :
    |staircaseH K p| ≤ 1 := by
  unfold staircaseH
  have hterm : ∀ k ∈ Finset.range K,
      |hTerm (staircaseDelta K) (staircaseLambda K) k p| ≤ (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k _
    unfold hTerm
    have hA0 := ampProd_nonneg (staircaseDelta K) (staircaseLambda K) k p
    have hA1 := ampProd_le_one (staircaseDelta K) (staircaseLambda K) k p
    have hτ := abs_tauWave_le (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
      (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
    have hΛ_pos := staircaseLambda_pos K k
    have hΛ_pow : (2 : ℝ) ^ (k + 1) ≤ staircaseLambda K k := by
      unfold staircaseLambda
      have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k + 16) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have hM := pow_le_staircaseM K k
      rw [pow_succ']
      linarith
    have hinv : 1 / staircaseLambda K k ≤ (1 / 2 : ℝ) ^ k := by
      have h2k : (2 : ℝ) ^ k ≤ staircaseLambda K k := by
        have hp : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        linarith
      rw [one_div_pow]
      exact one_div_le_one_div_of_le (by positivity) h2k
    rw [abs_mul, abs_mul, abs_mul]
    have hc1 : |-(1 / 8 : ℝ)| = 1 / 8 := by norm_num
    have hc2 : |1 / staircaseLambda K k| = 1 / staircaseLambda K k :=
      abs_of_pos (one_div_pos.mpr hΛ_pos)
    rw [hc1, hc2, abs_of_nonneg hA0]
    calc
      (1 / 8 : ℝ) * (1 / staircaseLambda K k) * ampProd (staircaseDelta K) (staircaseLambda K) k p *
          |tauWave (staircaseDelta K) _|
          ≤ (1 / 8 : ℝ) * (1 / 2 : ℝ) ^ k * 1 * (1 / 4) := by
            gcongr
      _ = (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k := by ring
  calc
    |∑ k ∈ Finset.range K, hTerm (staircaseDelta K) (staircaseLambda K) k p|
        ≤ ∑ k ∈ Finset.range K, |hTerm (staircaseDelta K) (staircaseLambda K) k p| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum hterm
    _ = (1 / 32 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 32 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
    _ ≤ 1 := by norm_num

private lemma stopped_ray_sum_bound (K : ℕ) (p : Euclidean 2) (v s : ℕ → ℝ)
    (hv_diff : ∀ k, v k = s (k + 1) - s k)
    (hv_abs : ∀ k, |v k| ≤ 1)
    (hs0 : s 0 = 0)
    (hs_abs : ∀ k, |s k| ≤ 1) :
    |∑ k ∈ Finset.range K,
      ampProd (staircaseDelta K) (staircaseLambda K) k p *
        tauDerivWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * v k| ≤ 2 := by
  let δ := staircaseDelta K
  let Λ := staircaseLambda K
  let a : ℕ → ℝ := fun k => ampProd δ Λ k p
  have ha0_le : a 0 ≤ 1 := ampProd_le_one δ Λ 0 p
  have ha_nonneg : ∀ k, 0 ≤ a k := fun k => ampProd_nonneg δ Λ k p
  have ha_anti : ∀ k, a (k + 1) ≤ a k := fun k => ampProd_succ_le δ Λ k p
  have hstop : ∀ k,
      a k * tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * v k =
        (a k - a (k + 1)) *
            tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * v k +
          a (k + 1) * (s (k + 1) - s k) := by
    intro k
    set τ' := tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
    have heta_stop : a (k + 1) * τ' = a (k + 1) := by
      dsimp [a, ampProd, τ']
      rw [mul_assoc, etaWave_mul_tauDerivWave (staircaseDelta_pos K)]
    have hsub : a k * τ' = (a k - a (k + 1)) * τ' + a (k + 1) := by
      calc
        a k * τ' = (a k - a (k + 1)) * τ' + a (k + 1) * τ' := by ring
        _ = (a k - a (k + 1)) * τ' + a (k + 1) := by rw [heta_stop]
    rw [hsub, add_mul, ← hv_diff k]
  rw [Finset.sum_congr rfl fun k _ => hstop k, Finset.sum_add_distrib]
  have hb1 : |∑ k ∈ Finset.range K,
      (a k - a (k + 1)) *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * v k| ≤ 1 := by
    have hterm : ∀ k ∈ Finset.range K,
        |(a k - a (k + 1)) *
          tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * v k| ≤
          a k - a (k + 1) := by
      intro k _
      have hdiff : 0 ≤ a k - a (k + 1) := sub_nonneg.mpr (ha_anti k)
      have hτ := abs_tauDerivWave_le_one (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
        (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
      rw [abs_mul, abs_mul, abs_of_nonneg hdiff]
      calc
        (a k - a (k + 1)) * |tauDerivWave δ _| * |v k|
            ≤ (a k - a (k + 1)) * 1 * 1 := by gcongr; exact hv_abs k
        _ = a k - a (k + 1) := by ring
    calc
      |∑ k ∈ Finset.range K, _|
          ≤ ∑ k ∈ Finset.range K, |(a k - a (k + 1)) * _ * v k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range K, (a k - a (k + 1)) := Finset.sum_le_sum hterm
      _ = a 0 - a K := Finset.sum_range_sub' a K
      _ ≤ 1 := by linarith [ha0_le, ha_nonneg K]
  have hb2 : |∑ k ∈ Finset.range K, a (k + 1) * (s (k + 1) - s k)| ≤ 1 :=
    (abel_sum_bound K a s ha_nonneg ha_anti hs0 hs_abs).trans ha0_le
  linarith [abs_add_le
    (∑ k ∈ Finset.range K,
      (a k - a (k + 1)) *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * v k)
    (∑ k ∈ Finset.range K, a (k + 1) * (s (k + 1) - s k))]

theorem abs_planarDx_staircaseH_le_half (K : ℕ) (p : Euclidean 2) :
    |planarDx (staircaseH K) p| ≤ 1 / 2 := by
  unfold staircaseH
  rw [planarDx_finset_sum (Finset.range K) (fun k _ =>
    diff_of_c1 (r := 3)
      (contDiff_hTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K) (staircaseLambda K) k) p)]
  have hsplit : ∀ k ∈ Finset.range K,
      planarDx (hTerm (staircaseDelta K) (staircaseLambda K) k) p =
        (-(1 / (8 * staircaseLambda K k)) *
            planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
            tauWave (staircaseDelta K)
              (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) +
        (-(1 / 8 : ℝ) *
          (ampProd (staircaseDelta K) (staircaseLambda K) k p *
            tauDerivWave (staircaseDelta K)
              (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
            (spin3Ray k).1)) := by
    intro k _
    rw [(hTerm_partials (staircaseDelta K) (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
      (staircaseLambda K) k (ne_of_gt (staircaseLambda_pos K k)) p).1]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have herr : |∑ k ∈ Finset.range K,
      -(1 / (8 * staircaseLambda K k)) *
        planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
        tauWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤ 1 / 32 := by
    have hterm : ∀ k ∈ Finset.range K,
        |-(1 / (8 * staircaseLambda K k)) *
          planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
          tauWave (staircaseDelta K)
            (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤
          (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := by
      intro k _
      have hAk_reg := contDiff_ampProd (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
        (staircaseLambda K) k
      have hdx_bound := (abs_planarPartial_le_unitSqSup_everywhere
        (fun q hq => ampProd_zero_outside (staircaseDelta K) (staircaseLambda K) k hq)
        (contDiff_planarDx_b1 (r := 3) hAk_reg).continuous
        (contDiff_planarDy_b1 (r := 3) hAk_reg).continuous p).1
      have hdy_nn := unitSqSup_nonneg (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))
      have hτ := abs_tauWave_le (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
        (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
      have hM_pos := staircaseM_pos K k
      have hbg := bGrad_div_staircaseM_le K k
      rw [abs_mul, abs_mul]
      have hc : |-(1 / (8 * staircaseLambda K k))| = 1 / (16 * (staircaseM K k : ℝ)) := by
        unfold staircaseLambda
        rw [abs_neg, abs_of_pos (by positivity)]
        ring
      rw [hc]
      have hdx_div : (1 / (16 * (staircaseM K k : ℝ))) *
          |planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p| ≤
          (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
        calc
          (1 / (16 * (staircaseM K k : ℝ))) *
              |planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p|
              ≤ (1 / 16 : ℝ) *
                ((unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
                  unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))) /
                  (staircaseM K k : ℝ)) := by
                have hle : |planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p| ≤
                    unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
                      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) := by
                  linarith
                calc
                  (1 / (16 * (staircaseM K k : ℝ))) * |planarDx _ p|
                      ≤ (1 / (16 * (staircaseM K k : ℝ))) * (unitSqSup _ + unitSqSup _) :=
                        mul_le_mul_of_nonneg_left hle (by positivity)
                  _ = (1 / 16 : ℝ) * ((unitSqSup _ + unitSqSup _) / (staircaseM K k : ℝ)) := by ring
          _ ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_left hbg (by norm_num)
      calc
        (1 / (16 * (staircaseM K k : ℝ))) * |planarDx _ p| * |tauWave _ _|
            ≤ ((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k) * (1 / 4) :=
              mul_le_mul hdx_div hτ (abs_nonneg _) (by positivity)
        _ = (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := by ring
    calc
      |∑ k ∈ Finset.range K, _|
          ≤ ∑ k ∈ Finset.range K, |-(1 / (8 * staircaseLambda K k)) * _ * _| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range K, (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum hterm
      _ = (1 / 64 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / 64 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
      _ = 1 / 32 := by norm_num
  have hmain : |∑ k ∈ Finset.range K, -(1 / 8 : ℝ) *
      (ampProd (staircaseDelta K) (staircaseLambda K) k p *
        tauDerivWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
        (spin3Ray k).1)| ≤ 1 / 4 := by
    rw [← Finset.mul_sum, abs_mul]
    have hc : |-(1 / 8 : ℝ)| = 1 / 8 := by norm_num
    rw [hc]
    have hab := stopped_ray_sum_bound K p
      (fun k => (spin3Ray k).1) (fun k => (rayPartialSum k).1)
      (fun k => by simp [rayPartialSum])
      abs_spin3Ray_fst_le_one
      (by simp [rayPartialSum])
      (fun k => (abs_rayPartialSum_le_one k).1)
    linarith
  linarith [abs_add_le
    (∑ k ∈ Finset.range K,
      -(1 / (8 * staircaseLambda K k)) *
        planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
        tauWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)))
    (∑ k ∈ Finset.range K, -(1 / 8 : ℝ) *
      (ampProd (staircaseDelta K) (staircaseLambda K) k p *
        tauDerivWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
        (spin3Ray k).1))]

theorem abs_planarDy_staircaseH_le_half (K : ℕ) (p : Euclidean 2) :
    |planarDy (staircaseH K) p| ≤ 1 / 2 := by
  unfold staircaseH
  rw [planarDy_finset_sum (Finset.range K) (fun k _ =>
    diff_of_c1 (r := 3)
      (contDiff_hTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K) (staircaseLambda K) k) p)]
  have hsplit : ∀ k ∈ Finset.range K,
      planarDy (hTerm (staircaseDelta K) (staircaseLambda K) k) p =
        (-(1 / (8 * staircaseLambda K k)) *
            planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
            tauWave (staircaseDelta K)
              (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) +
        (-(1 / 8 : ℝ) *
          (ampProd (staircaseDelta K) (staircaseLambda K) k p *
            tauDerivWave (staircaseDelta K)
              (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
            (spin3Ray k).2)) := by
    intro k _
    rw [(hTerm_partials (staircaseDelta K) (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
      (staircaseLambda K) k (ne_of_gt (staircaseLambda_pos K k)) p).2]
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have herr : |∑ k ∈ Finset.range K,
      -(1 / (8 * staircaseLambda K k)) *
        planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
        tauWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤ 1 / 32 := by
    have hterm : ∀ k ∈ Finset.range K,
        |-(1 / (8 * staircaseLambda K k)) *
          planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
          tauWave (staircaseDelta K)
            (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤
          (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := by
      intro k _
      have hAk_reg := contDiff_ampProd (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
        (staircaseLambda K) k
      have hdy_bound := (abs_planarPartial_le_unitSqSup_everywhere
        (fun q hq => ampProd_zero_outside (staircaseDelta K) (staircaseLambda K) k hq)
        (contDiff_planarDx_b1 (r := 3) hAk_reg).continuous
        (contDiff_planarDy_b1 (r := 3) hAk_reg).continuous p).2
      have hdx_nn := unitSqSup_nonneg (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k))
      have hτ := abs_tauWave_le (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
        (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
      have hM_pos := staircaseM_pos K k
      have hbg := bGrad_div_staircaseM_le K k
      rw [abs_mul, abs_mul]
      have hc : |-(1 / (8 * staircaseLambda K k))| = 1 / (16 * (staircaseM K k : ℝ)) := by
        unfold staircaseLambda
        rw [abs_neg, abs_of_pos (by positivity)]
        ring
      rw [hc]
      have hdy_div : (1 / (16 * (staircaseM K k : ℝ))) *
          |planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p| ≤
          (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k := by
        calc
          (1 / (16 * (staircaseM K k : ℝ))) *
              |planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p|
              ≤ (1 / 16 : ℝ) *
                ((unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
                  unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))) /
                  (staircaseM K k : ℝ)) := by
                have hle : |planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p| ≤
                    unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
                      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) := by
                  linarith
                calc
                  (1 / (16 * (staircaseM K k : ℝ))) * |planarDy _ p|
                      ≤ (1 / (16 * (staircaseM K k : ℝ))) * (unitSqSup _ + unitSqSup _) :=
                        mul_le_mul_of_nonneg_left hle (by positivity)
                  _ = (1 / 16 : ℝ) * ((unitSqSup _ + unitSqSup _) / (staircaseM K k : ℝ)) := by ring
          _ ≤ (1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k :=
              mul_le_mul_of_nonneg_left hbg (by norm_num)
      calc
        (1 / (16 * (staircaseM K k : ℝ))) * |planarDy _ p| * |tauWave _ _|
            ≤ ((1 / 16 : ℝ) * (1 / 2 : ℝ) ^ k) * (1 / 4) :=
              mul_le_mul hdy_div hτ (abs_nonneg _) (by positivity)
        _ = (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := by ring
    calc
      |∑ k ∈ Finset.range K, _|
          ≤ ∑ k ∈ Finset.range K, |-(1 / (8 * staircaseLambda K k)) * _ * _| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range K, (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum hterm
      _ = (1 / 64 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
      _ ≤ (1 / 64 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
      _ = 1 / 32 := by norm_num
  have hmain : |∑ k ∈ Finset.range K, -(1 / 8 : ℝ) *
      (ampProd (staircaseDelta K) (staircaseLambda K) k p *
        tauDerivWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
        (spin3Ray k).2)| ≤ 1 / 4 := by
    rw [← Finset.mul_sum, abs_mul]
    have hc : |-(1 / 8 : ℝ)| = 1 / 8 := by norm_num
    rw [hc]
    have hab := stopped_ray_sum_bound K p
      (fun k => (spin3Ray k).2) (fun k => (rayPartialSum k).2)
      (fun k => by simp [rayPartialSum])
      abs_spin3Ray_snd_le_one
      (by simp [rayPartialSum])
      (fun k => (abs_rayPartialSum_le_one k).2)
    linarith
  linarith [abs_add_le
    (∑ k ∈ Finset.range K,
      -(1 / (8 * staircaseLambda K k)) *
        planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k) p *
        tauWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)))
    (∑ k ∈ Finset.range K, -(1 / 8 : ℝ) *
      (ampProd (staircaseDelta K) (staircaseLambda K) k p *
        tauDerivWave (staircaseDelta K)
          (staircaseLambda K k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) *
        (spin3Ray k).2))]

theorem norm_fderiv_staircaseH_le_one (K : ℕ) (p : Euclidean 2) :
    ‖fderiv ℝ (staircaseH K) p‖ ≤ 1 := by
  have hd := diff_of_c1 (r := 3) (contDiff_staircaseH K) p
  calc
    ‖fderiv ℝ (staircaseH K) p‖
        ≤ |planarDx (staircaseH K) p| + |planarDy (staircaseH K) p| :=
          norm_fderiv_le_abs_planarDx_add_planarDy hd
    _ ≤ 1 / 2 + 1 / 2 :=
        add_le_add (abs_planarDx_staircaseH_le_half K p) (abs_planarDy_staircaseH_le_half K p)
    _ = 1 := by norm_num

/-! ### Section 4: Martingale Stopping Telescope and Uniform Spin-3 `L¹` Bound -/

private lemma cont_planarPt_swap {G : Euclidean 2 → ℝ} (hG : Continuous G) :
    Continuous (Function.uncurry fun y x : ℝ => G (planarPt x y)) := by
  have hpt : Continuous (fun q : ℝ × ℝ => planarPt q.2 q.1) := by
    have hrew : (fun q : ℝ × ℝ => planarPt q.2 q.1) =
        fun q : ℝ × ℝ => q.2 • coordinateVector 2 0 + q.1 • coordinateVector 2 1 := by
      funext q; ext i; fin_cases i <;> simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    rw [hrew]
    exact (continuous_snd.smul continuous_const).add (continuous_fst.smul continuous_const)
  exact hG.comp hpt

private lemma cont_planarPt_x {G : Euclidean 2 → ℝ} (hG : Continuous G) (y : ℝ) :
    Continuous (fun x : ℝ => G (planarPt x y)) :=
  (cont_planarPt_swap hG).comp (Continuous.prodMk_right y)

private lemma cont_inner_unitSq {G : Euclidean 2 → ℝ} (hG : Continuous G) :
    Continuous (fun y : ℝ => ∫ x in (0 : ℝ)..1, G (planarPt x y)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y x => G (planarPt x y)) (cont_planarPt_swap hG) 0 1

private lemma unitSq_integral_mono {F G : Euclidean 2 → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (hle : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1, F (planarPt x y) ≤ G (planarPt x y)) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F (planarPt x y)) ≤
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, G (planarPt x y) := by
  apply intervalIntegral.integral_mono_on zero_le_one
    ((cont_inner_unitSq hF).intervalIntegrable 0 1)
    ((cont_inner_unitSq hG).intervalIntegrable 0 1)
  intro y hy
  exact intervalIntegral.integral_mono_on zero_le_one
    ((cont_planarPt_x hF y).intervalIntegrable 0 1)
    ((cont_planarPt_x hG y).intervalIntegrable 0 1)
    (fun x hx => hle x hx y hy)

private lemma unitSq_integral_add {F G : Euclidean 2 → ℝ}
    (hF : Continuous F) (hG : Continuous G) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (F (planarPt x y) + G (planarPt x y))) =
      (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F (planarPt x y)) +
        ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, G (planarPt x y) := by
  have hinner : ∀ y : ℝ,
      (∫ x in (0 : ℝ)..1, (F (planarPt x y) + G (planarPt x y))) =
        (∫ x in (0 : ℝ)..1, F (planarPt x y)) + ∫ x in (0 : ℝ)..1, G (planarPt x y) :=
    fun y => intervalIntegral.integral_add
      ((cont_planarPt_x hF y).intervalIntegrable 0 1)
      ((cont_planarPt_x hG y).intervalIntegrable 0 1)
  simp_rw [hinner]
  exact intervalIntegral.integral_add
    ((cont_inner_unitSq hF).intervalIntegrable 0 1)
    ((cont_inner_unitSq hG).intervalIntegrable 0 1)

private lemma unitSq_integral_const_mul (c : ℝ) {F : Euclidean 2 → ℝ} (_hF : Continuous F) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, c * F (planarPt x y)) =
      c * ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F (planarPt x y) := by
  simp_rw [intervalIntegral.integral_const_mul]

private lemma unitSq_integral_finset_sum {ι : Type*} (s : Finset ι) {F : ι → Euclidean 2 → ℝ}
    (hF : ∀ i ∈ s, Continuous (F i)) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ∑ i ∈ s, F i (planarPt x y)) =
      ∑ i ∈ s, ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F i (planarPt x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have h1 : Continuous (F a) := hF a (Finset.mem_insert_self a s)
      have h2 : Continuous (fun p => ∑ i ∈ s, F i p) :=
        continuous_finsetSum s fun i hi => hF i (Finset.mem_insert_of_mem hi)
      simp_rw [Finset.sum_insert ha]
      rw [unitSq_integral_add (F := F a) (G := fun p => ∑ i ∈ s, F i p) h1 h2,
        ih (fun i hi => hF i (Finset.mem_insert_of_mem hi))]

private lemma unitSq_integral_abs_le {F : Euclidean 2 → ℝ} (hF : Continuous F) :
    |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F (planarPt x y)| ≤
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |F (planarPt x y)| := by
  calc
    |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, F (planarPt x y)|
        ≤ ∫ y in (0 : ℝ)..1, |∫ x in (0 : ℝ)..1, F (planarPt x y)| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm
              (f := fun y => ∫ x in (0 : ℝ)..1, F (planarPt x y)) zero_le_one
    _ ≤ ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |F (planarPt x y)| := by
          apply intervalIntegral.integral_mono_on zero_le_one
            ((cont_inner_unitSq hF).abs.intervalIntegrable 0 1)
            ((cont_inner_unitSq hF.abs).intervalIntegrable 0 1)
          intro y _
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm
              (f := fun x => F (planarPt x y)) zero_le_one

private lemma unitSq_integral_const (C : ℝ) :
    (∫ _y in (0 : ℝ)..1, ∫ _x in (0 : ℝ)..1, C) = C := by
  simp [intervalIntegral.integral_const]

/-- Master bound extracting any nonnegative sub-expression from `reqBound_le_staircaseM`. -/
private lemma term_le_staircaseM_div (K k : ℕ) {X : ℝ}
    (hX : X ≤ 1 + (unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
        unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k))) +
      unitSqXLip (ampProd (staircaseDelta K) (staircaseLambda K) k) +
      unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      (∑ j ∈ Finset.range k,
        unitSqSup (planarDx (planarDx (planarDy (planarDy
          (uTerm (staircaseDelta K) (staircaseLambda K) j)))))) +
      (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
        ∑ j ∈ Finset.range k,
          (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
            unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
              ampProd (staircaseDelta K) (staircaseLambda K) k p))) :
    (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * X ≤ (staircaseM K k : ℝ) := by
  have hreq := reqBound_le_staircaseM K k
  unfold reqBound at hreq
  dsimp only at hreq
  exact (mul_le_mul_of_nonneg_left hX (by positivity)).trans hreq

private lemma bLip_bound_staircaseM (K k : ℕ) :
    (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) *
      unitSqXLip (ampProd (staircaseDelta K) (staircaseLambda K) k) ≤
      (staircaseM K k : ℝ) := by
  apply term_le_staircaseM_div
  have hb1 : 0 ≤ unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) :=
    add_nonneg (unitSqSup_nonneg _) (unitSqSup_nonneg _)
  have hb3 := unitSqSup_nonneg (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))
  have hb4 : 0 ≤ ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) j))))) :=
    Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
  have hb5 : 0 ≤ (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
      ∑ j ∈ Finset.range k,
        (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
          unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
            ampProd (staircaseDelta K) (staircaseLambda K) k p)) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ =>
      add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _))
  linarith

private lemma bJet3_bound_staircaseM (K k : ℕ) :
    (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) *
      unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k)) ≤
      (staircaseM K k : ℝ) := by
  apply term_le_staircaseM_div
  have hb1 : 0 ≤ unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) :=
    add_nonneg (unitSqSup_nonneg _) (unitSqSup_nonneg _)
  have hb2 := unitSqXLip_nonneg (ampProd (staircaseDelta K) (staircaseLambda K) k)
  have hb4 : 0 ≤ ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) j))))) :=
    Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
  have hb5 : 0 ≤ (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
      ∑ j ∈ Finset.range k,
        (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
          unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
            ampProd (staircaseDelta K) (staircaseLambda K) k p)) :=
    mul_nonneg (by linarith [unitSqSup_nonneg (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))])
      (Finset.sum_nonneg fun _ _ => add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _))
  linarith

private lemma integral_etaWave_le_half {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    (∫ t in (0 : ℝ)..1, etaWave δ t) ≤ 1 / 2 := by
  have hcont := (contDiff_etaWave hδ0 hδ1).continuous
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) 0 (1 / 2))
    (hcont.intervalIntegrable (μ := volume) (1 / 2) 1)).symm
  have h1 : (∫ t in (0 : ℝ)..(1 / 2), etaWave δ t) ≤ 1 / 2 := by
    calc
      (∫ t in (0 : ℝ)..(1 / 2), etaWave δ t) ≤ ∫ _t in (0 : ℝ)..(1 / 2), (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num)
          (hcont.intervalIntegrable (μ := volume) 0 (1 / 2))
          (continuous_const.intervalIntegrable (μ := volume) 0 (1 / 2))
          (fun t _ => etaWave_le_one δ t)
      _ = 1 / 2 := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have h2 : (∫ t in (1 / 2 : ℝ)..1, etaWave δ t) = 0 := by
    have hcongr : (∫ t in (1 / 2 : ℝ)..1, etaWave δ t) = ∫ _t in (1 / 2 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num)] at ht
      dsimp only
      by_cases ht1 : t = 1
      · subst ht1
        unfold etaWave
        have hfr1 : Int.fract (1 : ℝ) = 0 := by simp
        rw [hfr1]
        exact etaBump_eq_zero_of_le hδ0 (by positivity)
      · have hlt : t < 1 := lt_of_le_of_ne ht.2 ht1
        unfold etaWave
        have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], hlt⟩
        rw [hfr]
        exact etaBump_eq_zero_of_ge hδ0 (by linarith [ht.1, hδ0])
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_zero]
  linarith

/-- Stopping transition discrepancy `q_δ(t) = τ'_δ(t) + 1 - 2 η_δ(t)`, supported on three
`O(δ)`-strips per period. -/
def stopDiffWave (δ t : ℝ) : ℝ :=
  tauDerivWave δ t + 1 - 2 * etaWave δ t

private lemma cont_stopDiffWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    Continuous (stopDiffWave δ) := by
  unfold stopDiffWave
  exact ((contDiff_tauDerivWave hδ0 hδ1).continuous.add continuous_const).sub
    (continuous_const.mul (contDiff_etaWave hδ0 hδ1).continuous)

private lemma stopDiffWave_periodic {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    stopDiffWave δ (t + 1) = stopDiffWave δ t := by
  unfold stopDiffWave
  have hτ1 : tauDerivWave δ (t + 1) = tauDerivWave δ t := by
    have h1 : t + 1 = (t + 1 / 2) + 1 / 2 := by ring
    rw [h1, tauDerivWave_antiperiodic hδ0 hδ1, tauDerivWave_antiperiodic hδ0 hδ1, neg_neg]
  rw [hτ1, etaWave_periodic]

private lemma abs_stopDiffWave_le_two {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    |stopDiffWave δ t| ≤ 2 := by
  unfold stopDiffWave
  have hτ := abs_le.mp (abs_tauDerivWave_le_one hδ0 hδ1 t)
  have hη0 := etaWave_nonneg δ t
  have hη1 := etaWave_le_one δ t
  rw [abs_le]
  constructor <;> linarith

private lemma integral_abs_stopDiffWave_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    (∫ t in (0 : ℝ)..1, |stopDiffWave δ t|) ≤ 6 * δ := by
  have hc : Continuous (fun t => |stopDiffWave δ t|) := (cont_stopDiffWave hδ0 hδ1).abs
  let pts : ℕ → ℝ
    | 0 => 0
    | 1 => δ
    | 2 => 1 / 2 - δ
    | 3 => 1 / 2 + δ / 2
    | 4 => 1 - δ / 2
    | _ => 1
  have hsum := (intervalIntegral.sum_integral_adjacent_intervals (a := pts) (n := 5)
    (fun k _ => hc.intervalIntegrable (μ := volume) _ _)).symm
  have hp0 : pts 0 = 0 := rfl
  have hp5 : pts 5 = 1 := rfl
  rw [hp0, hp5] at hsum
  rw [hsum]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, pts]
  have hbound_seg : ∀ a b : ℝ, a ≤ b → (∫ t in a..b, |stopDiffWave δ t|) ≤ 2 * (b - a) := by
    intro a b hab
    calc
      (∫ t in a..b, |stopDiffWave δ t|) ≤ ∫ _t in a..b, (2 : ℝ) :=
        intervalIntegral.integral_mono_on hab (hc.intervalIntegrable a b)
          (continuous_const.intervalIntegrable a b)
          (fun t _ => abs_stopDiffWave_le_two hδ0 hδ1 t)
      _ = 2 * (b - a) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  have hs0 : (∫ t in (0 : ℝ)..δ, |stopDiffWave δ t|) ≤ 2 * (δ - 0) :=
    hbound_seg 0 δ hδ0.le
  have hs2 : (∫ t in (1 / 2 - δ)..(1 / 2 + δ / 2), |stopDiffWave δ t|) ≤
      2 * ((1 / 2 + δ / 2) - (1 / 2 - δ)) :=
    hbound_seg _ _ (by linarith)
  have hs4 : (∫ t in (1 - δ / 2)..1, |stopDiffWave δ t|) ≤ 2 * (1 - (1 - δ / 2)) :=
    hbound_seg _ _ (by linarith)
  have hs1 : (∫ t in δ..(1 / 2 - δ), |stopDiffWave δ t|) = 0 := by
    have hcongr : (∫ t in δ..(1 / 2 - δ), |stopDiffWave δ t|) =
        ∫ _t in δ..(1 / 2 - δ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      dsimp only
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hη : etaWave δ t = 1 := etaWave_eq_one_of_mem_Icc hδ0 hδ1 ht.1 ht.2
      have hτ : tauDerivWave δ t = 1 :=
        tauDerivWave_eq_one_of_fract_mem hδ0 (by rw [hfr]; linarith [ht.1])
          (by rw [hfr]; linarith [ht.2])
      unfold stopDiffWave
      rw [hτ, hη]
      norm_num
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_zero]
  have hs3 : (∫ t in (1 / 2 + δ / 2)..(1 - δ / 2), |stopDiffWave δ t|) = 0 := by
    have hcongr : (∫ t in (1 / 2 + δ / 2)..(1 - δ / 2), |stopDiffWave δ t|) =
        ∫ _t in (1 / 2 + δ / 2)..(1 - δ / 2), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by linarith)] at ht
      dsimp only
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hη : etaWave δ t = 0 := by
        unfold etaWave; rw [hfr]; exact etaBump_eq_zero_of_ge hδ0 (by linarith [ht.1])
      have hτ : tauDerivWave δ t = -1 := by
        let s := t - 1 / 2
        have ht_eq : t = s + 1 / 2 := by dsimp [s]; ring
        have hfrs : Int.fract s = s :=
          Int.fract_eq_self.mpr ⟨by dsimp [s]; linarith [ht.1], by dsimp [s]; linarith [ht.2]⟩
        have hτs : tauDerivWave δ s = 1 :=
          tauDerivWave_eq_one_of_fract_mem hδ0
            (by rw [hfrs]; dsimp [s]; linarith [ht.1])
            (by rw [hfrs]; dsimp [s]; linarith [ht.2])
        rw [ht_eq, tauDerivWave_antiperiodic hδ0 hδ1 s, hτs]
      unfold stopDiffWave
      rw [hτ, hη]
      norm_num
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul, mul_zero]
  linarith

/-- Inductive `L¹([0, 1]²)` bound `(2 : ℝ) ^ k * ∫_{[0,1]²} A_k ≤ 2 - (1/2)^k ≤ 2`. -/
lemma ampProd_l1_bound (K k : ℕ) :
    (2 : ℝ) ^ k *
      (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        ampProd (staircaseDelta K) (staircaseLambda K) k (planarPt x y)) ≤
      2 - (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero =>
      simp only [pow_zero, one_mul, ampProd]
      have hle : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, boxCutoff2D (planarPt x y)) ≤
          ∫ _y in (0 : ℝ)..1, ∫ _x in (0 : ℝ)..1, (1 : ℝ) :=
        unitSq_integral_mono contDiff_boxCutoff2D.continuous continuous_const
          (fun _ _ _ _ => boxCutoff2D_le_one _)
      rw [unitSq_integral_const] at hle
      linarith
  | succ k ih =>
      let δ := staircaseDelta K
      let Λ := staircaseLambda K
      have hδ0 := staircaseDelta_pos K
      have hδ1 := staircaseDelta_le_eighth K
      have hAk_reg := contDiff_ampProd hδ0 hδ1 Λ k
      have hAk1_reg := contDiff_ampProd hδ0 hδ1 Λ (k + 1)
      let L := unitSqXLip (ampProd δ Λ k)
      have hL0 := unitSqXLip_nonneg (ampProd δ Λ k)
      let Nk := xFreqNat k (staircaseM K k)
      have hM_le_N : staircaseM K k ≤ Nk := le_xFreqNat k (staircaseM K k)
      have hNk1 : 1 ≤ Nk := (one_le_staircaseM K k).trans hM_le_N
      have hNk_pos : (0 : ℝ) < (Nk : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hNk1)
      have hrow : ∀ y ∈ Icc (0 : ℝ) 1,
          (∫ x in (0 : ℝ)..1, ampProd δ Λ (k + 1) (planarPt x y)) ≤
            (1 / 2) * (∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
              (2 * L) / (staircaseM K k : ℝ) := by
        intro y hy
        have hrew : ∀ x : ℝ, ampProd δ Λ (k + 1) (planarPt x y) =
            ampProd δ Λ k (planarPt x y) *
              etaWave δ ((Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y)) := by
          intro x; simp only [ampProd, planarPt_apply_zero, planarPt_apply_one]; congr 2; ring
        simp_rw [hrew]
        have hper := periodic_phase_sign_mean_bound_1d (N := Nk)
          (F := fun x => ampProd δ Λ k (planarPt x y)) (q := etaWave δ)
          (L := L) (B := 1) (a := Λ k * (spin3Ray k).1) (φ := Λ k * (spin3Ray k).2 * y)
          hNk1 hL0 zero_le_one (xFreqNat_ray_fst k (staircaseM K k))
          (cont_planarPt_x hAk_reg.continuous y) (contDiff_etaWave hδ0 hδ1).continuous
          (fun x₁ hx₁ x₂ hx₂ => sub_le_unitSqXLip (hAk_reg.of_le (by norm_cast)) hy hx₁ hx₂)
          (etaWave_periodic δ)
          (fun t => by rw [abs_of_nonneg (etaWave_nonneg δ t)]; exact etaWave_le_one δ t)
        have hFk_nn : 0 ≤ ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y) :=
          intervalIntegral.integral_nonneg zero_le_one (fun x _ => ampProd_nonneg δ Λ k _)
        have hμ_le : (∫ t in (0 : ℝ)..1, etaWave δ t) *
            (∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) ≤
            (1 / 2) * ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y) :=
          mul_le_mul_of_nonneg_right (integral_etaWave_le_half hδ0 hδ1) hFk_nn
        have herr_le : (2 * 1 * L) / (Nk : ℝ) ≤ (2 * L) / (staircaseM K k : ℝ) := by
          rw [mul_one]
          exact div_le_div_of_nonneg_left (by positivity) (staircaseM_pos K k)
            (by exact_mod_cast hM_le_N)
        linarith [(abs_le.mp hper).2]
      have hint : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ (k + 1) (planarPt x y)) ≤
          (1 / 2) * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
            (2 * L) / (staircaseM K k : ℝ) := by
        have hc_int_Ak := cont_inner_unitSq hAk_reg.continuous
        have hmono := intervalIntegral.integral_mono_on zero_le_one
          ((cont_inner_unitSq hAk1_reg.continuous).intervalIntegrable (μ := volume) 0 1)
          ((by fun_prop : Continuous (fun y : ℝ =>
            (1 / 2) * (∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
              (2 * L) / (staircaseM K k : ℝ))).intervalIntegrable (μ := volume) 0 1)
          hrow
        rw [intervalIntegral.integral_add
          ((by fun_prop : Continuous (fun y : ℝ =>
            (1 / 2) * ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y))).intervalIntegrable (μ := volume) 0 1)
          (continuous_const.intervalIntegrable (μ := volume) 0 1),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hmono
        linarith
      have h2k_err : (2 : ℝ) ^ (k + 1) * ((2 * L) / (staircaseM K k : ℝ)) ≤
          (1 / 2 : ℝ) ^ (k + 1) := by
        rw [mul_div_assoc', div_le_iff₀ (staircaseM_pos K k)]
        have hb := bLip_bound_staircaseM K k
        have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
        have hexp : (2 : ℝ) ^ (2 * k + 3) ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
          have hp : (2 : ℝ) ^ (2 * k + 3) ≤ (2 : ℝ) ^ (3 * k + 16) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          calc
            (2 : ℝ) ^ (2 * k + 3) = (2 : ℝ) ^ (2 * k + 3) * 1 := (mul_one _).symm
            _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
                mul_le_mul hp hK1 zero_le_one (by positivity)
        have hlhs : (2 : ℝ) ^ (k + 1) * (2 * L) =
            (1 / 2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (2 * k + 3) * L) := by
          have h1 : (2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1) = 1 := by
            rw [← mul_pow]; norm_num
          have h2 : (2 : ℝ) ^ (2 * k + 3) = (2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1) * 2) := by
            rw [show 2 * k + 3 = (k + 1) + (k + 1) + 1 by omega, pow_succ, pow_add]; ring
          rw [h2]
          calc
            (2 : ℝ) ^ (k + 1) * (2 * L)
                = ((2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1)) * ((2 : ℝ) ^ (k + 1) * 2 * L) := by
                  rw [h1]; ring
            _ = (1 / 2 : ℝ) ^ (k + 1) *
                  ((2 : ℝ) ^ (k + 1) * ((2 : ℝ) ^ (k + 1) * 2) * L) := by ring
        rw [hlhs]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_right hexp hL0).trans hb
      have hmul := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1))
      have hcancel : (2 : ℝ) ^ (k + 1) *
          ((1 / 2) * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
            (2 * L) / (staircaseM K k : ℝ)) =
          (2 : ℝ) ^ k * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
            (2 : ℝ) ^ (k + 1) * ((2 * L) / (staircaseM K k : ℝ)) := by
        rw [pow_succ]; ring
      rw [hcancel] at hmul
      have hhalf_succ : (1 / 2 : ℝ) ^ (k + 1) = (1 / 2) * (1 / 2 : ℝ) ^ k := by
        rw [pow_succ]; ring
      linarith

/-- Pure oscillatory rank-one wave factor of `uTerm`. -/
def uPureWave (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) : Euclidean 2 → ℝ :=
  fun p => ((1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3) *
    planarPlaneWave (Λ k * (spin3Ray k).1) (Λ k * (spin3Ray k).2) (gammaWave δ) p

private lemma uTerm_eq_mul_uPureWave (δ : ℝ) (Λ : ℕ → ℝ) (k : ℕ) :
    uTerm δ Λ k = fun p => ampProd δ Λ k p * uPureWave δ Λ k p := by
  funext p; unfold uTerm uPureWave planarPlaneWave; ring_nf

private lemma uPureWave_jet2_and_third_partials (K k : ℕ) (p : Euclidean 2) :
    let δ := staircaseDelta K
    let Λ := staircaseLambda K
    let E := (2 : ℝ) ^ k / (16 * Λ k)
    (|uPureWave δ Λ k p| ≤ E ∧
      |planarDx (uPureWave δ Λ k) p| ≤ E ∧
      |planarDy (uPureWave δ Λ k) p| ≤ E ∧
      |planarDx (planarDx (uPureWave δ Λ k)) p| ≤ E ∧
      |planarDx (planarDy (uPureWave δ Λ k)) p| ≤ E ∧
      |planarDy (planarDy (uPureWave δ Λ k)) p| ≤ E) ∧
    planarDx (planarDy (planarDy (uPureWave δ Λ k))) p =
      (1 / 4 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 * (spin3Ray k).2 ^ 2) *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) ∧
    spin3A1 (uPureWave δ Λ k) p =
      (1 / 4 : ℝ) * (2 : ℝ) ^ k *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) ∧
    spin3A2 (uPureWave δ Λ k) p = 0 := by
  dsimp only
  set δ := staircaseDelta K
  set Λ := staircaseLambda K
  have hδ0 := staircaseDelta_pos K
  have hδ1 := staircaseDelta_le_eighth K
  have hΛ1 := one_le_staircaseLambda K k
  have hΛ_pos : 0 < Λ k := staircaseLambda_pos K k
  have hΛ_ne : Λ k ≠ 0 := ne_of_gt hΛ_pos
  set α := Λ k * (spin3Ray k).1
  set β := Λ k * (spin3Ray k).2
  set c := (1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3
  have hc_nn : 0 ≤ c := by dsimp [c]; positivity
  let W0 := planarPlaneWave α β (gammaWave δ)
  have hW0_reg : ContDiff ℝ (4 : ℕ) W0 := contDiff_planarPlaneWave α β (contDiff_gammaWave hδ0 hδ1)
  have hd_x : planarDx W0 = planarPlaneWave α β (fun t => α * gammaDerivWave δ t) :=
    planarDx_planarPlaneWave_s α β (hasDerivAt_gammaWave hδ0 hδ1)
  have hd_y : planarDy W0 = planarPlaneWave α β (fun t => β * gammaDerivWave δ t) :=
    planarDy_planarPlaneWave_s α β (hasDerivAt_gammaWave hδ0 hδ1)
  have hd_xx : planarDx (planarDx W0) = planarPlaneWave α β (fun t => α * (α * tauWave δ t)) := by
    rw [hd_x]; exact planarDx_planarPlaneWave_s α β (fun t => (hasDerivAt_gammaDerivWave hδ0 hδ1 t).const_mul α)
  have hd_xy : planarDx (planarDy W0) = planarPlaneWave α β (fun t => α * (β * tauWave δ t)) := by
    rw [hd_y]; exact planarDx_planarPlaneWave_s α β (fun t => (hasDerivAt_gammaDerivWave hδ0 hδ1 t).const_mul β)
  have hd_yy : planarDy (planarDy W0) = planarPlaneWave α β (fun t => β * (β * tauWave δ t)) := by
    rw [hd_y]; exact planarDy_planarPlaneWave_s α β (fun t => (hasDerivAt_gammaDerivWave hδ0 hδ1 t).const_mul β)
  have hd_xyy : planarDx (planarDy (planarDy W0)) =
      planarPlaneWave α β (fun t => α * (β * (β * tauDerivWave δ t))) := by
    rw [hd_yy]
    exact planarDx_planarPlaneWave_s α β
      (fun t => ((hasDerivAt_tauWave hδ0 hδ1 t).const_mul β).const_mul β)
  have hconst_dx : ∀ {G : Euclidean 2 → ℝ}, ContDiff ℝ (1 : ℕ) G →
      planarDx (fun q => c * G q) = fun q => c * planarDx G q :=
    fun hG => funext fun q => planarDx_const_mul_s c (diff_of_c1 (r := 0) hG q)
  have hconst_dy : ∀ {G : Euclidean 2 → ℝ}, ContDiff ℝ (1 : ℕ) G →
      planarDy (fun q => c * G q) = fun q => c * planarDy G q :=
    fun hG => funext fun q => planarDy_const_mul_s c (diff_of_c1 (r := 0) hG q)
  have hW_eq : uPureWave δ Λ k = fun q => c * W0 q := rfl
  have hp_dx : planarDx (uPureWave δ Λ k) = fun q => c * planarDx W0 q :=
    hW_eq ▸ hconst_dx (hW0_reg.of_le (by norm_cast))
  have hp_dy : planarDy (uPureWave δ Λ k) = fun q => c * planarDy W0 q :=
    hW_eq ▸ hconst_dy (hW0_reg.of_le (by norm_cast))
  have hp_dxx : planarDx (planarDx (uPureWave δ Λ k)) = fun q => c * planarDx (planarDx W0) q := by
    rw [hp_dx]; exact hconst_dx ((contDiff_planarDx_b1 (r := 3) hW0_reg).of_le (by norm_cast))
  have hp_dxy : planarDx (planarDy (uPureWave δ Λ k)) = fun q => c * planarDx (planarDy W0) q := by
    rw [hp_dy]; exact hconst_dx ((contDiff_planarDy_b1 (r := 3) hW0_reg).of_le (by norm_cast))
  have hp_dyy : planarDy (planarDy (uPureWave δ Λ k)) = fun q => c * planarDy (planarDy W0) q := by
    rw [hp_dy]; exact hconst_dy ((contDiff_planarDy_b1 (r := 3) hW0_reg).of_le (by norm_cast))
  have hp_dxyy : planarDx (planarDy (planarDy (uPureWave δ Λ k))) =
      fun q => c * planarDx (planarDy (planarDy W0)) q := by
    rw [hp_dyy]
    exact hconst_dx
      ((contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hW0_reg)).of_le (by norm_cast))
  have hp_dxxx : planarDx (planarDx (planarDx (uPureWave δ Λ k))) =
      fun q => c * planarDx (planarDx (planarDx W0)) q := by
    rw [hp_dxx]
    exact hconst_dx
      ((contDiff_planarDx_b1 (r := 2) (contDiff_planarDx_b1 (r := 3) hW0_reg)).of_le (by norm_cast))
  have hp_dxxy : planarDx (planarDx (planarDy (uPureWave δ Λ k))) =
      fun q => c * planarDx (planarDx (planarDy W0)) q := by
    rw [hp_dxy]
    exact hconst_dx
      ((contDiff_planarDx_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hW0_reg)).of_le (by norm_cast))
  have hp_dyyy : planarDy (planarDy (planarDy (uPureWave δ Λ k))) =
      fun q => c * planarDy (planarDy (planarDy W0)) q := by
    rw [hp_dyy]
    exact hconst_dy
      ((contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hW0_reg)).of_le (by norm_cast))
  have hα_abs : |α| ≤ Λ k := by
    dsimp [α]; rw [abs_mul, abs_of_pos hΛ_pos]
    calc Λ k * |(spin3Ray k).1| ≤ Λ k * 1 := mul_le_mul_of_nonneg_left (abs_spin3Ray_fst_le_one k) hΛ_pos.le
      _ = Λ k := mul_one _
  have hβ_abs : |β| ≤ Λ k := by
    dsimp [β]; rw [abs_mul, abs_of_pos hΛ_pos]
    calc Λ k * |(spin3Ray k).2| ≤ Λ k * 1 := mul_le_mul_of_nonneg_left (abs_spin3Ray_snd_le_one k) hΛ_pos.le
      _ = Λ k := mul_one _
  have hΛ_sq : Λ k ≤ (Λ k) ^ 2 := by nlinarith
  have hΛ_cb : Λ k ≤ (Λ k) ^ 3 := by nlinarith
  have h0_le : c * (1 / 64) ≤ (2 : ℝ) ^ k / (16 * Λ k) := by
    dsimp [c]
    have h1 : (2 : ℝ) ^ k / (256 * (Λ k) ^ 3) ≤ (2 : ℝ) ^ k / (16 * Λ k) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    linarith [show (1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3 * (1 / 64) =
      (2 : ℝ) ^ k / (256 * (Λ k) ^ 3) by ring]
  have h1_le : c * (Λ k * (1 / 16)) ≤ (2 : ℝ) ^ k / (16 * Λ k) := by
    dsimp [c]
    have h1 : (2 : ℝ) ^ k / (64 * (Λ k) ^ 2) ≤ (2 : ℝ) ^ k / (16 * Λ k) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have heq : (1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3 * (Λ k * (1 / 16)) =
        (2 : ℝ) ^ k / (64 * (Λ k) ^ 2) := by field_simp [hΛ_ne]; ring
    linarith
  have h2_le : c * (Λ k * (Λ k * (1 / 4))) ≤ (2 : ℝ) ^ k / (16 * Λ k) := by
    dsimp [c]
    have heq : (1 / 4 : ℝ) * (2 : ℝ) ^ k / (Λ k) ^ 3 * (Λ k * (Λ k * (1 / 4))) =
        (2 : ℝ) ^ k / (16 * Λ k) := by field_simp [hΛ_ne]; ring
    linarith
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hW_eq]; dsimp [W0, planarPlaneWave]
    rw [abs_mul, abs_of_nonneg hc_nn]
    exact (mul_le_mul_of_nonneg_left (abs_gammaWave_le hδ0 hδ1 _) hc_nn).trans h0_le
  · rw [hp_dx, hd_x]; dsimp [planarPlaneWave]
    rw [abs_mul, abs_mul, abs_of_nonneg hc_nn]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hα_abs (abs_gammaDerivWave_le hδ0 hδ1 _) (abs_nonneg _) hΛ_pos.le) hc_nn).trans h1_le
  · rw [hp_dy, hd_y]; dsimp [planarPlaneWave]
    rw [abs_mul, abs_mul, abs_of_nonneg hc_nn]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hβ_abs (abs_gammaDerivWave_le hδ0 hδ1 _) (abs_nonneg _) hΛ_pos.le) hc_nn).trans h1_le
  · rw [hp_dxx, hd_xx]; dsimp [planarPlaneWave]
    rw [abs_mul c, abs_mul α, abs_mul α, abs_of_nonneg hc_nn]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hα_abs (mul_le_mul hα_abs (abs_tauWave_le hδ0 hδ1 _) (abs_nonneg _) hΛ_pos.le)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hΛ_pos.le) hc_nn).trans h2_le
  · rw [hp_dxy, hd_xy]; dsimp [planarPlaneWave]
    rw [abs_mul c, abs_mul α, abs_mul β, abs_of_nonneg hc_nn]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hα_abs (mul_le_mul hβ_abs (abs_tauWave_le hδ0 hδ1 _) (abs_nonneg _) hΛ_pos.le)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hΛ_pos.le) hc_nn).trans h2_le
  · rw [hp_dyy, hd_yy]; dsimp [planarPlaneWave]
    rw [abs_mul c, abs_mul β, abs_mul β, abs_of_nonneg hc_nn]
    exact (mul_le_mul_of_nonneg_left
      (mul_le_mul hβ_abs (mul_le_mul hβ_abs (abs_tauWave_le hδ0 hδ1 _) (abs_nonneg _) hΛ_pos.le)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hΛ_pos.le) hc_nn).trans h2_le
  · rw [hp_dxyy, hd_xyy]; dsimp [planarPlaneWave, c, α, β]
    have harg : Λ k * (spin3Ray k).1 * p 0 + Λ k * (spin3Ray k).2 * p 1 =
        Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1) := by ring
    rw [harg]
    field_simp [hΛ_ne]
  · have hspin := (spin3_ray_planeWave k (Λ k)
      (hasDerivAt_gammaWave hδ0 hδ1)
      (hasDerivAt_gammaDerivWave hδ0 hδ1)
      (hasDerivAt_tauWave hδ0 hδ1) p).1
    have hlin : spin3A1 (uPureWave δ Λ k) p = c * spin3A1 W0 p := by
      unfold spin3A1; rw [hp_dxxx, hp_dxyy]; ring
    rw [hlin]; dsimp [W0, α, β, c]; rw [hspin]
    field_simp [hΛ_ne]; ring
  · have hspin := (spin3_ray_planeWave k (Λ k)
      (hasDerivAt_gammaWave hδ0 hδ1)
      (hasDerivAt_gammaDerivWave hδ0 hδ1)
      (hasDerivAt_tauWave hδ0 hδ1) p).2
    have hlin : spin3A2 (uPureWave δ Λ k) p = c * spin3A2 W0 p := by
      unfold spin3A2; rw [hp_dxxy, hp_dyyy]; ring
    rw [hlin]; dsimp [W0, α, β]; rw [hspin, mul_zero]

private lemma uTerm_third_commutators (K k : ℕ) (p : Euclidean 2) :
    let δ := staircaseDelta K
    let Λ := staircaseLambda K
    let E := (2 : ℝ) ^ k / (16 * Λ k)
    |planarDx (planarDy (planarDy (uTerm δ Λ k))) p -
        (1 / 4 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 * (spin3Ray k).2 ^ 2) *
          ampProd δ Λ k p *
          tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤
      3 * jet3Norm (ampProd δ Λ k) p * E ∧
    |spin3A1 (uTerm δ Λ k) p -
        (1 / 4 : ℝ) * (2 : ℝ) ^ k * ampProd δ Λ k p *
          tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤
      12 * jet3Norm (ampProd δ Λ k) p * E ∧
    |spin3A2 (uTerm δ Λ k) p| ≤ 12 * jet3Norm (ampProd δ Λ k) p * E := by
  dsimp only
  have hδ0 := staircaseDelta_pos K
  have hδ1 := staircaseDelta_le_eighth K
  have hA3 : ContDiff ℝ (3 : ℕ) (ampProd (staircaseDelta K) (staircaseLambda K) k) :=
    (contDiff_ampProd hδ0 hδ1 (staircaseLambda K) k).of_le (by norm_cast)
  have hW3 : ContDiff ℝ (3 : ℕ) (uPureWave (staircaseDelta K) (staircaseLambda K) k) := by
    unfold uPureWave
    exact contDiff_const.mul
      (contDiff_planarPlaneWave _ _ ((contDiff_gammaWave hδ0 hδ1).of_le (by norm_cast)))
  have hΛ_pos := staircaseLambda_pos K k
  have hE_nn : 0 ≤ (2 : ℝ) ^ k / (16 * staircaseLambda K k) := by positivity
  obtain ⟨hjet2, hxyy, ha1, ha2⟩ := uPureWave_jet2_and_third_partials K k p
  have hcomm := third_partials_commutator_jet3Norm hA3 hW3 hE_nn p hjet2
  rw [← uTerm_eq_mul_uPureWave] at hcomm
  rw [hxyy] at hcomm
  rw [ha1] at hcomm
  rw [ha2, mul_zero, sub_zero] at hcomm
  refine ⟨?_, ?_, hcomm.2.2⟩
  · convert hcomm.1 using 2; ring
  · convert hcomm.2.1 using 2; ring

private lemma spin3A1_finset_sum (K : ℕ) (p : Euclidean 2) :
    spin3A1 (staircaseU K) p =
      ∑ k ∈ Finset.range K, spin3A1 (uTerm (staircaseDelta K) (staircaseLambda K) k) p := by
  unfold spin3A1 staircaseU
  have hr := fun k => contDiff_uTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
    (staircaseLambda K) k
  have hdx1 : planarDx (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q) =
      fun q => ∑ k ∈ Finset.range K, planarDx (uTerm (staircaseDelta K) (staircaseLambda K) k) q :=
    funext fun q => planarDx_finset_sum _ (fun k _ => diff_of_c1 (r := 3) (hr k) q)
  have hdy1 : planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q) =
      fun q => ∑ k ∈ Finset.range K, planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k) q :=
    funext fun q => planarDy_finset_sum _ (fun k _ => diff_of_c1 (r := 3) (hr k) q)
  have hdxx : planarDx (planarDx (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q)) =
      fun q => ∑ k ∈ Finset.range K, planarDx (planarDx (uTerm (staircaseDelta K) (staircaseLambda K) k)) q := by
    rw [hdx1]
    exact funext fun q => planarDx_finset_sum _
      (fun k _ => diff_of_c1 (r := 2) (contDiff_planarDx_b1 (r := 3) (hr k)) q)
  have hdyy : planarDy (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q)) =
      fun q => ∑ k ∈ Finset.range K, planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k)) q := by
    rw [hdy1]
    exact funext fun q => planarDy_finset_sum _
      (fun k _ => diff_of_c1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hr k)) q)
  have hdxxx : planarDx (planarDx (planarDx (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q))) p =
      ∑ k ∈ Finset.range K, planarDx (planarDx (planarDx (uTerm (staircaseDelta K) (staircaseLambda K) k))) p := by
    rw [hdxx]
    exact planarDx_finset_sum _
      (fun k _ => diff_of_c1 (r := 1) (contDiff_planarDx_b1 (r := 2) (contDiff_planarDx_b1 (r := 3) (hr k))) p)
  have hdxyy : planarDx (planarDy (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q))) p =
      ∑ k ∈ Finset.range K, planarDx (planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k))) p := by
    rw [hdyy]
    exact planarDx_finset_sum _
      (fun k _ => diff_of_c1 (r := 1) (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hr k))) p)
  rw [hdxxx, hdxyy, Finset.mul_sum, ← Finset.sum_sub_distrib]

private lemma spin3A2_finset_sum (K : ℕ) (p : Euclidean 2) :
    spin3A2 (staircaseU K) p =
      ∑ k ∈ Finset.range K, spin3A2 (uTerm (staircaseDelta K) (staircaseLambda K) k) p := by
  unfold spin3A2 staircaseU
  have hr := fun k => contDiff_uTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
    (staircaseLambda K) k
  have hdy1 : planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q) =
      fun q => ∑ k ∈ Finset.range K, planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k) q :=
    funext fun q => planarDy_finset_sum _ (fun k _ => diff_of_c1 (r := 3) (hr k) q)
  have hdxy : planarDx (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q)) =
      fun q => ∑ k ∈ Finset.range K, planarDx (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k)) q := by
    rw [hdy1]
    exact funext fun q => planarDx_finset_sum _
      (fun k _ => diff_of_c1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hr k)) q)
  have hdyy : planarDy (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q)) =
      fun q => ∑ k ∈ Finset.range K, planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k)) q := by
    rw [hdy1]
    exact funext fun q => planarDy_finset_sum _
      (fun k _ => diff_of_c1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hr k)) q)
  have hdxxy : planarDx (planarDx (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q))) p =
      ∑ k ∈ Finset.range K, planarDx (planarDx (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k))) p := by
    rw [hdxy]
    exact planarDx_finset_sum _
      (fun k _ => diff_of_c1 (r := 1) (contDiff_planarDx_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hr k))) p)
  have hdyyy : planarDy (planarDy (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q))) p =
      ∑ k ∈ Finset.range K, planarDy (planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k))) p := by
    rw [hdyy]
    exact planarDy_finset_sum _
      (fun k _ => diff_of_c1 (r := 1) (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hr k))) p)
  rw [hdxxy, hdyyy, Finset.mul_sum, ← Finset.sum_sub_distrib]

private lemma cont_spin3A1 {U : Euclidean 2 → ℝ} (hU : ContDiff ℝ (4 : ℕ) U) :
    Continuous (spin3A1 U) := by
  unfold spin3A1
  have h1 := (contDiff_planarDx_b1 (r := 1)
    (contDiff_planarDx_b1 (r := 2) (contDiff_planarDx_b1 (r := 3) hU))).continuous
  have h2 := (contDiff_planarDx_b1 (r := 1)
    (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hU))).continuous
  exact h1.sub (continuous_const.mul h2)

private lemma cont_spin3A2 {U : Euclidean 2 → ℝ} (hU : ContDiff ℝ (4 : ℕ) U) :
    Continuous (spin3A2 U) := by
  unfold spin3A2
  have h1 := (contDiff_planarDx_b1 (r := 1)
    (contDiff_planarDx_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hU))).continuous
  have h2 := (contDiff_planarDy_b1 (r := 1)
    (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hU))).continuous
  exact (continuous_const.mul h1).sub h2

/-- **Uniform Spin-3 `L¹([0, 1]²)` Bound (`≤ 1`):**
For every scale count `K : ℕ`,
`∫_0^1 ∫_0^1 (|spin3A1 (staircaseU K)| + |spin3A2 (staircaseU K)|) ≤ 1`. -/
theorem spin3_l1_staircaseU_le_one (K : ℕ) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      (|spin3A1 (staircaseU K) (planarPt x y)| +
        |spin3A2 (staircaseU K) (planarPt x y)|)) ≤ 1 := by
  let δ := staircaseDelta K
  let Λ := staircaseLambda K
  have hδ0 := staircaseDelta_pos K
  have hδ1 := staircaseDelta_le_eighth K
  have hU_reg := contDiff_staircaseU K
  let mainTerm : ℕ → Euclidean 2 → ℝ := fun k p =>
    (1 / 4 : ℝ) * (2 : ℝ) ^ k * ampProd δ Λ k p *
      tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
  let telMain : Euclidean 2 → ℝ := fun p =>
    (1 / 4 : ℝ) * ((2 : ℝ) ^ K * ampProd δ Λ K p - ampProd δ Λ 0 p)
  let transTerm : ℕ → Euclidean 2 → ℝ := fun k p =>
    (1 / 4 : ℝ) * (2 : ℝ) ^ k * ampProd δ Λ k p *
      |stopDiffWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))|
  have htel_id : ∀ p : Euclidean 2,
      (∑ k ∈ Finset.range K, mainTerm k p) =
        telMain p +
          ∑ k ∈ Finset.range K,
            (1 / 4 : ℝ) * (2 : ℝ) ^ k * ampProd δ Λ k p *
              stopDiffWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) := by
    intro p
    have hstep : ∀ k : ℕ,
        mainTerm k p =
          (1 / 4 : ℝ) * ((2 : ℝ) ^ (k + 1) * ampProd δ Λ (k + 1) p -
              (2 : ℝ) ^ k * ampProd δ Λ k p) +
            (1 / 4 : ℝ) * (2 : ℝ) ^ k * ampProd δ Λ k p *
              stopDiffWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) := by
      intro k
      dsimp [mainTerm, stopDiffWave, ampProd]
      rw [pow_succ]
      ring
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have htel := Finset.sum_range_sub (fun k => (2 : ℝ) ^ k * ampProd δ Λ k p) K
    rw [htel]
    dsimp [telMain]
    simp only [pow_zero, one_mul]
  have hpt_bound : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |spin3A1 (staircaseU K) (planarPt x y)| + |spin3A2 (staircaseU K) (planarPt x y)| ≤
        ((1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K (planarPt x y) +
          (1 / 4 : ℝ) * ampProd δ Λ 0 (planarPt x y)) +
        (∑ k ∈ Finset.range K, transTerm k (planarPt x y)) +
        (∑ k ∈ Finset.range K, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k) := by
    intro x hx y hy
    set p := planarPt x y
    rw [spin3A1_finset_sum K p, spin3A2_finset_sum K p]
    have hcomm_k : ∀ k ∈ Finset.range K,
        |spin3A1 (uTerm δ Λ k) p - mainTerm k p| + |spin3A2 (uTerm δ Λ k) p| ≤
          (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k := by
      intro k _
      have hc := uTerm_third_commutators K k p
      have hAk3 : ContDiff ℝ (3 : ℕ) (ampProd δ Λ k) :=
        (contDiff_ampProd hδ0 hδ1 Λ k).of_le (by norm_cast)
      have hj_sup : jet3Norm (ampProd δ Λ k) p ≤ unitSqSup (jet3Norm (ampProd δ Λ k)) :=
        (le_abs_self _).trans (abs_le_unitSqSup (continuous_jet3Norm hAk3) hx hy)
      have hE_nn : 0 ≤ (2 : ℝ) ^ k / (16 * Λ k) := by
        have := staircaseLambda_pos K k; positivity
      have hsum24 : |spin3A1 (uTerm δ Λ k) p - mainTerm k p| + |spin3A2 (uTerm δ Λ k) p| ≤
          24 * unitSqSup (jet3Norm (ampProd δ Λ k)) * ((2 : ℝ) ^ k / (16 * Λ k)) := by
        have h12 := hc.2.1
        have h12' := hc.2.2
        have hmul : 24 * jet3Norm (ampProd δ Λ k) p * ((2 : ℝ) ^ k / (16 * Λ k)) ≤
            24 * unitSqSup (jet3Norm (ampProd δ Λ k)) * ((2 : ℝ) ^ k / (16 * Λ k)) :=
          mul_le_mul_of_nonneg_right (by linarith) hE_nn
        linarith
      have h24_eq : 24 * unitSqSup (jet3Norm (ampProd δ Λ k)) * ((2 : ℝ) ^ k / (16 * Λ k)) =
          ((3 / 4 : ℝ) * (2 : ℝ) ^ k * unitSqSup (jet3Norm (ampProd δ Λ k))) /
            (staircaseM K k : ℝ) := by
        dsimp [Λ, staircaseLambda]; field_simp [ne_of_gt (staircaseM_pos K k)]; ring
      rw [h24_eq] at hsum24
      have hbJ := bJet3_bound_staircaseM K k
      have hdiv : ((3 / 4 : ℝ) * (2 : ℝ) ^ k * unitSqSup (jet3Norm (ampProd δ Λ k))) /
          (staircaseM K k : ℝ) ≤ (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k := by
        rw [div_le_iff₀ (staircaseM_pos K k)]
        set J := unitSqSup (jet3Norm (ampProd δ Λ k))
        have hJ0 := unitSqSup_nonneg (jet3Norm (ampProd δ Λ k))
        have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
        have hexp : 24 * (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
          have hp : 24 * (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (3 * k + 16) := by
            have h2k : (2 : ℝ) ^ (2 * k) * 24 ≤ (2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ 16 :=
              mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
            have h3k : (2 : ℝ) ^ (2 * k + 16) ≤ (2 : ℝ) ^ (3 * k + 16) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            rw [pow_add] at h3k
            linarith
          calc
            24 * (2 : ℝ) ^ (2 * k) = (24 * (2 : ℝ) ^ (2 * k)) * 1 := (mul_one _).symm
            _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
                mul_le_mul hp hK1 zero_le_one (by positivity)
        have hlhs : (3 / 4 : ℝ) * (2 : ℝ) ^ k * J =
            (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k * (24 * (2 : ℝ) ^ (2 * k) * J) := by
          have h1 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
          have h2 : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
            rw [show 2 * k = k + k by omega, pow_add]
          rw [h2]
          calc
            (3 / 4 : ℝ) * (2 : ℝ) ^ k * J
                = ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) * ((3 / 4 : ℝ) * (2 : ℝ) ^ k * J) := by
                  rw [h1, one_mul]
            _ = (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k *
                  (24 * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) * J) := by ring
        rw [hlhs]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (mul_le_mul_of_nonneg_right hexp hJ0).trans hbJ
      exact hsum24.trans hdiv
    have ha1_split : |∑ k ∈ Finset.range K, spin3A1 (uTerm δ Λ k) p| ≤
        |∑ k ∈ Finset.range K, mainTerm k p| +
          ∑ k ∈ Finset.range K, |spin3A1 (uTerm δ Λ k) p - mainTerm k p| := by
      have heq : (∑ k ∈ Finset.range K, spin3A1 (uTerm δ Λ k) p) =
          (∑ k ∈ Finset.range K, mainTerm k p) +
            ∑ k ∈ Finset.range K, (spin3A1 (uTerm δ Λ k) p - mainTerm k p) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [heq]
      exact (abs_add_le _ _).trans
        (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
    have ha2_split : |∑ k ∈ Finset.range K, spin3A2 (uTerm δ Λ k) p| ≤
        ∑ k ∈ Finset.range K, |spin3A2 (uTerm δ Λ k) p| :=
      Finset.abs_sum_le_sum_abs _ _
    have hmain_abs : |∑ k ∈ Finset.range K, mainTerm k p| ≤
        ((1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p) +
          ∑ k ∈ Finset.range K, transTerm k p := by
      rw [htel_id p]
      have htel_b : |telMain p| ≤
          (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p := by
        dsimp [telMain]
        have hAK := ampProd_nonneg δ Λ K p
        have hA0 := ampProd_nonneg δ Λ 0 p
        have hsub : |(2 : ℝ) ^ K * ampProd δ Λ K p - ampProd δ Λ 0 p| ≤
            (2 : ℝ) ^ K * ampProd δ Λ K p + ampProd δ Λ 0 p := by
          calc
            |(2 : ℝ) ^ K * ampProd δ Λ K p - ampProd δ Λ 0 p|
                ≤ |(2 : ℝ) ^ K * ampProd δ Λ K p| + |ampProd δ Λ 0 p| := abs_sub _ _
            _ = (2 : ℝ) ^ K * ampProd δ Λ K p + ampProd δ Λ 0 p := by
                  rw [abs_of_nonneg (by positivity), abs_of_nonneg hA0]
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
        linarith
      have htr_b : |∑ k ∈ Finset.range K,
          (1 / 4 : ℝ) * (2 : ℝ) ^ k * ampProd δ Λ k p *
            stopDiffWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤
          ∑ k ∈ Finset.range K, transTerm k p := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        dsimp [transTerm]
        rw [abs_mul, abs_of_nonneg (mul_nonneg (by positivity) (ampProd_nonneg δ Λ k p))]
      exact (abs_add_le _ _).trans (add_le_add htel_b htr_b)
    have hcomm_sum : (∑ k ∈ Finset.range K, |spin3A1 (uTerm δ Λ k) p - mainTerm k p|) +
        (∑ k ∈ Finset.range K, |spin3A2 (uTerm δ Λ k) p|) ≤
        ∑ k ∈ Finset.range K, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum hcomm_k
    linarith
  have hc_lhs : Continuous (fun p => |spin3A1 (staircaseU K) p| + |spin3A2 (staircaseU K) p|) :=
    (cont_spin3A1 hU_reg).abs.add (cont_spin3A2 hU_reg).abs
  have hc_tel1 : Continuous (fun p => (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p) :=
    continuous_const.mul (contDiff_ampProd hδ0 hδ1 Λ K).continuous
  have hc_tel0 : Continuous (fun p => (1 / 4 : ℝ) * ampProd δ Λ 0 p) :=
    continuous_const.mul (contDiff_ampProd hδ0 hδ1 Λ 0).continuous
  have hc_tr : ∀ k : ℕ, Continuous (transTerm k) := by
    intro k
    dsimp [transTerm]
    have hw : Continuous (fun p : Euclidean 2 =>
        |stopDiffWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))|) := by
      have hlin : Continuous (fun p : Euclidean 2 =>
          Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) :=
        continuous_const.mul
          ((continuous_const.mul (EuclideanSpace.proj (0 : Fin 2)).continuous).add
            (continuous_const.mul (EuclideanSpace.proj (1 : Fin 2)).continuous))
      exact (cont_stopDiffWave hδ0 hδ1).abs.comp hlin
    exact (continuous_const.mul (contDiff_ampProd hδ0 hδ1 Λ k).continuous).mul hw
  have hc_sum_tr : Continuous (fun p => ∑ k ∈ Finset.range K, transTerm k p) :=
    continuous_finsetSum _ fun k _ => hc_tr k
  have hc_pair : Continuous (fun p =>
      (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p) := by fun_prop
  have hc_triple : Continuous (fun p =>
      ((1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p) +
        ∑ k ∈ Finset.range K, transTerm k p) := by fun_prop
  have hc_rhs : Continuous (fun p =>
      (((1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p) +
        ∑ k ∈ Finset.range K, transTerm k p) +
      ∑ k ∈ Finset.range K, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k) := by fun_prop
  have hint_mono := unitSq_integral_mono hc_lhs hc_rhs hpt_bound
  rw [unitSq_integral_add
        (F := fun p => ((1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p) +
          ∑ k ∈ Finset.range K, transTerm k p)
        (G := fun _ => ∑ k ∈ Finset.range K, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k)
        hc_triple continuous_const,
      unitSq_integral_add
        (F := fun p => (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p + (1 / 4 : ℝ) * ampProd δ Λ 0 p)
        (G := fun p => ∑ k ∈ Finset.range K, transTerm k p)
        hc_pair hc_sum_tr,
      unitSq_integral_add (F := fun p => (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K p)
        (G := fun p => (1 / 4 : ℝ) * ampProd δ Λ 0 p) hc_tel1 hc_tel0,
      unitSq_integral_finset_sum (Finset.range K) (fun k _ => hc_tr k),
      unitSq_integral_const] at hint_mono
  have hI_K : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K (planarPt x y)) ≤ 1 / 2 := by
    have hrew : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        (1 / 4 : ℝ) * (2 : ℝ) ^ K * ampProd δ Λ K (planarPt x y)) =
        (1 / 4 : ℝ) * ((2 : ℝ) ^ K *
          ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ K (planarPt x y)) := by
      simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    rw [hrew]
    have hl1 := ampProd_l1_bound K K
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
    linarith
  have hI_0 : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      (1 / 4 : ℝ) * ampProd δ Λ 0 (planarPt x y)) ≤ 1 / 4 := by
    rw [unitSq_integral_const_mul _ (contDiff_ampProd hδ0 hδ1 Λ 0).continuous]
    have hl0 := ampProd_l1_bound K 0
    simp only [pow_zero, one_mul] at hl0
    linarith
  have htr_each : ∀ k ∈ Finset.range K,
      (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, transTerm k (planarPt x y)) ≤
        3 * δ + (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k _
    have hAk_reg := contDiff_ampProd hδ0 hδ1 Λ k
    let L := unitSqXLip (ampProd δ Λ k)
    have hL0 := unitSqXLip_nonneg (ampProd δ Λ k)
    let Nk := xFreqNat k (staircaseM K k)
    have hM_le_N : staircaseM K k ≤ Nk := le_xFreqNat k (staircaseM K k)
    have hNk1 : 1 ≤ Nk := (one_le_staircaseM K k).trans hM_le_N
    have hrow : ∀ y ∈ Icc (0 : ℝ) 1,
        (∫ x in (0 : ℝ)..1,
          ampProd δ Λ k (planarPt x y) *
            |stopDiffWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
              (spin3Ray k).2 * (planarPt x y) 1))|) ≤
          6 * δ * (∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
            (4 * L) / (staircaseM K k : ℝ) := by
      intro y hy
      have harg : ∀ x : ℝ,
          Λ k * ((spin3Ray k).1 * (planarPt x y) 0 + (spin3Ray k).2 * (planarPt x y) 1) =
            (Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y) := by
        intro x; simp only [planarPt_apply_zero, planarPt_apply_one]; ring
      simp_rw [harg]
      have hper := periodic_phase_sign_mean_bound_1d (N := Nk)
        (F := fun x => ampProd δ Λ k (planarPt x y))
        (q := fun t => |stopDiffWave δ t|)
        (L := L) (B := 2) (a := Λ k * (spin3Ray k).1) (φ := Λ k * (spin3Ray k).2 * y)
        hNk1 hL0 (by norm_num) (xFreqNat_ray_fst k (staircaseM K k))
        (cont_planarPt_x hAk_reg.continuous y) (cont_stopDiffWave hδ0 hδ1).abs
        (fun x₁ hx₁ x₂ hx₂ => sub_le_unitSqXLip (hAk_reg.of_le (by norm_cast)) hy hx₁ hx₂)
        (fun t => by rw [stopDiffWave_periodic hδ0 hδ1 t])
        (fun t => by rw [abs_abs]; exact abs_stopDiffWave_le_two hδ0 hδ1 t)
      have hFk_nn : 0 ≤ ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y) :=
        intervalIntegral.integral_nonneg zero_le_one (fun x _ => ampProd_nonneg δ Λ k _)
      have hμ_le : (∫ t in (0 : ℝ)..1, |stopDiffWave δ t|) *
          (∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) ≤
          (6 * δ) * ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y) :=
        mul_le_mul_of_nonneg_right (integral_abs_stopDiffWave_le hδ0 hδ1) hFk_nn
      have herr_le : (2 * 2 * L) / (Nk : ℝ) ≤ (4 * L) / (staircaseM K k : ℝ) := by
        have h4 : (2 : ℝ) * 2 * L = 4 * L := by ring
        rw [h4]
        exact div_le_div_of_nonneg_left (by positivity) (staircaseM_pos K k)
          (by exact_mod_cast hM_le_N)
      linarith [(abs_le.mp hper).2]
    have hc_base : Continuous (fun p : Euclidean 2 =>
        ampProd δ Λ k p * |stopDiffWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))|) := by
      have hlin : Continuous (fun p : Euclidean 2 =>
          Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) :=
        continuous_const.mul
          ((continuous_const.mul (EuclideanSpace.proj (0 : Fin 2)).continuous).add
            (continuous_const.mul (EuclideanSpace.proj (1 : Fin 2)).continuous))
      exact hAk_reg.continuous.mul ((cont_stopDiffWave hδ0 hδ1).abs.comp hlin)
    have hint_y : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        ampProd δ Λ k (planarPt x y) *
          |stopDiffWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
            (spin3Ray k).2 * (planarPt x y) 1))|) ≤
        6 * δ * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
          (4 * L) / (staircaseM K k : ℝ) := by
      have hc_int_Ak := cont_inner_unitSq hAk_reg.continuous
      have hm := intervalIntegral.integral_mono_on zero_le_one
        ((cont_inner_unitSq hc_base).intervalIntegrable (μ := volume) 0 1)
        ((by fun_prop : Continuous (fun y : ℝ =>
          6 * δ * (∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) +
            (4 * L) / (staircaseM K k : ℝ))).intervalIntegrable (μ := volume) 0 1)
        hrow
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous (fun y : ℝ =>
          6 * δ * ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y))).intervalIntegrable (μ := volume) 0 1)
        (continuous_const.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hm
      linarith
    have hrew_tr : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, transTerm k (planarPt x y)) =
        ((1 / 4 : ℝ) * (2 : ℝ) ^ k) *
          ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
            ampProd δ Λ k (planarPt x y) *
              |stopDiffWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
                (spin3Ray k).2 * (planarPt x y) 1))| := by
      dsimp [transTerm]
      simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
    rw [hrew_tr]
    have hmul := mul_le_mul_of_nonneg_left hint_y (by positivity : (0 : ℝ) ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ k)
    have h1 : ((1 / 4 : ℝ) * (2 : ℝ) ^ k) *
        (6 * δ * ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) ≤ 3 * δ := by
      have hl1 := ampProd_l1_bound K k
      have hk_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
      have h2k_le : (2 : ℝ) ^ k *
          (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y)) ≤ 2 := by linarith
      calc
        ((1 / 4 : ℝ) * (2 : ℝ) ^ k) * (6 * δ * ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, _)
            = (3 / 2 * δ) * ((2 : ℝ) ^ k * ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, _) := by ring
        _ ≤ (3 / 2 * δ) * 2 := mul_le_mul_of_nonneg_left h2k_le (by positivity)
        _ = 3 * δ := by ring
    have h2 : ((1 / 4 : ℝ) * (2 : ℝ) ^ k) * ((4 * L) / (staircaseM K k : ℝ)) ≤
        (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k := by
      have heq : ((1 / 4 : ℝ) * (2 : ℝ) ^ k) * ((4 * L) / (staircaseM K k : ℝ)) =
          ((2 : ℝ) ^ k * L) / (staircaseM K k : ℝ) := by ring
      rw [heq, div_le_iff₀ (staircaseM_pos K k)]
      have hb := bLip_bound_staircaseM K k
      have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
      have hexp : 64 * (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
        have hp : 64 * (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (3 * k + 16) := by
          have h2k : (2 : ℝ) ^ (2 * k) * 64 ≤ (2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ 16 :=
            mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
          have h3k : (2 : ℝ) ^ (2 * k + 16) ≤ (2 : ℝ) ^ (3 * k + 16) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          rw [pow_add] at h3k
          linarith
        calc
          64 * (2 : ℝ) ^ (2 * k) = (64 * (2 : ℝ) ^ (2 * k)) * 1 := (mul_one _).symm
          _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
              mul_le_mul hp hK1 zero_le_one (by positivity)
      have hlhs : (2 : ℝ) ^ k * L =
          (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k * (64 * (2 : ℝ) ^ (2 * k) * L) := by
        have hc1 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        have hc2 : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
          rw [show 2 * k = k + k by omega, pow_add]
        rw [hc2]
        calc
          (2 : ℝ) ^ k * L = ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) * ((2 : ℝ) ^ k * L) := by
            rw [hc1, one_mul]
          _ = (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k * (64 * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) * L) := by ring
      rw [hlhs]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (mul_le_mul_of_nonneg_right hexp hL0).trans hb
    linarith
  have htr_sum : (∑ k ∈ Finset.range K,
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, transTerm k (planarPt x y)) ≤ 3 / 32 := by
    calc
      (∑ k ∈ Finset.range K, ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, transTerm k (planarPt x y))
          ≤ ∑ k ∈ Finset.range K, (3 * δ + (1 / 64 : ℝ) * (1 / 2 : ℝ) ^ k) :=
            Finset.sum_le_sum htr_each
      _ = (K : ℝ) * (3 * δ) + (1 / 64 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := by
            rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
              Finset.mul_sum]
      _ ≤ 3 / 64 + (1 / 64 : ℝ) * 2 := by
            have hKδ : (K : ℝ) * (3 * δ) ≤ 3 / 64 := by
              dsimp [δ, staircaseDelta]
              rw [show (K : ℝ) * (3 * (1 / (64 * ((K : ℝ) + 3)))) =
                (3 * (K : ℝ)) / (64 * ((K : ℝ) + 3)) by ring]
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith [Nat.cast_nonneg (α := ℝ) K]
            exact add_le_add hKδ
              (mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num))
      _ ≤ 3 / 32 := by norm_num
  have hcomm_tot : (∑ k ∈ Finset.range K, (1 / 32 : ℝ) * (1 / 2 : ℝ) ^ k) ≤ 1 / 16 := by
    rw [← Finset.mul_sum]
    calc
      (1 / 32 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k ≤ (1 / 32 : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
      _ = 1 / 16 := by norm_num
  linarith

/-- Corollary with upper bound `2` matching the Stage B1 reduction budget. -/
theorem spin3_l1_staircaseU_le_two (K : ℕ) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      (|spin3A1 (staircaseU K) (planarPt x y)| +
        |spin3A2 (staircaseU K) (planarPt x y)|)) ≤ 2 :=
  (spin3_l1_staircaseU_le_one K).trans (by norm_num)

/-! ### Section 5: Linear Pairing Lower Bound `≳ m + 1` via 1D `x`-IBP and Haar Shift -/

private lemma sU4_bound_staircaseM (K k : ℕ) :
    (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) *
      (∑ j ∈ Finset.range k,
        unitSqSup (planarDx (planarDx (planarDy (planarDy
          (uTerm (staircaseDelta K) (staircaseLambda K) j)))))) ≤
      (staircaseM K k : ℝ) := by
  apply term_le_staircaseM_div
  have hb1 : 0 ≤ unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) :=
    add_nonneg (unitSqSup_nonneg _) (unitSqSup_nonneg _)
  have hb2 := unitSqXLip_nonneg (ampProd (staircaseDelta K) (staircaseLambda K) k)
  have hb3 := unitSqSup_nonneg (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))
  have hb5 : 0 ≤ (1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
      ∑ j ∈ Finset.range k,
        (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
          unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
            ampProd (staircaseDelta K) (staircaseLambda K) k p)) :=
    mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ =>
      add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _))
  linarith

private lemma sPast_bound_staircaseM (K k : ℕ) :
    (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) *
      ((1 + unitSqSup (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))) *
        ∑ j ∈ Finset.range k,
          (unitSqSup (planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j)) +
            unitSqXLip (fun p => planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) p *
              ampProd (staircaseDelta K) (staircaseLambda K) k p))) ≤
      (staircaseM K k : ℝ) := by
  apply term_le_staircaseM_div
  have hb1 : 0 ≤ unitSqSup (planarDx (ampProd (staircaseDelta K) (staircaseLambda K) k)) +
      unitSqSup (planarDy (ampProd (staircaseDelta K) (staircaseLambda K) k)) :=
    add_nonneg (unitSqSup_nonneg _) (unitSqSup_nonneg _)
  have hb2 := unitSqXLip_nonneg (ampProd (staircaseDelta K) (staircaseLambda K) k)
  have hb3 := unitSqSup_nonneg (jet3Norm (ampProd (staircaseDelta K) (staircaseLambda K) k))
  have hb4 : 0 ≤ ∑ j ∈ Finset.range k,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) j))))) :=
    Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
  linarith

/-- Inductive `L²([0, 1]²)` lower bound `(2 : ℝ)^k * ∫_{[0,1]²} A_k² ≥ 1/4 - 9 k δ_K`. -/
lemma ampProd_l2_lower_bound (K k : ℕ) :
    1 / 4 - 9 * (k : ℝ) * staircaseDelta K ≤
      (2 : ℝ) ^ k *
        ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          (ampProd (staircaseDelta K) (staircaseLambda K) k (planarPt x y)) ^ 2 := by
  induction k with
  | zero =>
      simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero, pow_zero, one_mul, ampProd]
      have hc2 : Continuous (fun p => (boxCutoff2D p) ^ 2) := contDiff_boxCutoff2D.continuous.pow 2
      have hinner_ge : ∀ y ∈ Icc (1 / 4 : ℝ) (3 / 4),
          (1 / 2 : ℝ) ≤ ∫ x in (0 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 := by
        intro y hy
        have hcx := cont_planarPt_x hc2 y
        have hi1 := hcx.intervalIntegrable (μ := volume) 0 (1 / 4)
        have hi2 := hcx.intervalIntegrable (μ := volume) (1 / 4) (3 / 4)
        have hi3 := hcx.intervalIntegrable (μ := volume) (3 / 4) 1
        have hsp1 := (intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3).symm
        have hsp2 := (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
        have hn1 : 0 ≤ ∫ x in (0 : ℝ)..(1 / 4), (boxCutoff2D (planarPt x y)) ^ 2 :=
          intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
        have hn3 : 0 ≤ ∫ x in (3 / 4 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 :=
          intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
        have hmid : (∫ x in (1 / 4 : ℝ)..(3 / 4), (boxCutoff2D (planarPt x y)) ^ 2) = 1 / 2 := by
          have hcgr : (∫ x in (1 / 4 : ℝ)..(3 / 4), (boxCutoff2D (planarPt x y)) ^ 2) =
              ∫ _x in (1 / 4 : ℝ)..(3 / 4), (1 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro x hx
            rw [uIcc_of_le (by norm_num)] at hx
            dsimp only [boxCutoff2D]
            rw [planarPt_apply_zero, planarPt_apply_one,
              boxCutoff1D_eq_one hx.1 hx.2, boxCutoff1D_eq_one hy.1 hy.2]
            norm_num
          rw [hcgr, intervalIntegral.integral_const, smul_eq_mul]; ring
        linarith
      have hcy := cont_inner_unitSq hc2
      have ho1 := hcy.intervalIntegrable (μ := volume) 0 (1 / 4)
      have ho2 := hcy.intervalIntegrable (μ := volume) (1 / 4) (3 / 4)
      have ho3 := hcy.intervalIntegrable (μ := volume) (3 / 4) 1
      have hspo1 := (intervalIntegral.integral_add_adjacent_intervals (ho1.trans ho2) ho3).symm
      have hspo2 := (intervalIntegral.integral_add_adjacent_intervals ho1 ho2).symm
      have hnn_inner : ∀ y : ℝ, 0 ≤ ∫ x in (0 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 :=
        fun y => intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
      have hno1 : 0 ≤ ∫ y in (0 : ℝ)..(1 / 4), ∫ x in (0 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 :=
        intervalIntegral.integral_nonneg (by norm_num) (fun y _ => hnn_inner y)
      have hno3 : 0 ≤ ∫ y in (3 / 4 : ℝ)..1, ∫ x in (0 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 :=
        intervalIntegral.integral_nonneg (by norm_num) (fun y _ => hnn_inner y)
      have hmido : (1 / 4 : ℝ) ≤
          ∫ y in (1 / 4 : ℝ)..(3 / 4), ∫ x in (0 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 := by
        calc
          (1 / 4 : ℝ) = ∫ _y in (1 / 4 : ℝ)..(3 / 4), (1 / 2 : ℝ) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
          _ ≤ ∫ y in (1 / 4 : ℝ)..(3 / 4), ∫ x in (0 : ℝ)..1, (boxCutoff2D (planarPt x y)) ^ 2 :=
            intervalIntegral.integral_mono_on (by norm_num)
              (continuous_const.intervalIntegrable (μ := volume) (1 / 4) (3 / 4)) ho2 hinner_ge
      linarith
  | succ k ih =>
      let δ := staircaseDelta K
      let Λ := staircaseLambda K
      have hδ0 := staircaseDelta_pos K
      have hδ1 := staircaseDelta_le_eighth K
      have hAk_reg := contDiff_ampProd hδ0 hδ1 Λ k
      have hAk1_reg := contDiff_ampProd hδ0 hδ1 Λ (k + 1)
      let L := unitSqXLip (ampProd δ Λ k)
      have hL0 := unitSqXLip_nonneg (ampProd δ Λ k)
      let Nk := xFreqNat k (staircaseM K k)
      have hM_le_N : staircaseM K k ≤ Nk := le_xFreqNat k (staircaseM K k)
      have hNk1 : 1 ≤ Nk := (one_le_staircaseM K k).trans hM_le_N
      have hsq_lip : ∀ y ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
          |(ampProd δ Λ k (planarPt x₁ y)) ^ 2 - (ampProd δ Λ k (planarPt x₂ y)) ^ 2| ≤
            (2 * L) * |x₁ - x₂| := by
        intro y hy x₁ hx₁ x₂ hx₂
        have hfac : (ampProd δ Λ k (planarPt x₁ y)) ^ 2 - (ampProd δ Λ k (planarPt x₂ y)) ^ 2 =
            (ampProd δ Λ k (planarPt x₁ y) + ampProd δ Λ k (planarPt x₂ y)) *
              (ampProd δ Λ k (planarPt x₁ y) - ampProd δ Λ k (planarPt x₂ y)) := by ring
        have hsum_le : |ampProd δ Λ k (planarPt x₁ y) + ampProd δ Λ k (planarPt x₂ y)| ≤ 2 := by
          rw [abs_of_nonneg (add_nonneg (ampProd_nonneg δ Λ k _) (ampProd_nonneg δ Λ k _))]
          linarith [ampProd_le_one δ Λ k (planarPt x₁ y), ampProd_le_one δ Λ k (planarPt x₂ y)]
        have hdiff_le := sub_le_unitSqXLip (hAk_reg.of_le (by norm_cast)) hy hx₁ hx₂
        rw [hfac, abs_mul]
        calc
          |ampProd δ Λ k (planarPt x₁ y) + ampProd δ Λ k (planarPt x₂ y)| *
              |ampProd δ Λ k (planarPt x₁ y) - ampProd δ Λ k (planarPt x₂ y)|
              ≤ 2 * (L * |x₁ - x₂|) :=
                mul_le_mul hsum_le hdiff_le (abs_nonneg _) zero_le_two
          _ = (2 * L) * |x₁ - x₂| := by ring
      have hrow : ∀ y ∈ Icc (0 : ℝ) 1,
          (1 / 2 - 2 * δ) * (∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) -
            (4 * L) / (staircaseM K k : ℝ) ≤
            ∫ x in (0 : ℝ)..1, (ampProd δ Λ (k + 1) (planarPt x y)) ^ 2 := by
        intro y hy
        have hrew : ∀ x : ℝ, (ampProd δ Λ (k + 1) (planarPt x y)) ^ 2 =
            (ampProd δ Λ k (planarPt x y)) ^ 2 *
              (etaWave δ ((Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y))) ^ 2 := by
          intro x
          simp only [ampProd, planarPt_apply_zero, planarPt_apply_one]
          have harg : Λ k * ((spin3Ray k).1 * x + (spin3Ray k).2 * y) =
              (Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y) := by ring
          rw [harg]; ring
        simp_rw [hrew]
        have hper := periodic_phase_sign_mean_bound_1d (N := Nk)
          (F := fun x => (ampProd δ Λ k (planarPt x y)) ^ 2)
          (q := fun t => (etaWave δ t) ^ 2)
          (L := 2 * L) (B := 1) (a := Λ k * (spin3Ray k).1) (φ := Λ k * (spin3Ray k).2 * y)
          hNk1 (by positivity) zero_le_one (xFreqNat_ray_fst k (staircaseM K k))
          (cont_planarPt_x (hAk_reg.continuous.pow 2) y)
          ((contDiff_etaWave hδ0 hδ1).continuous.pow 2)
          (hsq_lip y hy)
          (fun t => by rw [etaWave_periodic])
          (fun t => by
            rw [abs_of_nonneg (sq_nonneg _)]
            nlinarith [etaWave_nonneg δ t, etaWave_le_one δ t])
        have hFk_nn : 0 ≤ ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2 :=
          intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
        have hμ_ge : (1 / 2 - 2 * δ) * (∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) ≤
            (∫ t in (0 : ℝ)..1, (etaWave δ t) ^ 2) *
              ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2 :=
          mul_le_mul_of_nonneg_right (integral_etaWave_sq_ge hδ0 hδ1) hFk_nn
        have herr_le : (2 * 1 * (2 * L)) / (Nk : ℝ) ≤ (4 * L) / (staircaseM K k : ℝ) := by
          rw [show (2 : ℝ) * 1 * (2 * L) = 4 * L by ring]
          exact div_le_div_of_nonneg_left (by positivity) (staircaseM_pos K k)
            (by exact_mod_cast hM_le_N)
        linarith [(abs_le.mp hper).1]
      have hAk_sq_cont : Continuous (fun p => (ampProd δ Λ k p) ^ 2) := hAk_reg.continuous.pow 2
      have hAk1_sq_cont : Continuous (fun p => (ampProd δ Λ (k + 1) p) ^ 2) :=
        hAk1_reg.continuous.pow 2
      have hc_int_sq := cont_inner_unitSq hAk_sq_cont
      have hc_int_sq1 := cont_inner_unitSq hAk1_sq_cont
      have hint : (1 / 2 - 2 * δ) *
          (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) -
          (4 * L) / (staircaseM K k : ℝ) ≤
          ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ (k + 1) (planarPt x y)) ^ 2 := by
        have hm := intervalIntegral.integral_mono_on zero_le_one
          ((by fun_prop : Continuous (fun y : ℝ =>
            (1 / 2 - 2 * δ) * (∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) -
              (4 * L) / (staircaseM K k : ℝ))).intervalIntegrable (μ := volume) 0 1)
          (hc_int_sq1.intervalIntegrable (μ := volume) 0 1)
          hrow
        rw [intervalIntegral.integral_sub
          ((by fun_prop : Continuous (fun y : ℝ =>
            (1 / 2 - 2 * δ) * ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2)).intervalIntegrable
            (μ := volume) 0 1)
          (continuous_const.intervalIntegrable (μ := volume) 0 1),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hm
        linarith
      have hJk_le_Ik : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) ≤
          ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, ampProd δ Λ k (planarPt x y) :=
        unitSq_integral_mono hAk_sq_cont hAk_reg.continuous
          (fun x _ y _ => by
            have h0 := ampProd_nonneg δ Λ k (planarPt x y)
            have h1 := ampProd_le_one δ Λ k (planarPt x y)
            nlinarith)
      have h2k_Jk_le_two : (2 : ℝ) ^ k *
          (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) ≤ 2 := by
        have hl1 := ampProd_l1_bound K k
        have hnn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
        have hm := mul_le_mul_of_nonneg_left hJk_le_Ik (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
        linarith
      have herr_δ : (2 : ℝ) ^ (k + 1) * ((4 * L) / (staircaseM K k : ℝ)) ≤ δ := by
        dsimp [δ, staircaseDelta]
        rw [mul_div_assoc', div_le_div_iff₀ (staircaseM_pos K k) (by positivity)]
        have hb := bLip_bound_staircaseM K k
        have hexp : (2 : ℝ) ^ (k + 1) * (4 * L) * (64 * ((K : ℝ) + 3)) ≤
            (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * L := by
          have hp : 512 * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k + 16) := by
            have h1 : (2 : ℝ) ^ k * 512 ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ 16 :=
              mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
            have h2 : (2 : ℝ) ^ (k + 16) ≤ (2 : ℝ) ^ (3 * k + 16) :=
              pow_le_pow_right₀ (by norm_num) (by omega)
            rw [pow_add] at h2
            linarith
          have hrew : (2 : ℝ) ^ (k + 1) * (4 * L) * (64 * ((K : ℝ) + 3)) =
              (512 * (2 : ℝ) ^ k) * (((K : ℝ) + 3) * L) := by rw [pow_succ]; ring
          have hrew2 : (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * L =
              (2 : ℝ) ^ (3 * k + 16) * (((K : ℝ) + 3) * L) := by ring
          rw [hrew, hrew2]
          exact mul_le_mul_of_nonneg_right hp
            (mul_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) K]) hL0)
        linarith
      have hmul := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (k + 1))
      have hrew_mul : (2 : ℝ) ^ (k + 1) *
          ((1 / 2 - 2 * δ) *
            (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) -
            (4 * L) / (staircaseM K k : ℝ)) =
          (2 : ℝ) ^ k *
            (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) -
          4 * δ * ((2 : ℝ) ^ k *
            ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) -
          (2 : ℝ) ^ (k + 1) * ((4 * L) / (staircaseM K k : ℝ)) := by
        rw [pow_succ]; ring
      rw [hrew_mul] at hmul
      have h4δ : 4 * δ * ((2 : ℝ) ^ k *
          ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (ampProd δ Λ k (planarPt x y)) ^ 2) ≤ 8 * δ := by
        nlinarith [hδ0]
      push_cast
      dsimp [δ] at hmul h4δ herr_δ
      linarith

lemma ampProd_l2_ge_sixteenth {K k : ℕ} (hk : k ≤ K) :
    (1 / 16 : ℝ) ≤
      (2 : ℝ) ^ k *
        ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          (ampProd (staircaseDelta K) (staircaseLambda K) k (planarPt x y)) ^ 2 := by
  have hlb := ampProd_l2_lower_bound K k
  have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk
  have h9δ : 9 * (k : ℝ) * staircaseDelta K ≤ 9 / 64 := by
    unfold staircaseDelta
    rw [show 9 * (k : ℝ) * (1 / (64 * ((K : ℝ) + 3))) =
      (9 * (k : ℝ)) / (64 * ((K : ℝ) + 3)) by ring]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith [Nat.cast_nonneg (α := ℝ) K]
  linarith

/-- Bilinear pairing matrix entry `I_{j, k} = ∫_{[0,1]²} hTerm j · ∂_x² ∂_y² (uTerm k)`. -/
def pairTerm (K j k : ℕ) : ℝ :=
  ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    hTerm (staircaseDelta K) (staircaseLambda K) j (planarPt x y) *
      planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) k)))) (planarPt x y)

private lemma sum_square_trichotomy (K : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K, f j k) =
      (∑ k ∈ Finset.range K, f k k) +
      (∑ j ∈ Finset.range K, ∑ k ∈ Finset.range j, f j k) +
      (∑ k ∈ Finset.range K, ∑ j ∈ Finset.range k, f j k) := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp_rw [Finset.sum_range_succ (n := K)]
      rw [Finset.sum_add_distrib, ih]
      ring

private lemma cont_uTerm_dxxyy (K k : ℕ) :
    Continuous (planarDx (planarDx (planarDy (planarDy
      (uTerm (staircaseDelta K) (staircaseLambda K) k))))) := by
  have hr := contDiff_uTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K) (staircaseLambda K) k
  exact (contDiff_planarDx_b1 (r := 0) (contDiff_planarDx_b1 (r := 1)
    (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) hr)))).continuous

private lemma pairing_eq_double_sum (K : ℕ) :
    (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
      staircaseH K (planarPt x y) *
        planarDx (planarDx (planarDy (planarDy (staircaseU K)))) (planarPt x y)) =
      ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K, pairTerm K j k := by
  have hδ0 := staircaseDelta_pos K
  have hδ1 := staircaseDelta_le_eighth K
  have hu_reg := fun k => contDiff_uTerm hδ0 hδ1 (staircaseLambda K) k
  have hh_reg := fun j => contDiff_hTerm hδ0 hδ1 (staircaseLambda K) j
  have hU_dxxyy : ∀ p : Euclidean 2,
      planarDx (planarDx (planarDy (planarDy (staircaseU K)))) p =
        ∑ k ∈ Finset.range K,
          planarDx (planarDx (planarDy (planarDy
            (uTerm (staircaseDelta K) (staircaseLambda K) k)))) p := by
    intro p
    unfold staircaseU
    have hdy1 : planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q) =
        fun q => ∑ k ∈ Finset.range K, planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k) q :=
      funext fun q => planarDy_finset_sum _ (fun k _ => diff_of_c1 (r := 3) (hu_reg k) q)
    have hdyy : planarDy (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q)) =
        fun q => ∑ k ∈ Finset.range K, planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k)) q := by
      rw [hdy1]
      exact funext fun q => planarDy_finset_sum _
        (fun k _ => diff_of_c1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hu_reg k)) q)
    have hdxyy : planarDx (planarDy (planarDy (fun q => ∑ k ∈ Finset.range K, uTerm (staircaseDelta K) (staircaseLambda K) k q))) =
        fun q => ∑ k ∈ Finset.range K, planarDx (planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k))) q := by
      rw [hdyy]
      exact funext fun q => planarDx_finset_sum _
        (fun k _ => diff_of_c1 (r := 1) (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hu_reg k))) q)
    rw [hdxyy]
    exact planarDx_finset_sum _
      (fun k _ => diff_of_c1 (r := 0) (contDiff_planarDx_b1 (r := 1)
        (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3) (hu_reg k)))) p)
  have hprod : ∀ p : Euclidean 2,
      staircaseH K p * planarDx (planarDx (planarDy (planarDy (staircaseU K)))) p =
        ∑ j ∈ Finset.range K, ∑ k ∈ Finset.range K,
          (hTerm (staircaseDelta K) (staircaseLambda K) j p *
            planarDx (planarDx (planarDy (planarDy
              (uTerm (staircaseDelta K) (staircaseLambda K) k)))) p) := by
    intro p
    rw [hU_dxxyy p]
    unfold staircaseH
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  simp_rw [hprod]
  rw [unitSq_integral_finset_sum (Finset.range K)
    (F := fun j p => ∑ k ∈ Finset.range K,
      hTerm (staircaseDelta K) (staircaseLambda K) j p *
        planarDx (planarDx (planarDy (planarDy
          (uTerm (staircaseDelta K) (staircaseLambda K) k)))) p)
    (fun j _ => continuous_finsetSum _ fun k _ =>
      (hh_reg j).continuous.mul (cont_uTerm_dxxyy K k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [unitSq_integral_finset_sum (Finset.range K)
    (F := fun k p =>
      hTerm (staircaseDelta K) (staircaseLambda K) j p *
        planarDx (planarDx (planarDy (planarDy
          (uTerm (staircaseDelta K) (staircaseLambda K) k)))) p)
    (fun k _ => (hh_reg j).continuous.mul (cont_uTerm_dxxyy K k))]
  rfl

private lemma hasDerivAt_planarPt_x_s {f : Euclidean 2 → ℝ}
    (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun s : ℝ => f (planarPt s y)) (planarDx f (planarPt x y)) x := by
  have hpt : HasDerivAt (fun s : ℝ => planarPt s y) (coordinateVector 2 0) x := by
    have hrew : (fun s : ℝ => planarPt s y) =
        fun s : ℝ => y • coordinateVector 2 1 + s • coordinateVector 2 0 := by
      funext s; ext i; fin_cases i <;>
        simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply, add_comm]
    rw [hrew]
    simpa [one_smul] using
      ((hasDerivAt_id x).smul_const (coordinateVector 2 0)).const_add (y • coordinateVector 2 1)
  unfold planarDx
  rw [coordinatePartial_eq_fderiv (hf (planarPt x y))]
  exact (hf (planarPt x y)).hasFDerivAt.comp_hasDerivAt x hpt

private lemma pairTerm_ibp_x (K j k : ℕ) :
    pairTerm K j k =
      - ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          planarDx (hTerm (staircaseDelta K) (staircaseLambda K) j) (planarPt x y) *
            planarDx (planarDy (planarDy
              (uTerm (staircaseDelta K) (staircaseLambda K) k))) (planarPt x y) := by
  unfold pairTerm
  have hδ0 := staircaseDelta_pos K
  have hδ1 := staircaseDelta_le_eighth K
  let hj_fn := hTerm (staircaseDelta K) (staircaseLambda K) j
  let uk_dxyy := planarDx (planarDy (planarDy (uTerm (staircaseDelta K) (staircaseLambda K) k)))
  have hhj_reg := contDiff_hTerm hδ0 hδ1 (staircaseLambda K) j
  have huk_reg := contDiff_planarDx_b1 (r := 1) (contDiff_planarDy_b1 (r := 2)
    (contDiff_planarDy_b1 (r := 3) (contDiff_uTerm hδ0 hδ1 (staircaseLambda K) k)))
  have hinner : ∀ y : ℝ,
      (∫ x in (0 : ℝ)..1, hj_fn (planarPt x y) * planarDx uk_dxyy (planarPt x y)) =
        - ∫ x in (0 : ℝ)..1, planarDx hj_fn (planarPt x y) * uk_dxyy (planarPt x y) := by
    intro y
    have hprod : ∀ x ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun s => hj_fn (planarPt s y) * uk_dxyy (planarPt s y))
          (planarDx hj_fn (planarPt x y) * uk_dxyy (planarPt x y) +
            hj_fn (planarPt x y) * planarDx uk_dxyy (planarPt x y)) x :=
      fun x _ => (hasDerivAt_planarPt_x_s (diff_of_c1 (r := 3) hhj_reg) x y).mul
        (hasDerivAt_planarPt_x_s (diff_of_c1 (r := 0) huk_reg) x y)
    have hi1 : IntervalIntegrable
        (fun x => planarDx hj_fn (planarPt x y) * uk_dxyy (planarPt x y)) volume 0 1 :=
      (cont_planarPt_x ((contDiff_planarDx_b1 (r := 3) hhj_reg).continuous.mul huk_reg.continuous) y).intervalIntegrable
        (μ := volume) 0 1
    have hi2 : IntervalIntegrable
        (fun x => hj_fn (planarPt x y) * planarDx uk_dxyy (planarPt x y)) volume 0 1 :=
      (cont_planarPt_x (hhj_reg.continuous.mul (contDiff_planarDx_b1 (r := 0) huk_reg).continuous) y).intervalIntegrable
        (μ := volume) 0 1
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod (hi1.add hi2)
    have hz0 : hj_fn (planarPt 0 y) = 0 :=
      hTerm_zero_outside _ _ j (Or.inl (by simp))
    have hz1 : hj_fn (planarPt 1 y) = 0 :=
      hTerm_zero_outside _ _ j (Or.inr (Or.inl (by simp; norm_num)))
    rw [intervalIntegral.integral_add hi1 hi2, hz0, hz1, zero_mul, zero_mul, sub_self] at hftc
    linarith
  change (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
    hj_fn (planarPt x y) * planarDx uk_dxyy (planarPt x y)) = _
  simp_rw [hinner, intervalIntegral.integral_neg]
  rfl

private lemma future_sum_bound (K : ℕ) :
    |∑ j ∈ Finset.range K, ∑ k ∈ Finset.range j, pairTerm K j k| ≤ 1 / 32768 := by
  have hj_bound : ∀ j ∈ Finset.range K,
      |∑ k ∈ Finset.range j, pairTerm K j k| ≤ (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ j := by
    intro j _
    let sU4 := ∑ k ∈ Finset.range j,
      unitSqSup (planarDx (planarDx (planarDy (planarDy
        (uTerm (staircaseDelta K) (staircaseLambda K) k)))))
    have hsU4_nn : 0 ≤ sU4 := Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
    have hk_bound : ∀ k ∈ Finset.range j,
        |pairTerm K j k| ≤ sU4 / (64 * (staircaseM K j : ℝ)) := by
      intro k hk
      unfold pairTerm
      have hc_prod : Continuous (fun p =>
          hTerm (staircaseDelta K) (staircaseLambda K) j p *
            planarDx (planarDx (planarDy (planarDy
              (uTerm (staircaseDelta K) (staircaseLambda K) k)))) p) :=
        (contDiff_hTerm (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
          (staircaseLambda K) j).continuous.mul (cont_uTerm_dxxyy K k)
      have hpt : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
          |hTerm (staircaseDelta K) (staircaseLambda K) j (planarPt x y) *
            planarDx (planarDx (planarDy (planarDy
              (uTerm (staircaseDelta K) (staircaseLambda K) k)))) (planarPt x y)| ≤
            sU4 / (64 * (staircaseM K j : ℝ)) := by
        intro x hx y hy
        set p := planarPt x y
        have hh_abs : |hTerm (staircaseDelta K) (staircaseLambda K) j p| ≤
            1 / (64 * (staircaseM K j : ℝ)) := by
          unfold hTerm
          have hA0 := ampProd_nonneg (staircaseDelta K) (staircaseLambda K) j p
          have hA1 := ampProd_le_one (staircaseDelta K) (staircaseLambda K) j p
          have hτ := abs_tauWave_le (staircaseDelta_pos K) (staircaseDelta_le_eighth K)
            (staircaseLambda K j * ((spin3Ray j).1 * p 0 + (spin3Ray j).2 * p 1))
          have hΛ_pos := staircaseLambda_pos K j
          rw [abs_mul, abs_mul, abs_mul,
            show |-(1 / 8 : ℝ)| = 1 / 8 by norm_num,
            abs_of_pos (show 0 < 1 / staircaseLambda K j by positivity),
            abs_of_nonneg hA0]
          calc
            (1 / 8 : ℝ) * (1 / staircaseLambda K j) *
                ampProd (staircaseDelta K) (staircaseLambda K) j p * |tauWave _ _|
                ≤ (1 / 8 : ℝ) * (1 / staircaseLambda K j) * 1 * (1 / 4) := by gcongr
            _ = 1 / (64 * (staircaseM K j : ℝ)) := by dsimp [staircaseLambda]; ring
        have hu_abs : |planarDx (planarDx (planarDy (planarDy
            (uTerm (staircaseDelta K) (staircaseLambda K) k)))) p| ≤ sU4 := by
          have h1 := abs_le_unitSqSup (cont_uTerm_dxxyy K k) hx hy
          have h2 : unitSqSup (planarDx (planarDx (planarDy (planarDy
              (uTerm (staircaseDelta K) (staircaseLambda K) k))))) ≤ sU4 :=
            Finset.single_le_sum
              (f := fun m => unitSqSup (planarDx (planarDx (planarDy (planarDy
                (uTerm (staircaseDelta K) (staircaseLambda K) m))))))
              (fun _ _ => unitSqSup_nonneg _) hk
          exact h1.trans h2
        rw [abs_mul]
        calc
          |hTerm _ _ j p| * |planarDx _ p|
              ≤ (1 / (64 * (staircaseM K j : ℝ))) * sU4 :=
                mul_le_mul hh_abs hu_abs (abs_nonneg _)
                  (by have := staircaseM_pos K j; positivity)
          _ = sU4 / (64 * (staircaseM K j : ℝ)) := by ring
      calc
        |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, _|
            ≤ ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |_ * _| := unitSq_integral_abs_le hc_prod
        _ ≤ ∫ _y in (0 : ℝ)..1, ∫ _x in (0 : ℝ)..1, (sU4 / (64 * (staircaseM K j : ℝ))) :=
            unitSq_integral_mono hc_prod.abs continuous_const hpt
        _ = sU4 / (64 * (staircaseM K j : ℝ)) := unitSq_integral_const _
    have hsum_j : |∑ k ∈ Finset.range j, pairTerm K j k| ≤
        ((j : ℝ) * sU4) / (64 * (staircaseM K j : ℝ)) := by
      calc
        |∑ k ∈ Finset.range j, pairTerm K j k|
            ≤ ∑ k ∈ Finset.range j, |pairTerm K j k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k ∈ Finset.range j, (sU4 / (64 * (staircaseM K j : ℝ))) :=
            Finset.sum_le_sum hk_bound
        _ = ((j : ℝ) * sU4) / (64 * (staircaseM K j : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    refine hsum_j.trans ?_
    have hM_pos := staircaseM_pos K j
    rw [div_le_iff₀ (by positivity)]
    have hj_pow : (j : ℝ) ≤ (2 : ℝ) ^ j := by
      exact_mod_cast le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))
    have hsM := sU4_bound_staircaseM K j
    have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
    have hexp : 1024 * (2 : ℝ) ^ (2 * j) ≤ (2 : ℝ) ^ (3 * j + 16) * ((K : ℝ) + 3) := by
      have hp : 1024 * (2 : ℝ) ^ (2 * j) ≤ (2 : ℝ) ^ (3 * j + 16) := by
        have h1 : (2 : ℝ) ^ (2 * j) * 1024 ≤ (2 : ℝ) ^ (2 * j) * (2 : ℝ) ^ 16 :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        have h2 : (2 : ℝ) ^ (2 * j + 16) ≤ (2 : ℝ) ^ (3 * j + 16) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        rw [pow_add] at h2
        linarith
      calc
        1024 * (2 : ℝ) ^ (2 * j) = (1024 * (2 : ℝ) ^ (2 * j)) * 1 := (mul_one _).symm
        _ ≤ (2 : ℝ) ^ (3 * j + 16) * ((K : ℝ) + 3) :=
            mul_le_mul hp hK1 zero_le_one (by positivity)
    calc
      (j : ℝ) * sU4
          ≤ (2 : ℝ) ^ j * sU4 := mul_le_mul_of_nonneg_right hj_pow hsU4_nn
      _ = (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ j * (64 * (1024 * (2 : ℝ) ^ (2 * j) * sU4)) := by
            have hc1 : (2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
            have hc2 : (2 : ℝ) ^ (2 * j) = (2 : ℝ) ^ j * (2 : ℝ) ^ j := by
              rw [show 2 * j = j + j by omega, pow_add]
            rw [hc2]
            calc
              (2 : ℝ) ^ j * sU4 = ((2 : ℝ) ^ j * (1 / 2 : ℝ) ^ j) * ((2 : ℝ) ^ j * sU4) := by
                rw [hc1, one_mul]
              _ = (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ j *
                    (64 * (1024 * ((2 : ℝ) ^ j * (2 : ℝ) ^ j) * sU4)) := by ring
      _ ≤ (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ j * (64 * (staircaseM K j : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact (mul_le_mul_of_nonneg_right hexp hsU4_nn).trans hsM
  calc
    |∑ j ∈ Finset.range K, ∑ k ∈ Finset.range j, pairTerm K j k|
        ≤ ∑ j ∈ Finset.range K, |∑ k ∈ Finset.range j, pairTerm K j k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range K, (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ j := Finset.sum_le_sum hj_bound
    _ = (1 / 65536 : ℝ) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 65536 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
    _ = 1 / 32768 := by norm_num

private lemma past_sum_bound (K : ℕ) :
    |∑ k ∈ Finset.range K, ∑ j ∈ Finset.range k, pairTerm K j k| ≤ 1 / 32768 := by
  have hk_bound : ∀ k ∈ Finset.range K,
      |∑ j ∈ Finset.range k, pairTerm K j k| ≤ (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k := by
    intro k _
    let δ := staircaseDelta K
    let Λ := staircaseLambda K
    have hδ0 := staircaseDelta_pos K
    have hδ1 := staircaseDelta_le_eighth K
    let Ak := ampProd δ Λ k
    have hAk_reg := contDiff_ampProd hδ0 hδ1 Λ k
    let bJet3 := unitSqSup (jet3Norm Ak)
    let sPast := ∑ j ∈ Finset.range k,
      (unitSqSup (planarDx (hTerm δ Λ j)) +
        unitSqXLip (fun p => planarDx (hTerm δ Λ j) p * Ak p))
    have hbJet3_nn : 0 ≤ bJet3 := unitSqSup_nonneg _
    have hsPast_nn : 0 ≤ sPast :=
      Finset.sum_nonneg fun _ _ => add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _)
    let Umain : Euclidean 2 → ℝ := fun p =>
      (1 / 4 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 * (spin3Ray k).2 ^ 2) * Ak p *
        tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
    let Udxyy : Euclidean 2 → ℝ := planarDx (planarDy (planarDy (uTerm δ Λ k)))
    have hc_Umain : Continuous Umain := by
      dsimp [Umain]
      have hlin : Continuous (fun p : Euclidean 2 =>
          Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) :=
        continuous_const.mul
          ((continuous_const.mul (EuclideanSpace.proj (0 : Fin 2)).continuous).add
            (continuous_const.mul (EuclideanSpace.proj (1 : Fin 2)).continuous))
      exact (continuous_const.mul hAk_reg.continuous).mul
        ((contDiff_tauDerivWave hδ0 hδ1).continuous.comp hlin)
    have hc_Udxyy : Continuous Udxyy :=
      (contDiff_planarDx_b1 (r := 1) (contDiff_planarDy_b1 (r := 2)
        (contDiff_planarDy_b1 (r := 3) (contDiff_uTerm hδ0 hδ1 Λ k)))).continuous
    have hj_each : ∀ j ∈ Finset.range k,
        |pairTerm K j k| ≤
          ((2 : ℝ) ^ k * ((1 + bJet3) * sPast)) / (8 * (staircaseM K k : ℝ)) := by
      intro j hj
      rw [pairTerm_ibp_x K j k, abs_neg]
      let Hx := planarDx (hTerm δ Λ j)
      have hHx_reg : ContDiff ℝ (3 : ℕ) Hx :=
        contDiff_planarDx_b1 (r := 3) (contDiff_hTerm hδ0 hδ1 Λ j)
      have hG_reg : ContDiff ℝ (1 : ℕ) (fun p => Hx p * Ak p) :=
        (hHx_reg.of_le (by norm_cast)).mul (hAk_reg.of_le (by norm_cast))
      have hsplit_int :
          (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, Hx (planarPt x y) * Udxyy (planarPt x y)) =
            (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, Hx (planarPt x y) * Umain (planarPt x y)) +
            (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
              Hx (planarPt x y) * (Udxyy (planarPt x y) - Umain (planarPt x y))) := by
        have hpt_eq : ∀ p : Euclidean 2,
            Hx p * Udxyy p = Hx p * Umain p + Hx p * (Udxyy p - Umain p) := fun _ => by ring
        simp_rw [hpt_eq]
        exact unitSq_integral_add (F := fun p => Hx p * Umain p)
          (G := fun p => Hx p * (Udxyy p - Umain p))
          (hHx_reg.continuous.mul hc_Umain)
          (hHx_reg.continuous.mul (hc_Udxyy.sub hc_Umain))
      rw [hsplit_int]
      have hj_in_sPast : unitSqSup Hx + unitSqXLip (fun p => Hx p * Ak p) ≤ sPast :=
        Finset.single_le_sum
          (f := fun m => unitSqSup (planarDx (hTerm δ Λ m)) +
            unitSqXLip (fun p => planarDx (hTerm δ Λ m) p * Ak p))
          (fun _ _ => add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _)) hj
      have hHx_le_sPast : unitSqSup Hx ≤ sPast :=
        by linarith [unitSqXLip_nonneg (fun p => Hx p * Ak p)]
      have hLip_le_sPast : unitSqXLip (fun p => Hx p * Ak p) ≤ sPast :=
        by linarith [unitSqSup_nonneg Hx]
      -- Bound 1: Oscillatory part via `antiperiodic_phase_sign_bound_1d`
      have hosc : |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          Hx (planarPt x y) * Umain (planarPt x y)| ≤
          ((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ)) := by
        let Nk := xFreqNat k (staircaseM K k)
        have hM_le_N : staircaseM K k ≤ Nk := le_xFreqNat k (staircaseM K k)
        have hNk1 : 1 ≤ Nk := (one_le_staircaseM K k).trans hM_le_N
        have hrow : ∀ y ∈ Icc (0 : ℝ) 1,
            |∫ x in (0 : ℝ)..1, Hx (planarPt x y) * Umain (planarPt x y)| ≤
              ((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ)) := by
          intro y hy
          have hrew : ∀ x : ℝ, Hx (planarPt x y) * Umain (planarPt x y) =
              ((1 / 4 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 * (spin3Ray k).2 ^ 2)) *
                ((Hx (planarPt x y) * Ak (planarPt x y)) *
                  tauDerivWave δ ((Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y))) := by
            intro x
            dsimp [Umain]
            simp only [planarPt_apply_zero, planarPt_apply_one]
            have harg : Λ k * ((spin3Ray k).1 * x + (spin3Ray k).2 * y) =
                (Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y) := by ring
            rw [harg]; ring
          simp_rw [hrew]
          rw [intervalIntegral.integral_const_mul, abs_mul]
          have hray_le : |(1 / 4 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 * (spin3Ray k).2 ^ 2)| ≤
              (1 / 4 : ℝ) * (2 : ℝ) ^ k := by
            rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
              abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ k), abs_mul, abs_pow]
            have h1 := abs_spin3Ray_fst_le_one k
            have h2 : |(spin3Ray k).2| ^ 2 ≤ 1 := by
              have hb := abs_spin3Ray_snd_le_one k
              nlinarith [abs_nonneg (spin3Ray k).2]
            have hprod1 : |(spin3Ray k).1| * |(spin3Ray k).2| ^ 2 ≤ 1 := by
              nlinarith [abs_nonneg (spin3Ray k).1, sq_nonneg |(spin3Ray k).2|]
            calc
              (1 / 4 : ℝ) * (2 : ℝ) ^ k * (|(spin3Ray k).1| * |(spin3Ray k).2| ^ 2)
                  ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ k * 1 :=
                    mul_le_mul_of_nonneg_left hprod1 (by positivity)
              _ = (1 / 4 : ℝ) * (2 : ℝ) ^ k := mul_one _
          have hanti := antiperiodic_phase_sign_bound_1d (N := Nk)
            (F := fun x => Hx (planarPt x y) * Ak (planarPt x y))
            (g := tauDerivWave δ)
            (L := unitSqXLip (fun p => Hx p * Ak p)) (B := 1)
            (a := Λ k * (spin3Ray k).1) (φ := Λ k * (spin3Ray k).2 * y)
            hNk1 (unitSqXLip_nonneg _) zero_le_one (xFreqNat_ray_fst k (staircaseM K k))
            (cont_planarPt_x hG_reg.continuous y)
            (contDiff_tauDerivWave hδ0 hδ1).continuous
            (fun x₁ hx₁ x₂ hx₂ => sub_le_unitSqXLip hG_reg hy hx₁ hx₂)
            (tauDerivWave_antiperiodic hδ0 hδ1)
            (abs_tauDerivWave_le_one hδ0 hδ1)
          have hanti' : |∫ x in (0 : ℝ)..1,
              (Hx (planarPt x y) * Ak (planarPt x y)) *
                tauDerivWave δ ((Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y))| ≤
              sPast / (4 * (staircaseM K k : ℝ)) := by
            refine hanti.trans ?_
            rw [mul_one]
            exact div_le_div₀ hsPast_nn hLip_le_sPast
              (by have := staircaseM_pos K k; positivity)
              (by exact_mod_cast Nat.mul_le_mul_left 4 hM_le_N)
          calc
            |(1 / 4 : ℝ) * (2 : ℝ) ^ k * _| * |∫ x in (0 : ℝ)..1, _|
                ≤ ((1 / 4 : ℝ) * (2 : ℝ) ^ k) * (sPast / (4 * (staircaseM K k : ℝ))) :=
                  mul_le_mul hray_le hanti' (abs_nonneg _) (by positivity)
            _ = ((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ)) := by ring
        calc
          |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, Hx (planarPt x y) * Umain (planarPt x y)|
              ≤ ∫ y in (0 : ℝ)..1, |∫ x in (0 : ℝ)..1, Hx (planarPt x y) * Umain (planarPt x y)| := by
                simpa only [Real.norm_eq_abs] using
                  intervalIntegral.norm_integral_le_integral_norm
                    (f := fun y => ∫ x in (0 : ℝ)..1, Hx (planarPt x y) * Umain (planarPt x y))
                    zero_le_one
          _ ≤ ∫ _y in (0 : ℝ)..1, (((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ))) :=
              intervalIntegral.integral_mono_on zero_le_one
                ((cont_inner_unitSq (hHx_reg.continuous.mul hc_Umain)).abs.intervalIntegrable
                  (μ := volume) 0 1)
                (continuous_const.intervalIntegrable (μ := volume) 0 1)
                hrow
          _ = ((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ)) := by
              rw [intervalIntegral.integral_const, smul_eq_mul]; ring
      -- Bound 2: Commutator part
      have hcomm_b : |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          Hx (planarPt x y) * (Udxyy (planarPt x y) - Umain (planarPt x y))| ≤
          ((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ)) := by
        have hc_err := hHx_reg.continuous.mul (hc_Udxyy.sub hc_Umain)
        have hpt : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
            |Hx (planarPt x y) * (Udxyy (planarPt x y) - Umain (planarPt x y))| ≤
              ((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ)) := by
          intro x hx y hy
          set p := planarPt x y
          have hHx_b : |Hx p| ≤ sPast :=
            (abs_le_unitSqSup hHx_reg.continuous hx hy).trans hHx_le_sPast
          have hAk3 : ContDiff ℝ (3 : ℕ) Ak := hAk_reg.of_le (by norm_cast)
          have hj_b : jet3Norm Ak p ≤ bJet3 :=
            (le_abs_self _).trans (abs_le_unitSqSup (continuous_jet3Norm hAk3) hx hy)
          have hc_u := (uTerm_third_commutators K k p).1
          have hE_nn : 0 ≤ (2 : ℝ) ^ k / (16 * Λ k) := by
            have := staircaseLambda_pos K k; positivity
          have hu_b : |Udxyy p - Umain p| ≤
              (3 * bJet3 * (2 : ℝ) ^ k) / (32 * (staircaseM K k : ℝ)) := by
            calc
              |Udxyy p - Umain p| ≤ 3 * jet3Norm Ak p * ((2 : ℝ) ^ k / (16 * Λ k)) := hc_u
              _ ≤ 3 * bJet3 * ((2 : ℝ) ^ k / (16 * Λ k)) :=
                  mul_le_mul_of_nonneg_right (by linarith) hE_nn
              _ = (3 * bJet3 * (2 : ℝ) ^ k) / (32 * (staircaseM K k : ℝ)) := by
                  dsimp [Λ, staircaseLambda]; ring
          rw [abs_mul]
          calc
            |Hx p| * |Udxyy p - Umain p|
                ≤ sPast * ((3 * bJet3 * (2 : ℝ) ^ k) / (32 * (staircaseM K k : ℝ))) :=
                  mul_le_mul hHx_b hu_b (abs_nonneg _)
                    (by have := staircaseM_pos K k; positivity)
            _ ≤ ((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ)) := by
                  rw [mul_div_assoc', div_le_div_iff₀
                    (by have := staircaseM_pos K k; positivity)
                    (by have := staircaseM_pos K k; positivity)]
                  have hnn : 0 ≤ (2 : ℝ) ^ k * (bJet3 * sPast) * (staircaseM K k : ℝ) := by
                    have := staircaseM_pos K k; positivity
                  linarith
        calc
          |∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, _|
              ≤ ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, |_ * _| := unitSq_integral_abs_le hc_err
          _ ≤ ∫ _y in (0 : ℝ)..1, ∫ _x in (0 : ℝ)..1,
                (((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ))) :=
              unitSq_integral_mono hc_err.abs continuous_const hpt
          _ = ((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ)) :=
              unitSq_integral_const _
      have hcomb : ((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ)) +
          ((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ)) ≤
          ((2 : ℝ) ^ k * ((1 + bJet3) * sPast)) / (8 * (staircaseM K k : ℝ)) := by
        have h1 : ((2 : ℝ) ^ k * sPast) / (16 * (staircaseM K k : ℝ)) ≤
            ((2 : ℝ) ^ k * sPast) / (8 * (staircaseM K k : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity)
            (by have := staircaseM_pos K k; positivity)
            (by linarith [staircaseM_pos K k])
        have hsum_eq : ((2 : ℝ) ^ k * sPast) / (8 * (staircaseM K k : ℝ)) +
            ((2 : ℝ) ^ k * (bJet3 * sPast)) / (8 * (staircaseM K k : ℝ)) =
            ((2 : ℝ) ^ k * ((1 + bJet3) * sPast)) / (8 * (staircaseM K k : ℝ)) := by ring
        linarith
      exact (abs_add_le _ _).trans ((add_le_add hosc hcomm_b).trans hcomb)
    have hsum_k : |∑ j ∈ Finset.range k, pairTerm K j k| ≤
        ((k : ℝ) * ((2 : ℝ) ^ k * ((1 + bJet3) * sPast))) / (8 * (staircaseM K k : ℝ)) := by
      calc
        |∑ j ∈ Finset.range k, pairTerm K j k|
            ≤ ∑ j ∈ Finset.range k, |pairTerm K j k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ Finset.range k,
              (((2 : ℝ) ^ k * ((1 + bJet3) * sPast)) / (8 * (staircaseM K k : ℝ))) :=
            Finset.sum_le_sum hj_each
        _ = ((k : ℝ) * ((2 : ℝ) ^ k * ((1 + bJet3) * sPast))) /
              (8 * (staircaseM K k : ℝ)) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    refine hsum_k.trans ?_
    rw [div_le_iff₀ (by have := staircaseM_pos K k; positivity)]
    set P := (1 + bJet3) * sPast
    have hP0 : 0 ≤ P := by positivity
    have hk_pow : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast le_of_lt (Nat.lt_pow_self (by decide : 1 < 2))
    have hsP := sPast_bound_staircaseM K k
    have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
    have hexp : 8192 * (2 : ℝ) ^ (3 * k) ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
      have hp : 8192 * (2 : ℝ) ^ (3 * k) ≤ (2 : ℝ) ^ (3 * k + 16) := by
        rw [pow_add]
        have : (8192 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
        linarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (3 * k))]
      calc
        8192 * (2 : ℝ) ^ (3 * k) = (8192 * (2 : ℝ) ^ (3 * k)) * 1 := (mul_one _).symm
        _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
            mul_le_mul hp hK1 zero_le_one (by positivity)
    calc
      (k : ℝ) * ((2 : ℝ) ^ k * P)
          ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ k * P) :=
            mul_le_mul_of_nonneg_right hk_pow (by positivity)
      _ = (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k * (8 * (8192 * (2 : ℝ) ^ (3 * k) * P)) := by
            have hc1 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
            have hc3 : (2 : ℝ) ^ (3 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
              rw [show 3 * k = k + k + k by omega, pow_add, pow_add]
            rw [hc3]
            calc
              (2 : ℝ) ^ k * ((2 : ℝ) ^ k * P)
                  = ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) * ((2 : ℝ) ^ k * ((2 : ℝ) ^ k * P)) := by
                    rw [hc1, one_mul]
              _ = (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k *
                    (8 * (8192 * ((2 : ℝ) ^ k * (2 : ℝ) ^ k * (2 : ℝ) ^ k) * P)) := by ring
      _ ≤ (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k * (8 * (staircaseM K k : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact (mul_le_mul_of_nonneg_right hexp hP0).trans hsP
  calc
    |∑ k ∈ Finset.range K, ∑ j ∈ Finset.range k, pairTerm K j k|
        ≤ ∑ k ∈ Finset.range K, |∑ j ∈ Finset.range k, pairTerm K j k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range K, (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k := Finset.sum_le_sum hk_bound
    _ = (1 / 65536 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k := (Finset.mul_sum _ _ _).symm
    _ ≤ (1 / 65536 : ℝ) * 2 := mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
    _ = 1 / 32768 := by norm_num

private lemma diag_term_lower_bound {K k : ℕ} (hk : k < K) :
    (if k % 3 = 0 then (0 : ℝ) else 3 / 16384) - (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k ≤
      pairTerm K k k := by
  rw [pairTerm_ibp_x K k k]
  let δ := staircaseDelta K
  let Λ := staircaseLambda K
  have hδ0 := staircaseDelta_pos K
  have hδ1 := staircaseDelta_le_eighth K
  let Ak := ampProd δ Λ k
  have hAk_reg := contDiff_ampProd hδ0 hδ1 Λ k
  let Hmain : Euclidean 2 → ℝ := fun p =>
    -(1 / 8 : ℝ) * Ak p *
      tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) * (spin3Ray k).1
  let Herr : Euclidean 2 → ℝ := fun p =>
    -(1 / (8 * Λ k)) * planarDx Ak p *
      tauWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
  let Umain : Euclidean 2 → ℝ := fun p =>
    (1 / 4 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 * (spin3Ray k).2 ^ 2) * Ak p *
      tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
  let Udxyy : Euclidean 2 → ℝ := planarDx (planarDy (planarDy (uTerm δ Λ k)))
  let PosCore : Euclidean 2 → ℝ := fun p =>
    (1 / 32 : ℝ) * (2 : ℝ) ^ k * ((spin3Ray k).1 ^ 2 * (spin3Ray k).2 ^ 2) * (Ak p) ^ 2 *
      (tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) ^ 2
  have hHx_split : ∀ p : Euclidean 2, planarDx (hTerm δ Λ k) p = Herr p + Hmain p := by
    intro p
    rw [(hTerm_partials δ hδ0 hδ1 Λ k (ne_of_gt (staircaseLambda_pos K k)) p).1]
    dsimp [Herr, Hmain]; ring
  have hpt_lb : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      PosCore (planarPt x y) - (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k ≤
        -(planarDx (hTerm δ Λ k) (planarPt x y) * Udxyy (planarPt x y)) := by
    intro x hx y hy
    set p := planarPt x y
    rw [hHx_split p]
    have hcore_eq : -(Hmain p * Umain p) = PosCore p := by
      dsimp [Hmain, Umain, PosCore]; ring
    have hident : -((Herr p + Hmain p) * Udxyy p) =
        PosCore p - (Hmain p * (Udxyy p - Umain p) + Herr p * Umain p +
          Herr p * (Udxyy p - Umain p)) := by
      rw [← hcore_eq]; ring
    rw [hident]
    have hHmain_abs : |Hmain p| ≤ 1 / 8 := by
      dsimp [Hmain]
      rw [abs_mul, abs_mul, abs_mul, show |-(1 / 8 : ℝ)| = 1 / 8 by norm_num,
        abs_of_nonneg (ampProd_nonneg δ Λ k p)]
      calc
        (1 / 8 : ℝ) * Ak p * |tauDerivWave δ _| * |(spin3Ray k).1|
            ≤ (1 / 8 : ℝ) * 1 * 1 * 1 := by
              gcongr
              · exact ampProd_le_one δ Λ k p
              · exact abs_tauDerivWave_le_one hδ0 hδ1 _
              · exact abs_spin3Ray_fst_le_one k
        _ = 1 / 8 := by ring
    have hHerr_abs : |Herr p| ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ (3 * k) := by
      dsimp [Herr]
      have hdx_b := abs_le_unitSqSup (contDiff_planarDx_b1 (r := 3) hAk_reg).continuous hx hy
      have hτ_b := abs_tauWave_le hδ0 hδ1 (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
      rw [abs_mul, abs_mul, show |-(1 / (8 * Λ k))| = 1 / (16 * (staircaseM K k : ℝ)) by
        dsimp [Λ, staircaseLambda]; rw [abs_neg, abs_of_pos (by have := staircaseM_pos K k; positivity)]; ring]
      have hreq := reqBound_le_staircaseM K k
      unfold reqBound at hreq; dsimp only at hreq
      have hdx_M : (2 : ℝ) ^ (3 * k + 16) * unitSqSup (planarDx Ak) ≤ (staircaseM K k : ℝ) := by
        have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
        have hm : (2 : ℝ) ^ (3 * k + 16) * unitSqSup (planarDx Ak) ≤
            (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * unitSqSup (planarDx Ak) := by
          have : (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) * unitSqSup (planarDx Ak) =
              (2 : ℝ) ^ (3 * k + 16) * (((K : ℝ) + 3) * unitSqSup (planarDx Ak)) := by ring
          rw [this]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [unitSqSup_nonneg (planarDx Ak)]
        refine hm.trans (term_le_staircaseM_div K k ?_)
        have hb2 := unitSqXLip_nonneg Ak
        have hb3 := unitSqSup_nonneg (jet3Norm Ak)
        have hb4 : 0 ≤ ∑ j ∈ Finset.range k,
            unitSqSup (planarDx (planarDx (planarDy (planarDy (uTerm δ Λ j))))) :=
          Finset.sum_nonneg fun _ _ => unitSqSup_nonneg _
        have hb5 : 0 ≤ (1 + unitSqSup (jet3Norm Ak)) *
            ∑ j ∈ Finset.range k,
              (unitSqSup (planarDx (hTerm δ Λ j)) +
                unitSqXLip (fun q => planarDx (hTerm δ Λ j) q * Ak q)) :=
          mul_nonneg (by linarith) (Finset.sum_nonneg fun _ _ =>
            add_nonneg (unitSqSup_nonneg _) (unitSqXLip_nonneg _))
        linarith [unitSqSup_nonneg (planarDy Ak)]
      have hdiv : (1 / (16 * (staircaseM K k : ℝ))) * |planarDx Ak p| ≤
          (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (3 * k) := by
        rw [mul_comm, ← div_eq_mul_one_div, div_le_iff₀ (by have := staircaseM_pos K k; positivity)]
        calc
          |planarDx Ak p| ≤ unitSqSup (planarDx Ak) := hdx_b
          _ = (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (3 * k) *
                (16 * ((2 : ℝ) ^ (3 * k + 16) * unitSqSup (planarDx Ak))) := by
                have hc1 : (2 : ℝ) ^ (3 * k) * (1 / 2 : ℝ) ^ (3 * k) = 1 := by
                  rw [← mul_pow]; norm_num
                rw [pow_add]
                calc
                  unitSqSup (planarDx Ak) =
                      ((2 : ℝ) ^ (3 * k) * (1 / 2 : ℝ) ^ (3 * k)) * unitSqSup (planarDx Ak) := by
                    rw [hc1, one_mul]
                  _ = (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (3 * k) *
                        (16 * ((2 : ℝ) ^ (3 * k) * (2 : ℝ) ^ 16 * unitSqSup (planarDx Ak))) := by
                    norm_num; ring
          _ ≤ (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (3 * k) * (16 * (staircaseM K k : ℝ)) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith
      calc
        (1 / (16 * (staircaseM K k : ℝ))) * |planarDx Ak p| * |tauWave δ _|
            ≤ ((1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (3 * k)) * (1 / 4) :=
              mul_le_mul hdiv hτ_b (abs_nonneg _) (by positivity)
        _ ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ (3 * k) := by
              have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 * k) := by positivity
              linarith
    have hUmain_abs : |Umain p| ≤ (1 / 4 : ℝ) * (2 : ℝ) ^ k := by
      dsimp [Umain]
      rw [abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4),
        abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ k),
        abs_mul, abs_pow, abs_of_nonneg (ampProd_nonneg δ Λ k p)]
      have h1 := abs_spin3Ray_fst_le_one k
      have h2 : |(spin3Ray k).2| ^ 2 ≤ 1 := by
        have hb := abs_spin3Ray_snd_le_one k
        nlinarith [abs_nonneg (spin3Ray k).2]
      have hprod1 : |(spin3Ray k).1| * |(spin3Ray k).2| ^ 2 ≤ 1 := by
        nlinarith [abs_nonneg (spin3Ray k).1, sq_nonneg |(spin3Ray k).2|]
      have hAk0 : 0 ≤ Ak p := ampProd_nonneg δ Λ k p
      have hAk1 : Ak p ≤ 1 := ampProd_le_one δ Λ k p
      have hτ1 := abs_tauDerivWave_le_one hδ0 hδ1
        (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))
      have hsub1 : (|(spin3Ray k).1| * |(spin3Ray k).2| ^ 2) *
          (Ak p * |tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))|) ≤ 1 := by
        have hAτ : Ak p *
            |tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))| ≤ 1 :=
          (mul_le_mul_of_nonneg_right hAk1 (abs_nonneg _)).trans (by linarith)
        exact (mul_le_mul_of_nonneg_right hprod1 (mul_nonneg hAk0 (abs_nonneg _))).trans
          (by linarith)
      calc
        (1 / 4 : ℝ) * (2 : ℝ) ^ k * (|(spin3Ray k).1| * |(spin3Ray k).2| ^ 2) *
            Ak p * |tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))|
            = ((1 / 4 : ℝ) * (2 : ℝ) ^ k) *
              ((|(spin3Ray k).1| * |(spin3Ray k).2| ^ 2) *
                (Ak p * |tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))|)) := by
              ring
        _ ≤ ((1 / 4 : ℝ) * (2 : ℝ) ^ k) * 1 :=
            mul_le_mul_of_nonneg_left hsub1 (by positivity)
        _ = (1 / 4 : ℝ) * (2 : ℝ) ^ k := mul_one _
    have hUerr_abs : |Udxyy p - Umain p| ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := by
      have hc_u := (uTerm_third_commutators K k p).1
      have hAk3 : ContDiff ℝ (3 : ℕ) Ak := hAk_reg.of_le (by norm_cast)
      have hj_b := (le_abs_self _).trans (abs_le_unitSqSup (continuous_jet3Norm hAk3) hx hy)
      have hE_nn : 0 ≤ (2 : ℝ) ^ k / (16 * Λ k) := by
        have := staircaseLambda_pos K k; positivity
      have hu1 : |Udxyy p - Umain p| ≤
          (3 * unitSqSup (jet3Norm Ak) * (2 : ℝ) ^ k) / (32 * (staircaseM K k : ℝ)) := by
        calc
          |Udxyy p - Umain p| ≤ 3 * jet3Norm Ak p * ((2 : ℝ) ^ k / (16 * Λ k)) := hc_u
          _ ≤ 3 * unitSqSup (jet3Norm Ak) * ((2 : ℝ) ^ k / (16 * Λ k)) :=
              mul_le_mul_of_nonneg_right (by linarith) hE_nn
          _ = (3 * unitSqSup (jet3Norm Ak) * (2 : ℝ) ^ k) / (32 * (staircaseM K k : ℝ)) := by
              dsimp [Λ, staircaseLambda]; ring
      refine hu1.trans ?_
      rw [div_le_iff₀ (by have := staircaseM_pos K k; positivity)]
      set J := unitSqSup (jet3Norm Ak)
      have hJ0 := unitSqSup_nonneg (jet3Norm Ak)
      have hbJ := bJet3_bound_staircaseM K k
      have hK3 : (3 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
      have hexp : 24576 * (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
        have hp : 8192 * (2 : ℝ) ^ (2 * k) ≤ (2 : ℝ) ^ (3 * k + 16) := by
          have h1 : (2 : ℝ) ^ (2 * k) * 8192 ≤ (2 : ℝ) ^ (2 * k) * (2 : ℝ) ^ 16 :=
            mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
          have h2 : (2 : ℝ) ^ (2 * k + 16) ≤ (2 : ℝ) ^ (3 * k + 16) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          rw [pow_add] at h2
          linarith
        calc
          24576 * (2 : ℝ) ^ (2 * k) = (8192 * (2 : ℝ) ^ (2 * k)) * 3 := by ring
          _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
              mul_le_mul hp hK3 (by norm_num) (by positivity)
      calc
        3 * J * (2 : ℝ) ^ k
            = (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k * (32 * (24576 * (2 : ℝ) ^ (2 * k) * J)) := by
              have hc1 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
              have hc2 : (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by
                rw [show 2 * k = k + k by omega, pow_add]
              rw [hc2]
              calc
                3 * J * (2 : ℝ) ^ k = ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) * (3 * J * (2 : ℝ) ^ k) := by
                  rw [hc1, one_mul]
                _ = (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k *
                      (32 * (24576 * ((2 : ℝ) ^ k * (2 : ℝ) ^ k) * J)) := by ring
        _ ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k * (32 * (staircaseM K k : ℝ)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact (mul_le_mul_of_nonneg_right hexp hJ0).trans hbJ
    have he1 : |Hmain p * (Udxyy p - Umain p)| ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := by
      rw [abs_mul]
      calc
        |Hmain p| * |Udxyy p - Umain p|
            ≤ (1 / 8 : ℝ) * ((1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k) :=
              mul_le_mul hHmain_abs hUerr_abs (abs_nonneg _) (by norm_num)
        _ ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := by
              have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
              linarith
    have he2 : |Herr p * Umain p| ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := by
      rw [abs_mul]
      have hprod : ((1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ (3 * k)) * ((1 / 4 : ℝ) * (2 : ℝ) ^ k) =
          (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by
        have hc1 : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by rw [← mul_pow]; norm_num
        rw [show 3 * k = 2 * k + k by omega, pow_add]
        calc
          (1 / 262144 : ℝ) * ((1 / 2 : ℝ) ^ (2 * k) * (1 / 2 : ℝ) ^ k) *
              ((1 / 4 : ℝ) * (2 : ℝ) ^ k) =
              (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (2 * k) * ((1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k) := by ring
          _ = (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := by rw [hc1, mul_one]
      have hpow_le : (1 / 2 : ℝ) ^ (2 * k) ≤ (1 / 2 : ℝ) ^ k :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc
        |Herr p| * |Umain p|
            ≤ ((1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ (3 * k)) * ((1 / 4 : ℝ) * (2 : ℝ) ^ k) :=
              mul_le_mul hHerr_abs hUmain_abs (abs_nonneg _) (by positivity)
        _ = (1 / 1048576 : ℝ) * (1 / 2 : ℝ) ^ (2 * k) := hprod
        _ ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := by
              have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (2 * k) := by positivity
              linarith
    have he3 : |Herr p * (Udxyy p - Umain p)| ≤ (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := by
      rw [abs_mul]
      have hHerr1 : |Herr p| ≤ 1 := by
        have h1 : (1 / 2 : ℝ) ^ (3 * k) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
      calc
        |Herr p| * |Udxyy p - Umain p|
            ≤ 1 * ((1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k) :=
              mul_le_mul hHerr1 hUerr_abs (abs_nonneg _) zero_le_one
        _ = (1 / 262144 : ℝ) * (1 / 2 : ℝ) ^ k := one_mul _
    have hsum_err : Hmain p * (Udxyy p - Umain p) + Herr p * Umain p +
        Herr p * (Udxyy p - Umain p) ≤ (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k := by
      have : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
      linarith [le_abs_self (Hmain p * (Udxyy p - Umain p)),
                le_abs_self (Herr p * Umain p),
                le_abs_self (Herr p * (Udxyy p - Umain p))]
    linarith
  have hc_PosCore : Continuous PosCore := by
    dsimp [PosCore]
    have hlin : Continuous (fun p : Euclidean 2 =>
        Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) :=
      continuous_const.mul
        ((continuous_const.mul (EuclideanSpace.proj (0 : Fin 2)).continuous).add
          (continuous_const.mul (EuclideanSpace.proj (1 : Fin 2)).continuous))
    exact (continuous_const.mul (hAk_reg.continuous.pow 2)).mul
      (((contDiff_tauDerivWave hδ0 hδ1).continuous.comp hlin).pow 2)
  have hc_rhs_neg : Continuous (fun p => -(planarDx (hTerm δ Λ k) p * Udxyy p)) :=
    ((contDiff_planarDx_b1 (r := 3) (contDiff_hTerm hδ0 hδ1 Λ k)).continuous.mul
      (contDiff_planarDx_b1 (r := 1) (contDiff_planarDy_b1 (r := 2)
        (contDiff_planarDy_b1 (r := 3) (contDiff_uTerm hδ0 hδ1 Λ k)))).continuous).neg
  have hint_lb : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, PosCore (planarPt x y)) -
      (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k ≤
      - ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          planarDx (hTerm δ Λ k) (planarPt x y) * Udxyy (planarPt x y) := by
    have hm := unitSq_integral_mono
      (F := fun p => PosCore p + -((1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k))
      (G := fun p => -(planarDx (hTerm δ Λ k) p * Udxyy p))
      (hc_PosCore.add continuous_const) hc_rhs_neg
      (fun x hx y hy => by simpa [sub_eq_add_neg] using hpt_lb x hx y hy)
    rw [unitSq_integral_add (F := PosCore)
      (G := fun _ => -((1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k))
      hc_PosCore continuous_const, unitSq_integral_const] at hm
    have hneg_int : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        -(planarDx (hTerm δ Λ k) (planarPt x y) * Udxyy (planarPt x y))) =
        - ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
            planarDx (hTerm δ Λ k) (planarPt x y) * Udxyy (planarPt x y) := by
      simp_rw [intervalIntegral.integral_neg]
    rw [hneg_int] at hm
    linarith
  refine le_trans ?_ hint_lb
  apply sub_le_sub_right
  by_cases hmod : k % 3 = 0
  · simp only [hmod, ↓reduceIte]
    exact intervalIntegral.integral_nonneg zero_le_one fun y _ =>
      intervalIntegral.integral_nonneg zero_le_one fun x _ => by
        dsimp [PosCore]; positivity
  · split_ifs
    have hray_val : (spin3Ray k).1 ^ 2 * (spin3Ray k).2 ^ 2 = 3 / 16 := by
      rw [spin3Ray_sq_mul_sq k]; split_ifs; norm_num
    have hPos_rew : (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, PosCore (planarPt x y)) =
        (3 / 512 : ℝ) * ((2 : ℝ) ^ k *
          ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
            (Ak (planarPt x y)) ^ 2 *
              (tauDerivWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
                (spin3Ray k).2 * (planarPt x y) 1))) ^ 2) := by
      have hpt : ∀ x y : ℝ, PosCore (planarPt x y) =
          ((3 / 512 : ℝ) * (2 : ℝ) ^ k) *
            ((Ak (planarPt x y)) ^ 2 *
              (tauDerivWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
                (spin3Ray k).2 * (planarPt x y) 1))) ^ 2) := by
        intro x y; dsimp [PosCore]; rw [hray_val]; ring
      simp_rw [hpt, intervalIntegral.integral_const_mul]
      ring
    rw [hPos_rew]
    let L := unitSqXLip Ak
    have hL0 := unitSqXLip_nonneg Ak
    let Nk := xFreqNat k (staircaseM K k)
    have hM_le_N : staircaseM K k ≤ Nk := le_xFreqNat k (staircaseM K k)
    have hNk1 : 1 ≤ Nk := (one_le_staircaseM K k).trans hM_le_N
    have hsq_lip : ∀ y ∈ Icc (0 : ℝ) 1, ∀ x₁ ∈ Icc (0 : ℝ) 1, ∀ x₂ ∈ Icc (0 : ℝ) 1,
        |(Ak (planarPt x₁ y)) ^ 2 - (Ak (planarPt x₂ y)) ^ 2| ≤ (2 * L) * |x₁ - x₂| := by
      intro y hy x₁ hx₁ x₂ hx₂
      have hfac : (Ak (planarPt x₁ y)) ^ 2 - (Ak (planarPt x₂ y)) ^ 2 =
          (Ak (planarPt x₁ y) + Ak (planarPt x₂ y)) *
            (Ak (planarPt x₁ y) - Ak (planarPt x₂ y)) := by ring
      have hsum_le : |Ak (planarPt x₁ y) + Ak (planarPt x₂ y)| ≤ 2 := by
        rw [abs_of_nonneg (add_nonneg (ampProd_nonneg δ Λ k _) (ampProd_nonneg δ Λ k _))]
        linarith [ampProd_le_one δ Λ k (planarPt x₁ y), ampProd_le_one δ Λ k (planarPt x₂ y)]
      have hdiff_le := sub_le_unitSqXLip (hAk_reg.of_le (by norm_cast)) hy hx₁ hx₂
      rw [hfac, abs_mul]
      calc
        |Ak (planarPt x₁ y) + Ak (planarPt x₂ y)| * |Ak (planarPt x₁ y) - Ak (planarPt x₂ y)|
            ≤ 2 * (L * |x₁ - x₂|) := mul_le_mul hsum_le hdiff_le (abs_nonneg _) zero_le_two
        _ = (2 * L) * |x₁ - x₂| := by ring
    have hrow : ∀ y ∈ Icc (0 : ℝ) 1,
        (3 / 4 : ℝ) * (∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2) -
          (4 * L) / (staircaseM K k : ℝ) ≤
          ∫ x in (0 : ℝ)..1,
            (Ak (planarPt x y)) ^ 2 *
              (tauDerivWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
                (spin3Ray k).2 * (planarPt x y) 1))) ^ 2 := by
      intro y hy
      have harg : ∀ x : ℝ,
          Λ k * ((spin3Ray k).1 * (planarPt x y) 0 + (spin3Ray k).2 * (planarPt x y) 1) =
            (Λ k * (spin3Ray k).1) * x + (Λ k * (spin3Ray k).2 * y) := by
        intro x; simp only [planarPt_apply_zero, planarPt_apply_one]; ring
      simp_rw [harg]
      have hper := periodic_phase_sign_mean_bound_1d (N := Nk)
        (F := fun x => (Ak (planarPt x y)) ^ 2)
        (q := fun t => (tauDerivWave δ t) ^ 2)
        (L := 2 * L) (B := 1) (a := Λ k * (spin3Ray k).1) (φ := Λ k * (spin3Ray k).2 * y)
        hNk1 (by positivity) zero_le_one (xFreqNat_ray_fst k (staircaseM K k))
        (cont_planarPt_x (hAk_reg.continuous.pow 2) y)
        ((contDiff_tauDerivWave hδ0 hδ1).continuous.pow 2)
        (hsq_lip y hy)
        (fun t => by
          have h1 : t + 1 = (t + 1 / 2) + 1 / 2 := by ring
          rw [h1, tauDerivWave_antiperiodic hδ0 hδ1, tauDerivWave_antiperiodic hδ0 hδ1, neg_neg])
        (fun t => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have hb : |tauDerivWave δ t| ≤ 1 := abs_tauDerivWave_le_one hδ0 hδ1 t
          rcases abs_le.mp hb with ⟨hb1, hb2⟩
          nlinarith)
      have hFk_nn : 0 ≤ ∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2 :=
        intervalIntegral.integral_nonneg zero_le_one (fun _ _ => sq_nonneg _)
      have hτ_sq : (3 / 4 : ℝ) ≤ ∫ t in (0 : ℝ)..1, (tauDerivWave δ t) ^ 2 := by
        have hge := integral_tauDerivWave_sq_ge hδ0 hδ1
        linarith
      have hμ_ge : (3 / 4 : ℝ) * (∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2) ≤
          (∫ t in (0 : ℝ)..1, (tauDerivWave δ t) ^ 2) *
            ∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2 :=
        mul_le_mul_of_nonneg_right hτ_sq hFk_nn
      have herr_le : (2 * 1 * (2 * L)) / (Nk : ℝ) ≤ (4 * L) / (staircaseM K k : ℝ) := by
        rw [show (2 : ℝ) * 1 * (2 * L) = 4 * L by ring]
        exact div_le_div_of_nonneg_left (by positivity) (staircaseM_pos K k)
          (by exact_mod_cast hM_le_N)
      linarith [(abs_le.mp hper).1]
    have hc_int_sq := cont_inner_unitSq (hAk_reg.continuous.pow 2)
    have hc_prod_τ : Continuous (fun p : Euclidean 2 =>
        (Ak p) ^ 2 * (tauDerivWave δ (Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1))) ^ 2) := by
      have hlin : Continuous (fun p : Euclidean 2 =>
          Λ k * ((spin3Ray k).1 * p 0 + (spin3Ray k).2 * p 1)) :=
        continuous_const.mul
          ((continuous_const.mul (EuclideanSpace.proj (0 : Fin 2)).continuous).add
            (continuous_const.mul (EuclideanSpace.proj (1 : Fin 2)).continuous))
      exact (hAk_reg.continuous.pow 2).mul
        (((contDiff_tauDerivWave hδ0 hδ1).continuous.comp hlin).pow 2)
    have hint_y : (3 / 4 : ℝ) *
        (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2) -
        (4 * L) / (staircaseM K k : ℝ) ≤
        ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          (Ak (planarPt x y)) ^ 2 *
            (tauDerivWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
              (spin3Ray k).2 * (planarPt x y) 1))) ^ 2 := by
      have hm := intervalIntegral.integral_mono_on zero_le_one
        ((by fun_prop : Continuous (fun y : ℝ =>
          (3 / 4 : ℝ) * (∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2) -
            (4 * L) / (staircaseM K k : ℝ))).intervalIntegrable (μ := volume) 0 1)
        ((cont_inner_unitSq hc_prod_τ).intervalIntegrable (μ := volume) 0 1)
        hrow
      rw [intervalIntegral.integral_sub
        ((by fun_prop : Continuous (fun y : ℝ =>
          (3 / 4 : ℝ) * ∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2)).intervalIntegrable
          (μ := volume) 0 1)
        (continuous_const.intervalIntegrable (μ := volume) 0 1),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul] at hm
      linarith
    have hJk := ampProd_l2_ge_sixteenth (le_of_lt hk)
    have herr_128 : (2 : ℝ) ^ k * ((4 * L) / (staircaseM K k : ℝ)) ≤ 1 / 128 := by
      rw [mul_div_assoc', div_le_iff₀ (staircaseM_pos K k)]
      have hb := bLip_bound_staircaseM K k
      have hK1 : (1 : ℝ) ≤ (K : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) K]
      have hexp : 512 * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) := by
        have hp : 512 * (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (3 * k + 16) := by
          have h1 : (2 : ℝ) ^ k * 512 ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ 16 :=
            mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
          have h2 : (2 : ℝ) ^ (k + 16) ≤ (2 : ℝ) ^ (3 * k + 16) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
          rw [pow_add] at h2
          linarith
        calc
          512 * (2 : ℝ) ^ k = (512 * (2 : ℝ) ^ k) * 1 := (mul_one _).symm
          _ ≤ (2 : ℝ) ^ (3 * k + 16) * ((K : ℝ) + 3) :=
              mul_le_mul hp hK1 zero_le_one (by positivity)
      have hlhs : (2 : ℝ) ^ k * (4 * L) = (1 / 128 : ℝ) * (512 * (2 : ℝ) ^ k * L) := by ring
      rw [hlhs]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (mul_le_mul_of_nonneg_right hexp hL0).trans hb
    have h2k_int : (1 / 32 : ℝ) ≤ (2 : ℝ) ^ k *
        ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
          (Ak (planarPt x y)) ^ 2 *
            (tauDerivWave δ (Λ k * ((spin3Ray k).1 * (planarPt x y) 0 +
              (spin3Ray k).2 * (planarPt x y) 1))) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left hint_y (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      have hrew_m : (2 : ℝ) ^ k *
          ((3 / 4 : ℝ) * (∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2) -
            (4 * L) / (staircaseM K k : ℝ)) =
          (3 / 4 : ℝ) * ((2 : ℝ) ^ k *
            ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, (Ak (planarPt x y)) ^ 2) -
          (2 : ℝ) ^ k * ((4 * L) / (staircaseM K k : ℝ)) := by ring
      rw [hrew_m] at hm
      linarith
    linarith

private lemma sum_mod_three_nonzero (n : ℕ) :
    (∑ k ∈ Finset.range (3 * n), (if k % 3 = 0 then (0 : ℝ) else 3 / 16384)) =
      (n : ℝ) * (3 / 8192) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 3 * (n + 1) = 3 * n + 1 + 1 + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h0 : (3 * n) % 3 = 0 := by omega
      have h1 : (3 * n + 1) % 3 = 1 := by omega
      have h2 : (3 * n + 2) % 3 = 2 := by omega
      simp only [h0, h1, h2, ↓reduceIte, Nat.one_ne_zero, OfNat.ofNat_ne_zero]
      push_cast
      ring

/-- **Linear `≳ m + 1` Pairing Lower Bound:**
At `K = 3 * (m + 1)` scales, the pairing between `staircaseH K` and `∂_x² ∂_y² (staircaseU K)`
on `[0, 1]²` grows linearly in `m + 1`:
`((m + 1 : ℝ) / 4096) ≤ ∫_0^1 ∫_0^1 staircaseH (3 * (m + 1)) · ∂_x² ∂_y² (staircaseU (3 * (m + 1)))`. -/
theorem pairing_staircase_lower_bound (m : ℕ) :
    ((m + 1 : ℝ) / 4096) ≤
      ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
        staircaseH (3 * (m + 1)) (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (staircaseU (3 * (m + 1))))))
            (planarPt x y) := by
  set K := 3 * (m + 1)
  rw [pairing_eq_double_sum K, sum_square_trichotomy K (pairTerm K)]
  have hfut := (abs_le.mp (future_sum_bound K)).1
  have hpast := (abs_le.mp (past_sum_bound K)).1
  have hdiag : ((m + 1 : ℝ) * (3 / 8192)) - 1 / 32768 ≤
      ∑ k ∈ Finset.range K, pairTerm K k k := by
    have h1 : ∑ k ∈ Finset.range K,
        ((if k % 3 = 0 then (0 : ℝ) else 3 / 16384) - (1 / 65536 : ℝ) * (1 / 2 : ℝ) ^ k) ≤
        ∑ k ∈ Finset.range K, pairTerm K k k :=
      Finset.sum_le_sum fun k hk => diag_term_lower_bound (Finset.mem_range.mp hk)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h1
    have hmod_sum : (∑ k ∈ Finset.range K, (if k % 3 = 0 then (0 : ℝ) else 3 / 16384)) =
        ((m + 1 : ℝ) * (3 / 8192)) := by
      dsimp [K]
      exact_mod_cast sum_mod_three_nonzero (m + 1)
    have herr_sum : (1 / 65536 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k ≤ 1 / 32768 := by
      calc
        (1 / 65536 : ℝ) * ∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k ≤ (1 / 65536 : ℝ) * 2 :=
          mul_le_mul_of_nonneg_left (sum_half_pow_lt_two K) (by norm_num)
        _ = 1 / 32768 := by norm_num
    linarith
  have hm_ge : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

end Rudin.PMA.Chapter10

/-! Verify module ownership and standard foundations for all declarations in this module. -/
run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.Research.Stage4B1Staircase
    #[`Rudin.PMA.Chapter10.norm_fderiv_le_abs_planarDx_add_planarDy,
      `Rudin.PMA.Chapter10.third_partials_commutator_jet3Norm,
      `Rudin.PMA.Chapter10.antiperiodic_phase_sign_bound_1d,
      `Rudin.PMA.Chapter10.periodic_phase_sign_mean_bound_1d,
      `Rudin.PMA.Chapter10.contDiff_staircaseU,
      `Rudin.PMA.Chapter10.contDiff_staircaseH,
      `Rudin.PMA.Chapter10.staircaseU_zero_outside,
      `Rudin.PMA.Chapter10.staircaseH_zero_outside,
      `Rudin.PMA.Chapter10.vanishesThirdPartialsOnRectBdry_staircaseU,
      `Rudin.PMA.Chapter10.abs_staircaseH_le_one,
      `Rudin.PMA.Chapter10.abs_planarDx_staircaseH_le_half,
      `Rudin.PMA.Chapter10.abs_planarDy_staircaseH_le_half,
      `Rudin.PMA.Chapter10.norm_fderiv_staircaseH_le_one,
      `Rudin.PMA.Chapter10.spin3_l1_staircaseU_le_one,
      `Rudin.PMA.Chapter10.spin3_l1_staircaseU_le_two,
      `Rudin.PMA.Chapter10.pairing_staircase_lower_bound]
