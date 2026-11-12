import Rudin.Research.Stage4B1Staircase

/-!
# Stage B1 Gliding-Hump Witness Instantiation and Unconditional Disproof of `pma10_43_contract`

This module completes **Stage B1** of `rudin-lean` #29 (Rudin *Principles of Mathematical
Analysis*, Theorem 10.43). We rescale the compactly supported 3-ray stopped-martingale
staircase `(staircaseU K, staircaseH K)` from `Rudin.Research.Stage4B1Staircase` onto pairwise
disjoint dyadic sub-squares `R_m = [a_m, b_m] × [0, r_m] ⊂ [0, 1]²` accumulating only at `(0, 0)`,
form the `C¹(ℝ²)` gliding-hump sum `f = ∑' m, ε_m * h_m`, and instantiate
`not_pma10_43_contract_of_spin3_gliding_hump` (`PMA1043Stage4B1.lean:1320`) to establish the
unconditional closed theorem:

`theorem not_pma10_43_contract : ¬ pma10_43_contract`
-/

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

/-! ### Section 1: 2D Affine Box Rescaling and Scaling of Partial Derivatives and Integrals -/

/-- Affine rescaling map `(x, y) ↦ ((x - a) / r, y / r)` sending `[a, a + r] × [0, r]` to `[0, 1]²`. -/
def affScalePt (a r : ℝ) (p : Euclidean 2) : Euclidean 2 :=
  planarPt ((p 0 - a) / r) (p 1 / r)

private lemma affScalePt_eq_linear (a r : ℝ) (p : Euclidean 2) :
    affScalePt a r p =
      ((p 0 - a) / r) • coordinateVector 2 0 + (p 1 / r) • coordinateVector 2 1 := by
  ext i
  fin_cases i <;>
    simp [affScalePt, planarPt, coordinateVector, EuclideanSpace.basisFun_apply]

private lemma contDiff_affScalePt (a r : ℝ) : ContDiff ℝ ⊤ (affScalePt a r) := by
  have hrew : affScalePt a r = fun p : Euclidean 2 =>
      ((p 0 - a) * r⁻¹) • coordinateVector 2 0 + (p 1 * r⁻¹) • coordinateVector 2 1 := by
    funext p
    simpa only [div_eq_mul_inv] using affScalePt_eq_linear a r p
  rw [hrew]
  have hp0 : ContDiff ℝ ⊤ (fun p : Euclidean 2 => p 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff
  have hp1 : ContDiff ℝ ⊤ (fun p : Euclidean 2 => p 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff
  exact (((hp0.sub contDiff_const).mul contDiff_const).smul contDiff_const).add
    ((hp1.mul contDiff_const).smul contDiff_const)

private lemma contDiff_comp_affScalePt {n : ℕ} (a r : ℝ) {G : Euclidean 2 → ℝ}
    (hG : ContDiff ℝ (n : ℕ) G) :
    ContDiff ℝ (n : ℕ) (fun p => G (affScalePt a r p)) :=
  hG.comp ((contDiff_affScalePt a r).of_le le_top)

private lemma diff_of_c1_b1 {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) f) : Differentiable ℝ f :=
  (hf.of_le (by exact_mod_cast Nat.le_add_left 1 r)).differentiable one_ne_zero

private lemma planarDx_const_mul_fn (c : ℝ) {G : Euclidean 2 → ℝ} (hG : Differentiable ℝ G) :
    planarDx (fun p => c * G p) = fun p => c * planarDx G p := by
  funext p
  unfold planarDx
  exact coordinatePartial_const_mul (hG p) c 0

private lemma planarDy_const_mul_fn (c : ℝ) {G : Euclidean 2 → ℝ} (hG : Differentiable ℝ G) :
    planarDy (fun p => c * G p) = fun p => c * planarDy G p := by
  funext p
  unfold planarDy
  exact coordinatePartial_const_mul (hG p) c 1

private lemma planarDx_comp_affScalePt (a r : ℝ) {G : Euclidean 2 → ℝ}
    (hG : Differentiable ℝ G) :
    planarDx (fun p => G (affScalePt a r p)) =
      fun p => r⁻¹ * planarDx G (affScalePt a r p) := by
  funext p
  set q := affScalePt a r p
  have hshift : ∀ t : ℝ,
      affScalePt a r (p + t • coordinateVector 2 0) =
        q + (r⁻¹ * t) • coordinateVector 2 0 := by
    intro t
    ext i
    fin_cases i <;>
      simp [q, affScalePt, planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    ring
  have ht : HasDerivAt (fun t : ℝ => r⁻¹ * t) r⁻¹ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r⁻¹
  have hcurve : HasDerivAt (fun t : ℝ => q + (r⁻¹ * t) • coordinateVector 2 0)
      (r⁻¹ • coordinateVector 2 0) 0 :=
    (ht.smul_const (coordinateVector 2 0)).const_add q
  have hG_at : HasFDerivAt G (fderiv ℝ G q) (q + (r⁻¹ * 0) • coordinateVector 2 0) := by
    simpa [mul_zero, zero_smul, add_zero] using (hG q).hasFDerivAt
  have hcomp := hG_at.comp_hasDerivAt 0 hcurve
  have hval : (fderiv ℝ G q) (r⁻¹ • coordinateVector 2 0) = r⁻¹ * planarDx G q := by
    rw [map_smul, smul_eq_mul]
    unfold planarDx
    rw [coordinatePartial_eq_fderiv (hG q) 0]
  conv_lhs => unfold planarDx coordinatePartial
  simp_rw [hshift]
  exact hcomp.deriv.trans hval

private lemma planarDy_comp_affScalePt (a r : ℝ) {G : Euclidean 2 → ℝ}
    (hG : Differentiable ℝ G) :
    planarDy (fun p => G (affScalePt a r p)) =
      fun p => r⁻¹ * planarDy G (affScalePt a r p) := by
  funext p
  set q := affScalePt a r p
  have hshift : ∀ t : ℝ,
      affScalePt a r (p + t • coordinateVector 2 1) =
        q + (r⁻¹ * t) • coordinateVector 2 1 := by
    intro t
    ext i
    fin_cases i <;>
      simp [q, affScalePt, planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    ring
  have ht : HasDerivAt (fun t : ℝ => r⁻¹ * t) r⁻¹ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r⁻¹
  have hcurve : HasDerivAt (fun t : ℝ => q + (r⁻¹ * t) • coordinateVector 2 1)
      (r⁻¹ • coordinateVector 2 1) 0 :=
    (ht.smul_const (coordinateVector 2 1)).const_add q
  have hG_at : HasFDerivAt G (fderiv ℝ G q) (q + (r⁻¹ * 0) • coordinateVector 2 1) := by
    simpa [mul_zero, zero_smul, add_zero] using (hG q).hasFDerivAt
  have hcomp := hG_at.comp_hasDerivAt 0 hcurve
  have hval : (fderiv ℝ G q) (r⁻¹ • coordinateVector 2 1) = r⁻¹ * planarDy G q := by
    rw [map_smul, smul_eq_mul]
    unfold planarDy
    rw [coordinatePartial_eq_fderiv (hG q) 1]
  conv_lhs => unfold planarDy coordinatePartial
  simp_rw [hshift]
  exact hcomp.deriv.trans hval

private lemma integral_sub_div_box {g : ℝ → ℝ} (a r : ℝ) (hr : 0 < r) :
    (∫ x in a..(a + r), g ((x - a) / r)) = r * ∫ u in (0 : ℝ)..1, g u := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hrinv_ne : r⁻¹ ≠ 0 := inv_ne_zero hr_ne
  have hshift : (∫ x in a..(a + r), g ((x - a) / r)) =
      ∫ y in (0 : ℝ)..r, g (r⁻¹ * y) := by
    calc
      (∫ x in a..(a + r), g ((x - a) / r))
          = ∫ x in ((0 : ℝ) + a)..(r + a), g ((x - a) / r) := by
              congr 1 <;> ring
      _ = ∫ y in (0 : ℝ)..r, g (((y + a) - a) / r) :=
            (intervalIntegral.integral_comp_add_right (fun x => g ((x - a) / r)) a).symm
      _ = ∫ y in (0 : ℝ)..r, g (r⁻¹ * y) := by
            apply intervalIntegral.integral_congr
            intro y _
            dsimp only
            congr 1
            ring
  rw [hshift, intervalIntegral.integral_comp_mul_left (f := g) hrinv_ne]
  have he0 : r⁻¹ * (0 : ℝ) = 0 := by ring
  have he1 : r⁻¹ * r = 1 := inv_mul_cancel₀ hr_ne
  rw [he0, he1, inv_inv, smul_eq_mul]

private lemma integral_2d_affScalePt (Φ : Euclidean 2 → ℝ) (a r : ℝ) (hr : 0 < r) :
    (∫ y in (0 : ℝ)..r, ∫ x in a..(a + r), Φ (affScalePt a r (planarPt x y))) =
      r ^ 2 * ∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, Φ (planarPt u v) := by
  have hpt : ∀ x y : ℝ, affScalePt a r (planarPt x y) = planarPt ((x - a) / r) (y / r) := by
    intro x y
    unfold affScalePt
    simp only [planarPt_apply_zero, planarPt_apply_one]
  have hinner : ∀ y : ℝ,
      (∫ x in a..(a + r), Φ (affScalePt a r (planarPt x y))) =
        r * ∫ u in (0 : ℝ)..1, Φ (planarPt u ((y - 0) / r)) := by
    intro y
    simp_rw [hpt, sub_zero]
    exact integral_sub_div_box (g := fun u => Φ (planarPt u (y / r))) a r hr
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  have hout : (∫ y in (0 : ℝ)..r, ∫ u in (0 : ℝ)..1, Φ (planarPt u ((y - 0) / r))) =
      r * ∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, Φ (planarPt u v) := by
    have h0r : (∫ y in (0 : ℝ)..r, ∫ u in (0 : ℝ)..1, Φ (planarPt u ((y - 0) / r))) =
        ∫ y in (0 : ℝ)..((0 : ℝ) + r), ∫ u in (0 : ℝ)..1, Φ (planarPt u ((y - 0) / r)) := by
      rw [zero_add]
    rw [h0r]
    exact integral_sub_div_box (g := fun v => ∫ u in (0 : ℝ)..1, Φ (planarPt u v)) 0 r hr
  rw [hout]
  ring

/-! ### Section 2: Pairwise Disjoint Dyadic Sub-Squares and Rescaled Witnesses -/

/-- Left `x`-endpoint `a_m = 2^{-(m+1)}` of the `m`-th dyadic sub-square. -/
def boxA (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (m + 1)

/-- Side length `r_m = 2^{-(m+3)}` of the `m`-th dyadic sub-square. -/
def boxR (m : ℕ) : ℝ := (1 / 2 : ℝ) ^ (m + 3)

/-- Right `x`-endpoint `b_m = a_m + r_m = 5 · 2^{-(m+3)}`. -/
def boxB (m : ℕ) : ℝ := boxA m + boxR m

/-- Bottom `y`-endpoint `c_m = 0`. -/
def boxC (_m : ℕ) : ℝ := 0

/-- Top `y`-endpoint `d_m = r_m`. -/
def boxD (m : ℕ) : ℝ := boxR m

/-- Gliding-hump amplitude weight `ε_m = 1 / (m + 1) > 0`. -/
def boxEps (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

/-- Scale index `m' = m² + 2m` so that `3 * (m' + 1) = 3 * (m + 1)²`. -/
def boxM (m : ℕ) : ℕ := m ^ 2 + 2 * m

/-- Staircase depth `K_m = 3 * (boxM m + 1) = 3 * (m + 1)²`. -/
def boxK (m : ℕ) : ℕ := 3 * (boxM m + 1)

/-- Rescaled local `C⁴` datum `h_m(p) = r_m · staircaseH(K_m)((p - (a_m, 0)) / r_m)`. -/
def hBox (m : ℕ) (p : Euclidean 2) : ℝ :=
  boxR m * staircaseH (boxK m) (affScalePt (boxA m) (boxR m) p)

/-- Rescaled local `C⁴` spin-3 test potential `U_m(p) = r_m³ · staircaseU(K_m)((p - (a_m, 0)) / r_m)`. -/
def uBox (m : ℕ) (p : Euclidean 2) : ℝ :=
  (boxR m) ^ 3 * staircaseU (boxK m) (affScalePt (boxA m) (boxR m) p)

/-- Global `C¹(ℝ²)` gliding-hump counterexample datum `f(p) = ∑' m, ε_m * h_m(p)`. -/
def glidingHumpF (p : Euclidean 2) : ℝ :=
  ∑' m : ℕ, boxEps m * hBox m p

private lemma boxR_pos (m : ℕ) : 0 < boxR m := by
  unfold boxR; positivity

private lemma boxA_pos (m : ℕ) : 0 < boxA m := by
  unfold boxA; positivity

private lemma boxA_eq_four_boxR (m : ℕ) : boxA m = 4 * boxR m := by
  unfold boxA boxR
  rw [show m + 3 = (m + 1) + 2 by omega, pow_add]
  ring

private lemma boxEps_pos (m : ℕ) : 0 < boxEps m := by
  unfold boxEps; positivity

private lemma boxes_in_unit_square (m : ℕ) :
    (0 : ℝ) ≤ boxA m ∧ boxA m ≤ boxB m ∧ boxB m ≤ 1 ∧
    (0 : ℝ) ≤ boxC m ∧ boxC m ≤ boxD m ∧ boxD m ≤ 1 := by
  have hr0 : 0 ≤ boxR m := (boxR_pos m).le
  have hr_le : boxR m ≤ 1 / 8 := by
    unfold boxR
    have h1 : (1 / 2 : ℝ) ^ (m + 3) ≤ (1 / 2 : ℝ) ^ 3 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at h1
    exact h1
  have ha_eq := boxA_eq_four_boxR m
  unfold boxB boxC boxD
  refine ⟨by linarith, by linarith, by linarith, le_rfl, hr0, by linarith⟩

private lemma boxB_lt_boxA_of_lt {n m : ℕ} (hnm : n < m) : boxB m < boxA n := by
  have hm_ge : n + 1 ≤ m := Nat.succ_le_of_lt hnm
  have hpow : (1 / 2 : ℝ) ^ (m + 3) ≤ (1 / 2 : ℝ) ^ (n + 4) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hBn : (5 : ℝ) * (1 / 2 : ℝ) ^ (n + 4) = (5 / 8) * boxA n := by
    unfold boxA
    rw [show n + 4 = (n + 1) + 3 by omega, pow_add]
    ring
  have hBm : boxB m = 5 * (1 / 2 : ℝ) ^ (m + 3) := by
    unfold boxB
    rw [boxA_eq_four_boxR m]
    unfold boxR
    ring
  have han : 0 < boxA n := boxA_pos n
  linarith

private lemma disjoint_box_x {m n : ℕ} (hmn : m ≠ n) {x : ℝ}
    (hxm : x ∈ Icc (boxA m) (boxB m)) (hxn : x ∈ Icc (boxA n) (boxB n)) : False := by
  rcases lt_trichotomy m n with hlt | rfl | hgt
  · linarith [boxB_lt_boxA_of_lt hlt, hxm.1, hxn.2]
  · exact hmn rfl
  · linarith [boxB_lt_boxA_of_lt hgt, hxn.1, hxm.2]

private lemma contDiff_hBox (m : ℕ) : ContDiff ℝ (4 : ℕ) (hBox m) := by
  unfold hBox
  exact contDiff_const.mul (contDiff_comp_affScalePt _ _ (contDiff_staircaseH (boxK m)))

private lemma contDiff_uBox (m : ℕ) : ContDiff ℝ (4 : ℕ) (uBox m) := by
  unfold uBox
  exact contDiff_const.mul (contDiff_comp_affScalePt _ _ (contDiff_staircaseU (boxK m)))

private lemma affScalePt_outside_of_subrect {m : ℕ} {p : Euclidean 2}
    (hp : p 0 ≤ boxA m + boxR m / 8 ∨ boxA m + 7 * boxR m / 8 ≤ p 0 ∨
      p 1 ≤ boxR m / 8 ∨ 7 * boxR m / 8 ≤ p 1) :
    (affScalePt (boxA m) (boxR m) p) 0 ≤ 1 / 8 ∨
    7 / 8 ≤ (affScalePt (boxA m) (boxR m) p) 0 ∨
    (affScalePt (boxA m) (boxR m) p) 1 ≤ 1 / 8 ∨
    7 / 8 ≤ (affScalePt (boxA m) (boxR m) p) 1 := by
  have hr := boxR_pos m
  unfold affScalePt
  simp only [planarPt_apply_zero, planarPt_apply_one]
  rcases hp with h | h | h | h
  · exact Or.inl ((div_le_iff₀ hr).mpr (by linarith))
  · exact Or.inr (Or.inl ((le_div_iff₀ hr).mpr (by linarith)))
  · exact Or.inr (Or.inr (Or.inl ((div_le_iff₀ hr).mpr (by linarith))))
  · exact Or.inr (Or.inr (Or.inr ((le_div_iff₀ hr).mpr (by linarith))))

private lemma hBox_zero_outside_subrect (m : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ boxA m + boxR m / 8 ∨ boxA m + 7 * boxR m / 8 ≤ p 0 ∨
      p 1 ≤ boxR m / 8 ∨ 7 * boxR m / 8 ≤ p 1) :
    hBox m p = 0 := by
  unfold hBox
  rw [staircaseH_zero_outside (boxK m) (affScalePt_outside_of_subrect hp), mul_zero]

private lemma uBox_zero_outside_subrect (m : ℕ) {p : Euclidean 2}
    (hp : p 0 ≤ boxA m + boxR m / 8 ∨ boxA m + 7 * boxR m / 8 ≤ p 0 ∨
      p 1 ≤ boxR m / 8 ∨ 7 * boxR m / 8 ≤ p 1) :
    uBox m p = 0 := by
  unfold uBox
  rw [staircaseU_zero_outside (boxK m) (affScalePt_outside_of_subrect hp), mul_zero]

private lemma vanishesThirdPartialsOnRectBdry_uBox (m : ℕ) :
    vanishesThirdPartialsOnRectBdry (boxA m) (boxB m) (boxC m) (boxD m) (uBox m) := by
  have hr := boxR_pos m
  unfold boxB boxC boxD
  apply vanishesThirdPartialsOnRectBdry_of_zero_outside_subrect
    (a' := boxA m + boxR m / 8) (b' := boxA m + 7 * boxR m / 8)
    (c' := boxR m / 8) (d' := 7 * boxR m / 8)
    (by linarith) (by linarith) (by linarith) (by linarith)
  intro p hp
  rcases hp with h | h | h | h
  · exact uBox_zero_outside_subrect m (Or.inl (le_of_lt h))
  · exact uBox_zero_outside_subrect m (Or.inr (Or.inl (le_of_lt h)))
  · exact uBox_zero_outside_subrect m (Or.inr (Or.inr (Or.inl (le_of_lt h))))
  · exact uBox_zero_outside_subrect m (Or.inr (Or.inr (Or.inr (le_of_lt h))))

/-! ### Section 3: Support, Norm Bounds, and `C¹(ℝ²)` Regularity of `glidingHumpF` -/

private def inBox (m : ℕ) (p : Euclidean 2) : Prop :=
  p 0 ∈ Icc (boxA m) (boxB m) ∧ p 1 ∈ Icc 0 (boxR m)

private lemma hBox_eventually_zero_of_not_inBox {m : ℕ} {p : Euclidean 2}
    (hp : ¬ inBox m p) : hBox m =ᶠ[𝓝 p] 0 := by
  let O : Set (Euclidean 2) :=
    {q | q 0 < boxA m + boxR m / 8} ∪ {q | boxA m + 7 * boxR m / 8 < q 0} ∪
      {q | q 1 < boxR m / 8} ∪ {q | 7 * boxR m / 8 < q 1}
  have hO_open : IsOpen O := by
    have hc0 : Continuous (fun q : Euclidean 2 => q 0) :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous
    have hc1 : Continuous (fun q : Euclidean 2 => q 1) :=
      (EuclideanSpace.proj (1 : Fin 2)).continuous
    exact (((isOpen_lt hc0 continuous_const).union (isOpen_lt continuous_const hc0)).union
      (isOpen_lt hc1 continuous_const)).union (isOpen_lt continuous_const hc1)
  have hpO : p ∈ O := by
    have hr := boxR_pos m
    have hb : boxB m = boxA m + boxR m := rfl
    by_contra hnot
    apply hp
    have h1 : ¬ p 0 < boxA m + boxR m / 8 := fun h => hnot (Or.inl (Or.inl (Or.inl h)))
    have h2 : ¬ boxA m + 7 * boxR m / 8 < p 0 := fun h => hnot (Or.inl (Or.inl (Or.inr h)))
    have h3 : ¬ p 1 < boxR m / 8 := fun h => hnot (Or.inl (Or.inr h))
    have h4 : ¬ 7 * boxR m / 8 < p 1 := fun h => hnot (Or.inr h)
    exact ⟨⟨by linarith [not_lt.mp h1], by linarith [not_lt.mp h2]⟩,
      ⟨by linarith [not_lt.mp h3], by linarith [not_lt.mp h4]⟩⟩
  filter_upwards [hO_open.mem_nhds hpO] with q hq
  rcases hq with ((h | h) | h) | h
  · exact hBox_zero_outside_subrect m (Or.inl (le_of_lt h))
  · exact hBox_zero_outside_subrect m (Or.inr (Or.inl (le_of_lt h)))
  · exact hBox_zero_outside_subrect m (Or.inr (Or.inr (Or.inl (le_of_lt h))))
  · exact hBox_zero_outside_subrect m (Or.inr (Or.inr (Or.inr (le_of_lt h))))

private lemma hBox_eq_zero_of_not_inBox {m : ℕ} {p : Euclidean 2} (hp : ¬ inBox m p) :
    hBox m p = 0 :=
  (hBox_eventually_zero_of_not_inBox hp).eq_of_nhds

private lemma fderiv_hBox_eq_zero_of_not_inBox {m : ℕ} {p : Euclidean 2} (hp : ¬ inBox m p) :
    fderiv ℝ (hBox m) p = 0 := by
  have heq := hBox_eventually_zero_of_not_inBox hp
  rw [heq.fderiv_eq]
  exact fderiv_const_apply (0 : ℝ)

private lemma norm_bounds_of_inBox {m : ℕ} {p : Euclidean 2} (hp : inBox m p) :
    (1 / 2 : ℝ) ^ (m + 1) ≤ ‖p‖ ∧ 4 * boxR m ≤ ‖p‖ ∧ ‖p‖ ≤ (1 / 2 : ℝ) ^ m := by
  rcases hp with ⟨⟨hx1, hx2⟩, ⟨hy1, hy2⟩⟩
  have hx_norm : |p 0| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le p 0
  have ha_pos := boxA_pos m
  have ha_le : boxA m ≤ ‖p‖ := by
    have hp0_abs : boxA m ≤ |p 0| := hx1.trans (le_abs_self _)
    exact hp0_abs.trans hx_norm
  have h1 : (1 / 2 : ℝ) ^ (m + 1) ≤ ‖p‖ := ha_le
  have h2 : 4 * boxR m ≤ ‖p‖ := by rw [← boxA_eq_four_boxR m]; exact ha_le
  have hp_decomp : p = p 0 • coordinateVector 2 0 + p 1 • coordinateVector 2 1 := by
    ext i
    fin_cases i <;> simp [coordinateVector, EuclideanSpace.basisFun_apply]
  have he0_norm : ‖coordinateVector 2 0‖ ≤ 1 := by
    rw [show coordinateVector 2 0 = EuclideanSpace.single (0 : Fin 2) (1 : ℝ) by
      ext i; fin_cases i <;> simp [coordinateVector, EuclideanSpace.basisFun_apply]]
    simp
  have he1_norm : ‖coordinateVector 2 1‖ ≤ 1 := by
    rw [show coordinateVector 2 1 = EuclideanSpace.single (1 : Fin 2) (1 : ℝ) by
      ext i; fin_cases i <;> simp [coordinateVector, EuclideanSpace.basisFun_apply]]
    simp
  have hp_upper : ‖p‖ ≤ |p 0| + |p 1| := by
    calc
      ‖p‖ = ‖p 0 • coordinateVector 2 0 + p 1 • coordinateVector 2 1‖ := by rw [← hp_decomp]
      _ ≤ ‖p 0 • coordinateVector 2 0‖ + ‖p 1 • coordinateVector 2 1‖ := norm_add_le _ _
      _ = |p 0| * ‖coordinateVector 2 0‖ + |p 1| * ‖coordinateVector 2 1‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |p 0| * 1 + |p 1| * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left he0_norm (abs_nonneg _))
            (mul_le_mul_of_nonneg_left he1_norm (abs_nonneg _))
      _ = |p 0| + |p 1| := by ring
  have h3 : ‖p‖ ≤ (1 / 2 : ℝ) ^ m := by
    have hx_nn : 0 ≤ p 0 := ha_pos.le.trans hx1
    have hsum : |p 0| + |p 1| ≤ boxB m + boxR m := by
      rw [abs_of_nonneg hx_nn, abs_of_nonneg hy1]
      exact add_le_add hx2 hy2
    have hpow : boxB m + boxR m ≤ (1 / 2 : ℝ) ^ m := by
      unfold boxB
      rw [boxA_eq_four_boxR m]
      unfold boxR
      rw [show m + 3 = m + 3 by rfl, pow_add]
      have hp_nn : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ m := by positivity
      norm_num
      linarith
    exact hp_upper.trans (hsum.trans hpow)
  exact ⟨h1, h2, h3⟩

private lemma abs_hBox_le_boxR (m : ℕ) (p : Euclidean 2) :
    |hBox m p| ≤ boxR m := by
  unfold hBox
  rw [abs_mul, abs_of_pos (boxR_pos m)]
  calc
    boxR m * |staircaseH (boxK m) (affScalePt (boxA m) (boxR m) p)|
        ≤ boxR m * 1 :=
          mul_le_mul_of_nonneg_left (abs_staircaseH_le_one (boxK m) _) (boxR_pos m).le
    _ = boxR m := mul_one _

private lemma norm_fderiv_hBox_le_one (m : ℕ) (p : Euclidean 2) :
    ‖fderiv ℝ (hBox m) p‖ ≤ 1 := by
  have hr_ne : boxR m ≠ 0 := ne_of_gt (boxR_pos m)
  have hH_diff : Differentiable ℝ (staircaseH (boxK m)) :=
    diff_of_c1_b1 (r := 3) (contDiff_staircaseH (boxK m))
  have hh_diff : Differentiable ℝ (hBox m) :=
    diff_of_c1_b1 (r := 3) (contDiff_hBox m)
  have hcomp_diff : Differentiable ℝ (fun q =>
      staircaseH (boxK m) (affScalePt (boxA m) (boxR m) q)) :=
    diff_of_c1_b1 (r := 3) (contDiff_comp_affScalePt _ _ (contDiff_staircaseH (boxK m)))
  have hdx : planarDx (hBox m) p =
      planarDx (staircaseH (boxK m)) (affScalePt (boxA m) (boxR m) p) := by
    have hfn : planarDx (hBox m) =
        planarDx (fun q => boxR m * staircaseH (boxK m) (affScalePt (boxA m) (boxR m) q)) := rfl
    rw [hfn, planarDx_const_mul_fn (boxR m) hcomp_diff,
      planarDx_comp_affScalePt (boxA m) (boxR m) hH_diff]
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul]
  have hdy : planarDy (hBox m) p =
      planarDy (staircaseH (boxK m)) (affScalePt (boxA m) (boxR m) p) := by
    have hfn : planarDy (hBox m) =
        planarDy (fun q => boxR m * staircaseH (boxK m) (affScalePt (boxA m) (boxR m) q)) := rfl
    rw [hfn, planarDy_const_mul_fn (boxR m) hcomp_diff,
      planarDy_comp_affScalePt (boxA m) (boxR m) hH_diff]
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ hr_ne, one_mul]
  calc
    ‖fderiv ℝ (hBox m) p‖ ≤ |planarDx (hBox m) p| + |planarDy (hBox m) p| :=
      norm_fderiv_le_abs_planarDx_add_planarDy (hh_diff p)
    _ = |planarDx (staircaseH (boxK m)) (affScalePt (boxA m) (boxR m) p)| +
          |planarDy (staircaseH (boxK m)) (affScalePt (boxA m) (boxR m) p)| := by
        rw [hdx, hdy]
    _ ≤ 1 / 2 + 1 / 2 := add_le_add
        (abs_planarDx_staircaseH_le_half (boxK m) _)
        (abs_planarDy_staircaseH_le_half (boxK m) _)
    _ = 1 := by norm_num

private lemma glidingHumpF_eq_single_of_mem_x {k : ℕ} {p : Euclidean 2}
    (hx : p 0 ∈ Icc (boxA k) (boxB k)) :
    glidingHumpF p = boxEps k * hBox k p := by
  unfold glidingHumpF
  apply tsum_eq_single k
  intro m hmk
  have hnot : ¬ inBox m p := fun hm => disjoint_box_x hmk hm.1 hx
  rw [hBox_eq_zero_of_not_inBox hnot, mul_zero]

private lemma glidingHumpF_eq_zero_of_forall_not_inBox {p : Euclidean 2}
    (h : ∀ m : ℕ, ¬ inBox m p) : glidingHumpF p = 0 := by
  unfold glidingHumpF
  rw [tsum_eq_single 0]
  · rw [hBox_eq_zero_of_not_inBox (h 0), mul_zero]
  · intro m _
    rw [hBox_eq_zero_of_not_inBox (h m), mul_zero]

private lemma glidingHumpF_local (k : ℕ) (x : ℝ) (hx : x ∈ Icc (boxA k) (boxB k))
    (y : ℝ) (_hy : y ∈ Icc (boxC k) (boxD k)) :
    glidingHumpF (planarPt x y) = boxEps k * hBox k (planarPt x y) := by
  apply glidingHumpF_eq_single_of_mem_x
  simpa only [planarPt_apply_zero] using hx

private lemma half_pow_le_inv_succ (n : ℕ) :
    (1 / 2 : ℝ) ^ (n + 1) ≤ 1 / ((n : ℝ) + 1) := by
  have hpow : (n : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1) := by
    induction n with
    | zero => norm_num
    | succ k ih =>
        push_cast
        rw [pow_succ]
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ (by norm_num)
        linarith
  rw [one_div_pow]
  exact one_div_le_one_div_of_le (by positivity) hpow

private lemma exists_half_pow_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
  refine ⟨k + 1, ?_⟩
  have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlt : 1 / ((k : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hk_pos]
    have hk' : 1 < (k : ℝ) * ε := (div_lt_iff₀ hε).mp hk
    linarith
  exact (half_pow_le_inv_succ k).trans_lt hlt

private lemma glidingHumpF_eventuallyEq_sum_of_ne_zero {p : Euclidean 2} (hp : p ≠ 0) :
    ∃ N : ℕ,
      glidingHumpF =ᶠ[𝓝 p] fun q => ∑ m ∈ Finset.range N, boxEps m * hBox m q := by
  have hp_pos : 0 < ‖p‖ := norm_pos_iff.mpr hp
  obtain ⟨N, hN⟩ := exists_half_pow_lt (half_pos hp_pos)
  refine ⟨N, ?_⟩
  filter_upwards [Metric.ball_mem_nhds p (half_pos hp_pos)] with q hq
  have hq_norm : ‖p‖ / 2 < ‖q‖ := by
    rw [Metric.mem_ball, dist_eq_norm] at hq
    have htri : ‖p‖ ≤ ‖q‖ + ‖p - q‖ := norm_le_insert' p q
    rw [norm_sub_rev] at htri
    linarith
  have hzero_ge : ∀ m : ℕ, N ≤ m → boxEps m * hBox m q = 0 := by
    intro m hm
    have hnot : ¬ inBox m q := by
      intro hin
      have hup := (norm_bounds_of_inBox hin).2.2
      have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      linarith
    rw [hBox_eq_zero_of_not_inBox hnot, mul_zero]
  unfold glidingHumpF
  by_cases hex : ∃ m₀ : ℕ, inBox m₀ q
  · rcases hex with ⟨m₀, hm₀⟩
    have hm₀_lt : m₀ < N := by
      by_contra hge
      have h0 : boxEps m₀ * hBox m₀ q = 0 := hzero_ge m₀ (not_lt.mp hge)
      have hup := (norm_bounds_of_inBox hm₀).2.2
      have hpow : (1 / 2 : ℝ) ^ m₀ ≤ (1 / 2 : ℝ) ^ N :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (not_lt.mp hge)
      linarith
    have htsum : (∑' m : ℕ, boxEps m * hBox m q) = boxEps m₀ * hBox m₀ q := by
      apply tsum_eq_single m₀
      intro m hm
      have hnot : ¬ inBox m q := fun hmq => disjoint_box_x hm hmq.1 hm₀.1
      rw [hBox_eq_zero_of_not_inBox hnot, mul_zero]
    have hfin : (∑ m ∈ Finset.range N, boxEps m * hBox m q) = boxEps m₀ * hBox m₀ q := by
      apply Finset.sum_eq_single m₀
      · intro m _ hm
        have hnot : ¬ inBox m q := fun hmq => disjoint_box_x hm hmq.1 hm₀.1
        rw [hBox_eq_zero_of_not_inBox hnot, mul_zero]
      · intro hnot_mem
        exact False.elim (hnot_mem (Finset.mem_range.mpr hm₀_lt))
    rw [htsum, hfin]
  · have hall : ∀ m : ℕ, ¬ inBox m q := fun m hm => hex ⟨m, hm⟩
    have htsum0 : (∑' m : ℕ, boxEps m * hBox m q) = 0 :=
      glidingHumpF_eq_zero_of_forall_not_inBox hall
    rw [htsum0]
    symm
    apply Finset.sum_eq_zero
    intro m _
    rw [hBox_eq_zero_of_not_inBox (hall m), mul_zero]

private lemma glidingHumpF_zero : glidingHumpF 0 = 0 := by
  apply glidingHumpF_eq_zero_of_forall_not_inBox
  intro m hm
  have ha := boxA_pos m
  have hp0 : (0 : Euclidean 2) 0 = 0 := rfl
  linarith [hm.1.1]

private lemma quotient_glidingHumpF_le_inv_succ {M : ℕ} {q : Euclidean 2}
    (hq : ‖q‖ < (1 / 2 : ℝ) ^ M) :
    ‖q‖⁻¹ * |glidingHumpF q| ≤ 1 / ((M : ℝ) + 1) := by
  by_cases hex : ∃ m₀ : ℕ, inBox m₀ q
  · rcases hex with ⟨m₀, hm₀⟩
    obtain ⟨hlow, h4r, _⟩ := norm_bounds_of_inBox hm₀
    have hM_le : M ≤ m₀ := by
      by_contra hlt
      have hm_succ : m₀ + 1 ≤ M := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlt)
      have hpow : (1 / 2 : ℝ) ^ M ≤ (1 / 2 : ℝ) ^ (m₀ + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_succ
      linarith
    have hval := glidingHumpF_eq_single_of_mem_x hm₀.1
    have hq_pos : 0 < ‖q‖ := lt_of_lt_of_le (by positivity) hlow
    have hratio : ‖q‖⁻¹ * boxR m₀ ≤ 1 := by
      rw [inv_mul_le_iff₀ hq_pos]
      linarith [boxR_pos m₀]
    rw [hval, abs_mul, abs_of_pos (boxEps_pos m₀)]
    calc
      ‖q‖⁻¹ * (boxEps m₀ * |hBox m₀ q|)
          = boxEps m₀ * (‖q‖⁻¹ * |hBox m₀ q|) := by ring
      _ ≤ boxEps m₀ * (‖q‖⁻¹ * boxR m₀) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (abs_hBox_le_boxR m₀ q) (inv_nonneg.mpr hq_pos.le))
            (boxEps_pos m₀).le
      _ ≤ boxEps m₀ * 1 := mul_le_mul_of_nonneg_left hratio (boxEps_pos m₀).le
      _ = 1 / ((m₀ : ℝ) + 1) := by unfold boxEps; ring
      _ ≤ 1 / ((M : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hM_le 1)
  · have hall : ∀ m : ℕ, ¬ inBox m q := fun m hm => hex ⟨m, hm⟩
    rw [glidingHumpF_eq_zero_of_forall_not_inBox hall, abs_zero, mul_zero]
    positivity

private lemma hasFDerivAt_glidingHumpF_zero :
    HasFDerivAt (𝕜 := ℝ) glidingHumpF (0 : Euclidean 2 →L[ℝ] ℝ) 0 := by
  rw [hasFDerivAt_iff_tendsto]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hM_lt : 1 / ((M : ℝ) + 1) < ε := by
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    rw [div_lt_iff₀ hpos]
    have h1 : 1 < (M : ℝ) * ε := (div_lt_iff₀ hε).mp hM
    linarith
  filter_upwards [Metric.ball_mem_nhds (0 : Euclidean 2)
    (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ M)] with q hq
  rw [Metric.mem_ball, dist_zero_right] at hq
  simp only [sub_zero, zero_apply, glidingHumpF_zero,
    Real.norm_eq_abs, dist_zero_right]
  have hle := quotient_glidingHumpF_le_inv_succ hq
  rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg q)) (abs_nonneg _))]
  exact hle.trans_lt hM_lt

private lemma diff_and_contAt_fderiv_of_ne_zero {p : Euclidean 2} (hp : p ≠ 0) :
    DifferentiableAt ℝ glidingHumpF p ∧ ContinuousAt (fderiv ℝ glidingHumpF) p := by
  obtain ⟨N, heq⟩ := glidingHumpF_eventuallyEq_sum_of_ne_zero hp
  let S : Euclidean 2 → ℝ := fun q => ∑ m ∈ Finset.range N, boxEps m * hBox m q
  have hS_c4 : ContDiff ℝ (4 : ℕ) S :=
    ContDiff.sum fun m _ => contDiff_const.mul (contDiff_hBox m)
  have hS_c1 : ContDiff ℝ 1 S := hS_c4.of_le (by norm_cast)
  obtain ⟨hS_diff, hS_fderiv_cont⟩ := contDiff_one_iff_fderiv.mp hS_c1
  have hhas : HasFDerivAt glidingHumpF (fderiv ℝ S p) p :=
    (hS_diff p).hasFDerivAt.congr_of_eventuallyEq heq
  have hfderiv_eq : fderiv ℝ glidingHumpF =ᶠ[𝓝 p] fderiv ℝ S := by
    filter_upwards [heq.eventuallyEq_nhds] with q hq
    exact hq.fderiv_eq
  exact ⟨hhas.differentiableAt, (hS_fderiv_cont.continuousAt).congr_of_eventuallyEq hfderiv_eq⟩

private lemma norm_fderiv_glidingHumpF_le_inv_succ {M : ℕ} {q : Euclidean 2}
    (hq : ‖q‖ < (1 / 2 : ℝ) ^ M) :
    ‖fderiv ℝ glidingHumpF q‖ ≤ 1 / ((M : ℝ) + 1) := by
  by_cases hq0 : q = 0
  · subst hq0
    rw [(hasFDerivAt_glidingHumpF_zero).fderiv, norm_zero]
    positivity
  · obtain ⟨N, heq⟩ := glidingHumpF_eventuallyEq_sum_of_ne_zero hq0
    have hf_eq : fderiv ℝ glidingHumpF q =
        ∑ m ∈ Finset.range N, boxEps m • fderiv ℝ (hBox m) q := by
      rw [heq.fderiv_eq]
      have hfn : (fun p' => ∑ m ∈ Finset.range N, boxEps m * hBox m p') =
          ∑ m ∈ Finset.range N, fun p' => boxEps m * hBox m p' := by
        funext p'; simp [Finset.sum_apply]
      rw [hfn]
      exact (HasFDerivAt.sum fun m _ =>
        ((diff_of_c1_b1 (r := 3) (contDiff_hBox m) q).hasFDerivAt.const_mul (boxEps m))).fderiv
    rw [hf_eq]
    by_cases hex : ∃ m₀ : ℕ, inBox m₀ q
    · rcases hex with ⟨m₀, hm₀⟩
      have hM_le : M ≤ m₀ := by
        obtain ⟨hlow, _, _⟩ := norm_bounds_of_inBox hm₀
        by_contra hlt
        have hm_succ : m₀ + 1 ≤ M := Nat.succ_le_of_lt (Nat.lt_of_not_ge hlt)
        have hpow : (1 / 2 : ℝ) ^ M ≤ (1 / 2 : ℝ) ^ (m₀ + 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm_succ
        linarith
      by_cases hm₀_mem : m₀ ∈ Finset.range N
      · rw [Finset.sum_eq_single m₀]
        · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (boxEps_pos m₀)]
          calc
            boxEps m₀ * ‖fderiv ℝ (hBox m₀) q‖ ≤ boxEps m₀ * 1 :=
              mul_le_mul_of_nonneg_left (norm_fderiv_hBox_le_one m₀ q) (boxEps_pos m₀).le
            _ = 1 / ((m₀ : ℝ) + 1) := by unfold boxEps; ring
            _ ≤ 1 / ((M : ℝ) + 1) :=
              one_div_le_one_div_of_le (by positivity)
                (by exact_mod_cast Nat.add_le_add_right hM_le 1)
        · intro m _ hm_ne
          have hnot : ¬ inBox m q := fun hmq => disjoint_box_x hm_ne hmq.1 hm₀.1
          rw [fderiv_hBox_eq_zero_of_not_inBox hnot, smul_zero]
        · intro hnot_mem
          exact False.elim (hnot_mem hm₀_mem)
      · have hsum0 : (∑ m ∈ Finset.range N, boxEps m • fderiv ℝ (hBox m) q) = 0 := by
          apply Finset.sum_eq_zero
          intro m hm
          have hm_ne : m ≠ m₀ := fun h => hm₀_mem (h ▸ hm)
          have hnot : ¬ inBox m q := fun hmq => disjoint_box_x hm_ne hmq.1 hm₀.1
          rw [fderiv_hBox_eq_zero_of_not_inBox hnot, smul_zero]
        rw [hsum0, norm_zero]
        positivity
    · have hall : ∀ m : ℕ, ¬ inBox m q := fun m hm => hex ⟨m, hm⟩
      have hsum0 : (∑ m ∈ Finset.range N, boxEps m • fderiv ℝ (hBox m) q) = 0 := by
        apply Finset.sum_eq_zero
        intro m _
        rw [fderiv_hBox_eq_zero_of_not_inBox (hall m), smul_zero]
      rw [hsum0, norm_zero]
      positivity

private lemma contDiff_glidingHumpF : ContDiff ℝ 1 glidingHumpF := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun p => ?_, continuous_iff_continuousAt.mpr fun p => ?_⟩
  · by_cases hp : p = 0
    · subst hp; exact (hasFDerivAt_glidingHumpF_zero).differentiableAt
    · exact (diff_and_contAt_fderiv_of_ne_zero hp).1
  · by_cases hp : p = 0
    · subst hp
      rw [Metric.continuousAt_iff']
      intro ε hε
      obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
      have hM_lt : 1 / ((M : ℝ) + 1) < ε := by
        have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
        rw [div_lt_iff₀ hpos]
        have h1 : 1 < (M : ℝ) * ε := (div_lt_iff₀ hε).mp hM
        linarith
      filter_upwards [Metric.ball_mem_nhds (0 : Euclidean 2)
        (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ M)] with q hq
      rw [Metric.mem_ball, dist_zero_right] at hq
      rw [(hasFDerivAt_glidingHumpF_zero).fderiv, dist_zero_right]
      exact (norm_fderiv_glidingHumpF_le_inv_succ hq).trans_lt hM_lt
    · exact (diff_and_contAt_fderiv_of_ne_zero hp).2

/-! ### Section 4: Rescaled Spin-3 `L¹` and Pairing Estimates and `¬ pma10_43_contract` -/

private lemma third_partials_uBox (m : ℕ) :
    let U := staircaseU (boxK m)
    let a := boxA m
    let r := boxR m
    planarDx (planarDx (planarDx (uBox m))) =
      (fun p => planarDx (planarDx (planarDx U)) (affScalePt a r p)) ∧
    planarDx (planarDx (planarDy (uBox m))) =
      (fun p => planarDx (planarDx (planarDy U)) (affScalePt a r p)) ∧
    planarDx (planarDy (planarDy (uBox m))) =
      (fun p => planarDx (planarDy (planarDy U)) (affScalePt a r p)) ∧
    planarDy (planarDy (planarDy (uBox m))) =
      (fun p => planarDy (planarDy (planarDy U)) (affScalePt a r p)) := by
  intro U a r
  have hr_ne : r ≠ 0 := ne_of_gt (boxR_pos m)
  have hU4 : ContDiff ℝ (4 : ℕ) U := contDiff_staircaseU (boxK m)
  have hU_d := diff_of_c1_b1 (r := 3) hU4
  have hUx_c3 := contDiff_planarDx_b1 (r := 3) hU4
  have hUy_c3 := contDiff_planarDy_b1 (r := 3) hU4
  have hUx_d := diff_of_c1_b1 (r := 2) hUx_c3
  have hUy_d := diff_of_c1_b1 (r := 2) hUy_c3
  have hUxx_c2 := contDiff_planarDx_b1 (r := 2) hUx_c3
  have hUxy_c2 := contDiff_planarDx_b1 (r := 2) hUy_c3
  have hUyy_c2 := contDiff_planarDy_b1 (r := 2) hUy_c3
  have hUxx_d := diff_of_c1_b1 (r := 1) hUxx_c2
  have hUxy_d := diff_of_c1_b1 (r := 1) hUxy_c2
  have hUyy_d := diff_of_c1_b1 (r := 1) hUyy_c2
  have hcomp_U := diff_of_c1_b1 (r := 3) (contDiff_comp_affScalePt a r hU4)
  have hcomp_Ux := diff_of_c1_b1 (r := 2) (contDiff_comp_affScalePt a r hUx_c3)
  have hcomp_Uy := diff_of_c1_b1 (r := 2) (contDiff_comp_affScalePt a r hUy_c3)
  have hcomp_Uxx := diff_of_c1_b1 (r := 1) (contDiff_comp_affScalePt a r hUxx_c2)
  have hcomp_Uxy := diff_of_c1_b1 (r := 1) (contDiff_comp_affScalePt a r hUxy_c2)
  have hcomp_Uyy := diff_of_c1_b1 (r := 1) (contDiff_comp_affScalePt a r hUyy_c2)
  have h1x : planarDx (uBox m) = fun p => r ^ 3 * (r⁻¹ * planarDx U (affScalePt a r p)) := by
    change planarDx (fun p => r ^ 3 * U (affScalePt a r p)) = _
    rw [planarDx_const_mul_fn (r ^ 3) hcomp_U, planarDx_comp_affScalePt a r hU_d]
  have h1y : planarDy (uBox m) = fun p => r ^ 3 * (r⁻¹ * planarDy U (affScalePt a r p)) := by
    change planarDy (fun p => r ^ 3 * U (affScalePt a r p)) = _
    rw [planarDy_const_mul_fn (r ^ 3) hcomp_U, planarDy_comp_affScalePt a r hU_d]
  have h1x' : planarDx (uBox m) = fun p => (r ^ 3 * r⁻¹) * planarDx U (affScalePt a r p) := by
    rw [h1x]; funext p; ring
  have h1y' : planarDy (uBox m) = fun p => (r ^ 3 * r⁻¹) * planarDy U (affScalePt a r p) := by
    rw [h1y]; funext p; ring
  have h2xx : planarDx (planarDx (uBox m)) =
      fun p => (r ^ 3 * r⁻¹ * r⁻¹) * planarDx (planarDx U) (affScalePt a r p) := by
    rw [h1x', planarDx_const_mul_fn _ hcomp_Ux, planarDx_comp_affScalePt a r hUx_d]
    funext p; ring
  have h2xy : planarDx (planarDy (uBox m)) =
      fun p => (r ^ 3 * r⁻¹ * r⁻¹) * planarDx (planarDy U) (affScalePt a r p) := by
    rw [h1y', planarDx_const_mul_fn _ hcomp_Uy, planarDx_comp_affScalePt a r hUy_d]
    funext p; ring
  have h2yy : planarDy (planarDy (uBox m)) =
      fun p => (r ^ 3 * r⁻¹ * r⁻¹) * planarDy (planarDy U) (affScalePt a r p) := by
    rw [h1y', planarDy_const_mul_fn _ hcomp_Uy, planarDy_comp_affScalePt a r hUy_d]
    funext p; ring
  have hcancel : r ^ 3 * r⁻¹ * r⁻¹ * r⁻¹ = 1 := by field_simp [hr_ne]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h2xx, planarDx_const_mul_fn _ hcomp_Uxx, planarDx_comp_affScalePt a r hUxx_d]
    funext p; dsimp only; rw [← mul_assoc, hcancel, one_mul]
  · rw [h2xy, planarDx_const_mul_fn _ hcomp_Uxy, planarDx_comp_affScalePt a r hUxy_d]
    funext p; dsimp only; rw [← mul_assoc, hcancel, one_mul]
  · rw [h2yy, planarDx_const_mul_fn _ hcomp_Uyy, planarDx_comp_affScalePt a r hUyy_d]
    funext p; dsimp only; rw [← mul_assoc, hcancel, one_mul]
  · rw [h2yy, planarDy_const_mul_fn _ hcomp_Uyy, planarDy_comp_affScalePt a r hUyy_d]
    funext p; dsimp only; rw [← mul_assoc, hcancel, one_mul]

private lemma spin3_l1_uBox_le (m : ℕ) :
    (∫ y in boxC m..boxD m, ∫ x in boxA m..boxB m,
      (|spin3A1 (uBox m) (planarPt x y)| + |spin3A2 (uBox m) (planarPt x y)|)) ≤
      (boxR m) ^ 2 := by
  obtain ⟨hxxx, hxxy, hxyy, hyyy⟩ := third_partials_uBox m
  have hpt : ∀ p : Euclidean 2,
      |spin3A1 (uBox m) p| + |spin3A2 (uBox m) p| =
        |spin3A1 (staircaseU (boxK m)) (affScalePt (boxA m) (boxR m) p)| +
          |spin3A2 (staircaseU (boxK m)) (affScalePt (boxA m) (boxR m) p)| := by
    intro p
    unfold spin3A1 spin3A2
    rw [hxxx, hxxy, hxyy, hyyy]
  simp_rw [hpt]
  unfold boxB boxC boxD
  rw [integral_2d_affScalePt
    (fun q => |spin3A1 (staircaseU (boxK m)) q| + |spin3A2 (staircaseU (boxK m)) q|)
    (boxA m) (boxR m) (boxR_pos m)]
  calc
    (boxR m) ^ 2 *
        (∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1,
          (|spin3A1 (staircaseU (boxK m)) (planarPt u v)| +
            |spin3A2 (staircaseU (boxK m)) (planarPt u v)|))
        ≤ (boxR m) ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (spin3_l1_staircaseU_le_one (boxK m)) (sq_nonneg _)
    _ = (boxR m) ^ 2 := mul_one _

private lemma pairing_uBox_ge (m : ℕ) :
    (boxR m) ^ 2 * (((m : ℝ) + 1) ^ 2 / 4096) ≤
      ∫ y in boxC m..boxD m, ∫ x in boxA m..boxB m,
        hBox m (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (uBox m)))) (planarPt x y) := by
  obtain ⟨_, _, hxyy, _⟩ := third_partials_uBox m
  have hr_ne : boxR m ≠ 0 := ne_of_gt (boxR_pos m)
  have hUxyy_d : Differentiable ℝ
      (planarDx (planarDy (planarDy (staircaseU (boxK m))))) :=
    diff_of_c1_b1 (r := 0) (contDiff_planarDx_b1 (r := 1)
      (contDiff_planarDy_b1 (r := 2) (contDiff_planarDy_b1 (r := 3)
        (contDiff_staircaseU (boxK m)))))
  have hdxxyy : planarDx (planarDx (planarDy (planarDy (uBox m)))) =
      fun p => (boxR m)⁻¹ *
        planarDx (planarDx (planarDy (planarDy (staircaseU (boxK m)))))
          (affScalePt (boxA m) (boxR m) p) := by
    rw [hxyy, planarDx_comp_affScalePt (boxA m) (boxR m) hUxyy_d]
  have hpt : ∀ p : Euclidean 2,
      hBox m p * planarDx (planarDx (planarDy (planarDy (uBox m)))) p =
        staircaseH (boxK m) (affScalePt (boxA m) (boxR m) p) *
          planarDx (planarDx (planarDy (planarDy (staircaseU (boxK m)))))
            (affScalePt (boxA m) (boxR m) p) := by
    intro p
    rw [hdxxyy]
    unfold hBox
    dsimp only
    have hmul : boxR m * (boxR m)⁻¹ = 1 := mul_inv_cancel₀ hr_ne
    calc
      (boxR m * staircaseH (boxK m) (affScalePt (boxA m) (boxR m) p)) *
          ((boxR m)⁻¹ * planarDx (planarDx (planarDy (planarDy (staircaseU (boxK m)))))
            (affScalePt (boxA m) (boxR m) p))
          = (boxR m * (boxR m)⁻¹) *
            (staircaseH (boxK m) (affScalePt (boxA m) (boxR m) p) *
              planarDx (planarDx (planarDy (planarDy (staircaseU (boxK m)))))
                (affScalePt (boxA m) (boxR m) p)) := by ring
      _ = staircaseH (boxK m) (affScalePt (boxA m) (boxR m) p) *
            planarDx (planarDx (planarDy (planarDy (staircaseU (boxK m)))))
              (affScalePt (boxA m) (boxR m) p) := by rw [hmul, one_mul]
  simp_rw [hpt]
  unfold boxB boxC boxD
  rw [integral_2d_affScalePt
    (fun q => staircaseH (boxK m) q *
      planarDx (planarDx (planarDy (planarDy (staircaseU (boxK m))))) q)
    (boxA m) (boxR m) (boxR_pos m)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  have hlb := pairing_staircase_lower_bound (boxM m)
  have hm_eq : ((boxM m : ℝ) + 1) / 4096 = ((m : ℝ) + 1) ^ 2 / 4096 := by
    unfold boxM
    push_cast
    ring
  unfold boxK
  linarith

private lemma gliding_hump_divergence (M : ℝ) (_hM0 : 0 ≤ M) :
    ∃ k : ℕ,
      M * (∫ y in boxC k..boxD k, ∫ x in boxA k..boxB k,
        (|spin3A1 (uBox k) (planarPt x y)| + |spin3A2 (uBox k) (planarPt x y)|)) <
      2 * boxEps k * |∫ y in boxC k..boxD k, ∫ x in boxA k..boxB k,
        hBox k (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (uBox k)))) (planarPt x y)| := by
  obtain ⟨k, hk⟩ := exists_nat_gt (2048 * M)
  refine ⟨k, ?_⟩
  have hr2_pos : 0 < (boxR k) ^ 2 := sq_pos_of_pos (boxR_pos k)
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hlhs : M * (∫ y in boxC k..boxD k, ∫ x in boxA k..boxB k,
      (|spin3A1 (uBox k) (planarPt x y)| + |spin3A2 (uBox k) (planarPt x y)|)) ≤
      M * (boxR k) ^ 2 :=
    mul_le_mul_of_nonneg_left (spin3_l1_uBox_le k) _hM0
  have hstrict : M * (boxR k) ^ 2 < (((k : ℝ) + 1) / 2048) * (boxR k) ^ 2 := by
    apply mul_lt_mul_of_pos_right _ hr2_pos
    linarith
  have halg : (((k : ℝ) + 1) / 2048) * (boxR k) ^ 2 =
      2 * boxEps k * ((boxR k) ^ 2 * (((k : ℝ) + 1) ^ 2 / 4096)) := by
    unfold boxEps
    field_simp [ne_of_gt hk1_pos]
    ring
  have hpair_ge := pairing_uBox_ge k
  have hpair_abs : (boxR k) ^ 2 * (((k : ℝ) + 1) ^ 2 / 4096) ≤
      |∫ y in boxC k..boxD k, ∫ x in boxA k..boxB k,
        hBox k (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (uBox k)))) (planarPt x y)| :=
    hpair_ge.trans (le_abs_self _)
  have hrhs : 2 * boxEps k * ((boxR k) ^ 2 * (((k : ℝ) + 1) ^ 2 / 4096)) ≤
      2 * boxEps k * |∫ y in boxC k..boxD k, ∫ x in boxA k..boxB k,
        hBox k (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (uBox k)))) (planarPt x y)| :=
    mul_le_mul_of_nonneg_left hpair_abs (by have := boxEps_pos k; positivity)
  linarith

/-- **Unconditional Disproof of `pma10_43_contract` (Rudin PMA Theorem 10.43, `C²` Clause):**
The printed `C²` vector-potential assertion in `pma10_43_contract` is false: the global
`C¹(ℝ²)` gliding-hump datum `glidingHumpF` built from the 3-ray stopped-martingale spline
staircase possesses no `C²` planar divergence solution on `ℝ²`, hence its divergence-free
vertical lift `verticalField glidingHumpF ∈ C¹(ℝ³; ℝ³)` possesses no `C²` curl potential on `ℝ³`. -/
theorem not_pma10_43_contract : ¬ pma10_43_contract :=
  not_pma10_43_contract_of_spin3_gliding_hump
    (A := 0) (B := 1) (C := 0) (D := 1)
    contDiff_glidingHumpF
    boxes_in_unit_square
    boxEps_pos
    contDiff_uBox
    vanishesThirdPartialsOnRectBdry_uBox
    glidingHumpF_local
    gliding_hump_divergence

end Rudin.PMA.Chapter10

/-! Verify module ownership and standard foundations for all declarations in this module. -/
run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.Research.Stage4B1Disproof
    #[`Rudin.PMA.Chapter10.not_pma10_43_contract]
