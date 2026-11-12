import Rudin.Research.PMA1043Stage4B1

/-!
# Stage 4 Branch B1 — 1D Polynomial-Spline Antiperiodic Waves and Plateau Cutoffs

This module constructs the closed-form 1D degree-9 clamped polynomial-spline
building blocks for the 3-ray stopped-martingale witness `(Ũ_K, h̃_K)`:

1. `smoothstep9`: degree-9 monotone transition spline clamped to `0` on `(-∞, 0]`
   and `1` on `[1, ∞)`, proved `ContDiff ℝ (4 : ℕ)` via explicit derivatives up to
   order `4` (`clampSpline`).
2. `boxCutoff1D`: smooth `C⁴` outer cutoff supported in `[1/8, 7/8]` and identically
   `1` on `[1/4, 3/4]`.
3. `etaWave δ`: 1-periodic `C⁴` plateau cutoff supported in `(δ/2, 1/2 - δ/2) + ℤ`
   and identically `1` on `[δ, 1/2 - δ] + ℤ`.
4. `tauDerivWave δ`, `tauWave δ`, `gammaDerivWave δ`, `gammaWave δ`: `(1/2)`-antiperiodic
   `C⁴` spline wave and its three `(1/2)`-antiperiodic primitives satisfying
   `Γ_δ' = gammaDerivWave δ`, `Γ_δ'' = tauWave δ`, `Γ_δ''' = tauDerivWave δ`,
   the pointwise stopping identity `etaWave δ t * tauDerivWave δ t = etaWave δ t`,
   sharp `L^∞` bounds (`1`, `1/4`, `1/16`, `1/64`), and plateau `L²` lower bounds.
-/

noncomputable section
set_option autoImplicit false

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators Interval

namespace Rudin.PMA.Chapter10

/-! ### Section 1: Clamped Spline Gluing and Degree-9 Smoothstep -/

/-- Clamps a polynomial profile `P` on `[0, 1]` to `cL` on `(-∞, 0]` and `cR` on `(1, ∞)`. -/
def clampSpline (cL cR : ℝ) (P : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ≤ 0 then cL else if u ≤ 1 then P u else cR

lemma clampSpline_of_le_zero (cL cR : ℝ) (P : ℝ → ℝ) {u : ℝ} (hu : u ≤ 0) :
    clampSpline cL cR P u = cL := by
  simp [clampSpline, hu]

lemma clampSpline_of_one_le (cL cR : ℝ) (P : ℝ → ℝ) (hP1 : P 1 = cR) {u : ℝ} (hu : 1 ≤ u) :
    clampSpline cL cR P u = cR := by
  unfold clampSpline
  have hnot0 : ¬ u ≤ 0 := by linarith
  split_ifs with h1
  · have hu1 : u = 1 := le_antisymm h1 hu
    rw [hu1, hP1]
  · rfl

lemma clampSpline_of_mem_Icc (cL cR : ℝ) (P : ℝ → ℝ) (hP0 : P 0 = cL)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    clampSpline cL cR P u = P u := by
  unfold clampSpline
  split_ifs with h0
  · have hu : u = 0 := le_antisymm h0 hu0
    rw [hu, hP0]
  · rfl

lemma continuous_clampSpline {cL cR : ℝ} {P : ℝ → ℝ}
    (hP : Continuous P) (hP0 : P 0 = cL) (hP1 : P 1 = cR) :
    Continuous (clampSpline cL cR P) := by
  have hR : Continuous (fun u : ℝ => if u ≤ 1 then P u else cR) :=
    continuous_if_le continuous_id continuous_const hP.continuousOn continuousOn_const
      (fun u hu => by simp [hu, hP1])
  exact continuous_if_le continuous_id continuous_const continuousOn_const hR.continuousOn
    (fun u hu => by
      have hu0 : u = 0 := hu
      subst hu0
      simp [hP0])

private lemma hasDerivAt_of_Iic_Ici {f : ℝ → ℝ} {d x₀ : ℝ}
    (hL : HasDerivWithinAt f d (Iic x₀) x₀)
    (hR : HasDerivWithinAt f d (Ici x₀) x₀) :
    HasDerivAt f d x₀ := by
  have hunion := hL.hasFDerivWithinAt.union hR.hasFDerivWithinAt
  rw [Iic_union_Ici, hasFDerivWithinAt_univ] at hunion
  simpa using hunion.hasDerivAt

lemma hasDerivAt_clampSpline {cL cR : ℝ} {P P' : ℝ → ℝ}
    (hP : ∀ u : ℝ, HasDerivAt P (P' u) u)
    (hP0 : P 0 = cL) (hP1 : P 1 = cR) (hP'0 : P' 0 = 0) (hP'1 : P' 1 = 0)
    (u : ℝ) :
    HasDerivAt (clampSpline cL cR P) (clampSpline 0 0 P' u) u := by
  rcases lt_trichotomy u 0 with hu_neg | rfl | hu_pos
  · have hev : clampSpline cL cR P =ᶠ[𝓝 u] fun _ => cL := by
      filter_upwards [Iio_mem_nhds hu_neg] with s hs
      exact clampSpline_of_le_zero cL cR P (le_of_lt hs)
    rw [clampSpline_of_le_zero 0 0 P' (le_of_lt hu_neg)]
    exact (hasDerivAt_const u cL).congr_of_eventuallyEq hev
  · rw [clampSpline_of_le_zero 0 0 P' le_rfl]
    have hL : HasDerivWithinAt (clampSpline cL cR P) 0 (Iic 0) 0 :=
      (hasDerivWithinAt_const (0 : ℝ) (Iic 0) cL).congr
        (fun s hs => clampSpline_of_le_zero cL cR P hs)
        (clampSpline_of_le_zero cL cR P le_rfl)
    have hP0_deriv : HasDerivWithinAt P 0 (Ici 0) 0 := by
      simpa [hP'0] using (hP 0).hasDerivWithinAt (s := Ici 0)
    have hevR : clampSpline cL cR P =ᶠ[𝓝[≥] (0 : ℝ)] P := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one), self_mem_nhdsWithin]
        with s hs1 hs0
      exact clampSpline_of_mem_Icc cL cR P hP0 hs0 (le_of_lt hs1)
    have hR : HasDerivWithinAt (clampSpline cL cR P) 0 (Ici 0) 0 :=
      hP0_deriv.congr_of_eventuallyEq hevR
        (clampSpline_of_mem_Icc cL cR P hP0 le_rfl zero_le_one)
    exact hasDerivAt_of_Iic_Ici hL hR
  · rcases lt_trichotomy u 1 with hu_lt1 | rfl | hu_gt1
    · have hev : clampSpline cL cR P =ᶠ[𝓝 u] P := by
        filter_upwards [Ioo_mem_nhds hu_pos hu_lt1] with s hs
        exact clampSpline_of_mem_Icc cL cR P hP0 (le_of_lt hs.1) (le_of_lt hs.2)
      rw [clampSpline_of_mem_Icc 0 0 P' hP'0 (le_of_lt hu_pos) (le_of_lt hu_lt1)]
      exact (hP u).congr_of_eventuallyEq hev
    · rw [clampSpline_of_one_le 0 0 P' hP'1 le_rfl]
      have hP1_deriv : HasDerivWithinAt P 0 (Iic 1) 1 := by
        simpa [hP'1] using (hP 1).hasDerivWithinAt (s := Iic 1)
      have hevL : clampSpline cL cR P =ᶠ[𝓝[≤] (1 : ℝ)] P := by
        filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds zero_lt_one), self_mem_nhdsWithin]
          with s hs0 hs1
        exact clampSpline_of_mem_Icc cL cR P hP0 (le_of_lt hs0) hs1
      have hL : HasDerivWithinAt (clampSpline cL cR P) 0 (Iic 1) 1 :=
        hP1_deriv.congr_of_eventuallyEq hevL
          (clampSpline_of_mem_Icc cL cR P hP0 zero_le_one le_rfl)
      have hR : HasDerivWithinAt (clampSpline cL cR P) 0 (Ici 1) 1 :=
        (hasDerivWithinAt_const (1 : ℝ) (Ici 1) cR).congr
          (fun s hs => clampSpline_of_one_le cL cR P hP1 hs)
          (clampSpline_of_one_le cL cR P hP1 le_rfl)
      exact hasDerivAt_of_Iic_Ici hL hR
    · have hev : clampSpline cL cR P =ᶠ[𝓝 u] fun _ => cR := by
        filter_upwards [Ioi_mem_nhds hu_gt1] with s hs
        exact clampSpline_of_one_le cL cR P hP1 (le_of_lt hs)
      rw [clampSpline_of_one_le 0 0 P' hP'1 (le_of_lt hu_gt1)]
      exact (hasDerivAt_const u cR).congr_of_eventuallyEq hev

private lemma contDiff_succ_of_hasDerivAt {n : ℕ} {f f' : ℝ → ℝ}
    (hf : ∀ u : ℝ, HasDerivAt f (f' u) u) (hf' : ContDiff ℝ (n : ℕ) f') :
    ContDiff ℝ ((n + 1 : ℕ)) f := by
  rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
  refine ⟨fun u => (hf u).differentiableAt, by simp, ?_⟩
  have hderiv : deriv f = f' := funext fun u => (hf u).deriv
  rw [hderiv]
  exact hf'

private def polyS0 (u : ℝ) : ℝ :=
  126 * u ^ 5 - 420 * u ^ 6 + 540 * u ^ 7 - 315 * u ^ 8 + 70 * u ^ 9

private def polyS1 (u : ℝ) : ℝ :=
  630 * u ^ 4 * (1 - u) ^ 4

private def polyS2 (u : ℝ) : ℝ :=
  2520 * u ^ 3 * (1 - u) ^ 3 * (1 - 2 * u)

private def polyS3 (u : ℝ) : ℝ :=
  2520 * u ^ 2 * (1 - u) ^ 2 * (3 - 14 * u + 14 * u ^ 2)

private def polyS4 (u : ℝ) : ℝ :=
  15120 * u * (1 - u) * (1 - 2 * u) * (1 - 7 * u + 7 * u ^ 2)

private lemma hasDerivAt_monomial (c : ℝ) (k : ℕ) (u : ℝ) :
    HasDerivAt (fun s : ℝ => c * s ^ k) (c * ((k : ℝ) * u ^ (k - 1))) u :=
  (hasDerivAt_pow k u).const_mul c

private lemma hasDerivAt_polyS0 (u : ℝ) : HasDerivAt polyS0 (polyS1 u) u := by
  unfold polyS0 polyS1
  have h5 := hasDerivAt_monomial 126 5 u
  have h6 := hasDerivAt_monomial 420 6 u
  have h7 := hasDerivAt_monomial 540 7 u
  have h8 := hasDerivAt_monomial 315 8 u
  have h9 := hasDerivAt_monomial 70 9 u
  convert ((((h5.sub h6).add h7).sub h8).add h9) using 1
  norm_num
  ring

private lemma hasDerivAt_polyS1 (u : ℝ) : HasDerivAt polyS1 (polyS2 u) u := by
  have heq : polyS1 = fun s : ℝ =>
      630 * s ^ 4 - 2520 * s ^ 5 + 3780 * s ^ 6 - 2520 * s ^ 7 + 630 * s ^ 8 := by
    funext s; unfold polyS1; ring
  rw [heq]
  unfold polyS2
  have h4 := hasDerivAt_monomial 630 4 u
  have h5 := hasDerivAt_monomial 2520 5 u
  have h6 := hasDerivAt_monomial 3780 6 u
  have h7 := hasDerivAt_monomial 2520 7 u
  have h8 := hasDerivAt_monomial 630 8 u
  convert ((((h4.sub h5).add h6).sub h7).add h8) using 1
  norm_num
  ring

private lemma hasDerivAt_polyS2 (u : ℝ) : HasDerivAt polyS2 (polyS3 u) u := by
  have heq : polyS2 = fun s : ℝ =>
      2520 * s ^ 3 - 12600 * s ^ 4 + 22680 * s ^ 5 - 17640 * s ^ 6 + 5040 * s ^ 7 := by
    funext s; unfold polyS2; ring
  rw [heq]
  unfold polyS3
  have h3 := hasDerivAt_monomial 2520 3 u
  have h4 := hasDerivAt_monomial 12600 4 u
  have h5 := hasDerivAt_monomial 22680 5 u
  have h6 := hasDerivAt_monomial 17640 6 u
  have h7 := hasDerivAt_monomial 5040 7 u
  convert ((((h3.sub h4).add h5).sub h6).add h7) using 1
  norm_num
  ring

private lemma hasDerivAt_polyS3 (u : ℝ) : HasDerivAt polyS3 (polyS4 u) u := by
  have heq : polyS3 = fun s : ℝ =>
      7560 * s ^ 2 - 50400 * s ^ 3 + 113400 * s ^ 4 - 105840 * s ^ 5 + 35280 * s ^ 6 := by
    funext s; unfold polyS3; ring
  rw [heq]
  unfold polyS4
  have h2 := hasDerivAt_monomial 7560 2 u
  have h3 := hasDerivAt_monomial 50400 3 u
  have h4 := hasDerivAt_monomial 113400 4 u
  have h5 := hasDerivAt_monomial 105840 5 u
  have h6 := hasDerivAt_monomial 35280 6 u
  convert ((((h2.sub h3).add h4).sub h5).add h6) using 1
  norm_num
  ring

/-- Closed-form degree-9 clamped transition spline `S : ℝ → ℝ` with `S ≡ 0` on `(-∞, 0]`,
`S ≡ 1` on `[1, ∞)`, and `ContDiff ℝ 4 S`. -/
def smoothstep9 : ℝ → ℝ := clampSpline 0 1 polyS0

/-- First derivative of `smoothstep9`. -/
def smoothstep9D1 : ℝ → ℝ := clampSpline 0 0 polyS1

/-- Second derivative of `smoothstep9`. -/
def smoothstep9D2 : ℝ → ℝ := clampSpline 0 0 polyS2

/-- Third derivative of `smoothstep9`. -/
def smoothstep9D3 : ℝ → ℝ := clampSpline 0 0 polyS3

/-- Fourth derivative of `smoothstep9`. -/
def smoothstep9D4 : ℝ → ℝ := clampSpline 0 0 polyS4

lemma hasDerivAt_smoothstep9 (u : ℝ) : HasDerivAt smoothstep9 (smoothstep9D1 u) u :=
  hasDerivAt_clampSpline hasDerivAt_polyS0
    (by unfold polyS0; norm_num) (by unfold polyS0; norm_num)
    (by unfold polyS1; norm_num) (by unfold polyS1; norm_num) u

lemma hasDerivAt_smoothstep9D1 (u : ℝ) : HasDerivAt smoothstep9D1 (smoothstep9D2 u) u :=
  hasDerivAt_clampSpline hasDerivAt_polyS1
    (by unfold polyS1; norm_num) (by unfold polyS1; norm_num)
    (by unfold polyS2; norm_num) (by unfold polyS2; norm_num) u

lemma hasDerivAt_smoothstep9D2 (u : ℝ) : HasDerivAt smoothstep9D2 (smoothstep9D3 u) u :=
  hasDerivAt_clampSpline hasDerivAt_polyS2
    (by unfold polyS2; norm_num) (by unfold polyS2; norm_num)
    (by unfold polyS3; norm_num) (by unfold polyS3; norm_num) u

lemma hasDerivAt_smoothstep9D3 (u : ℝ) : HasDerivAt smoothstep9D3 (smoothstep9D4 u) u :=
  hasDerivAt_clampSpline hasDerivAt_polyS3
    (by unfold polyS3; norm_num) (by unfold polyS3; norm_num)
    (by unfold polyS4; norm_num) (by unfold polyS4; norm_num) u

/-- `smoothstep9` is `C⁴` on `ℝ`. -/
theorem contDiff_smoothstep9 : ContDiff ℝ (4 : ℕ) smoothstep9 := by
  have hpoly4 : Continuous polyS4 := by unfold polyS4; fun_prop
  have h4 : ContDiff ℝ (0 : ℕ) smoothstep9D4 :=
    contDiff_zero.mpr (continuous_clampSpline hpoly4
      (by unfold polyS4; norm_num) (by unfold polyS4; norm_num))
  have h3 : ContDiff ℝ (1 : ℕ) smoothstep9D3 :=
    contDiff_succ_of_hasDerivAt hasDerivAt_smoothstep9D3 h4
  have h2 : ContDiff ℝ (2 : ℕ) smoothstep9D2 :=
    contDiff_succ_of_hasDerivAt hasDerivAt_smoothstep9D2 h3
  have h1 : ContDiff ℝ (3 : ℕ) smoothstep9D1 :=
    contDiff_succ_of_hasDerivAt hasDerivAt_smoothstep9D1 h2
  exact contDiff_succ_of_hasDerivAt hasDerivAt_smoothstep9 h1

lemma smoothstep9_of_le_zero {u : ℝ} (hu : u ≤ 0) : smoothstep9 u = 0 :=
  clampSpline_of_le_zero 0 1 polyS0 hu

lemma smoothstep9_of_one_le {u : ℝ} (hu : 1 ≤ u) : smoothstep9 u = 1 :=
  clampSpline_of_one_le 0 1 polyS0 (by unfold polyS0; norm_num) hu

lemma smoothstep9D1_nonneg (u : ℝ) : 0 ≤ smoothstep9D1 u := by
  unfold smoothstep9D1 clampSpline polyS1
  split_ifs <;> positivity

lemma monotone_smoothstep9 : Monotone smoothstep9 := by
  apply monotone_of_deriv_nonneg (fun u => (hasDerivAt_smoothstep9 u).differentiableAt)
  intro u
  rw [(hasDerivAt_smoothstep9 u).deriv]
  exact smoothstep9D1_nonneg u

lemma smoothstep9_nonneg (u : ℝ) : 0 ≤ smoothstep9 u := by
  rcases le_total u 0 with hu | hu
  · rw [smoothstep9_of_le_zero hu]
  · calc
      (0 : ℝ) = smoothstep9 0 := (smoothstep9_of_le_zero le_rfl).symm
      _ ≤ smoothstep9 u := monotone_smoothstep9 hu

lemma smoothstep9_le_one (u : ℝ) : smoothstep9 u ≤ 1 := by
  rcases le_total 1 u with hu | hu
  · rw [smoothstep9_of_one_le hu]
  · calc
      smoothstep9 u ≤ smoothstep9 1 := monotone_smoothstep9 hu
      _ = 1 := smoothstep9_of_one_le le_rfl

/-! ### Section 2: 1D Compactly Supported Outer Cutoff on `[1/8, 7/8]` -/

/-- Smooth `C⁴` 1D cutoff supported in `[1/8, 7/8]` and equal to `1` on `[1/4, 3/4]`. -/
def boxCutoff1D (t : ℝ) : ℝ :=
  smoothstep9 (8 * (t - 1 / 8)) * smoothstep9 (8 * (7 / 8 - t))

theorem contDiff_boxCutoff1D : ContDiff ℝ (4 : ℕ) boxCutoff1D := by
  unfold boxCutoff1D
  have h1 : ContDiff ℝ (4 : ℕ) (fun t : ℝ => 8 * (t - 1 / 8)) := by fun_prop
  have h2 : ContDiff ℝ (4 : ℕ) (fun t : ℝ => 8 * (7 / 8 - t)) := by fun_prop
  exact (contDiff_smoothstep9.comp h1).mul (contDiff_smoothstep9.comp h2)

lemma boxCutoff1D_of_le {t : ℝ} (ht : t ≤ 1 / 8) : boxCutoff1D t = 0 := by
  unfold boxCutoff1D
  have h : smoothstep9 (8 * (t - 1 / 8)) = 0 := smoothstep9_of_le_zero (by linarith)
  rw [h, zero_mul]

lemma boxCutoff1D_of_ge {t : ℝ} (ht : 7 / 8 ≤ t) : boxCutoff1D t = 0 := by
  unfold boxCutoff1D
  have h : smoothstep9 (8 * (7 / 8 - t)) = 0 := smoothstep9_of_le_zero (by linarith)
  rw [h, mul_zero]

lemma boxCutoff1D_eq_one {t : ℝ} (ht1 : 1 / 4 ≤ t) (ht2 : t ≤ 3 / 4) : boxCutoff1D t = 1 := by
  unfold boxCutoff1D
  have h1 : smoothstep9 (8 * (t - 1 / 8)) = 1 := smoothstep9_of_one_le (by linarith)
  have h2 : smoothstep9 (8 * (7 / 8 - t)) = 1 := smoothstep9_of_one_le (by linarith)
  rw [h1, h2, mul_one]

lemma boxCutoff1D_nonneg (t : ℝ) : 0 ≤ boxCutoff1D t :=
  mul_nonneg (smoothstep9_nonneg _) (smoothstep9_nonneg _)

lemma boxCutoff1D_le_one (t : ℝ) : boxCutoff1D t ≤ 1 := by
  calc
    boxCutoff1D t ≤ 1 * 1 :=
      mul_le_mul (smoothstep9_le_one _) (smoothstep9_le_one _)
        (smoothstep9_nonneg _) zero_le_one
    _ = 1 := mul_one 1

/-! ### Section 3: 1-Periodic Plateau Cutoff `etaWave δ` -/

/-- Single-cell bump supported in `[δ/2, 1/2 - δ/2]` and equal to `1` on `[δ, 1/2 - δ]`. -/
def etaBump (δ t : ℝ) : ℝ :=
  smoothstep9 ((t - δ / 2) / (δ / 2)) * smoothstep9 (((1 / 2 - δ / 2) - t) / (δ / 2))

/-- 1-periodic `C⁴` plateau cutoff supported in `(δ/2, 1/2 - δ/2) + ℤ`. -/
def etaWave (δ t : ℝ) : ℝ :=
  etaBump δ (Int.fract t)

lemma etaBump_eq_zero_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ / 2) :
    etaBump δ t = 0 := by
  unfold etaBump
  have harg : (t - δ / 2) / (δ / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  rw [smoothstep9_of_le_zero harg, zero_mul]

lemma etaBump_eq_zero_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : 1 / 2 - δ / 2 ≤ t) :
    etaBump δ t = 0 := by
  unfold etaBump
  have harg : ((1 / 2 - δ / 2) - t) / (δ / 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h : smoothstep9 (((1 / 2 - δ / 2) - t) / (δ / 2)) = 0 := smoothstep9_of_le_zero harg
  rw [h, mul_zero]

lemma etaBump_eq_one_of_mem {δ t : ℝ} (hδ : 0 < δ) (ht1 : δ ≤ t) (ht2 : t ≤ 1 / 2 - δ) :
    etaBump δ t = 1 := by
  unfold etaBump
  have hd2 : 0 < δ / 2 := by positivity
  have harg1 : 1 ≤ (t - δ / 2) / (δ / 2) := (one_le_div hd2).mpr (by linarith)
  have harg2 : 1 ≤ ((1 / 2 - δ / 2) - t) / (δ / 2) := (one_le_div hd2).mpr (by linarith)
  rw [smoothstep9_of_one_le harg1, smoothstep9_of_one_le harg2, mul_one]

lemma contDiff_etaBump (δ : ℝ) : ContDiff ℝ (4 : ℕ) (etaBump δ) := by
  unfold etaBump
  have h1 : ContDiff ℝ (4 : ℕ) (fun t : ℝ => (t - δ / 2) / (δ / 2)) := by fun_prop
  have h2 : ContDiff ℝ (4 : ℕ) (fun t : ℝ => ((1 / 2 - δ / 2) - t) / (δ / 2)) := by fun_prop
  exact (contDiff_smoothstep9.comp h1).mul (contDiff_smoothstep9.comp h2)

/-- `etaWave δ` is `C⁴` on `ℝ` for every `0 < δ ≤ 1/8`. -/
theorem contDiff_etaWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ContDiff ℝ (4 : ℕ) (etaWave δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t₀
  by_cases hfr : Int.fract t₀ = 0
  · have ht₀_int : (⌊t₀⌋ : ℝ) = t₀ := by
      have := Int.floor_add_fract t₀
      linarith
    have hev : etaWave δ =ᶠ[𝓝 t₀] fun _ => (0 : ℝ) := by
      have hd2 : 0 < δ / 2 := by positivity
      filter_upwards [Ioo_mem_nhds (sub_lt_self t₀ hd2) (lt_add_of_pos_right t₀ hd2)] with s hs
      unfold etaWave
      rcases le_or_gt t₀ s with hle | hlt
      · have hfl : ⌊s⌋ = ⌊t₀⌋ := by
          apply Int.floor_eq_iff.mpr
          exact ⟨by linarith [ht₀_int, hle], by linarith [ht₀_int, hs.2, hδ1]⟩
        have hfs : Int.fract s ≤ δ / 2 := by
          unfold Int.fract
          rw [hfl, ht₀_int]
          linarith [hs.2]
        exact etaBump_eq_zero_of_le hδ0 hfs
      · have hfl : ⌊s⌋ = ⌊t₀⌋ - 1 := by
          apply Int.floor_eq_iff.mpr
          push_cast
          exact ⟨by linarith [ht₀_int, hs.1, hδ1], by linarith [ht₀_int, hlt]⟩
        have hfs : 1 / 2 - δ / 2 ≤ Int.fract s := by
          unfold Int.fract
          rw [hfl]
          push_cast
          linarith [ht₀_int, hs.1, hδ1]
        exact etaBump_eq_zero_of_ge hδ0 hfs
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hpos : 0 < Int.fract t₀ := lt_of_le_of_ne (Int.fract_nonneg t₀) (Ne.symm hfr)
    have hlt1 : Int.fract t₀ < 1 := Int.fract_lt_one t₀
    have hlo : (⌊t₀⌋ : ℝ) < t₀ := by
      have := Int.floor_add_fract t₀
      linarith
    have hhi : t₀ < (⌊t₀⌋ : ℝ) + 1 := by
      have := Int.floor_add_fract t₀
      linarith
    have hev : etaWave δ =ᶠ[𝓝 t₀] fun s : ℝ => etaBump δ (s - (⌊t₀⌋ : ℝ)) := by
      filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
      unfold etaWave Int.fract
      have hfl : ⌊s⌋ = ⌊t₀⌋ := Int.floor_eq_iff.mpr ⟨le_of_lt hs.1, hs.2⟩
      rw [hfl]
    have hsmooth : ContDiff ℝ (4 : ℕ) (fun s : ℝ => etaBump δ (s - (⌊t₀⌋ : ℝ))) :=
      (contDiff_etaBump δ).comp (contDiff_id.sub contDiff_const)
    exact hsmooth.contDiffAt.congr_of_eventuallyEq hev

theorem etaWave_periodic (δ t : ℝ) : etaWave δ (t + 1) = etaWave δ t := by
  simp [etaWave, Int.fract_add_one]

lemma etaWave_nonneg (δ t : ℝ) : 0 ≤ etaWave δ t :=
  mul_nonneg (smoothstep9_nonneg _) (smoothstep9_nonneg _)

lemma etaWave_le_one (δ t : ℝ) : etaWave δ t ≤ 1 := by
  unfold etaWave etaBump
  calc
    smoothstep9 _ * smoothstep9 _ ≤ 1 * 1 :=
      mul_le_mul (smoothstep9_le_one _) (smoothstep9_le_one _)
        (smoothstep9_nonneg _) zero_le_one
    _ = 1 := mul_one 1

lemma etaWave_eq_one_of_mem_Icc {δ t : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (ht1 : δ ≤ t) (ht2 : t ≤ 1 / 2 - δ) :
    etaWave δ t = 1 := by
  unfold etaWave
  have hfr : Int.fract t = t :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  rw [hfr]
  exact etaBump_eq_one_of_mem hδ0 ht1 ht2

theorem integral_etaWave_sq_ge {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    1 / 2 - 2 * δ ≤ ∫ t in (0 : ℝ)..1, (etaWave δ t) ^ 2 := by
  have hcont : Continuous (fun t : ℝ => (etaWave δ t) ^ 2) :=
    (contDiff_etaWave hδ0 hδ1).continuous.pow 2
  have hi1 := hcont.intervalIntegrable (μ := volume) (0 : ℝ) δ
  have hi2 := hcont.intervalIntegrable (μ := volume) δ (1 / 2 - δ)
  have hi3 := hcont.intervalIntegrable (μ := volume) (1 / 2 - δ) 1
  have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3).symm
  have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hnonneg1 : 0 ≤ ∫ t in (0 : ℝ)..δ, (etaWave δ t) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)
  have hnonneg3 : 0 ≤ ∫ t in (1 / 2 - δ)..1, (etaWave δ t) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)
  have hmid : (∫ t in δ..(1 / 2 - δ), (etaWave δ t) ^ 2) = 1 / 2 - 2 * δ := by
    have hcongr : ∫ t in δ..(1 / 2 - δ), (etaWave δ t) ^ 2 =
        ∫ _t in δ..(1 / 2 - δ), (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [uIcc_of_le (by linarith)] at ht
      rw [etaWave_eq_one_of_mem_Icc hδ0 hδ1 ht.1 ht.2]
      norm_num
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-! ### Section 4: `(1/2)`-Antiperiodic Square-Wave Spline `tauDerivWave δ` -/

/-- Single-period profile for `tauDerivWave δ` with seam inside the `+1` plateau at `t ≡ 1/4`. -/
def tauBase (δ u : ℝ) : ℝ :=
  1 - 2 * smoothstep9 ((u - (1 / 4 - δ / 2)) / δ) +
    2 * smoothstep9 ((u - (3 / 4 - δ / 2)) / δ)

/-- Smooth `(1/2)`-antiperiodic `C⁴` square-wave spline taking values in `[-1, 1]` and equal to
`+1` on `[δ/2, 1/2 - δ/2] + ℤ`. -/
def tauDerivWave (δ t : ℝ) : ℝ :=
  tauBase δ (Int.fract (t - 1 / 4))

lemma tauBase_of_le {δ u : ℝ} (hδ : 0 < δ) (hu : u ≤ 1 / 4 - δ / 2) :
    tauBase δ u = 1 := by
  unfold tauBase
  have h1 : (u - (1 / 4 - δ / 2)) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  have h2 : (u - (3 / 4 - δ / 2)) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  rw [smoothstep9_of_le_zero h1, smoothstep9_of_le_zero h2]
  ring

lemma tauBase_of_ge {δ u : ℝ} (hδ : 0 < δ) (hu : 3 / 4 + δ / 2 ≤ u) :
    tauBase δ u = 1 := by
  unfold tauBase
  have h1 : 1 ≤ (u - (1 / 4 - δ / 2)) / δ := (one_le_div hδ).mpr (by linarith)
  have h2 : 1 ≤ (u - (3 / 4 - δ / 2)) / δ := (one_le_div hδ).mpr (by linarith)
  rw [smoothstep9_of_one_le h1, smoothstep9_of_one_le h2]
  ring

lemma tauBase_add_half {δ u : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8)
    (hu0 : 0 ≤ u) (hu1 : u < 1 / 2) :
    tauBase δ (u + 1 / 2) = -tauBase δ u := by
  unfold tauBase
  have h_one : 1 ≤ ((u + 1 / 2) - (1 / 4 - δ / 2)) / δ :=
    (one_le_div hδ0).mpr (by linarith)
  have h_zero : (u - (3 / 4 - δ / 2)) / δ ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hδ0.le
  have h_match : ((u + 1 / 2) - (3 / 4 - δ / 2)) / δ = (u - (1 / 4 - δ / 2)) / δ := by ring
  rw [smoothstep9_of_one_le h_one, smoothstep9_of_le_zero h_zero, h_match]
  ring

lemma contDiff_tauBase (δ : ℝ) : ContDiff ℝ (4 : ℕ) (tauBase δ) := by
  unfold tauBase
  have h1 : ContDiff ℝ (4 : ℕ) (fun u : ℝ => (u - (1 / 4 - δ / 2)) / δ) := by fun_prop
  have h2 : ContDiff ℝ (4 : ℕ) (fun u : ℝ => (u - (3 / 4 - δ / 2)) / δ) := by fun_prop
  exact (contDiff_const.sub (contDiff_const.mul (contDiff_smoothstep9.comp h1))).add
    (contDiff_const.mul (contDiff_smoothstep9.comp h2))

/-- `tauDerivWave δ` is `C⁴` on `ℝ` for every `0 < δ ≤ 1/8`. -/
theorem contDiff_tauDerivWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ContDiff ℝ (4 : ℕ) (tauDerivWave δ) := by
  have hshift_smooth : ContDiff ℝ (4 : ℕ) (fun t : ℝ => tauBase δ (Int.fract t)) := by
    rw [contDiff_iff_contDiffAt]
    intro t₀
    by_cases hfr : Int.fract t₀ = 0
    · have ht₀_int : (⌊t₀⌋ : ℝ) = t₀ := by
        have := Int.floor_add_fract t₀
        linarith
      have hev : (fun t : ℝ => tauBase δ (Int.fract t)) =ᶠ[𝓝 t₀] fun _ => (1 : ℝ) := by
        have hrad : (0 : ℝ) < 1 / 16 := by norm_num
        filter_upwards [Ioo_mem_nhds (sub_lt_self t₀ hrad) (lt_add_of_pos_right t₀ hrad)]
          with s hs
        rcases le_or_gt t₀ s with hle | hlt
        · have hfl : ⌊s⌋ = ⌊t₀⌋ := by
            apply Int.floor_eq_iff.mpr
            exact ⟨by linarith [ht₀_int, hle], by linarith [ht₀_int, hs.2]⟩
          have hfs : Int.fract s ≤ 1 / 4 - δ / 2 := by
            unfold Int.fract
            rw [hfl, ht₀_int]
            linarith [hs.2, hδ1]
          exact tauBase_of_le hδ0 hfs
        · have hfl : ⌊s⌋ = ⌊t₀⌋ - 1 := by
            apply Int.floor_eq_iff.mpr
            push_cast
            exact ⟨by linarith [ht₀_int, hs.1], by linarith [ht₀_int, hlt]⟩
          have hfs : 3 / 4 + δ / 2 ≤ Int.fract s := by
            unfold Int.fract
            rw [hfl]
            push_cast
            linarith [ht₀_int, hs.1, hδ1]
          exact tauBase_of_ge hδ0 hfs
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hpos : 0 < Int.fract t₀ := lt_of_le_of_ne (Int.fract_nonneg t₀) (Ne.symm hfr)
      have hlt1 : Int.fract t₀ < 1 := Int.fract_lt_one t₀
      have hlo : (⌊t₀⌋ : ℝ) < t₀ := by
        have := Int.floor_add_fract t₀
        linarith
      have hhi : t₀ < (⌊t₀⌋ : ℝ) + 1 := by
        have := Int.floor_add_fract t₀
        linarith
      have hev : (fun t : ℝ => tauBase δ (Int.fract t)) =ᶠ[𝓝 t₀]
          fun s : ℝ => tauBase δ (s - (⌊t₀⌋ : ℝ)) := by
        filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
        unfold Int.fract
        have hfl : ⌊s⌋ = ⌊t₀⌋ := Int.floor_eq_iff.mpr ⟨le_of_lt hs.1, hs.2⟩
        rw [hfl]
      have hsm : ContDiff ℝ (4 : ℕ) (fun s : ℝ => tauBase δ (s - (⌊t₀⌋ : ℝ))) :=
        (contDiff_tauBase δ).comp (contDiff_id.sub contDiff_const)
      exact hsm.contDiffAt.congr_of_eventuallyEq hev
  exact hshift_smooth.comp (contDiff_id.sub contDiff_const)

/-- `tauDerivWave δ` is `(1/2)`-antiperiodic. -/
theorem tauDerivWave_antiperiodic {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    tauDerivWave δ (t + 1 / 2) = -tauDerivWave δ t := by
  unfold tauDerivWave
  set s : ℝ := t - 1 / 4
  have harg : t + 1 / 2 - 1 / 4 = s + 1 / 2 := by dsimp [s]; ring
  rw [harg]
  set u : ℝ := Int.fract s
  have hu0 : 0 ≤ u := Int.fract_nonneg s
  have hu1 : u < 1 := Int.fract_lt_one s
  have hs_eq : s = (⌊s⌋ : ℝ) + u := (Int.floor_add_fract s).symm
  rcases lt_or_ge u (1 / 2) with hlt | hge
  · have hfl : ⌊s + 1 / 2⌋ = ⌊s⌋ :=
      Int.floor_eq_iff.mpr ⟨by linarith [hs_eq], by linarith [hs_eq]⟩
    have hfr : Int.fract (s + 1 / 2) = u + 1 / 2 := by
      unfold Int.fract
      rw [hfl]
      linarith [hs_eq]
    rw [hfr]
    exact tauBase_add_half hδ0 hδ1 hu0 hlt
  · have hfl : ⌊s + 1 / 2⌋ = ⌊s⌋ + 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      exact ⟨by linarith [hs_eq], by linarith [hs_eq]⟩
    have hfr : Int.fract (s + 1 / 2) = u - 1 / 2 := by
      unfold Int.fract
      rw [hfl]
      push_cast
      linarith [hs_eq]
    rw [hfr]
    have hprev := tauBase_add_half hδ0 hδ1 (u := u - 1 / 2) (by linarith) (by linarith)
    have hu_restore : u - 1 / 2 + 1 / 2 = u := by ring
    rw [hu_restore] at hprev
    linarith

/-- Uniform `L^∞` bound `|tauDerivWave δ t| ≤ 1`. -/
theorem abs_tauDerivWave_le_one {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    |tauDerivWave δ t| ≤ 1 := by
  have hbound_first_half : ∀ u : ℝ, 0 ≤ u → u < 1 / 2 → |tauBase δ u| ≤ 1 := by
    intro u _ hu1
    unfold tauBase
    have h_zero : (u - (3 / 4 - δ / 2)) / δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hδ0.le
    rw [smoothstep9_of_le_zero h_zero]
    have hs0 := smoothstep9_nonneg ((u - (1 / 4 - δ / 2)) / δ)
    have hs1 := smoothstep9_le_one ((u - (1 / 4 - δ / 2)) / δ)
    rw [abs_le]
    constructor <;> linarith
  unfold tauDerivWave
  set u := Int.fract (t - 1 / 4)
  rcases lt_or_ge u (1 / 2) with hlt | hge
  · exact hbound_first_half u (Int.fract_nonneg _) hlt
  · have hu1 : u < 1 := Int.fract_lt_one _
    have hprev := tauBase_add_half hδ0 hδ1 (u := u - 1 / 2) (by linarith) (by linarith)
    have hu_restore : u - 1 / 2 + 1 / 2 = u := by ring
    rw [hu_restore] at hprev
    rw [hprev, abs_neg]
    exact hbound_first_half (u - 1 / 2) (by linarith) (by linarith)

/-- `tauDerivWave δ` equals `+1` everywhere on `[δ/2, 1/2 - δ/2] + ℤ`. -/
lemma tauDerivWave_eq_one_of_fract_mem {δ t : ℝ} (hδ0 : 0 < δ)
    (ht1 : δ / 2 ≤ Int.fract t) (ht2 : Int.fract t ≤ 1 / 2 - δ / 2) :
    tauDerivWave δ t = 1 := by
  unfold tauDerivWave
  set w := Int.fract t
  have ht_eq : t = (⌊t⌋ : ℝ) + w := (Int.floor_add_fract t).symm
  rcases le_or_gt (1 / 4 : ℝ) w with hw | hw
  · have hfl : ⌊t - 1 / 4⌋ = ⌊t⌋ :=
      Int.floor_eq_iff.mpr ⟨by linarith [ht_eq], by linarith [ht_eq]⟩
    have hfr : Int.fract (t - 1 / 4) = w - 1 / 4 := by
      unfold Int.fract
      rw [hfl]
      linarith [ht_eq]
    rw [hfr]
    exact tauBase_of_le hδ0 (by linarith)
  · have hfl : ⌊t - 1 / 4⌋ = ⌊t⌋ - 1 := by
      apply Int.floor_eq_iff.mpr
      push_cast
      exact ⟨by linarith [ht_eq], by linarith [ht_eq]⟩
    have hfr : Int.fract (t - 1 / 4) = w + 3 / 4 := by
      unfold Int.fract
      rw [hfl]
      push_cast
      linarith [ht_eq]
    rw [hfr]
    exact tauBase_of_ge hδ0 (by linarith)

/-- **Pointwise Stopping-Time Identity:** `etaWave δ` is supported inside `{tauDerivWave δ = +1}`. -/
theorem etaWave_mul_tauDerivWave {δ : ℝ} (hδ0 : 0 < δ) (t : ℝ) :
    etaWave δ t * tauDerivWave δ t = etaWave δ t := by
  by_cases h1 : Int.fract t ≤ δ / 2
  · have hz : etaWave δ t = 0 := etaBump_eq_zero_of_le hδ0 h1
    rw [hz, zero_mul]
  · by_cases h2 : 1 / 2 - δ / 2 ≤ Int.fract t
    · have hz : etaWave δ t = 0 := etaBump_eq_zero_of_ge hδ0 h2
      rw [hz, zero_mul]
    · have h1' : δ / 2 < Int.fract t := not_le.mp h1
      have h2' : Int.fract t < 1 / 2 - δ / 2 := not_le.mp h2
      rw [tauDerivWave_eq_one_of_fract_mem hδ0 (le_of_lt h1') (le_of_lt h2'), mul_one]

/-- Plateau `L²` lower bound `1 - 2 δ ≤ ∫_0^1 (tauDerivWave δ t)^2 dt`. -/
theorem integral_tauDerivWave_sq_ge {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    1 - 2 * δ ≤ ∫ t in (0 : ℝ)..1, (tauDerivWave δ t) ^ 2 := by
  have hcont : Continuous (fun t : ℝ => (tauDerivWave δ t) ^ 2) :=
    (contDiff_tauDerivWave hδ0 hδ1).continuous.pow 2
  have hsq_half : ∀ t : ℝ, (tauDerivWave δ (t + 1 / 2)) ^ 2 = (tauDerivWave δ t) ^ 2 := by
    intro t
    rw [tauDerivWave_antiperiodic hδ0 hδ1 t]
    ring
  have hfull : (∫ t in (0 : ℝ)..1, (tauDerivWave δ t) ^ 2) =
      2 * ∫ t in (0 : ℝ)..(1 / 2), (tauDerivWave δ t) ^ 2 := by
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (μ := volume) (0 : ℝ) (1 / 2))
      (hcont.intervalIntegrable (μ := volume) (1 / 2 : ℝ) 1)).symm
    have hshift : (∫ t in (1 / 2 : ℝ)..1, (tauDerivWave δ t) ^ 2) =
        ∫ t in (0 : ℝ)..(1 / 2), (tauDerivWave δ t) ^ 2 := by
      calc
        (∫ t in (1 / 2 : ℝ)..1, (tauDerivWave δ t) ^ 2)
            = ∫ t in ((0 : ℝ) + 1 / 2)..((1 / 2 : ℝ) + 1 / 2), (tauDerivWave δ t) ^ 2 := by
                norm_num
        _ = ∫ t in (0 : ℝ)..(1 / 2), (tauDerivWave δ (t + 1 / 2)) ^ 2 :=
              (intervalIntegral.integral_comp_add_right
                (fun t => (tauDerivWave δ t) ^ 2) (1 / 2)).symm
        _ = ∫ t in (0 : ℝ)..(1 / 2), (tauDerivWave δ t) ^ 2 := by simp_rw [hsq_half]
    linarith
  have hi1 := hcont.intervalIntegrable (μ := volume) (0 : ℝ) (δ / 2)
  have hi2 := hcont.intervalIntegrable (μ := volume) (δ / 2) (1 / 2 - δ / 2)
  have hi3 := hcont.intervalIntegrable (μ := volume) (1 / 2 - δ / 2) (1 / 2)
  have hsp1 := (intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3).symm
  have hsp2 := (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  have hn1 : 0 ≤ ∫ t in (0 : ℝ)..(δ / 2), (tauDerivWave δ t) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)
  have hn3 : 0 ≤ ∫ t in (1 / 2 - δ / 2)..(1 / 2), (tauDerivWave δ t) ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => sq_nonneg _)
  have hmid : (∫ t in (δ / 2)..(1 / 2 - δ / 2), (tauDerivWave δ t) ^ 2) = 1 / 2 - δ := by
    have hcongr : ∫ t in (δ / 2)..(1 / 2 - δ / 2), (tauDerivWave δ t) ^ 2 =
        ∫ _t in (δ / 2)..(1 / 2 - δ / 2), (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [uIcc_of_le (by linarith)] at ht
      have hfr : Int.fract t = t := Int.fract_eq_self.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [tauDerivWave_eq_one_of_fract_mem hδ0 (by rw [hfr]; exact ht.1) (by rw [hfr]; exact ht.2)]
      norm_num
    rw [hcongr, intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-! ### Section 5: `(1/2)`-Antiperiodic Primitive Operator and `tauWave`, `gammaWave` -/

/-- Unique `(1/2)`-antiperiodic primitive of a `(1/2)`-antiperiodic continuous wave `g`. -/
def antiperiodicPrimitive (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..t, g s) - (1 / 2) * ∫ s in (0 : ℝ)..(1 / 2), g s

lemma hasDerivAt_antiperiodicPrimitive {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (antiperiodicPrimitive g) (g t) t := by
  unfold antiperiodicPrimitive
  have hint : HasDerivAt (fun x : ℝ => ∫ s in (0 : ℝ)..x, g s) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable (μ := volume) 0 t)
      (hg.stronglyMeasurableAtFilter volume (𝓝 t))
      hg.continuousAt
  simpa using hint.sub_const ((1 / 2) * ∫ s in (0 : ℝ)..(1 / 2), g s)

lemma contDiff_antiperiodicPrimitive {n : ℕ} {g : ℝ → ℝ} (hg : ContDiff ℝ (n : ℕ) g) :
    ContDiff ℝ ((n + 1 : ℕ)) (antiperiodicPrimitive g) :=
  contDiff_succ_of_hasDerivAt (hasDerivAt_antiperiodicPrimitive hg.continuous) hg

lemma antiperiodicPrimitive_antiperiodic {g : ℝ → ℝ} (hg : Continuous g)
    (hanti : ∀ t : ℝ, g (t + 1 / 2) = -g t) (t : ℝ) :
    antiperiodicPrimitive g (t + 1 / 2) = -antiperiodicPrimitive g t := by
  let H : ℝ → ℝ := fun x => antiperiodicPrimitive g (x + 1 / 2) + antiperiodicPrimitive g x
  have hH_deriv : ∀ x : ℝ, HasDerivAt H 0 x := by
    intro x
    have hinner : HasDerivAt (fun y : ℝ => y + (1 / 2 : ℝ)) 1 x :=
      (hasDerivAt_id x).add_const (1 / 2 : ℝ)
    have h1 : HasDerivAt (fun y : ℝ => antiperiodicPrimitive g (y + 1 / 2))
        (g (x + 1 / 2) * 1) x :=
      HasDerivAt.comp (h₂ := antiperiodicPrimitive g) (h := fun y : ℝ => y + (1 / 2 : ℝ)) x
        (hasDerivAt_antiperiodicPrimitive hg (x + 1 / 2)) hinner
    have h2 := hasDerivAt_antiperiodicPrimitive hg x
    convert h1.add h2 using 1
    rw [hanti x]
    ring
  have hH_const : H t = H 0 :=
    is_const_of_deriv_eq_zero (fun x => (hH_deriv x).differentiableAt)
      (fun x => (hH_deriv x).deriv) t 0
  have hH0 : H 0 = 0 := by
    dsimp [H, antiperiodicPrimitive]
    simp only [zero_add, intervalIntegral.integral_same]
    ring
  linarith

lemma abs_antiperiodicPrimitive_le {g : ℝ → ℝ} {B : ℝ}
    (hg : Continuous g) (hanti : ∀ t : ℝ, g (t + 1 / 2) = -g t)
    (hB : ∀ t : ℝ, |g t| ≤ B) (t : ℝ) :
    |antiperiodicPrimitive g t| ≤ B / 4 := by
  have hcell : ∀ u : ℝ, 0 ≤ u → u ≤ 1 / 2 → |antiperiodicPrimitive g u| ≤ B / 4 := by
    intro u hu0 hu1
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (μ := volume) 0 u)
      (hg.intervalIntegrable (μ := volume) u (1 / 2))).symm
    have hdouble : 2 * antiperiodicPrimitive g u =
        (∫ s in (0 : ℝ)..u, g s) - ∫ s in u..(1 / 2), g s := by
      unfold antiperiodicPrimitive
      linarith
    have hb1 : |∫ s in (0 : ℝ)..u, g s| ≤ B * u := by
      calc
        |∫ s in (0 : ℝ)..u, g s| ≤ ∫ s in (0 : ℝ)..u, |g s| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm (f := g) hu0
        _ ≤ ∫ _s in (0 : ℝ)..u, B :=
          intervalIntegral.integral_mono_on hu0
            (hg.abs.intervalIntegrable (μ := volume) 0 u)
            (continuous_const.intervalIntegrable (μ := volume) 0 u)
            (fun s _ => hB s)
        _ = B * u := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hb2 : |∫ s in u..(1 / 2), g s| ≤ B * (1 / 2 - u) := by
      calc
        |∫ s in u..(1 / 2), g s| ≤ ∫ s in u..(1 / 2), |g s| := by
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.norm_integral_le_integral_norm (f := g) hu1
        _ ≤ ∫ _s in u..(1 / 2), B :=
          intervalIntegral.integral_mono_on hu1
            (hg.abs.intervalIntegrable (μ := volume) u (1 / 2))
            (continuous_const.intervalIntegrable (μ := volume) u (1 / 2))
            (fun s _ => hB s)
        _ = B * (1 / 2 - u) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have h2abs : 2 * |antiperiodicPrimitive g u| ≤ B / 2 := by
      calc
        2 * |antiperiodicPrimitive g u|
            = |2 * antiperiodicPrimitive g u| := by
                rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        _ = |(∫ s in (0 : ℝ)..u, g s) - ∫ s in u..(1 / 2), g s| := by rw [hdouble]
        _ ≤ |∫ s in (0 : ℝ)..u, g s| + |∫ s in u..(1 / 2), g s| := abs_sub _ _
        _ ≤ B * u + B * (1 / 2 - u) := add_le_add hb1 hb2
        _ = B / 2 := by ring
    linarith
  have habs_half : ∀ x : ℝ,
      |antiperiodicPrimitive g (x + 1 / 2)| = |antiperiodicPrimitive g x| := by
    intro x
    rw [antiperiodicPrimitive_antiperiodic hg hanti x, abs_neg]
  have habs_int : ∀ (k : ℤ) (x : ℝ),
      |antiperiodicPrimitive g (x + (k : ℝ) * (1 / 2))| = |antiperiodicPrimitive g x| := by
    intro k
    induction k using Int.induction_on with
    | zero => intro x; simp
    | succ n ih =>
        intro x
        have heq : x + (((n : ℤ) + 1 : ℤ) : ℝ) * (1 / 2) =
            (x + ((n : ℤ) : ℝ) * (1 / 2)) + 1 / 2 := by push_cast; ring
        rw [heq, habs_half, ih]
    | pred n ih =>
        intro x
        let m : ℤ := -(n : ℤ)
        have heq : x + (((-(n : ℤ) - 1 : ℤ) : ℝ) * (1 / 2)) =
            (x + (m : ℝ) * (1 / 2)) - 1 / 2 := by
          dsimp [m]; push_cast; ring
        rw [heq]
        have hstep := habs_half ((x + (m : ℝ) * (1 / 2)) - 1 / 2)
        have hrestore : (x + (m : ℝ) * (1 / 2)) - 1 / 2 + 1 / 2 =
            x + (m : ℝ) * (1 / 2) := by ring
        rw [hrestore] at hstep
        rw [← hstep]
        exact ih x
  let u : ℝ := (1 / 2) * Int.fract (2 * t)
  have ht_decomp : t = u + (⌊2 * t⌋ : ℝ) * (1 / 2) := by
    dsimp [u]
    have := Int.floor_add_fract (2 * t)
    linarith
  rw [ht_decomp, habs_int ⌊2 * t⌋ u]
  exact hcell u (by dsimp [u]; positivity) (by
    dsimp [u]
    have := Int.fract_lt_one (2 * t)
    linarith)

/-- First `(1/2)`-antiperiodic primitive `τ_δ` (`τ_δ' = tauDerivWave δ`). -/
def tauWave (δ : ℝ) : ℝ → ℝ :=
  antiperiodicPrimitive (tauDerivWave δ)

/-- Second `(1/2)`-antiperiodic primitive `Γ_δ'` (`(Γ_δ')' = tauWave δ`). -/
def gammaDerivWave (δ : ℝ) : ℝ → ℝ :=
  antiperiodicPrimitive (tauWave δ)

/-- Third `(1/2)`-antiperiodic primitive `Γ_δ` (`Γ_δ''' = tauDerivWave δ`). -/
def gammaWave (δ : ℝ) : ℝ → ℝ :=
  antiperiodicPrimitive (gammaDerivWave δ)

theorem contDiff_tauWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ContDiff ℝ (4 : ℕ) (tauWave δ) :=
  (contDiff_antiperiodicPrimitive (contDiff_tauDerivWave hδ0 hδ1)).of_le (by norm_cast)

theorem contDiff_gammaDerivWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ContDiff ℝ (4 : ℕ) (gammaDerivWave δ) :=
  (contDiff_antiperiodicPrimitive (contDiff_tauWave hδ0 hδ1)).of_le (by norm_cast)

theorem contDiff_gammaWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) :
    ContDiff ℝ (4 : ℕ) (gammaWave δ) :=
  (contDiff_antiperiodicPrimitive (contDiff_gammaDerivWave hδ0 hδ1)).of_le (by norm_cast)

theorem hasDerivAt_tauWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    HasDerivAt (tauWave δ) (tauDerivWave δ t) t :=
  hasDerivAt_antiperiodicPrimitive (contDiff_tauDerivWave hδ0 hδ1).continuous t

theorem hasDerivAt_gammaDerivWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    HasDerivAt (gammaDerivWave δ) (tauWave δ t) t :=
  hasDerivAt_antiperiodicPrimitive (contDiff_tauWave hδ0 hδ1).continuous t

theorem hasDerivAt_gammaWave {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    HasDerivAt (gammaWave δ) (gammaDerivWave δ t) t :=
  hasDerivAt_antiperiodicPrimitive (contDiff_gammaDerivWave hδ0 hδ1).continuous t

theorem tauWave_antiperiodic {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    tauWave δ (t + 1 / 2) = -tauWave δ t :=
  antiperiodicPrimitive_antiperiodic (contDiff_tauDerivWave hδ0 hδ1).continuous
    (tauDerivWave_antiperiodic hδ0 hδ1) t

theorem gammaDerivWave_antiperiodic {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    gammaDerivWave δ (t + 1 / 2) = -gammaDerivWave δ t :=
  antiperiodicPrimitive_antiperiodic (contDiff_tauWave hδ0 hδ1).continuous
    (tauWave_antiperiodic hδ0 hδ1) t

theorem gammaWave_antiperiodic {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    gammaWave δ (t + 1 / 2) = -gammaWave δ t :=
  antiperiodicPrimitive_antiperiodic (contDiff_gammaDerivWave hδ0 hδ1).continuous
    (gammaDerivWave_antiperiodic hδ0 hδ1) t

theorem abs_tauWave_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    |tauWave δ t| ≤ 1 / 4 := by
  unfold tauWave
  have h := abs_antiperiodicPrimitive_le (B := 1)
    (contDiff_tauDerivWave hδ0 hδ1).continuous
    (tauDerivWave_antiperiodic hδ0 hδ1)
    (abs_tauDerivWave_le_one hδ0 hδ1) t
  linarith

theorem abs_gammaDerivWave_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    |gammaDerivWave δ t| ≤ 1 / 16 := by
  unfold gammaDerivWave
  have h := abs_antiperiodicPrimitive_le (B := 1 / 4)
    (contDiff_tauWave hδ0 hδ1).continuous
    (tauWave_antiperiodic hδ0 hδ1)
    (abs_tauWave_le hδ0 hδ1) t
  linarith

theorem abs_gammaWave_le {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 8) (t : ℝ) :
    |gammaWave δ t| ≤ 1 / 64 := by
  unfold gammaWave
  have h := abs_antiperiodicPrimitive_le (B := 1 / 16)
    (contDiff_gammaDerivWave hδ0 hδ1).continuous
    (gammaDerivWave_antiperiodic hδ0 hδ1)
    (abs_gammaDerivWave_le hδ0 hδ1) t
  linarith

end Rudin.PMA.Chapter10

/-! Verify module ownership and standard foundations for all declarations in this module. -/
run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.Research.Stage4B1Waves
    #[`Rudin.PMA.Chapter10.contDiff_smoothstep9,
      `Rudin.PMA.Chapter10.contDiff_boxCutoff1D,
      `Rudin.PMA.Chapter10.contDiff_etaWave,
      `Rudin.PMA.Chapter10.etaWave_periodic,
      `Rudin.PMA.Chapter10.integral_etaWave_sq_ge,
      `Rudin.PMA.Chapter10.contDiff_tauDerivWave,
      `Rudin.PMA.Chapter10.tauDerivWave_antiperiodic,
      `Rudin.PMA.Chapter10.abs_tauDerivWave_le_one,
      `Rudin.PMA.Chapter10.etaWave_mul_tauDerivWave,
      `Rudin.PMA.Chapter10.integral_tauDerivWave_sq_ge,
      `Rudin.PMA.Chapter10.contDiff_tauWave,
      `Rudin.PMA.Chapter10.contDiff_gammaDerivWave,
      `Rudin.PMA.Chapter10.contDiff_gammaWave,
      `Rudin.PMA.Chapter10.tauWave_antiperiodic,
      `Rudin.PMA.Chapter10.gammaDerivWave_antiperiodic,
      `Rudin.PMA.Chapter10.gammaWave_antiperiodic,
      `Rudin.PMA.Chapter10.abs_tauWave_le,
      `Rudin.PMA.Chapter10.abs_gammaDerivWave_le,
      `Rudin.PMA.Chapter10.abs_gammaWave_le]
