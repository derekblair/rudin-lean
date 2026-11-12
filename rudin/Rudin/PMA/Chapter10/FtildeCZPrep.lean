/-
  Stage 4 preparation module for rudin-lean issue #29 (SymmetricDerivativeLifting).
  Branch: `rudin29-stage4-prep` (disjoint from PR #30 / Stage 2 / Stage 3).

  STATUS: FULLY PROVED STAGE 4 PREP & DIRECTION-ANALYSIS MODULE
  (Re-scoped after Stage 3 proved the `¬ SymmetricCurlSystem ftildeBall ftildeField`
   clause of the Stage 1–2 `ftildeField` witness target FALSE on the merits;
   no unproved L8 skeleton is built for the dead `ftildeField` disproof direction).

  Every declaration in this file is completely kernel-checked with standard foundations only
  (`propext`, `Classical.choice`, `Quot.sound`) and no fast-eval reflection tactics:
    - Section I.1: Exact unit-sphere surface measure (`Measure.toSphere volume`),
      exact monomial expectation formula via 3D Gaussian polar/Fubini factorization,
      antipodal parity vanishing, and part (A) of the completion-independence split.
    - Section I.2: Closing research gap (a2) in Lean — exact polynomial formula for
      `ftildeD` on the unit sphere, mean-zero property of the reconstructed CZ kernel,
      exact angular identification `A = ftildeC` via both the Biot–Savart dipole
      kernel and the G3/G4 degree-4 Fourier multiplier + Funk–Hecke eigenvalues,
      nonzero local symbol mean witness (`-1/30`), and part (B) (exact cancellation of
      the unshifted potential-compensated base field vs nonzero `-4/77` first-row partial).
    - Section I.3: Valid algebraic and radial calculus half of gap (b), L8, and L10 —
      Korn second-partial reconstruction, exact frequency-wise gauge orthogonality
      `<Sym(ξ⊗ξ⊗v), α(ξ⊗ξ⊗ξ) + β Sym(δ⊗ξ)> = 0` for `⟨ξ, v⟩ = 0`, outer-shell
      integrals `∫ ψ(s)/s = log(-log r) - log(-log r₀)` and `∫ ψ(s)²/s = ψ(r₀) - ψ(r)`
      (confirming the standing `O(1)` remainder law), ray log-log IBP, and `L10`
      (`l10_not_c1_of_log_log_symGrad`, proving Coulomb `S⁽⁰⁾ ∉ C¹`).
    - Section I.4: Structural classification informing the next #29 direction —
      (1) Universal `Sym³₀(ℝ³) = H₃(ℝ³)` harmonic trap (`traceFree_sym3_cubic_harmonic`):
          every constant symmetric trace-free 3-tensor is `(1/6) ∇³P` of a harmonic cubic,
          explaining why G6 fails for *every* non-oscillatory leading tensor `C`;
      (2) General Sublinear-Hessian Poincaré `C²` Regularity Theorem
          (`contDiffOn_two_poincareVectorPotential`,
           `symmetricCurlSystem_of_sublinear_second_deriv`): *any* `C¹` divergence-free
          field on `ball 0 R` that is `C²` on `ball 0 R \ {0}` with `‖z‖ * ‖D²F(z)‖ → 0`
          as `z → 0` has a global `C²` radial-homotopy vector potential `G`, ruling out
          the entire class of single-point sublinear-Hessian / radial-logarithmic candidates;
      (3) Gauge-invariant fourth-order planar duality identity & `L∞–L¹` bound
          (`planar_c2_div_fourth_order_duality`, `planar_c2_div_fourth_order_bound`),
          isolating the exact `∂ₓ²∂ᵧ²` vs `(∂ₓ³, ∂ᵧ³)` test functional across all `C²` gauges.
-/

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.Pi
import Rudin.PMA.AxiomAudit
import Rudin.PMA.Chapter10.FtildeDisproofStatement
import Rudin.PMA.Chapter10.VectorPotentials
import Rudin.PMA.Chapter10.RadialPrimitive
import Rudin.PMA.Chapter10.PotentialRegularity

noncomputable section
set_option autoImplicit false

open Set Function Filter MeasureTheory Metric
open scoped Topology BigOperators Interval

namespace Rudin.PMA.Chapter10

/-!
### Section I.1: Exact Surface-Measure Monomial Integrals on `S²` and Split `(A)`
-/

/-- The canonical Euclidean surface measure on the unit sphere `S² ⊂ ℝ³`,
given by `MeasureTheory.Measure.toSphere volume` (total mass `3 * (4π/3) = 4π`). -/
def sphereSurfaceMeasure : Measure (sphere (0 : Euclidean 3) 1) :=
  MeasureTheory.Measure.toSphere (volume : Measure (Euclidean 3))

instance : IsFiniteMeasure sphereSurfaceMeasure := by
  dsimp [sphereSurfaceMeasure]
  infer_instance

lemma sphereSurfaceMeasure_real_univ :
    sphereSurfaceMeasure.real univ = 4 * Real.pi := by
  rw [sphereSurfaceMeasure, Measure.toSphere_real_apply_univ]
  have hdim : Module.finrank ℝ (Euclidean 3) = 3 := by simp
  have hvol : (volume : Measure (Euclidean 3)).real (ball 0 1) = 4 * Real.pi / 3 := by
    rw [Measure.real, EuclideanSpace.volume_ball_fin_three]
    have hnn : 0 ≤ Real.pi * 4 / 3 := by positivity
    simp [ENNReal.toReal_ofReal hnn]
    ring
  rw [hdim, hvol]
  norm_num
  ring

/-- Odd double factorial `(2k - 1)!! = 1 · 3 · 5 ⋯ (2k - 1)`, with `(-1)!! = 1`. -/
def oddDoubleFact : ℕ → ℕ
  | 0 => 1
  | k + 1 => (2 * k + 1) * oddDoubleFact k

lemma oddDoubleFact_pos (k : ℕ) : 0 < oddDoubleFact k := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [oddDoubleFact]
    exact Nat.mul_pos (by omega) ih

/-- Normalized average `(1 / 4π) ∫_{S²} θ₀^e₀ θ₁^e₁ θ₂^e₂ dσ` on the unit sphere. -/
def sphereMonomialAvg (e₀ e₁ e₂ : ℕ) : ℝ :=
  if e₀ % 2 = 0 ∧ e₁ % 2 = 0 ∧ e₂ % 2 = 0 then
    ((oddDoubleFact (e₀ / 2) * oddDoubleFact (e₁ / 2) * oddDoubleFact (e₂ / 2) : ℕ) : ℝ) /
      (oddDoubleFact (e₀ / 2 + e₁ / 2 + e₂ / 2 + 1) : ℝ)
  else 0

lemma gamma_nat_add_half (k : ℕ) :
    Real.Gamma ((k : ℝ) + 1 / 2) =
      (oddDoubleFact k : ℝ) / (2 : ℝ) ^ k * √Real.pi := by
  induction k with
  | zero =>
    simp only [oddDoubleFact, Nat.cast_zero, zero_add, Nat.cast_one, pow_zero, div_one, one_mul]
    exact Real.Gamma_one_half_eq
  | succ k ih =>
    have hpos : (0 : ℝ) < (k : ℝ) + 1 / 2 := by positivity
    have hshift : ((k + 1 : ℕ) : ℝ) + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [hshift, Real.Gamma_add_one hpos.ne', ih]
    simp only [oddDoubleFact, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, pow_succ]
    ring

lemma integral_line_pow_mul_exp_neg_sq (e : ℕ) :
    (∫ t : ℝ, t ^ e * Real.exp (-t ^ 2)) =
      if e % 2 = 0 then Real.Gamma ((e / 2 : ℕ) + 1 / 2) else 0 := by
  split_ifs with he
  · obtain ⟨m, rfl⟩ : ∃ m, e = 2 * m := ⟨e / 2, by omega⟩
    have hm_div : (2 * m) / 2 = m := by omega
    rw [hm_div]
    have heven : (fun t : ℝ => t ^ (2 * m) * Real.exp (-t ^ 2)) =
        fun t : ℝ => |t| ^ ((2 * m : ℕ) : ℝ) * Real.exp (-|t| ^ (2 : ℝ)) := by
      funext t
      rw [Real.rpow_natCast, Real.rpow_two, sq_abs]
      have h1 : |t| ^ (2 * m) = t ^ (2 * m) := by
        rw [pow_mul, pow_mul, sq_abs]
      rw [h1]
    rw [heven, integral_comp_abs
      (f := fun x : ℝ => x ^ ((2 * m : ℕ) : ℝ) * Real.exp (-x ^ (2 : ℝ)))]
    have hIoi := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((2 * m : ℕ) : ℝ))
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (2 * m)])
    rw [hIoi]
    have harg : (((2 * m : ℕ) : ℝ) + 1) / 2 = (m : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [harg]
    ring
  · have hodd : Odd e := Nat.not_even_iff_odd.mp (fun h => he (Nat.even_iff.mp h))
    have hneg : ∀ t : ℝ, (-t) ^ e * Real.exp (-(-t) ^ 2) = -(t ^ e * Real.exp (-t ^ 2)) := by
      intro t
      rw [hodd.neg_pow, neg_sq, neg_mul]
    have hcomp := integral_neg_eq_self (f := fun t : ℝ => t ^ e * Real.exp (-t ^ 2)) (μ := volume)
    simp only [hneg, integral_neg] at hcomp
    linarith

lemma integral_euclidean3_monomial_gaussian (e₀ e₁ e₂ : ℕ) :
    (∫ x : Euclidean 3, x 0 ^ e₀ * x 1 ^ e₁ * x 2 ^ e₂ * Real.exp (-‖x‖ ^ 2)) =
      (∫ t : ℝ, t ^ e₀ * Real.exp (-t ^ 2)) *
        (∫ t : ℝ, t ^ e₁ * Real.exp (-t ^ 2)) *
        (∫ t : ℝ, t ^ e₂ * Real.exp (-t ^ 2)) := by
  let expAt : Fin 3 → ℕ := fun i =>
    if i = 0 then e₀ else if i = 1 then e₁ else e₂
  have hmp := PiLp.volume_preserving_toLp (Fin 3)
  rw [← hmp.integral_comp (MeasurableEquiv.measurableEmbedding (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)))]
  have hfun : (fun y : Fin 3 → ℝ =>
      (WithLp.toLp 2 y) 0 ^ e₀ * (WithLp.toLp 2 y) 1 ^ e₁ * (WithLp.toLp 2 y) 2 ^ e₂ *
        Real.exp (-‖(WithLp.toLp 2 y : Euclidean 3)‖ ^ 2)) =
      fun y : Fin 3 → ℝ => ∏ i : Fin 3, (y i ^ (expAt i) * Real.exp (-y i ^ 2)) := by
    funext y
    have hnorm : ‖(WithLp.toLp 2 y : Euclidean 3)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, add_assoc] using
        EuclideanSpace.norm_sq_eq (WithLp.toLp 2 y : Euclidean 3)
    have hexp : Real.exp (-(y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2)) =
        Real.exp (-y 0 ^ 2) * Real.exp (-y 1 ^ 2) * Real.exp (-y 2 ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    change y 0 ^ e₀ * y 1 ^ e₁ * y 2 ^ e₂ * Real.exp (-‖(WithLp.toLp 2 y : Euclidean 3)‖ ^ 2) = _
    rw [hnorm, hexp]
    simp only [Fin.prod_univ_three, expAt]
    norm_num
    ring
  change ∫ y : Fin 3 → ℝ,
      (WithLp.toLp 2 y) 0 ^ e₀ * (WithLp.toLp 2 y) 1 ^ e₁ * (WithLp.toLp 2 y) 2 ^ e₂ *
        Real.exp (-‖(WithLp.toLp 2 y : Euclidean 3)‖ ^ 2) = _
  rw [hfun, MeasureTheory.integral_fin_nat_prod_volume_eq_prod
    (fun i (t : ℝ) => t ^ (expAt i) * Real.exp (-t ^ 2))]
  simp only [Fin.prod_univ_three, expAt]
  norm_num

lemma integral_polar_monomial_gaussian (e₀ e₁ e₂ : ℕ) :
    (∫ x : Euclidean 3, x 0 ^ e₀ * x 1 ^ e₁ * x 2 ^ e₂ * Real.exp (-‖x‖ ^ 2)) =
      (∫ θ : sphere (0 : Euclidean 3) 1,
        (θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂ ∂sphereSurfaceMeasure) *
      ((1 / 2 : ℝ) * Real.Gamma (((e₀ + e₁ + e₂ : ℕ) + 3 : ℝ) / 2)) := by
  let g : Euclidean 3 → ℝ := fun x => x 0 ^ e₀ * x 1 ^ e₁ * x 2 ^ e₂ * Real.exp (-‖x‖ ^ 2)
  change ∫ x : Euclidean 3, g x = _
  have h1 : ∫ x : Euclidean 3, g x =
      ∫ x : ({(0 : Euclidean 3)}ᶜ : Set (Euclidean 3)), g x.1 ∂(volume.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]
  rw [h1]
  have hmp := (volume : Measure (Euclidean 3)).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ (Euclidean 3) - 1 = 2 := by simp
  let G : sphere (0 : Euclidean 3) 1 × Ioi (0 : ℝ) → ℝ := fun p =>
    ((p.1.1 0) ^ e₀ * (p.1.1 1) ^ e₁ * (p.1.1 2) ^ e₂) *
      (p.2.1 ^ (e₀ + e₁ + e₂) * Real.exp (-p.2.1 ^ 2))
  have hcomp : (g ∘ Subtype.val) = G ∘ homeomorphUnitSphereProd (Euclidean 3) := by
    funext x
    have hx0 : (x : Euclidean 3) ≠ 0 := x.2
    have hnorm : 0 < ‖(x : Euclidean 3)‖ := norm_pos_iff.mpr hx0
    simp only [Function.comp_apply, g, G, homeomorphUnitSphereProd_apply_fst_coe,
      homeomorphUnitSphereProd_apply_snd_coe, PiLp.smul_apply, smul_eq_mul]
    have hinv : ‖(x : Euclidean 3)‖⁻¹ * ‖(x : Euclidean 3)‖ = 1 := inv_mul_cancel₀ hnorm.ne'
    calc
      (x.1 0) ^ e₀ * (x.1 1) ^ e₁ * (x.1 2) ^ e₂ * Real.exp (-‖x.1‖ ^ 2)
        = (‖x.1‖⁻¹ * x.1 0) ^ e₀ * (‖x.1‖⁻¹ * x.1 1) ^ e₁ * (‖x.1‖⁻¹ * x.1 2) ^ e₂ *
            (‖x.1‖ ^ (e₀ + e₁ + e₂) * Real.exp (-‖x.1‖ ^ 2)) := by
          rw [mul_pow, mul_pow, mul_pow, pow_add, pow_add]
          have he0 : ‖x.1‖⁻¹ ^ e₀ * ‖x.1‖ ^ e₀ = 1 := by rw [← mul_pow, hinv, one_pow]
          have he1 : ‖x.1‖⁻¹ ^ e₁ * ‖x.1‖ ^ e₁ = 1 := by rw [← mul_pow, hinv, one_pow]
          have he2 : ‖x.1‖⁻¹ ^ e₂ * ‖x.1‖ ^ e₂ = 1 := by rw [← mul_pow, hinv, one_pow]
          linear_combination
            -(x.1 0 ^ e₀ * x.1 1 ^ e₁ * x.1 2 ^ e₂ * Real.exp (-‖x.1‖ ^ 2) *
              (‖x.1‖⁻¹ ^ e₁ * ‖x.1‖ ^ e₁ * (‖x.1‖⁻¹ ^ e₂ * ‖x.1‖ ^ e₂))) * he0 -
            (x.1 0 ^ e₀ * x.1 1 ^ e₁ * x.1 2 ^ e₂ * Real.exp (-‖x.1‖ ^ 2) *
              (‖x.1‖⁻¹ ^ e₂ * ‖x.1‖ ^ e₂)) * he1 -
            (x.1 0 ^ e₀ * x.1 1 ^ e₁ * x.1 2 ^ e₂ * Real.exp (-‖x.1‖ ^ 2)) * he2
      _ = _ := rfl
  change ∫ x : ({(0 : Euclidean 3)}ᶜ : Set (Euclidean 3)), (g ∘ Subtype.val) x ∂(volume.comap Subtype.val) = _
  rw [hcomp]
  change ∫ x : ({(0 : Euclidean 3)}ᶜ : Set (Euclidean 3)),
      G (homeomorphUnitSphereProd (Euclidean 3) x) ∂(volume.comap Subtype.val) = _
  rw [hmp.integral_comp (Homeomorph.measurableEmbedding _) G, hdim]
  dsimp only [G]
  rw [MeasureTheory.integral_prod_mul
    (f := fun θ : sphere (0 : Euclidean 3) 1 => (θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂)
    (g := fun r : Ioi (0 : ℝ) => r.1 ^ (e₀ + e₁ + e₂) * Real.exp (-r.1 ^ 2))]
  congr 1
  · simp only [Measure.volumeIoiPow, ENNReal.ofReal]
    rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const 2).real_toNNReal)]
    rw [integral_subtype_comap measurableSet_Ioi
      (fun a : ℝ => Real.toNNReal (a ^ 2) • (a ^ (e₀ + e₁ + e₂) * Real.exp (-a ^ 2)))]
    have hcongr : EqOn
        (fun a : ℝ => Real.toNNReal (a ^ 2) • (a ^ (e₀ + e₁ + e₂) * Real.exp (-a ^ 2)))
        (fun a : ℝ => a ^ ((e₀ + e₁ + e₂ : ℕ) + 2 : ℝ) * Real.exp (-a ^ (2 : ℝ)))
        (Ioi 0) := by
      intro a (ha : 0 < a)
      dsimp only
      rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg a), Real.rpow_two]
      have hpow : a ^ ((e₀ + e₁ + e₂ : ℕ) + 2 : ℝ) = a ^ 2 * a ^ (e₀ + e₁ + e₂) := by
        have hnat : ((e₀ + e₁ + e₂ : ℕ) + 2 : ℝ) = ((e₀ + e₁ + e₂ + 2 : ℕ) : ℝ) := by push_cast; ring
        rw [hnat, Real.rpow_natCast, pow_add]
        ring
      rw [hpow]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    have hgam := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((e₀ + e₁ + e₂ : ℕ) + 2 : ℝ))
      (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) (e₀ + e₁ + e₂)])
    rw [hgam]
    congr 2
    ring

/-- Exact closed-form evaluation of every monomial integral over `S²` with respect to
Mathlib's canonical surface measure `sphereSurfaceMeasure = Measure.toSphere volume`. -/
theorem integral_sphere_monomial (e₀ e₁ e₂ : ℕ) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      (θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂ ∂sphereSurfaceMeasure) =
      (4 * Real.pi) * sphereMonomialAvg e₀ e₁ e₂ := by
  have hpol := integral_polar_monomial_gaussian e₀ e₁ e₂
  have hcart := integral_euclidean3_monomial_gaussian e₀ e₁ e₂
  rw [hcart, integral_line_pow_mul_exp_neg_sq, integral_line_pow_mul_exp_neg_sq,
    integral_line_pow_mul_exp_neg_sq] at hpol
  have hrad_pos : 0 < (1 / 2 : ℝ) * Real.Gamma (((e₀ + e₁ + e₂ : ℕ) + 3 : ℝ) / 2) := by
    apply mul_pos (by norm_num)
    exact Real.Gamma_pos_of_pos (by positivity)
  by_cases he : e₀ % 2 = 0 ∧ e₁ % 2 = 0 ∧ e₂ % 2 = 0
  · rcases he with ⟨h0, h1, h2⟩
    simp only [sphereMonomialAvg, h0, h1, h2, and_self, ↓reduceIte]
    simp only [h0, h1, h2, ↓reduceIte] at hpol
    obtain ⟨a, rfl⟩ : ∃ a, e₀ = 2 * a := ⟨e₀ / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, e₁ = 2 * b := ⟨e₁ / 2, by omega⟩
    obtain ⟨c, rfl⟩ : ∃ c, e₂ = 2 * c := ⟨e₂ / 2, by omega⟩
    have ha : (2 * a) / 2 = a := by omega
    have hb : (2 * b) / 2 = b := by omega
    have hc : (2 * c) / 2 = c := by omega
    rw [ha, hb, hc] at hpol ⊢
    have hsum : (((2 * a + 2 * b + 2 * c : ℕ) + 3 : ℝ) / 2) =
        ((a + b + c + 1 : ℕ) : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hsum] at hpol hrad_pos
    rw [gamma_nat_add_half a, gamma_nat_add_half b, gamma_nat_add_half c,
      gamma_nat_add_half (a + b + c + 1)] at hpol
    have hdf_pos : (0 : ℝ) < (oddDoubleFact (a + b + c + 1) : ℝ) :=
      Nat.cast_pos.mpr (oddDoubleFact_pos _)
    have hsq2 : √Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
    have hpow2 : (2 : ℝ) ^ (a + b + c + 1) = 2 * ((2 : ℝ) ^ a * (2 : ℝ) ^ b * (2 : ℝ) ^ c) := by
      rw [pow_add, pow_add, pow_add, pow_one]
      ring
    apply mul_right_cancel₀ hrad_pos.ne'
    rw [gamma_nat_add_half (a + b + c + 1), ← hpol, hpow2]
    have h2a : (2 : ℝ) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2b : (2 : ℝ) ^ b ≠ 0 := pow_ne_zero _ two_ne_zero
    have h2c : (2 : ℝ) ^ c ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp [hdf_pos.ne', h2a, h2b, h2c]
    push_cast
    rw [hsq2]
    ring
  · simp only [sphereMonomialAvg, he, ↓reduceIte, mul_zero]
    have hzero : ((if e₀ % 2 = 0 then Real.Gamma (↑(e₀ / 2) + 1 / 2) else 0) *
        (if e₁ % 2 = 0 then Real.Gamma (↑(e₁ / 2) + 1 / 2) else 0) *
        if e₂ % 2 = 0 then Real.Gamma (↑(e₂ / 2) + 1 / 2) else 0) = 0 := by
      by_cases h0 : e₀ % 2 = 0
      · by_cases h1 : e₁ % 2 = 0
        · have h2 : e₂ % 2 ≠ 0 := fun h2 => he ⟨h0, h1, h2⟩
          simp [h2]
        · simp [h1]
      · simp [h0]
    rw [hzero] at hpol
    exact (mul_eq_zero.mp hpol.symm).resolve_right hrad_pos.ne'

lemma integrable_sphere_of_continuous {f : sphere (0 : Euclidean 3) 1 → ℝ}
    (hf : Continuous f) : Integrable f sphereSurfaceMeasure := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ fun θ => hC θ (mem_univ θ))

/-- Any antipodally odd function on `S²` has integral zero with respect to `sphereSurfaceMeasure`. -/
theorem integral_sphere_odd_eq_zero (f : Euclidean 3 → ℝ)
    (hodd : ∀ θ : Euclidean 3, ‖θ‖ = 1 → f (-θ) = -f θ) :
    (∫ θ : sphere (0 : Euclidean 3) 1, f θ.1 ∂sphereSurfaceMeasure) = 0 := by
  let g : Euclidean 3 → ℝ := fun x =>
    if x = 0 then 0 else f (‖x‖⁻¹ • x) * Real.exp (-‖x‖ ^ 2)
  have hg_odd : ∀ x : Euclidean 3, g (-x) = -g x := by
    intro x
    by_cases hx : x = 0
    · simp [g, hx]
    · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
      have hunit : ‖‖x‖⁻¹ • x‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      simp only [g, hx, hnx, ↓reduceIte, norm_neg, smul_neg]
      rw [hodd _ hunit, neg_mul]
  have hint_zero : (∫ x : Euclidean 3, g x) = 0 := by
    have hneg := integral_neg_eq_self (f := g) (μ := volume)
    simp only [hg_odd, integral_neg] at hneg
    linarith
  have h1 : ∫ x : Euclidean 3, g x =
      ∫ x : ({(0 : Euclidean 3)}ᶜ : Set (Euclidean 3)), g x.1 ∂(volume.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl g, restrict_compl_singleton]
  have hmp := (volume : Measure (Euclidean 3)).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ (Euclidean 3) - 1 = 2 := by simp
  let G : sphere (0 : Euclidean 3) 1 × Ioi (0 : ℝ) → ℝ := fun p =>
    f p.1.1 * Real.exp (-p.2.1 ^ 2)
  have hcomp : ∀ x : ({(0 : Euclidean 3)}ᶜ : Set (Euclidean 3)),
      g x.1 = G (homeomorphUnitSphereProd (Euclidean 3) x) := by
    intro x
    have hx0 : (x : Euclidean 3) ≠ 0 := x.2
    simp [g, G, hx0, homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe]
  rw [h1, integral_congr_ae (ae_of_all _ hcomp),
    hmp.integral_comp (Homeomorph.measurableEmbedding _) G, hdim] at hint_zero
  dsimp only [G] at hint_zero
  rw [MeasureTheory.integral_prod_mul
    (f := fun θ : sphere (0 : Euclidean 3) 1 => f θ.1)
    (g := fun r : Ioi (0 : ℝ) => Real.exp (-r.1 ^ 2))] at hint_zero
  have hrad : (∫ r : Ioi (0 : ℝ), Real.exp (-r.1 ^ 2) ∂Measure.volumeIoiPow 2) =
      (1 / 2 : ℝ) * Real.Gamma (3 / 2) := by
    simp only [Measure.volumeIoiPow, ENNReal.ofReal]
    rw [integral_withDensity_eq_integral_smul ((measurable_subtype_coe.pow_const 2).real_toNNReal),
      integral_subtype_comap measurableSet_Ioi
        (fun a : ℝ => Real.toNNReal (a ^ 2) • Real.exp (-a ^ 2))]
    have hcongr : EqOn (fun a : ℝ => Real.toNNReal (a ^ 2) • Real.exp (-a ^ 2))
        (fun a : ℝ => a ^ (2 : ℝ) * Real.exp (-a ^ (2 : ℝ))) (Ioi 0) := by
      intro a (_ha : 0 < a)
      dsimp only
      rw [NNReal.smul_def, Real.coe_toNNReal _ (sq_nonneg a), Real.rpow_two, smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr]
    have hgam := integral_rpow_mul_exp_neg_rpow (p := 2) (q := 2) (by norm_num) (by norm_num)
    rw [hgam]
    norm_num
  rw [hrad] at hint_zero
  have hpos : 0 < (1 / 2 : ℝ) * Real.Gamma (3 / 2) :=
    mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by norm_num))
  exact (mul_eq_zero.mp hint_zero).resolve_right hpos.ne'

/-- First Fréchet derivative of an antipodally odd scalar function is antipodally even. -/
lemma fderiv_odd_is_even {χ : Euclidean 3 → ℝ} (hodd : ∀ x, χ (-x) = -χ x)
    (y v : Euclidean 3) :
    fderiv ℝ χ (-y) v = fderiv ℝ χ y v := by
  let negCLM : Euclidean 3 →L[ℝ] Euclidean 3 := -ContinuousLinearMap.id ℝ (Euclidean 3)
  have h1 : fderiv ℝ (χ ∘ negCLM) y = (fderiv ℝ χ (negCLM y)).comp negCLM := by
    by_cases hy : DifferentiableAt ℝ χ (negCLM y)
    · rw [fderiv_comp y hy negCLM.differentiableAt, negCLM.fderiv]
    · have hny : ¬ DifferentiableAt ℝ (χ ∘ negCLM) y := by
        intro hc
        apply hy
        have hinv : χ = (χ ∘ negCLM) ∘ negCLM := by
          funext z
          simp [negCLM]
        have heq : negCLM (negCLM y) = y := by simp [negCLM]
        rw [hinv]
        rw [← heq] at hc
        exact hc.comp (negCLM y) negCLM.differentiableAt
      rw [fderiv_zero_of_not_differentiableAt hny, fderiv_zero_of_not_differentiableAt hy]
      simp
  have h2 : χ ∘ negCLM = -χ := by
    funext z
    simpa [negCLM] using hodd z
  rw [h2, fderiv_neg] at h1
  have hv := congrArg (fun L : Euclidean 3 →L[ℝ] ℝ => L v) h1
  simp only [neg_apply, ContinuousLinearMap.comp_apply, negCLM,
    ContinuousLinearMap.id_apply, map_neg, neg_inj] at hv
  exact hv.symm

/-- Second directional derivative of an antipodally odd scalar function is antipodally odd. -/
lemma twice_fderiv_odd_is_odd {χ : Euclidean 3 → ℝ} (hodd : ∀ x, χ (-x) = -χ x)
    (a b : Fin 3) (θ : Euclidean 3) :
    fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector 3 b)) (-θ) (coordinateVector 3 a) =
      -fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector 3 b)) θ (coordinateVector 3 a) := by
  let g : Euclidean 3 → ℝ := fun y => fderiv ℝ χ y (coordinateVector 3 b)
  have hg_even : ∀ y, g (-y) = g y := fun y => fderiv_odd_is_even hodd y (coordinateVector 3 b)
  let negCLM : Euclidean 3 →L[ℝ] Euclidean 3 := -ContinuousLinearMap.id ℝ (Euclidean 3)
  have h1 : fderiv ℝ (g ∘ negCLM) θ = (fderiv ℝ g (negCLM θ)).comp negCLM := by
    by_cases hθ : DifferentiableAt ℝ g (negCLM θ)
    · rw [fderiv_comp θ hθ negCLM.differentiableAt, negCLM.fderiv]
    · have hnθ : ¬ DifferentiableAt ℝ (g ∘ negCLM) θ := by
        intro hc
        apply hθ
        have hinv : g = (g ∘ negCLM) ∘ negCLM := by
          funext z
          simp [negCLM]
        have heq : negCLM (negCLM θ) = θ := by simp [negCLM]
        rw [hinv]
        rw [← heq] at hc
        exact hc.comp (negCLM θ) negCLM.differentiableAt
      rw [fderiv_zero_of_not_differentiableAt hnθ, fderiv_zero_of_not_differentiableAt hθ]
      simp
  have h2 : g ∘ negCLM = g := by
    funext z
    simpa [negCLM] using hg_even z
  rw [h2] at h1
  have hv := congrArg (fun L : Euclidean 3 →L[ℝ] ℝ => L (coordinateVector 3 a)) h1
  simp only [ContinuousLinearMap.comp_apply, negCLM, neg_apply,
    ContinuousLinearMap.id_apply, map_neg] at hv
  linarith

/-- Transverse stream-shift vector field `(0, -∂₃χ, ∂₂χ)` (in 0-based indices `(0, -∂₂χ, ∂₁χ)`)
used in issue #29 comments 6543364135, 6543703714, and 6544302798. -/
def streamShiftField (χ : Euclidean 3 → ℝ) : VectorField :=
  fun x => coordEquivEuclidean 3
    ![0, -fderiv ℝ χ x (coordinateVector 3 2), fderiv ℝ χ x (coordinateVector 3 1)]

/-- Jacobian profile of a transverse stream-shift field. -/
def streamShiftD (χ : Euclidean 3 → ℝ) (a n : Fin 3) (θ : Euclidean 3) : ℝ :=
  fderiv ℝ (fun y => streamShiftField χ y n) θ (coordinateVector 3 a)

/-- **Part `(A)` of Derek's Completion-Independence Split (comments 6543364135 & 6543703714):**
For any antipodally even CZ kernel `Ω` (`Ω (-θ) = Ω θ`, satisfied by all `l ∈ {2, 4}` kernels)
and any antipodally odd stream function `χ` (`χ (-x) = -χ x`, e.g. `χ(x) = ‖x‖² c(x/‖x‖)` with
`c(-θ) = -c(θ)`), every angular pairing of `streamShiftD χ` against `Ω(-θ)` vanishes identically. -/
theorem odd_stream_completion_cz_vanishes {Ω χ : Euclidean 3 → ℝ}
    (hΩ : ∀ θ, Ω (-θ) = Ω θ) (hχ : ∀ x, χ (-x) = -χ x) (a n : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      Ω (-θ.1) * streamShiftD χ a n θ.1 ∂sphereSurfaceMeasure) = 0 := by
  refine integral_sphere_odd_eq_zero (fun y => Ω (-y) * streamShiftD χ a n y) ?_
  intro θ _hθ
  rw [neg_neg, hΩ θ]
  have hd : streamShiftD χ a n (-θ) = -streamShiftD χ a n θ := by
    fin_cases n
    · simp [streamShiftD, streamShiftField]
    · change fderiv ℝ (-(fun y => fderiv ℝ χ y (coordinateVector 3 2))) (-θ) (coordinateVector 3 a) =
        -fderiv ℝ (-(fun y => fderiv ℝ χ y (coordinateVector 3 2))) θ (coordinateVector 3 a)
      rw [fderiv_neg, fderiv_neg, neg_apply, neg_apply, twice_fderiv_odd_is_odd hχ a 2 θ, neg_neg]
    · change fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector 3 1)) (-θ) (coordinateVector 3 a) =
        -fderiv ℝ (fun y => fderiv ℝ χ y (coordinateVector 3 1)) θ (coordinateVector 3 a)
      exact twice_fderiv_odd_is_odd hχ a 1 θ
  rw [hd, mul_neg]

/-!
## Section I.2: Closing Gap `(a2)` and Split `(B)` (Angular Identification `A = ftildeC`)

We formalize BOTH independent routes to `A = ftildeC` over Mathlib's genuine surface measure
`sphereSurfaceMeasure = Measure.toSphere volume`:
1. **Route 1 (Biot–Savart dipole kernel):** pairing `ftildeD` against the mean-zero `l = 2`
   dipole kernel `-(1/(4π))((δ_{km} - 3 θ_k θ_m))` contracted with the 3D Levi-Civita tensor;
2. **Route 2 (G3/G4 degree-4 Fourier symbol + Funk–Hecke eigenvalues):** decomposing the exact
   symbol `m_{ijk}^{an}(ξ̂)` on `S²` into `l = 0, 2, 4` spherical harmonics, isolating the local
   `l = 0` contact mean `c₀` (`48` nonzero entries `±1/15, ±1/30`, which produces `c₀ · dF̃(x) = O(ψ)`
   and never enters the shell coefficient per comment 6545396969), dividing the `l = 2` and `l = 4`
   parts by `c₂ = -4π/3` and `c₄ = 8π/15` to form the mean-zero physical CZ kernel `ftildeCZKernel`,
   and integrating `∑_{a,n} ∫_{S²} Ω_{ijk}^{an}(-θ) D_{a,n}(θ) dσ(θ) = ftildeC i j k`.

We also close **Part `(B)`** of Derek's split (comments 6543364135 & 6543703714) in Lean:
the unshifted potential-compensated field `ftildeVBase` has identically zero angular coefficient
`A_base = 0` for all `(i, j, k)`, NOT because the isolated first-row functional vanishes (we prove
at `(0, 2, 0)` it equals `-4 / 77 ≠ 0`), nor by radial suppression, but by exact algebraic
cancellation between `V_0 e_0` and the compensating potential rows `(∂_1 M, ∂_2 M)`.
-/

@[fun_prop]
private lemma continuous_euclidean_apply (i : Fin 3) :
    Continuous (fun x : Euclidean 3 => x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

@[fun_prop]
private lemma differentiable_euclidean_apply (i : Fin 3) :
    Differentiable ℝ (fun x : Euclidean 3 => x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).differentiable

@[fun_prop]
private lemma contDiff_euclidean_apply {m : WithTop ℕ∞} (i : Fin 3) :
    ContDiff ℝ m (fun x : Euclidean 3 => x i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff

@[fun_prop]
private lemma continuous_sphere_coord (i : Fin 3) :
    Continuous (fun θ : sphere (0 : Euclidean 3) 1 => θ.1 i) :=
  (continuous_euclidean_apply i).comp continuous_subtype_val

@[elab_as_elim]
private lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (i : Fin 3) : P i := by
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma integral_sphere_add' {f g : sphere (0 : Euclidean 3) 1 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ θ : sphere (0 : Euclidean 3) 1, f θ + g θ ∂sphereSurfaceMeasure) =
      (∫ θ : sphere (0 : Euclidean 3) 1, f θ ∂sphereSurfaceMeasure) +
      (∫ θ : sphere (0 : Euclidean 3) 1, g θ ∂sphereSurfaceMeasure) :=
  integral_add (integrable_sphere_of_continuous hf) (integrable_sphere_of_continuous hg)

lemma integral_sphere_sub' {f g : sphere (0 : Euclidean 3) 1 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    (∫ θ : sphere (0 : Euclidean 3) 1, f θ - g θ ∂sphereSurfaceMeasure) =
      (∫ θ : sphere (0 : Euclidean 3) 1, f θ ∂sphereSurfaceMeasure) -
      (∫ θ : sphere (0 : Euclidean 3) 1, g θ ∂sphereSurfaceMeasure) :=
  integral_sub (integrable_sphere_of_continuous hf) (integrable_sphere_of_continuous hg)

lemma integral_sphere_const_mul' (c : ℝ) (f : sphere (0 : Euclidean 3) 1 → ℝ) :
    (∫ θ : sphere (0 : Euclidean 3) 1, c * f θ ∂sphereSurfaceMeasure) =
      c * ∫ θ : sphere (0 : Euclidean 3) 1, f θ ∂sphereSurfaceMeasure :=
  integral_const_mul c f

lemma integral_sphere_monomial_mul_monomial (e₀ e₁ e₂ p₀ p₁ p₂ : ℕ) (c : ℝ) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      ((θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂) *
        (c * ((θ.1 0) ^ p₀ * (θ.1 1) ^ p₁ * (θ.1 2) ^ p₂)) ∂sphereSurfaceMeasure) =
      (4 * Real.pi) * (c * sphereMonomialAvg (e₀ + p₀) (e₁ + p₁) (e₂ + p₂)) := by
  have hcongr : (fun θ : sphere (0 : Euclidean 3) 1 =>
      ((θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂) *
        (c * ((θ.1 0) ^ p₀ * (θ.1 1) ^ p₁ * (θ.1 2) ^ p₂))) =
      fun θ : sphere (0 : Euclidean 3) 1 =>
        c * ((θ.1 0) ^ (e₀ + p₀) * (θ.1 1) ^ (e₁ + p₁) * (θ.1 2) ^ (e₂ + p₂)) := by
    funext θ
    simp only [pow_add]
    ring
  rw [hcongr, integral_const_mul, integral_sphere_monomial]
  ring

/-- Fast `simp`-reducible `Fin 3` lookup avoiding `Matrix.vecCons` closures and `ite` conditions. -/
def fin3Vec {α : Type*} (x₀ x₁ x₂ : α) (i : Fin 3) : α :=
  if i = 0 then x₀ else if i = 1 then x₁ else x₂

@[simp] private lemma fin3Vec_zero {α : Type*} (x₀ x₁ x₂ : α) : fin3Vec x₀ x₁ x₂ 0 = x₀ := rfl
@[simp] private lemma fin3Vec_one {α : Type*} (x₀ x₁ x₂ : α) : fin3Vec x₀ x₁ x₂ 1 = x₁ := rfl
@[simp] private lemma fin3Vec_two {α : Type*} (x₀ x₁ x₂ : α) : fin3Vec x₀ x₁ x₂ 2 = x₂ := rfl

/-- Fast `simp`-reducible `3 × 3` lookup avoiding `Matrix.vecCons` closures and `ite` conditions. -/
def fin3Mat {α : Type*}
    (x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ : α) (a n : Fin 3) : α :=
  fin3Vec (fin3Vec x₀₀ x₀₁ x₀₂ n) (fin3Vec x₁₀ x₁₁ x₁₂ n) (fin3Vec x₂₀ x₂₁ x₂₂ n) a

@[simp] private lemma fin3Mat_apply {α : Type*}
    (x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ : α) (a n : Fin 3) :
    fin3Mat x₀₀ x₀₁ x₀₂ x₁₀ x₁₁ x₁₂ x₂₀ x₂₁ x₂₂ a n =
      fin3Vec (fin3Vec x₀₀ x₀₁ x₀₂ n) (fin3Vec x₁₀ x₁₁ x₁₂ n) (fin3Vec x₂₀ x₂₁ x₂₂ n) a := rfl

/-- Indicator exponent `1` if `p = m`, else `0`, turning arbitrary index products `θ p * θ q * ...`
into canonical monomials `θ 0 ^ e₀ * θ 1 ^ e₁ * θ 2 ^ e₂` without case-splitting. -/
def coordInd (m p : Fin 3) : ℕ :=
  fin3Mat 1 0 0 0 1 0 0 0 1 m p

lemma coord_eq_pow_prod (v : Euclidean 3) (p : Fin 3) :
    v p = v 0 ^ coordInd 0 p * v 1 ^ coordInd 1 p * v 2 ^ coordInd 2 p := by
  cases p using fin3_cases <;> simp [coordInd]

lemma coord2_eq_pow_prod (v : Euclidean 3) (p q : Fin 3) :
    v p * v q =
      v 0 ^ (coordInd 0 p + coordInd 0 q) *
        v 1 ^ (coordInd 1 p + coordInd 1 q) *
        v 2 ^ (coordInd 2 p + coordInd 2 q) := by
  rw [coord_eq_pow_prod v p, coord_eq_pow_prod v q]
  simp only [pow_add]
  ring

lemma coord4_eq_pow_prod (v : Euclidean 3) (p q r s : Fin 3) :
    v p * v q * v r * v s =
      v 0 ^ (coordInd 0 p + coordInd 0 q + coordInd 0 r + coordInd 0 s) *
        v 1 ^ (coordInd 1 p + coordInd 1 q + coordInd 1 r + coordInd 1 s) *
        v 2 ^ (coordInd 2 p + coordInd 2 q + coordInd 2 r + coordInd 2 s) := by
  rw [coord_eq_pow_prod v p, coord_eq_pow_prod v q, coord_eq_pow_prod v r, coord_eq_pow_prod v s]
  simp only [pow_add]
  ring

/-- Kronecker delta on `Fin 3`. -/
def kronecker3 (i j : Fin 3) : ℝ :=
  fin3Mat 1 0 0 0 1 0 0 0 1 i j

/-- 3D Levi-Civita symbol `ε_{ijk}` in zero-based coordinates. -/
def leviCivita3 (i j k : Fin 3) : ℝ :=
  fin3Vec
    (fin3Mat 0 0 0 0 0 1 0 (-1) 0 j k)
    (fin3Mat 0 0 (-1) 0 0 0 1 0 0 j k)
    (fin3Mat 0 1 0 (-1) 0 0 0 0 0 j k)
    i

private lemma ftildeC_eq_fin3 (i j k : Fin 3) :
    ftildeC i j k =
      fin3Vec
        (fin3Mat (-8 / 35) 0 0 0 (32 / 105) 0 0 0 (-8 / 105) j k)
        (fin3Mat 0 (32 / 105) 0 (32 / 105) 0 0 0 0 0 j k)
        (fin3Mat 0 0 (-8 / 105) 0 0 0 (-8 / 105) 0 0 j k)
        i := by
  cases i using fin3_cases <;> cases j using fin3_cases <;> cases k using fin3_cases <;>
    norm_num [ftildeC, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]

/-- Exact polynomial formulas for all 9 Jacobian profile entries `ftildeD a n θ` on `‖θ‖ = 1`. -/
def ftildeDPoly (a n : Fin 3) (θ : Euclidean 3) : ℝ :=
  fin3Mat
    ((6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 7 * θ 1 ^ 1 * θ 2 ^ 0))
    ((1 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-8 : ℝ) * (θ 0 ^ 1 * θ 1 ^ 4 * θ 2 ^ 1) +
      (3 / 2 : ℝ) * (θ 0 ^ 2 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-3 : ℝ) * (θ 0 ^ 2 * θ 1 ^ 2 * θ 2 ^ 0) +
      (-9 / 4 : ℝ) * (θ 0 ^ 4 * θ 1 ^ 0 * θ 2 ^ 0) +
      (9 : ℝ) * (θ 0 ^ 4 * θ 1 ^ 2 * θ 2 ^ 0) +
      (1 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 2 * θ 2 ^ 0))
    ((-8 : ℝ) * (θ 0 ^ 1 * θ 1 ^ 3 * θ 2 ^ 0) +
      (8 : ℝ) * (θ 0 ^ 1 * θ 1 ^ 5 * θ 2 ^ 0) +
      (-3 : ℝ) * (θ 0 ^ 2 * θ 1 ^ 1 * θ 2 ^ 1) +
      (9 : ℝ) * (θ 0 ^ 4 * θ 1 ^ 1 * θ 2 ^ 1) +
      (-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 1 * θ 2 ^ 1))
    ((1 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 2 * θ 2 ^ 0))
    ((8 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 3 * θ 2 ^ 1) +
      (-8 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 5 * θ 2 ^ 1) +
      (-3 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 1 * θ 2 ^ 0) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 3 * θ 2 ^ 0) +
      (3 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 3 * θ 2 ^ 0))
    ((12 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 2 * θ 2 ^ 0) +
      (-18 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 4 * θ 2 ^ 0) +
      (8 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 6 * θ 2 ^ 0) +
      (-1 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 0 * θ 2 ^ 1) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 2 * θ 2 ^ 1) +
      (1 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 0 * θ 2 ^ 1) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 2 * θ 2 ^ 1))
    ((-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 1 * θ 2 ^ 1))
    ((2 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 4 * θ 2 ^ 0) +
      (-8 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 4 * θ 2 ^ 2) +
      (-1 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 0 * θ 2 ^ 1) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 2 * θ 2 ^ 1) +
      (1 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 0 * θ 2 ^ 1) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 2 * θ 2 ^ 1))
    ((-8 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 3 * θ 2 ^ 1) +
      (8 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 5 * θ 2 ^ 1) +
      (-1 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 1 * θ 2 ^ 0) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 1 * θ 2 ^ 2) +
      (1 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 2))
    a n

@[fun_prop]
private lemma continuous_ftildeDPoly (a n : Fin 3) : Continuous (ftildeDPoly a n) := by
  change Continuous (fun θ => ftildeDPoly a n θ)
  cases a using fin3_cases <;> cases n using fin3_cases <;>
    · simp only [ftildeDPoly, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      fun_prop

/-- Normalized sphere-average moments `(1/(4π)) ∫_{S²} θ₀^{e₀} θ₁^{e₁} θ₂^{e₂} D_{a,n}(θ) dσ(θ)`. -/
def ftildeDMoment (e₀ e₁ e₂ : ℕ) (a n : Fin 3) : ℝ :=
  fin3Mat
    ((6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 7) (e₁ + 1) (e₂ + 0))
    ((1 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 0) (e₂ + 0) +
      (-8 : ℝ) * sphereMonomialAvg (e₀ + 1) (e₁ + 4) (e₂ + 1) +
      (3 / 2 : ℝ) * sphereMonomialAvg (e₀ + 2) (e₁ + 0) (e₂ + 0) +
      (-3 : ℝ) * sphereMonomialAvg (e₀ + 2) (e₁ + 2) (e₂ + 0) +
      (-9 / 4 : ℝ) * sphereMonomialAvg (e₀ + 4) (e₁ + 0) (e₂ + 0) +
      (9 : ℝ) * sphereMonomialAvg (e₀ + 4) (e₁ + 2) (e₂ + 0) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 0) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 2) (e₂ + 0))
    ((-8 : ℝ) * sphereMonomialAvg (e₀ + 1) (e₁ + 3) (e₂ + 0) +
      (8 : ℝ) * sphereMonomialAvg (e₀ + 1) (e₁ + 5) (e₂ + 0) +
      (-3 : ℝ) * sphereMonomialAvg (e₀ + 2) (e₁ + 1) (e₂ + 1) +
      (9 : ℝ) * sphereMonomialAvg (e₀ + 4) (e₁ + 1) (e₂ + 1) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 1) (e₂ + 1))
    ((1 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 0) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 2) (e₂ + 0))
    ((8 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 3) (e₂ + 1) +
      (-8 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 5) (e₂ + 1) +
      (-3 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 1) (e₂ + 0) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 3) (e₂ + 0) +
      (3 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 3) (e₂ + 0))
    ((12 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 2) (e₂ + 0) +
      (-18 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 4) (e₂ + 0) +
      (8 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 6) (e₂ + 0) +
      (-1 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 0) (e₂ + 1) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 2) (e₂ + 1) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 0) (e₂ + 1) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 2) (e₂ + 1))
    ((-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 1) (e₂ + 1))
    ((2 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 4) (e₂ + 0) +
      (-8 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 4) (e₂ + 2) +
      (-1 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 0) (e₂ + 1) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 2) (e₂ + 1) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 0) (e₂ + 1) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 2) (e₂ + 1))
    ((-8 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 3) (e₂ + 1) +
      (8 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 5) (e₂ + 1) +
      (-1 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 1) (e₂ + 0) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 1) (e₂ + 2) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 2))
    a n

/-- Exact Fréchet derivative evaluation of `ftildeD a n θ` on `S²` (`‖θ‖ = 1`). -/
theorem ftildeD_eq_poly_of_unit {θ : Euclidean 3} (hnorm : ‖θ‖ = 1) (a n : Fin 3) :
    ftildeD a n θ = ftildeDPoly a n θ := by
  have hθ : θ ≠ 0 := by
    intro h0
    simp [h0] at hnorm
  have hr : DifferentiableAt ℝ (fun y : Euclidean 3 => ‖y‖) θ :=
    (differentiableAt_id (x := θ)).norm ℝ hθ
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun x => ftildeTh i (ftildeDir x)) θ := by
    unfold ftildeTh ftildeDir
    fun_prop (disch := aesop)
  cases n using fin3_cases
  · rw [ftildeD, fderiv_ftildeV_zero_eq_core hθ, fderiv_core₁_of_unit hθ hnorm]
    cases a using fin3_cases <;> simp [ftildeDPoly, fin3Mat, fin3Vec] <;> ring
  · rw [ftildeD, fderiv_ftildeV_one_eq_core hθ]
    unfold core₂ ftildeB ftildeB'
    simp (disch := fun_prop) only [div_eq_mul_inv, fderiv_fun_mul, fderiv_fun_pow,
      fderiv_fun_add, fderiv_fun_sub, add_apply, smul_apply, sub_apply, smul_eq_mul, nsmul_eq_mul]
    simp only [fderiv_dir_coordinate_of_unit hθ hnorm, fderiv_norm_euclidean hθ]
    simp only [ftildeTh, ftildeDir, hnorm, inv_one, one_smul]
    cases a using fin3_cases <;> simp [ftildeDPoly, fin3Mat, fin3Vec] <;> ring
  · rw [ftildeD, fderiv_ftildeV_two_eq_core hθ]
    unfold core₃ ftildeB ftildeB'
    simp (disch := fun_prop) only [div_eq_mul_inv, fderiv_fun_mul, fderiv_fun_pow,
      fderiv_fun_add, fderiv_fun_sub, add_apply, smul_apply, sub_apply, smul_eq_mul, nsmul_eq_mul]
    simp only [fderiv_dir_coordinate_of_unit hθ hnorm, fderiv_norm_euclidean hθ]
    simp only [ftildeTh, ftildeDir, hnorm, inv_one, one_smul]
    cases a using fin3_cases <;> simp [ftildeDPoly, fin3Mat, fin3Vec] <;> ring

lemma integral_sphere_monomial_mul_ftildeDPoly (e₀ e₁ e₂ : ℕ) (a n : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      ((θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂) * ftildeDPoly a n θ.1 ∂sphereSurfaceMeasure) =
      (4 * Real.pi) * ftildeDMoment e₀ e₁ e₂ a n := by
  cases a using fin3_cases <;> cases n using fin3_cases <;>
    · simp only [ftildeDPoly, ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try simp (disch := fun_prop) only [mul_add, integral_sphere_add']
      simp only [integral_sphere_monomial_mul_monomial]
      try ring

/-- **Route 1 (Biot–Savart Dipole Kernel):** The mean-zero `l = 2` kernel
`-(1/(4π))(δ_{km} - 3 θ_k θ_m)` governing `∂_k ∂_j (-Δ)⁻¹ (curl F)_i`. -/
noncomputable def biotSavartDipoleKernel (k m : Fin 3) (θ : Euclidean 3) : ℝ :=
  -(1 / (4 * Real.pi)) * (kronecker3 k m - 3 * (θ k * θ m))

lemma biotSavartDipoleKernel_even (k m : Fin 3) (θ : Euclidean 3) :
    biotSavartDipoleKernel k m (-θ) = biotSavartDipoleKernel k m θ := by
  simp [biotSavartDipoleKernel]

lemma biotSavartDipoleKernel_mean_zero (k m : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      biotSavartDipoleKernel k m θ.1 ∂sphereSurfaceMeasure) = 0 := by
  have hrew : (fun θ : sphere (0 : Euclidean 3) 1 => biotSavartDipoleKernel k m θ.1) =
      fun θ : sphere (0 : Euclidean 3) 1 =>
        -(1 / (4 * Real.pi)) *
          (kronecker3 k m * ((θ.1 0) ^ 0 * (θ.1 1) ^ 0 * (θ.1 2) ^ 0) +
            (-3 : ℝ) *
              ((θ.1 0) ^ (coordInd 0 k + coordInd 0 m) *
                (θ.1 1) ^ (coordInd 1 k + coordInd 1 m) *
                (θ.1 2) ^ (coordInd 2 k + coordInd 2 m))) := by
    funext θ
    simp only [biotSavartDipoleKernel, coord2_eq_pow_prod θ.1 k m]
    ring
  rw [hrew, integral_const_mul,
    integral_sphere_add' (by fun_prop) (by fun_prop),
    integral_const_mul, integral_const_mul,
    integral_sphere_monomial, integral_sphere_monomial]
  cases k using fin3_cases <;> cases m using fin3_cases <;>
    · norm_num [kronecker3, coordInd, sphereMonomialAvg, oddDoubleFact]
      try ring

lemma integral_biotSavartDipole_mul_ftildeD (k m a n : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      biotSavartDipoleKernel k m (-θ.1) * ftildeD a n θ.1 ∂sphereSurfaceMeasure) =
      -(kronecker3 k m * ftildeDMoment 0 0 0 a n -
          3 * ftildeDMoment (coordInd 0 k + coordInd 0 m)
            (coordInd 1 k + coordInd 1 m) (coordInd 2 k + coordInd 2 m) a n) := by
  have hcongr : (fun θ : sphere (0 : Euclidean 3) 1 =>
      biotSavartDipoleKernel k m (-θ.1) * ftildeD a n θ.1) =
      fun θ : sphere (0 : Euclidean 3) 1 =>
        -(1 / (4 * Real.pi)) *
          (kronecker3 k m * (((θ.1 0) ^ 0 * (θ.1 1) ^ 0 * (θ.1 2) ^ 0) * ftildeDPoly a n θ.1) -
            3 * (((θ.1 0) ^ (coordInd 0 k + coordInd 0 m) *
              (θ.1 1) ^ (coordInd 1 k + coordInd 1 m) *
              (θ.1 2) ^ (coordInd 2 k + coordInd 2 m)) * ftildeDPoly a n θ.1)) := by
    funext θ
    have hnorm : ‖θ.1‖ = 1 := by simp [mem_sphere_zero_iff_norm.mp θ.2]
    rw [biotSavartDipoleKernel_even, ftildeD_eq_poly_of_unit hnorm]
    simp only [biotSavartDipoleKernel, coord2_eq_pow_prod θ.1 k m]
    ring
  rw [hcongr, integral_const_mul,
    integral_sphere_sub' (by fun_prop) (by fun_prop),
    integral_const_mul, integral_const_mul,
    integral_sphere_monomial_mul_ftildeDPoly, integral_sphere_monomial_mul_ftildeDPoly]
  have hpi : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [hpi]

private lemma dipole_levi_sum_0 (b k : Fin 3) :
    (∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 0 m n *
      ∫ θ : sphere (0 : Euclidean 3) 1,
        biotSavartDipoleKernel k m (-θ.1) * ftildeD b n θ.1 ∂sphereSurfaceMeasure) =
      fin3Mat (-8 / 35) 0 0 0 (32 / 105) 0 0 0 (-8 / 105) b k := by
  simp only [integral_biotSavartDipole_mul_ftildeD, Fin.sum_univ_three, leviCivita3,
    fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
    zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  cases b using fin3_cases <;> cases k using fin3_cases <;>
    norm_num [kronecker3, coordInd, ftildeDMoment, fin3Mat_apply,
      fin3Vec_zero, fin3Vec_one, fin3Vec_two, sphereMonomialAvg, oddDoubleFact]

private lemma dipole_levi_sum_1 (b k : Fin 3) :
    (∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 1 m n *
      ∫ θ : sphere (0 : Euclidean 3) 1,
        biotSavartDipoleKernel k m (-θ.1) * ftildeD b n θ.1 ∂sphereSurfaceMeasure) =
      fin3Mat 0 (32 / 105) 0 (32 / 105) 0 0 0 0 0 b k := by
  simp only [integral_biotSavartDipole_mul_ftildeD, Fin.sum_univ_three, leviCivita3,
    fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
    zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  cases b using fin3_cases <;> cases k using fin3_cases <;>
    norm_num [kronecker3, coordInd, ftildeDMoment, fin3Mat_apply,
      fin3Vec_zero, fin3Vec_one, fin3Vec_two, sphereMonomialAvg, oddDoubleFact]

private lemma dipole_levi_sum_2 (b k : Fin 3) :
    (∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 2 m n *
      ∫ θ : sphere (0 : Euclidean 3) 1,
        biotSavartDipoleKernel k m (-θ.1) * ftildeD b n θ.1 ∂sphereSurfaceMeasure) =
      fin3Mat 0 0 (-8 / 105) 0 0 0 (-8 / 105) 0 0 b k := by
  simp only [integral_biotSavartDipole_mul_ftildeD, Fin.sum_univ_three, leviCivita3,
    fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
    zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
  cases b using fin3_cases <;> cases k using fin3_cases <;>
    norm_num [kronecker3, coordInd, ftildeDMoment, fin3Mat_apply,
      fin3Vec_zero, fin3Vec_one, fin3Vec_two, sphereMonomialAvg, oddDoubleFact]

private lemma dipole_levi_sum (i b k : Fin 3) :
    (∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 i m n *
      ∫ θ : sphere (0 : Euclidean 3) 1,
        biotSavartDipoleKernel k m (-θ.1) * ftildeD b n θ.1 ∂sphereSurfaceMeasure) =
      ftildeC i b k := by
  rw [ftildeC_eq_fin3]
  cases i using fin3_cases
  · simpa using dipole_levi_sum_0 b k
  · simpa using dipole_levi_sum_1 b k
  · simpa using dipole_levi_sum_2 b k

/-- **Closing Gap `(a2)` — Route 1 (Biot–Savart Dipole Kernel):**
Both unsymmetrized and `(i, j)`-symmetrized Biot–Savart dipole angular pairings of `ftildeD`
over `S²` equal `ftildeC i j k` (`-8/35`, `32/105`, `-8/105`). -/
theorem ftilde_dipole_angular_identification (i j k : Fin 3) :
    (1 / 2 : ℝ) *
        ((∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 i m n *
            ∫ θ : sphere (0 : Euclidean 3) 1,
              biotSavartDipoleKernel k m (-θ.1) * ftildeD j n θ.1 ∂sphereSurfaceMeasure) +
          (∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 j m n *
            ∫ θ : sphere (0 : Euclidean 3) 1,
              biotSavartDipoleKernel k m (-θ.1) * ftildeD i n θ.1 ∂sphereSurfaceMeasure)) =
      ftildeC i j k := by
  rw [dipole_levi_sum, dipole_levi_sum, ftildeC_swap_left j i k]
  ring

/-- **Route 2 (G3/G4 Degree-4 Symbol + Funk–Hecke Eigenvalues):**
The exact 0-homogeneous degree-4 Fourier multiplier symbol `m_{ijk}^{an}(ξ̂)` from G3
(comment 6545396969 & 6545747341). -/
def ftildeSymbol (i j k a n : Fin 3) (ξ : Euclidean 3) : ℝ :=
  -(1 / 2 : ℝ) * ∑ m : Fin 3,
    ξ k * (ξ j * leviCivita3 i m n + ξ i * leviCivita3 j m n) * ξ m * ξ a

/-- Normalized `l = 0` sphere average of `ξ_p ξ_q ξ_r ξ_s`. -/
def quarticMean (p q r s : Fin 3) : ℝ :=
  (1 / 15 : ℝ) *
    (kronecker3 p q * kronecker3 r s +
      kronecker3 p r * kronecker3 q s +
      kronecker3 p s * kronecker3 q r)

/-- Degree-2 solid spherical harmonic component `Y_2` of `ξ_p ξ_q ξ_r ξ_s` on `ℝ³`. -/
def quarticHarmonic2 (p q r s : Fin 3) (ξ : Euclidean 3) : ℝ :=
  (1 / 7 : ℝ) *
      (kronecker3 p q * (ξ r * ξ s) +
        kronecker3 p r * (ξ q * ξ s) +
        kronecker3 p s * (ξ q * ξ r) +
        kronecker3 q r * (ξ p * ξ s) +
        kronecker3 q s * (ξ p * ξ r) +
        kronecker3 r s * (ξ p * ξ q)) -
    (10 / 7 : ℝ) * quarticMean p q r s * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)

/-- Degree-4 solid spherical harmonic component `Y_4` of `ξ_p ξ_q ξ_r ξ_s` on `ℝ³`. -/
def quarticHarmonic4 (p q r s : Fin 3) (ξ : Euclidean 3) : ℝ :=
  ξ p * ξ q * ξ r * ξ s -
    (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) * quarticHarmonic2 p q r s ξ -
    quarticMean p q r s * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) ^ 2

/-- Exact solid harmonic decomposition `ξ_p ξ_q ξ_r ξ_s = Y_4(ξ) + |ξ|² Y_2(ξ) + c_0 |ξ|⁴`. -/
lemma quarticMonomial_harmonic_decomp (p q r s : Fin 3) (ξ : Euclidean 3) :
    ξ p * ξ q * ξ r * ξ s =
      quarticHarmonic4 p q r s ξ +
        (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) * quarticHarmonic2 p q r s ξ +
        quarticMean p q r s * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) ^ 2 := by
  unfold quarticHarmonic4
  ring

/-- Scalar Laplacian `∑_{b=0}^2 ∂_b ∂_b f(x)` on `ℝ³`. -/
def scalarLaplacian3 (f : Euclidean 3 → ℝ) (x : Euclidean 3) : ℝ :=
  ∑ b : Fin 3,
    fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector 3 b)) x (coordinateVector 3 b)

private lemma fderiv_coord_euclidean (i b : Fin 3) (y : Euclidean 3) :
    fderiv ℝ (fun z : Euclidean 3 => z i) y (coordinateVector 3 b) =
      if i = b then 1 else 0 := by
  have hc : fderiv ℝ (fun z : Euclidean 3 => z i) y = EuclideanSpace.proj (𝕜 := ℝ) i :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).fderiv
  rw [hc]
  simp [coordinateVector, EuclideanSpace.basisFun_apply]

private lemma scalarLaplacian3_add {f g : Euclidean 3 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Euclidean 3) :
    scalarLaplacian3 (fun z => f z + g z) x = scalarLaplacian3 f x + scalarLaplacian3 g x := by
  have hdf : ∀ b, Differentiable ℝ (fun y => fderiv ℝ f y (coordinateVector 3 b)) := fun b =>
    ((hf.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const).differentiable one_ne_zero
  have hdg : ∀ b, Differentiable ℝ (fun y => fderiv ℝ g y (coordinateVector 3 b)) := fun b =>
    ((hg.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const).differentiable one_ne_zero
  unfold scalarLaplacian3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => f z + g z) y (coordinateVector 3 b)) =
      fun y => fderiv ℝ f y (coordinateVector 3 b) + fderiv ℝ g y (coordinateVector 3 b) := by
    funext y
    rw [fderiv_fun_add (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y),
      add_apply]
  rw [h1, fderiv_fun_add (hdf b x) (hdg b x), add_apply]

private lemma scalarLaplacian3_sub {f g : Euclidean 3 → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Euclidean 3) :
    scalarLaplacian3 (fun z => f z - g z) x = scalarLaplacian3 f x - scalarLaplacian3 g x := by
  have hdf : ∀ b, Differentiable ℝ (fun y => fderiv ℝ f y (coordinateVector 3 b)) := fun b =>
    ((hf.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const).differentiable one_ne_zero
  have hdg : ∀ b, Differentiable ℝ (fun y => fderiv ℝ g y (coordinateVector 3 b)) := fun b =>
    ((hg.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const).differentiable one_ne_zero
  unfold scalarLaplacian3
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => f z - g z) y (coordinateVector 3 b)) =
      fun y => fderiv ℝ f y (coordinateVector 3 b) - fderiv ℝ g y (coordinateVector 3 b) := by
    funext y
    rw [fderiv_fun_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y),
      sub_apply]
  rw [h1, fderiv_fun_sub (hdf b x) (hdg b x), sub_apply]

private lemma scalarLaplacian3_const_mul (c : ℝ) {f : Euclidean 3 → ℝ}
    (hf : ContDiff ℝ 2 f) (x : Euclidean 3) :
    scalarLaplacian3 (fun z => c * f z) x = c * scalarLaplacian3 f x := by
  have hdf : ∀ b, Differentiable ℝ (fun y => fderiv ℝ f y (coordinateVector 3 b)) := fun b =>
    ((hf.fderiv_right (m := 1) le_rfl).clm_apply contDiff_const).differentiable one_ne_zero
  unfold scalarLaplacian3
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h1 : (fun y => fderiv ℝ (fun z => c * f z) y (coordinateVector 3 b)) =
      fun y => c * fderiv ℝ f y (coordinateVector 3 b) := by
    funext y
    rw [fderiv_const_mul (hf.differentiable (by norm_num) y), smul_apply, smul_eq_mul]
  rw [h1, fderiv_const_mul (hdf b x), smul_apply, smul_eq_mul]

private lemma scalarLaplacian3_coord_mul (a d : Fin 3) (x : Euclidean 3) :
    scalarLaplacian3 (fun z : Euclidean 3 => z a * z d) x = 2 * kronecker3 a d := by
  have hp : ∀ (i : Fin 3) (y : Euclidean 3),
      DifferentiableAt ℝ (fun z : Euclidean 3 => z i) y :=
    fun i y => (EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt
  unfold scalarLaplacian3
  have hterm : ∀ b : Fin 3,
      fderiv ℝ (fun y : Euclidean 3 =>
        fderiv ℝ (fun z : Euclidean 3 => z a * z d) y (coordinateVector 3 b)) x
          (coordinateVector 3 b) =
      (if d = b then (1 : ℝ) else 0) * (if a = b then 1 else 0) +
        (if a = b then 1 else 0) * (if d = b then 1 else 0) := by
    intro b
    have h1 : (fun y : Euclidean 3 =>
        fderiv ℝ (fun z : Euclidean 3 => z a * z d) y (coordinateVector 3 b)) =
        fun y : Euclidean 3 =>
          (if d = b then (1 : ℝ) else 0) * y a + (if a = b then 1 else 0) * y d := by
      funext y
      rw [fderiv_fun_mul (hp a y) (hp d y), add_apply, smul_apply, smul_apply,
        smul_eq_mul, smul_eq_mul, fderiv_coord_euclidean, fderiv_coord_euclidean]
      ring
    rw [h1, fderiv_fun_add ((hp a x).const_mul _) ((hp d x).const_mul _),
      add_apply, fderiv_const_mul (hp a x), fderiv_const_mul (hp d x),
      smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
      fderiv_coord_euclidean, fderiv_coord_euclidean]
  simp only [hterm, Fin.sum_univ_three]
  cases a using fin3_cases <;> cases d using fin3_cases <;>
    norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]

/-- `quarticHarmonic2 p q r s` is genuinely harmonic (`Δ Y_2 = 0`) everywhere on `ℝ³`. -/
theorem quarticHarmonic2_laplacian_eq_zero (p q r s : Fin 3) (x : Euclidean 3) :
    scalarLaplacian3 (quarticHarmonic2 p q r s) x = 0 := by
  have heq : quarticHarmonic2 p q r s =
      fun ξ =>
        (1 / 7 : ℝ) *
            (kronecker3 p q * (ξ r * ξ s) +
              (kronecker3 p r * (ξ q * ξ s) +
                (kronecker3 p s * (ξ q * ξ r) +
                  (kronecker3 q r * (ξ p * ξ s) +
                    (kronecker3 q s * (ξ p * ξ r) +
                      kronecker3 r s * (ξ p * ξ q)))))) -
          ((10 / 7 : ℝ) * quarticMean p q r s) *
            (ξ 0 * ξ 0 + (ξ 1 * ξ 1 + ξ 2 * ξ 2)) := by
    funext ξ; unfold quarticHarmonic2; ring
  rw [heq]
  simp (disch := fun_prop) only [scalarLaplacian3_sub, scalarLaplacian3_add,
    scalarLaplacian3_const_mul, scalarLaplacian3_coord_mul]
  unfold quarticMean
  norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
  ring

/-- Physical-space CZ kernel associated to `ξ_p ξ_q ξ_r ξ_s - c_0` via the exact G4 Funk–Hecke
eigenvalues `c_2 = -4π/3` and `c_4 = 8π/15`:
`Ω_{pqrs}(θ) = Y_2(θ) / (-4π/3) + Y_4(θ) / (8π/15)`. -/
noncomputable def quarticCZKernel (p q r s : Fin 3) (θ : Euclidean 3) : ℝ :=
  quarticHarmonic2 p q r s θ / (-4 * Real.pi / 3) +
    quarticHarmonic4 p q r s θ / (8 * Real.pi / 15)

@[fun_prop]
private lemma continuous_quarticCZKernel (p q r s : Fin 3) :
    Continuous (quarticCZKernel p q r s) := by
  unfold quarticCZKernel quarticHarmonic4 quarticHarmonic2
  fun_prop

lemma quarticCZKernel_eq_closed_of_unit {θ : Euclidean 3} (hnorm : ‖θ‖ = 1) (p q r s : Fin 3) :
    quarticCZKernel p q r s θ =
      (1 / (4 * Real.pi)) *
        ((15 / 2 : ℝ) * (θ p * θ q * θ r * θ s) -
          (3 / 2 : ℝ) *
            (kronecker3 p q * (θ r * θ s) +
              kronecker3 p r * (θ q * θ s) +
              kronecker3 p s * (θ q * θ r) +
              kronecker3 q r * (θ p * θ s) +
              kronecker3 q s * (θ p * θ r) +
              kronecker3 r s * (θ p * θ q)) +
          (1 / 2 : ℝ) *
            (kronecker3 p q * kronecker3 r s +
              kronecker3 p r * kronecker3 q s +
              kronecker3 p s * kronecker3 q r)) := by
  have hs : θ 0 ^ 2 + θ 1 ^ 2 + θ 2 ^ 2 = 1 := unit_sum_sq hnorm
  unfold quarticCZKernel quarticHarmonic4 quarticHarmonic2 quarticMean
  rw [hs]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi]
  ring

/-- Local `l = 0` contact mean `c_0 = (1/(4π)) ∫_{S²} m_{ijk}^{an}(ξ̂) dσ(ξ̂)` of `ftildeSymbol`. -/
def ftildeSymbolMean (i j k a n : Fin 3) : ℝ :=
  -(1 / 2 : ℝ) * ∑ m : Fin 3,
    (leviCivita3 i m n * quarticMean k j m a + leviCivita3 j m n * quarticMean k i m a)

/-- Explicit witness confirming comment 6545396969: the raw Fourier symbol `ftildeSymbol` has
nonzero `l = 0` mean (e.g. `-1/30` at `(0, 1, 0, 2, 0)`), which acts in physical space as the
local contact operator `c_0 · dF̃(x) = O(ψ(|x|)) → 0` and must NOT be included in the shell CZ kernel. -/
theorem ftildeSymbolMean_nonzero_witness :
    ftildeSymbolMean 0 1 0 2 0 = -1 / 30 := by
  norm_num [ftildeSymbolMean, Fin.sum_univ_three, leviCivita3, quarticMean, kronecker3]

/-- Exact mean-zero physical-space CZ kernel `Ω_{ijk}^{an}(θ)` from Route 2 (G3/G4). -/
noncomputable def ftildeCZKernel (i j k a n : Fin 3) (θ : Euclidean 3) : ℝ :=
  -(1 / 2 : ℝ) * ∑ m : Fin 3,
    (leviCivita3 i m n * quarticCZKernel k j m a θ +
      leviCivita3 j m n * quarticCZKernel k i m a θ)

lemma ftildeCZKernel_even (i j k a n : Fin 3) (θ : Euclidean 3) :
    ftildeCZKernel i j k a n (-θ) = ftildeCZKernel i j k a n θ := by
  unfold ftildeCZKernel quarticCZKernel quarticHarmonic4 quarticHarmonic2
  simp

lemma quarticCZKernel_mean_zero (p q r s : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1, quarticCZKernel p q r s θ.1 ∂sphereSurfaceMeasure) = 0 := by
  have hrew : (fun θ : sphere (0 : Euclidean 3) 1 => quarticCZKernel p q r s θ.1) =
      fun θ : sphere (0 : Euclidean 3) 1 =>
        (1 / (4 * Real.pi)) *
          ((15 / 2 : ℝ) *
              ((θ.1 0) ^ (coordInd 0 p + coordInd 0 q + coordInd 0 r + coordInd 0 s) *
                (θ.1 1) ^ (coordInd 1 p + coordInd 1 q + coordInd 1 r + coordInd 1 s) *
                (θ.1 2) ^ (coordInd 2 p + coordInd 2 q + coordInd 2 r + coordInd 2 s)) +
            ((-3 / 2 * kronecker3 p q) *
                ((θ.1 0) ^ (coordInd 0 r + coordInd 0 s) *
                  (θ.1 1) ^ (coordInd 1 r + coordInd 1 s) *
                  (θ.1 2) ^ (coordInd 2 r + coordInd 2 s)) +
              (-3 / 2 * kronecker3 p r) *
                ((θ.1 0) ^ (coordInd 0 q + coordInd 0 s) *
                  (θ.1 1) ^ (coordInd 1 q + coordInd 1 s) *
                  (θ.1 2) ^ (coordInd 2 q + coordInd 2 s)) +
              (-3 / 2 * kronecker3 p s) *
                ((θ.1 0) ^ (coordInd 0 q + coordInd 0 r) *
                  (θ.1 1) ^ (coordInd 1 q + coordInd 1 r) *
                  (θ.1 2) ^ (coordInd 2 q + coordInd 2 r)) +
              (-3 / 2 * kronecker3 q r) *
                ((θ.1 0) ^ (coordInd 0 p + coordInd 0 s) *
                  (θ.1 1) ^ (coordInd 1 p + coordInd 1 s) *
                  (θ.1 2) ^ (coordInd 2 p + coordInd 2 s)) +
              (-3 / 2 * kronecker3 q s) *
                ((θ.1 0) ^ (coordInd 0 p + coordInd 0 r) *
                  (θ.1 1) ^ (coordInd 1 p + coordInd 1 r) *
                  (θ.1 2) ^ (coordInd 2 p + coordInd 2 r)) +
              (-3 / 2 * kronecker3 r s) *
                ((θ.1 0) ^ (coordInd 0 p + coordInd 0 q) *
                  (θ.1 1) ^ (coordInd 1 p + coordInd 1 q) *
                  (θ.1 2) ^ (coordInd 2 p + coordInd 2 q)) +
              ((1 / 2 : ℝ) *
                  (kronecker3 p q * kronecker3 r s +
                    kronecker3 p r * kronecker3 q s +
                    kronecker3 p s * kronecker3 q r)) *
                ((θ.1 0) ^ 0 * (θ.1 1) ^ 0 * (θ.1 2) ^ 0))) := by
    funext θ
    have hnorm : ‖θ.1‖ = 1 := by simp [mem_sphere_zero_iff_norm.mp θ.2]
    rw [quarticCZKernel_eq_closed_of_unit hnorm, coord4_eq_pow_prod θ.1 p q r s]
    simp only [coord2_eq_pow_prod θ.1]
    ring
  rw [hrew, integral_const_mul]
  simp (disch := fun_prop) only [integral_sphere_add', integral_sphere_const_mul',
    integral_sphere_monomial]
  cases p using fin3_cases <;> cases q using fin3_cases <;>
    cases r using fin3_cases <;> cases s using fin3_cases <;>
    · norm_num [kronecker3, coordInd, sphereMonomialAvg, oddDoubleFact]
      try ring

/-- Every component of `ftildeCZKernel` has exact mean zero on `S²`. -/
theorem ftildeCZKernel_mean_zero (i j k a n : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      ftildeCZKernel i j k a n θ.1 ∂sphereSurfaceMeasure) = 0 := by
  unfold ftildeCZKernel
  simp only [Fin.sum_univ_three]
  rw [integral_const_mul]
  simp (disch := fun_prop) only [integral_sphere_add', integral_sphere_const_mul',
    quarticCZKernel_mean_zero, mul_zero, add_zero]

/-- Exact rational evaluation of `∫_{S²} quarticCZKernel p q r s θ * ftildeD a n θ dσ(θ)`. -/
def quarticCZPairingVal (p q r s a n : Fin 3) : ℝ :=
  (15 / 2 : ℝ) *
      ftildeDMoment
        (coordInd 0 p + coordInd 0 q + coordInd 0 r + coordInd 0 s)
        (coordInd 1 p + coordInd 1 q + coordInd 1 r + coordInd 1 s)
        (coordInd 2 p + coordInd 2 q + coordInd 2 r + coordInd 2 s) a n -
    (3 / 2 : ℝ) *
      (kronecker3 p q * ftildeDMoment (coordInd 0 r + coordInd 0 s)
          (coordInd 1 r + coordInd 1 s) (coordInd 2 r + coordInd 2 s) a n +
        kronecker3 p r * ftildeDMoment (coordInd 0 q + coordInd 0 s)
          (coordInd 1 q + coordInd 1 s) (coordInd 2 q + coordInd 2 s) a n +
        kronecker3 p s * ftildeDMoment (coordInd 0 q + coordInd 0 r)
          (coordInd 1 q + coordInd 1 r) (coordInd 2 q + coordInd 2 r) a n +
        kronecker3 q r * ftildeDMoment (coordInd 0 p + coordInd 0 s)
          (coordInd 1 p + coordInd 1 s) (coordInd 2 p + coordInd 2 s) a n +
        kronecker3 q s * ftildeDMoment (coordInd 0 p + coordInd 0 r)
          (coordInd 1 p + coordInd 1 r) (coordInd 2 p + coordInd 2 r) a n +
        kronecker3 r s * ftildeDMoment (coordInd 0 p + coordInd 0 q)
          (coordInd 1 p + coordInd 1 q) (coordInd 2 p + coordInd 2 q) a n) +
    (1 / 2 : ℝ) *
      (kronecker3 p q * kronecker3 r s +
        kronecker3 p r * kronecker3 q s +
        kronecker3 p s * kronecker3 q r) *
      ftildeDMoment 0 0 0 a n

lemma integral_quarticCZKernel_mul_ftildeD (p q r s a n : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      quarticCZKernel p q r s θ.1 * ftildeD a n θ.1 ∂sphereSurfaceMeasure) =
      quarticCZPairingVal p q r s a n := by
  have hrew : (fun θ : sphere (0 : Euclidean 3) 1 =>
      quarticCZKernel p q r s θ.1 * ftildeD a n θ.1) =
      fun θ : sphere (0 : Euclidean 3) 1 =>
        (1 / (4 * Real.pi)) *
          ((15 / 2 : ℝ) *
              (((θ.1 0) ^ (coordInd 0 p + coordInd 0 q + coordInd 0 r + coordInd 0 s) *
                (θ.1 1) ^ (coordInd 1 p + coordInd 1 q + coordInd 1 r + coordInd 1 s) *
                (θ.1 2) ^ (coordInd 2 p + coordInd 2 q + coordInd 2 r + coordInd 2 s)) *
                ftildeDPoly a n θ.1) +
            ((-3 / 2 * kronecker3 p q) *
                (((θ.1 0) ^ (coordInd 0 r + coordInd 0 s) *
                  (θ.1 1) ^ (coordInd 1 r + coordInd 1 s) *
                  (θ.1 2) ^ (coordInd 2 r + coordInd 2 s)) * ftildeDPoly a n θ.1) +
              (-3 / 2 * kronecker3 p r) *
                (((θ.1 0) ^ (coordInd 0 q + coordInd 0 s) *
                  (θ.1 1) ^ (coordInd 1 q + coordInd 1 s) *
                  (θ.1 2) ^ (coordInd 2 q + coordInd 2 s)) * ftildeDPoly a n θ.1) +
              (-3 / 2 * kronecker3 p s) *
                (((θ.1 0) ^ (coordInd 0 q + coordInd 0 r) *
                  (θ.1 1) ^ (coordInd 1 q + coordInd 1 r) *
                  (θ.1 2) ^ (coordInd 2 q + coordInd 2 r)) * ftildeDPoly a n θ.1) +
              (-3 / 2 * kronecker3 q r) *
                (((θ.1 0) ^ (coordInd 0 p + coordInd 0 s) *
                  (θ.1 1) ^ (coordInd 1 p + coordInd 1 s) *
                  (θ.1 2) ^ (coordInd 2 p + coordInd 2 s)) * ftildeDPoly a n θ.1) +
              (-3 / 2 * kronecker3 q s) *
                (((θ.1 0) ^ (coordInd 0 p + coordInd 0 r) *
                  (θ.1 1) ^ (coordInd 1 p + coordInd 1 r) *
                  (θ.1 2) ^ (coordInd 2 p + coordInd 2 r)) * ftildeDPoly a n θ.1) +
              (-3 / 2 * kronecker3 r s) *
                (((θ.1 0) ^ (coordInd 0 p + coordInd 0 q) *
                  (θ.1 1) ^ (coordInd 1 p + coordInd 1 q) *
                  (θ.1 2) ^ (coordInd 2 p + coordInd 2 q)) * ftildeDPoly a n θ.1) +
              ((1 / 2 : ℝ) *
                  (kronecker3 p q * kronecker3 r s +
                    kronecker3 p r * kronecker3 q s +
                    kronecker3 p s * kronecker3 q r)) *
                (((θ.1 0) ^ 0 * (θ.1 1) ^ 0 * (θ.1 2) ^ 0) * ftildeDPoly a n θ.1))) := by
    funext θ
    have hnorm : ‖θ.1‖ = 1 := by simp [mem_sphere_zero_iff_norm.mp θ.2]
    rw [quarticCZKernel_eq_closed_of_unit hnorm, ftildeD_eq_poly_of_unit hnorm,
      coord4_eq_pow_prod θ.1 p q r s]
    simp only [coord2_eq_pow_prod θ.1]
    ring
  rw [hrew, integral_const_mul]
  simp (disch := fun_prop) only [integral_sphere_add', integral_sphere_const_mul',
    integral_sphere_monomial_mul_ftildeDPoly]
  unfold quarticCZPairingVal
  have hpi : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [hpi]
  ring

private lemma sum_leviCivita3_0 (f : Fin 3 → Fin 3 → ℝ) :
    (∑ n : Fin 3, ∑ m : Fin 3, leviCivita3 0 m n * f m n) = f 1 2 - f 2 1 := by
  simp [Fin.sum_univ_three, leviCivita3, fin3Mat_apply]
  ring

private lemma sum_leviCivita3_1 (f : Fin 3 → Fin 3 → ℝ) :
    (∑ n : Fin 3, ∑ m : Fin 3, leviCivita3 1 m n * f m n) = f 2 0 - f 0 2 := by
  simp [Fin.sum_univ_three, leviCivita3, fin3Mat_apply]
  ring

private lemma sum_leviCivita3_2 (f : Fin 3 → Fin 3 → ℝ) :
    (∑ n : Fin 3, ∑ m : Fin 3, leviCivita3 2 m n * f m n) = f 0 1 - f 1 0 := by
  simp [Fin.sum_univ_three, leviCivita3, fin3Mat_apply]
  ring

private lemma cz_levi_sum_00 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 0 m n * quarticCZPairingVal k 0 m a a n) =
      fin3Vec (8 / 35) 0 0 k := by
  simp_rw [sum_leviCivita3_0]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_01 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 0 m n * quarticCZPairingVal k 1 m a a n) =
      fin3Vec 0 (-32 / 105) 0 k := by
  simp_rw [sum_leviCivita3_0]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_02 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 0 m n * quarticCZPairingVal k 2 m a a n) =
      fin3Vec 0 0 (8 / 105) k := by
  simp_rw [sum_leviCivita3_0]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_10 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 1 m n * quarticCZPairingVal k 0 m a a n) =
      fin3Vec 0 (-32 / 105) 0 k := by
  simp_rw [sum_leviCivita3_1]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_11 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 1 m n * quarticCZPairingVal k 1 m a a n) =
      fin3Vec (-32 / 105) 0 0 k := by
  simp_rw [sum_leviCivita3_1]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_12 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 1 m n * quarticCZPairingVal k 2 m a a n) =
      fin3Vec 0 0 0 k := by
  simp_rw [sum_leviCivita3_1]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_20 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 2 m n * quarticCZPairingVal k 0 m a a n) =
      fin3Vec 0 0 (8 / 105) k := by
  simp_rw [sum_leviCivita3_2]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_21 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 2 m n * quarticCZPairingVal k 1 m a a n) =
      fin3Vec 0 0 0 k := by
  simp_rw [sum_leviCivita3_2]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum_22 (k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 2 m n * quarticCZPairingVal k 2 m a a n) =
      fin3Vec (8 / 105) 0 0 k := by
  simp_rw [sum_leviCivita3_2]
  simp only [Fin.sum_univ_three]
  cases k using fin3_cases <;>
    · norm_num only [quarticCZPairingVal, kronecker3, coordInd, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      try norm_num only [ftildeDMoment, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        sphereMonomialAvg]
      try norm_num [oddDoubleFact]

private lemma cz_levi_sum (i b k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
      leviCivita3 i m n * quarticCZPairingVal k b m a a n) =
      -ftildeC i b k := by
  rw [ftildeC_eq_fin3]
  cases i using fin3_cases <;> cases b using fin3_cases
  · rw [cz_levi_sum_00]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_01]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_02]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_10]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_11]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_12]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_20]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_21]; cases k using fin3_cases <;> norm_num
  · rw [cz_levi_sum_22]; cases k using fin3_cases <;> norm_num

/-- **Closing Gap `(a2)` — Route 2 (G3/G4 Degree-4 Symbol + Funk–Hecke CZ Kernel):**
The exact angular pairing `∑_{a,n} ∫_{S²} Ω_{ijk}^{an}(-θ) D_{a,n}(θ) dσ(θ)` over Mathlib's
surface measure `sphereSurfaceMeasure` equals `ftildeC i j k` for all `i, j, k : Fin 3`. -/
theorem ftilde_angular_identification_a2 (i j k : Fin 3) :
    (∑ a : Fin 3, ∑ n : Fin 3,
      ∫ θ : sphere (0 : Euclidean 3) 1,
        ftildeCZKernel i j k a n (-θ.1) * ftildeD a n θ.1 ∂sphereSurfaceMeasure) =
      ftildeC i j k := by
  have hterm : ∀ a n : Fin 3,
      (∫ θ : sphere (0 : Euclidean 3) 1,
        ftildeCZKernel i j k a n (-θ.1) * ftildeD a n θ.1 ∂sphereSurfaceMeasure) =
      -(1 / 2 : ℝ) * ∑ m : Fin 3,
        (leviCivita3 i m n * quarticCZPairingVal k j m a a n +
          leviCivita3 j m n * quarticCZPairingVal k i m a a n) := by
    intro a n
    have hcongr : (fun θ : sphere (0 : Euclidean 3) 1 =>
        ftildeCZKernel i j k a n (-θ.1) * ftildeD a n θ.1) =
        fun θ : sphere (0 : Euclidean 3) 1 =>
          -(1 / 2 : ℝ) * ∑ m : Fin 3,
            (leviCivita3 i m n * (quarticCZKernel k j m a θ.1 * ftildeDPoly a n θ.1) +
              leviCivita3 j m n * (quarticCZKernel k i m a θ.1 * ftildeDPoly a n θ.1)) := by
      funext θ
      have hnorm : ‖θ.1‖ = 1 := by simp [mem_sphere_zero_iff_norm.mp θ.2]
      rw [ftildeCZKernel_even, ftildeD_eq_poly_of_unit hnorm]
      unfold ftildeCZKernel
      simp only [Fin.sum_univ_three]
      ring
    have hint : ∀ p q r s : Fin 3,
        (∫ θ : sphere (0 : Euclidean 3) 1,
          quarticCZKernel p q r s θ.1 * ftildeDPoly a n θ.1 ∂sphereSurfaceMeasure) =
        quarticCZPairingVal p q r s a n := by
      intro p q r s
      rw [← integral_quarticCZKernel_mul_ftildeD]
      refine integral_congr_ae (ae_of_all _ fun θ => ?_)
      dsimp only
      have hnorm : ‖θ.1‖ = 1 := by simp [mem_sphere_zero_iff_norm.mp θ.2]
      rw [ftildeD_eq_poly_of_unit hnorm]
    rw [hcongr, integral_const_mul]
    simp only [Fin.sum_univ_three]
    simp (disch := fun_prop) only [integral_sphere_add', integral_sphere_const_mul', hint]
  simp only [hterm]
  have hsplit :
      (∑ a : Fin 3, ∑ n : Fin 3, -(1 / 2 : ℝ) * ∑ m : Fin 3,
        (leviCivita3 i m n * quarticCZPairingVal k j m a a n +
          leviCivita3 j m n * quarticCZPairingVal k i m a a n)) =
      -(1 / 2 : ℝ) *
        ((∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
            leviCivita3 i m n * quarticCZPairingVal k j m a a n) +
          (∑ a : Fin 3, ∑ n : Fin 3, ∑ m : Fin 3,
            leviCivita3 j m n * quarticCZPairingVal k i m a a n)) := by
    simp only [Fin.sum_univ_three]
    ring
  rw [hsplit, cz_levi_sum, cz_levi_sum, ftildeC_swap_left j i k]
  ring

/-!
### Closing Part `(B)` of Derek's Split: Base Potential-Compensated Field & `5/7` Harmonic Law
-/

/-- Jacobian polynomial entries of the unshifted potential-compensated field `V_base`
(obtained by setting the Case-A stream shift `c = θ₁⁴` to `0` in `ftildeV`). -/
def ftildeDBasePoly (a n : Fin 3) (θ : Euclidean 3) : ℝ :=
  fin3Mat
    ((6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 7 * θ 1 ^ 1 * θ 2 ^ 0))
    ((1 : ℝ) * (θ 0 ^ 0 * θ 1 ^ 0 * θ 2 ^ 0) +
      (3 / 2 : ℝ) * (θ 0 ^ 2 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-3 : ℝ) * (θ 0 ^ 2 * θ 1 ^ 2 * θ 2 ^ 0) +
      (-9 / 4 : ℝ) * (θ 0 ^ 4 * θ 1 ^ 0 * θ 2 ^ 0) +
      (9 : ℝ) * (θ 0 ^ 4 * θ 1 ^ 2 * θ 2 ^ 0) +
      (1 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 2 * θ 2 ^ 0))
    ((-3 : ℝ) * (θ 0 ^ 2 * θ 1 ^ 1 * θ 2 ^ 1) +
      (9 : ℝ) * (θ 0 ^ 4 * θ 1 ^ 1 * θ 2 ^ 1) +
      (-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 1 * θ 2 ^ 1))
    ((1 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 0 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 2 * θ 2 ^ 0))
    ((-3 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 1 * θ 2 ^ 0) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 3 * θ 2 ^ 0) +
      (3 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 3 * θ 2 ^ 0))
    ((-1 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 0 * θ 2 ^ 1) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 2 * θ 2 ^ 1) +
      (1 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 0 * θ 2 ^ 1) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 2 * θ 2 ^ 1))
    ((-6 : ℝ) * (θ 0 ^ 6 * θ 1 ^ 1 * θ 2 ^ 1))
    ((-1 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 0 * θ 2 ^ 1) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 2 * θ 2 ^ 1) +
      (1 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 0 * θ 2 ^ 1) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 2 * θ 2 ^ 1))
    ((-1 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 1 * θ 2 ^ 0) +
      (4 : ℝ) * (θ 0 ^ 3 * θ 1 ^ 1 * θ 2 ^ 2) +
      (1 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 0) +
      (-6 : ℝ) * (θ 0 ^ 5 * θ 1 ^ 1 * θ 2 ^ 2))
    a n

@[fun_prop]
private lemma continuous_ftildeDBasePoly (a n : Fin 3) : Continuous (ftildeDBasePoly a n) := by
  change Continuous (fun θ => ftildeDBasePoly a n θ)
  cases a using fin3_cases <;> cases n using fin3_cases <;>
    · simp only [ftildeDBasePoly, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
      fun_prop

/-- Normalized sphere-average moments of `ftildeDBasePoly`. -/
def ftildeDBaseMoment (e₀ e₁ e₂ : ℕ) (a n : Fin 3) : ℝ :=
  fin3Mat
    ((6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 7) (e₁ + 1) (e₂ + 0))
    ((1 : ℝ) * sphereMonomialAvg (e₀ + 0) (e₁ + 0) (e₂ + 0) +
      (3 / 2 : ℝ) * sphereMonomialAvg (e₀ + 2) (e₁ + 0) (e₂ + 0) +
      (-3 : ℝ) * sphereMonomialAvg (e₀ + 2) (e₁ + 2) (e₂ + 0) +
      (-9 / 4 : ℝ) * sphereMonomialAvg (e₀ + 4) (e₁ + 0) (e₂ + 0) +
      (9 : ℝ) * sphereMonomialAvg (e₀ + 4) (e₁ + 2) (e₂ + 0) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 0) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 2) (e₂ + 0))
    ((-3 : ℝ) * sphereMonomialAvg (e₀ + 2) (e₁ + 1) (e₂ + 1) +
      (9 : ℝ) * sphereMonomialAvg (e₀ + 4) (e₁ + 1) (e₂ + 1) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 1) (e₂ + 1))
    ((1 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 0) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 2) (e₂ + 0))
    ((-3 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 1) (e₂ + 0) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 3) (e₂ + 0) +
      (3 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 3) (e₂ + 0))
    ((-1 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 0) (e₂ + 1) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 2) (e₂ + 1) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 0) (e₂ + 1) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 2) (e₂ + 1))
    ((-6 : ℝ) * sphereMonomialAvg (e₀ + 6) (e₁ + 1) (e₂ + 1))
    ((-1 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 0) (e₂ + 1) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 2) (e₂ + 1) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 0) (e₂ + 1) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 2) (e₂ + 1))
    ((-1 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 1) (e₂ + 0) +
      (4 : ℝ) * sphereMonomialAvg (e₀ + 3) (e₁ + 1) (e₂ + 2) +
      (1 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 0) +
      (-6 : ℝ) * sphereMonomialAvg (e₀ + 5) (e₁ + 1) (e₂ + 2))
    a n

lemma integral_biotSavartDipole_mul_ftildeDBase (k m a n : Fin 3) :
    (∫ θ : sphere (0 : Euclidean 3) 1,
      biotSavartDipoleKernel k m (-θ.1) * ftildeDBasePoly a n θ.1 ∂sphereSurfaceMeasure) =
      -(kronecker3 k m * ftildeDBaseMoment 0 0 0 a n -
          3 * ftildeDBaseMoment (coordInd 0 k + coordInd 0 m)
            (coordInd 1 k + coordInd 1 m) (coordInd 2 k + coordInd 2 m) a n) := by
  have hint : ∀ e₀ e₁ e₂ : ℕ,
      (∫ θ : sphere (0 : Euclidean 3) 1,
        ((θ.1 0) ^ e₀ * (θ.1 1) ^ e₁ * (θ.1 2) ^ e₂) *
          ftildeDBasePoly a n θ.1 ∂sphereSurfaceMeasure) =
      (4 * Real.pi) * ftildeDBaseMoment e₀ e₁ e₂ a n := by
    intro e₀ e₁ e₂
    cases a using fin3_cases <;> cases n using fin3_cases <;>
      · simp only [ftildeDBasePoly, ftildeDBaseMoment, fin3Mat_apply,
          fin3Vec_zero, fin3Vec_one, fin3Vec_two]
        try simp (disch := fun_prop) only [mul_add, integral_sphere_add']
        simp only [integral_sphere_monomial_mul_monomial]
        try ring
  have hcongr : (fun θ : sphere (0 : Euclidean 3) 1 =>
      biotSavartDipoleKernel k m (-θ.1) * ftildeDBasePoly a n θ.1) =
      fun θ : sphere (0 : Euclidean 3) 1 =>
        -(1 / (4 * Real.pi)) *
          (kronecker3 k m *
              (((θ.1 0) ^ 0 * (θ.1 1) ^ 0 * (θ.1 2) ^ 0) * ftildeDBasePoly a n θ.1) -
            3 * (((θ.1 0) ^ (coordInd 0 k + coordInd 0 m) *
              (θ.1 1) ^ (coordInd 1 k + coordInd 1 m) *
              (θ.1 2) ^ (coordInd 2 k + coordInd 2 m)) * ftildeDBasePoly a n θ.1)) := by
    funext θ
    rw [biotSavartDipoleKernel_even]
    simp only [biotSavartDipoleKernel, coord2_eq_pow_prod θ.1 k m]
    ring
  rw [hcongr, integral_const_mul,
    integral_sphere_sub' (by fun_prop) (by fun_prop),
    integral_const_mul, integral_const_mul, hint, hint]
  have hpi : 4 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  field_simp [hpi]

/-- **Closing Part `(B)` of Derek's Split (comments 6543364135 & 6543703714):**
The unshifted potential-compensated field `ftildeDBasePoly` has identically zero angular
coefficient `A_base = 0` for all `(i, j, k)`. Hence 100% of `ftildeC ≠ 0` comes from the even
`c = θ₁⁴` Case-A stream shift! -/
theorem ftildeBase_dipole_angular_eq_zero (i j k : Fin 3) :
    (1 / 2 : ℝ) *
        ((∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 i m n *
            ∫ θ : sphere (0 : Euclidean 3) 1,
              biotSavartDipoleKernel k m (-θ.1) * ftildeDBasePoly j n θ.1 ∂sphereSurfaceMeasure) +
          (∑ m : Fin 3, ∑ n : Fin 3, leviCivita3 j m n *
            ∫ θ : sphere (0 : Euclidean 3) 1,
              biotSavartDipoleKernel k m (-θ.1) * ftildeDBasePoly i n θ.1 ∂sphereSurfaceMeasure)) =
      0 := by
  simp only [integral_biotSavartDipole_mul_ftildeDBase]
  cases i using fin3_cases <;> cases j using fin3_cases <;> cases k using fin3_cases <;>
    · simp only [Fin.sum_univ_three, leviCivita3, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two,
        zero_mul, one_mul, neg_one_mul, add_zero, zero_add]
      norm_num [kronecker3, coordInd, ftildeDBaseMoment, fin3Mat_apply,
        fin3Vec_zero, fin3Vec_one, fin3Vec_two, sphereMonomialAvg, oddDoubleFact]

/-- **Diagnosing Part `(B)`:** The isolated first-row functional (`n = 0` only, ignoring the
potential-compensating rows `n = 1, 2`) is NONZERO (`-4/77` at `(i, j, k) = (0, 2, 0)`).
Thus `A_base = 0` holds NOT because `θ₀⁶ θ₁` lacks `l = 3` content, nor by radial suppression,
but by exact algebraic cancellation between `V_0 e_0` and `(∂_1 M, ∂_2 M)`. -/
theorem ftildeBase_row0_dipole_020 :
    (1 / 2 : ℝ) *
        ((∑ m : Fin 3, leviCivita3 0 m 0 *
            ∫ θ : sphere (0 : Euclidean 3) 1,
              biotSavartDipoleKernel 0 m (-θ.1) * ftildeDBasePoly 2 0 θ.1 ∂sphereSurfaceMeasure) +
          (∑ m : Fin 3, leviCivita3 2 m 0 *
            ∫ θ : sphere (0 : Euclidean 3) 1,
              biotSavartDipoleKernel 0 m (-θ.1) * ftildeDBasePoly 0 0 θ.1 ∂sphereSurfaceMeasure)) =
      -4 / 77 := by
  simp only [integral_biotSavartDipole_mul_ftildeDBase]
  norm_num [Fin.sum_univ_three, leviCivita3, kronecker3, coordInd, ftildeDBaseMoment,
    fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two, sphereMonomialAvg, oddDoubleFact]

/-!
## Section I.3 — Valid Algebraic & Radial Calculus Half of Gap `(b)`, L8, and L10

We establish the exact algebraic and radial-calculus theorems that DO hold on the merits:
1. `korn_second_partial_identity`: Korn's algebraic recovery of all second partials `∂_k ∂_i G_j`
   from first partials of the symmetric gradient `S_{ab} = (∂_a G_b + ∂_b G_a)/2`.
2. `sym3_gauge_orthogonality`: G5's exact frequency-wise Frobenius orthogonality between
   transverse symmetric tensors `Sym(ξ ⊗ ξ ⊗ v)` (`⟨ξ, v⟩ = 0`) and longitudinal/trace gauge
   tensors `α ξ^{\otimes 3} + β Sym(δ ⊗ ξ)`.
3. `hasDerivAt_log_neg_log`, `integral_ftildePsi_div_self`, `integral_ftildePsi_sq_div_self`,
   `integral_ftildePsi_sq_div_self_bounds`, and `ray_integral_log_neg_log_ibp`: the exact radial
   shell laws driving the `log|log r|` blow-up of the Coulomb gauge `S^{(0)}`, the `O(1)` bound
   on the `ψ²` shell remainder (`∫_r^{r₀} ψ(s)²/s ds = ψ(r₀) - ψ(r)`), and the L10 ray obstruction
   proving `¬ ContDiffOn ℝ 1 S ftildeBall` for any symmetric tensor field with a `log(-log ‖x‖)`
   gradient asymptotic along `ftildeC`.
-/

/-- **Korn Second-Partial Identity:** If `dG k i j` represents `∂_k ∂_i G_j` with commuting mixed
partials (`dG k i j = dG i k j`) and `dS k i j = (dG k i j + dG k j i) / 2` represents
`∂_k S_{ij}` for `S_{ij} = (∂_i G_j + ∂_j G_i) / 2`, then the linear Korn combination
`∂_k S_{ij} + ∂_i S_{kj} - ∂_j S_{ki}` recovers `∂_k ∂_i G_j` identically. -/
theorem korn_second_partial_identity (dG : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hcomm : ∀ a b c : Fin 3, dG a b c = dG b a c) (i j k : Fin 3) :
    ((dG k i j + dG k j i) / 2) + ((dG i k j + dG i j k) / 2) -
        ((dG j k i + dG j i k) / 2) =
      dG k i j := by
  have h1 : dG i k j = dG k i j := hcomm i k j
  have h2 : dG j k i = dG k j i := hcomm j k i
  have h3 : dG j i k = dG i j k := hcomm j i k
  linarith

/-- Symmetric 3-tensor `Sym_{ijk}(ξ_i ξ_j v_k)` appearing as the Fourier symbol of `Sym(∂S^{(0)})`
in G5 (comment 6546086985). -/
def sym3Tensor (ξ v : Euclidean 3) (i j k : Fin 3) : ℝ :=
  (1 / 3 : ℝ) * (ξ i * ξ j * v k + ξ j * ξ k * v i + ξ k * ξ i * v j)

/-- Longitudinal + trace gauge 3-tensor `α ξ_i ξ_j ξ_k + β (δ_{ij} ξ_k + δ_{jk} ξ_i + δ_{ki} ξ_j)`
parametrizing the kernel of the curl/trace symbol at fixed frequency `ξ` in G5. -/
def gauge3Tensor (ξ : Euclidean 3) (α β : ℝ) (i j k : Fin 3) : ℝ :=
  α * (ξ i * ξ j * ξ k) +
    β * (kronecker3 i j * ξ k + kronecker3 j k * ξ i + kronecker3 k i * ξ j)

/-- **G5 Pointwise Frequency Orthogonality:** For every frequency `ξ` and transverse vector `v`
(`∑_a ξ_a v_a = 0`), `sym3Tensor ξ v` is strictly Frobenius-orthogonal to `gauge3Tensor ξ α β`. -/
theorem sym3_gauge_orthogonality (ξ v : Euclidean 3)
    (horth : ∑ a : Fin 3, ξ a * v a = 0) (α β : ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
      sym3Tensor ξ v i j k * gauge3Tensor ξ α β i j k) = 0 := by
  simp only [Fin.sum_univ_three] at horth ⊢
  simp only [sym3Tensor, gauge3Tensor, kronecker3, fin3Mat_apply,
    fin3Vec_zero, fin3Vec_one, fin3Vec_two]
  linear_combination
    (α * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2) ^ 2 +
      3 * β * (ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2)) * horth

/-- Positivity of `ftildePsi r = 1 / |log r|` on `0 < r < 1`. -/
lemma ftildePsi_pos {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : 0 < ftildePsi r := by
  rw [ftildePsi_eq_neg_inv_log hr0 hr1]
  have hlog : Real.log r < 0 := Real.log_neg hr0 hr1
  exact neg_pos.mpr (inv_lt_zero.mpr hlog)

/-- On `(0, e⁻¹)`, `-Real.log s > 1`. -/
lemma one_lt_neg_log_of_lt_exp_neg_one {s : ℝ} (hs0 : 0 < s) (hse : s < Real.exp (-1)) :
    1 < -Real.log s := by
  have hlt : Real.log s < Real.log (Real.exp (-1)) := Real.log_lt_log hs0 hse
  rw [Real.log_exp] at hlt
  linarith

/-- Exact derivative `(d/ds) log(-log s) = -(ftildePsi s / s)` on `0 < s < e⁻¹`. -/
theorem hasDerivAt_log_neg_log {s : ℝ} (hs0 : 0 < s) (hse : s < Real.exp (-1)) :
    HasDerivAt (fun t => Real.log (-Real.log t)) (-(ftildePsi s / s)) s := by
  have hs1 : s < 1 := hse.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hneglog : 1 < -Real.log s := one_lt_neg_log_of_lt_exp_neg_one hs0 hse
  have h1 : HasDerivAt (fun t => -Real.log t) (-s⁻¹) s :=
    (Real.hasDerivAt_log hs0.ne').neg
  have h2 : HasDerivAt (fun t => Real.log (-Real.log t)) ((-s⁻¹) / (-Real.log s)) s :=
    h1.log (by linarith)
  convert h2 using 1
  rw [ftildePsi_eq_neg_inv_log hs0 hs1]
  have hlog_ne : Real.log s ≠ 0 := by linarith
  field_simp [hs0.ne', hlog_ne]

/-- **Main Shell Logarithmic Divergence Law (L8 Leading Term):**
For `0 < r ≤ r₀ < e⁻¹`, `∫_r^{r₀} (ψ(s) / s) ds = log(-log r) - log(-log r₀)`. -/
theorem integral_ftildePsi_div_self {r r₀ : ℝ}
    (hr0 : 0 < r) (hrr₀ : r ≤ r₀) (hr₀e : r₀ < Real.exp (-1)) :
    (∫ s in r..r₀, ftildePsi s / s) =
      Real.log (-Real.log r) - Real.log (-Real.log r₀) := by
  have hd : ∀ s ∈ uIcc r r₀,
      HasDerivAt (fun t => -Real.log (-Real.log t)) (ftildePsi s / s) s := by
    intro s hs
    rw [uIcc_of_le hrr₀] at hs
    have hs0 : 0 < s := lt_of_lt_of_le hr0 hs.1
    have hse : s < Real.exp (-1) := lt_of_le_of_lt hs.2 hr₀e
    convert (hasDerivAt_log_neg_log hs0 hse).neg using 1
    ring
  have hint : IntervalIntegrable (fun s => ftildePsi s / s) volume r r₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hrr₀]
    have hr₀1 : r₀ < 1 := hr₀e.trans (Real.exp_lt_one_iff.mpr (by norm_num))
    have hcpsi : ContinuousOn ftildePsi (Icc r r₀) :=
      continuousOn_ftildePsi_Ioo.mono (fun s hs => ⟨lt_of_lt_of_le hr0 hs.1, lt_of_le_of_lt hs.2 hr₀1⟩)
    exact hcpsi.div continuousOn_id (fun s hs => (lt_of_lt_of_le hr0 hs.1).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  ring

/-- **Standing `ψ²` Remainder Law (comment 6545396969):**
For `0 < r ≤ r₀ < 1`, `∫_r^{r₀} (ψ(s)² / s) ds = ψ(r₀) - ψ(r)`.
In particular, radial `ψ² / s` terms integrate to `O(1)` (bounded between `0` and `ψ(r₀)`)
and NEVER produce a secondary `log|log r|` divergence. -/
theorem integral_ftildePsi_sq_div_self {r r₀ : ℝ}
    (hr0 : 0 < r) (hrr₀ : r ≤ r₀) (hr₀1 : r₀ < 1) :
    (∫ s in r..r₀, ftildePsi s ^ 2 / s) = ftildePsi r₀ - ftildePsi r := by
  have hd : ∀ s ∈ uIcc r r₀, HasDerivAt ftildePsi (ftildePsi s ^ 2 / s) s := by
    intro s hs
    rw [uIcc_of_le hrr₀] at hs
    exact hasDerivAt_ftildePsi (lt_of_lt_of_le hr0 hs.1) (lt_of_le_of_lt hs.2 hr₀1)
  have hint : IntervalIntegrable (fun s => ftildePsi s ^ 2 / s) volume r r₀ := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hrr₀]
    have hcpsi : ContinuousOn ftildePsi (Icc r r₀) :=
      continuousOn_ftildePsi_Ioo.mono (fun s hs => ⟨lt_of_lt_of_le hr0 hs.1, lt_of_le_of_lt hs.2 hr₀1⟩)
    exact (hcpsi.pow 2).div continuousOn_id (fun s hs => (lt_of_lt_of_le hr0 hs.1).ne')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint

/-- Explicit uniform `[0, ψ(r₀)]` bounds on the `ψ² / s` shell integral for all `0 < r ≤ r₀ < 1`. -/
theorem integral_ftildePsi_sq_div_self_bounds {r r₀ : ℝ}
    (hr0 : 0 < r) (hrr₀ : r ≤ r₀) (hr₀1 : r₀ < 1) :
    0 ≤ (∫ s in r..r₀, ftildePsi s ^ 2 / s) ∧
      (∫ s in r..r₀, ftildePsi s ^ 2 / s) ≤ ftildePsi r₀ := by
  rw [integral_ftildePsi_sq_div_self hr0 hrr₀ hr₀1]
  have hpos : 0 < ftildePsi r := ftildePsi_pos hr0 (lt_of_le_of_lt hrr₀ hr₀1)
  constructor
  · have hmono : -Real.log r₀ ≤ -Real.log r := neg_le_neg (Real.log_le_log hr0 hrr₀)
    have hlogr₀ : 0 < -Real.log r₀ := neg_pos.mpr (Real.log_neg (lt_of_lt_of_le hr0 hrr₀) hr₀1)
    have hle : ftildePsi r ≤ ftildePsi r₀ := by
      rw [ftildePsi_eq_neg_inv_log hr0 (lt_of_le_of_lt hrr₀ hr₀1),
        ftildePsi_eq_neg_inv_log (lt_of_lt_of_le hr0 hrr₀) hr₀1]
      have hdiv := one_div_le_one_div_of_le hlogr₀ hmono
      simp only [one_div, inv_neg] at hdiv
      linarith
    linarith
  · linarith

/-- **L10 Ray Integration-by-Parts Identity:**
For `0 < a ≤ r < e⁻¹`, `∫_a^r log(-log t) dt = r log(-log r) - a log(-log a) + ∫_a^r ψ(t) dt`. -/
theorem ray_integral_log_neg_log_ibp {a r : ℝ}
    (ha0 : 0 < a) (har : a ≤ r) (hre : r < Real.exp (-1)) :
    (∫ t in a..r, Real.log (-Real.log t)) =
      r * Real.log (-Real.log r) - a * Real.log (-Real.log a) +
        ∫ t in a..r, ftildePsi t := by
  have hr1 : r < 1 := hre.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hd : ∀ t ∈ uIcc a r,
      HasDerivAt (fun s => s * Real.log (-Real.log s))
        (Real.log (-Real.log t) - ftildePsi t) t := by
    intro t ht
    rw [uIcc_of_le har] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have hte : t < Real.exp (-1) := lt_of_le_of_lt ht.2 hre
    have hmul := (hasDerivAt_id t).mul (hasDerivAt_log_neg_log ht0 hte)
    convert hmul using 1
    · rfl
    · simp only [id_eq]
      field_simp [ht0.ne']
      ring
  have hc_log : ContinuousOn (fun t => Real.log (-Real.log t)) (uIcc a r) := by
    rw [uIcc_of_le har]
    intro t ht
    exact (hasDerivAt_log_neg_log (lt_of_lt_of_le ha0 ht.1)
      (lt_of_le_of_lt ht.2 hre)).continuousAt.continuousWithinAt
  have hc_psi : ContinuousOn ftildePsi (uIcc a r) := by
    rw [uIcc_of_le har]
    exact continuousOn_ftildePsi_Ioo.mono
      (fun t ht => ⟨lt_of_lt_of_le ha0 ht.1, lt_of_le_of_lt ht.2 hr1⟩)
  have hint_log : IntervalIntegrable (fun t => Real.log (-Real.log t)) volume a r :=
    hc_log.intervalIntegrable
  have hint_psi : IntervalIntegrable ftildePsi volume a r :=
    hc_psi.intervalIntegrable
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hint_log.sub hint_psi)
  rw [intervalIntegral.integral_sub hint_log hint_psi] at hsub
  linarith

/-- `Real.log (-Real.log r) → +∞` as `r → 0⁺`. -/
lemma tendsto_log_neg_log_nhdsGT_zero :
    Filter.Tendsto (fun r : ℝ => Real.log (-Real.log r)) (𝓝[>] 0) Filter.atTop := by
  have h1 : Filter.Tendsto Real.log (𝓝[>] 0) Filter.atBot :=
    Real.tendsto_log_nhdsNE_zero.mono_left (nhdsWithin_mono 0 fun x hx => ne_of_gt hx)
  have h2 : Filter.Tendsto (fun r : ℝ => -Real.log r) (𝓝[>] 0) Filter.atTop :=
    Filter.tendsto_neg_atBot_atTop.comp h1
  exact Real.tendsto_log_atTop.comp h2

/-- **L10 (`C¹` Failure of Coulomb Symmetric Gradient):**
If a matrix field `S : Fin 3 → VectorField` on `ftildeBall` satisfies the L8 asymptotic
`coordinatePartial (fun y => S i y j) x k = ftildeC i j k * log(-log ‖x‖) + R i j k x`
with bounded remainder `|R i j k x| ≤ M` on `0 < ‖x‖ ≤ r₀` (`0 < r₀ < e⁻¹`), then `S` CANNOT have
`∀ i, ContDiffOn ℝ 1 (S i) ftildeBall`! In particular, the Coulomb potential `A_0 = (-Δ)⁻¹(curl F̃)`
genuinely fails to lie in `C²(B)` (`S^{(0)} = Sym(DA_0) ∉ C¹(B)`). -/
theorem l10_not_c1_of_log_log_symGrad
    (S : Fin 3 → VectorField)
    {r₀ M : ℝ} (hr₀0 : 0 < r₀) (hr₀e : r₀ < Real.exp (-1))
    (R : Fin 3 → Fin 3 → Fin 3 → Euclidean 3 → ℝ)
    (hR : ∀ x : Euclidean 3, 0 < ‖x‖ → ‖x‖ ≤ r₀ →
      ∀ i j k : Fin 3, |R i j k x| ≤ M)
    (hasymp : ∀ x : Euclidean 3, 0 < ‖x‖ → ‖x‖ ≤ r₀ →
      ∀ i j k : Fin 3,
        coordinatePartial (fun y => S i y j) x k =
          ftildeC i j k * Real.log (-Real.log ‖x‖) + R i j k x) :
    ¬ (∀ i : Fin 3, ContDiffOn ℝ 1 (S i) ftildeBall) := by
  intro hS
  -- Evaluate along `e₀ = coordinateVector 3 0`, where `ftildeC 0 0 0 = -8/35 ≠ 0`.
  let e₀ : Euclidean 3 := coordinateVector 3 0
  have he₀_norm : ‖e₀‖ = 1 := by
    simp [e₀, coordinateVector, EuclideanSpace.basisFun_apply]
  have hr₀1 : r₀ < 1 := hr₀e.trans (Real.exp_lt_one_iff.mpr (by norm_num))
  have hcomp : ContDiffOn ℝ 1 (fun x : Euclidean 3 => S 0 x 0) ftildeBall :=
    contDiffOn_map_coordinate (hS 0) 0
  have hpart_cont : ContinuousOn (fun x => coordinatePartial (fun y => S 0 y 0) x 0) ftildeBall :=
    continuousOn_coordinatePartial Metric.isOpen_ball hcomp 0
  have hsub : Metric.closedBall (0 : Euclidean 3) r₀ ⊆ ftildeBall :=
    Metric.closedBall_subset_ball hr₀1
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Euclidean 3) r₀).exists_bound_of_continuousOn
    (hpart_cont.mono hsub)
  -- Pick `r ∈ (0, r₀)` small enough that `(8/35) * log(-log r) > |B| + |M| + 1`.
  have hev : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (35 / 8 : ℝ) * (|B| + |M| + 1) < Real.log (-Real.log r) :=
    tendsto_log_neg_log_nhdsGT_zero.eventually
      (Filter.eventually_gt_atTop ((35 / 8 : ℝ) * (|B| + |M| + 1)))
  have hmem : Ioo (0 : ℝ) r₀ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hr₀0
  obtain ⟨r, hr_big, hr_Ioo⟩ := (hev.and hmem).exists
  have hr_pos : 0 < r := hr_Ioo.1
  have hr_lt : r < r₀ := hr_Ioo.2
  let x : Euclidean 3 := r • e₀
  have hx_norm : ‖x‖ = r := by
    rw [norm_smul, Real.norm_of_nonneg hr_pos.le, he₀_norm, mul_one]
  have hx_ball : x ∈ Metric.closedBall (0 : Euclidean 3) r₀ := by
    rw [Metric.mem_closedBall, dist_zero_right, hx_norm]
    exact hr_lt.le
  have hbound_B : |coordinatePartial (fun y => S 0 y 0) x 0| ≤ |B| :=
    (Real.norm_eq_abs _ ▸ hB x hx_ball).trans (le_abs_self B)
  have hbound_R : |R 0 0 0 x| ≤ |M| :=
    (hR x (hx_norm ▸ hr_pos) (hx_norm ▸ hr_lt.le) 0 0 0).trans (le_abs_self M)
  have heq := hasymp x (hx_norm ▸ hr_pos) (hx_norm ▸ hr_lt.le) 0 0 0
  have hC000 : ftildeC 0 0 0 = -8 / 35 := by norm_num [ftildeC]
  rw [hC000, hx_norm] at heq
  have htri : (8 / 35 : ℝ) * Real.log (-Real.log r) ≤
      |coordinatePartial (fun y => S 0 y 0) x 0| + |R 0 0 0 x| := by
    have hval : (8 / 35 : ℝ) * Real.log (-Real.log r) =
        R 0 0 0 x - coordinatePartial (fun y => S 0 y 0) x 0 := by linarith
    calc
      (8 / 35 : ℝ) * Real.log (-Real.log r)
          ≤ |R 0 0 0 x - coordinatePartial (fun y => S 0 y 0) x 0| := by
            rw [← hval]; exact le_abs_self _
      _ ≤ |R 0 0 0 x| + |coordinatePartial (fun y => S 0 y 0) x 0| := abs_sub _ _
      _ = |coordinatePartial (fun y => S 0 y 0) x 0| + |R 0 0 0 x| := add_comm _ _
  linarith

/-!
### Section I.4: Structural Classification for the Next `#29` Direction

Following Stage 3's refutation of `¬ SymmetricCurlSystem ftildeBall ftildeField` for the
Stage 1–2 `ftildeField` witness target (`rudin29-stage3-harmonic`, `6f2c75a5`), we establish
three general structural theorems that govern the choice between constructing a new
counterexample candidate and proving `pma10_43_contract`:

1. **Universal `Sym³₀(ℝ³) = H₃(ℝ³)` Harmonic Trap (`traceFree_sym3_cubic_harmonic`):**
   Every constant symmetric trace-free 3-tensor `C` on `ℝ³` is the exact third-derivative tensor
   `∇³ P` of the **harmonic** cubic polynomial `cubicOfTensor C`. Consequently, the `G6` physical-
   space gauge-orthogonality failure is not specific to `ftildeC`: *any* candidate whose Coulomb
   symmetric gradient blows up with a non-oscillatory trace-free rank-3 tensor `C · Φ(‖x‖)` allows
   local leading-order gauge cancellation by `-P(x) Φ(‖x‖)`.

2. **General Sublinear-Hessian Poincaré `C²` Regularity Theorem
   (`contDiffOn_two_poincareVectorPotential`, `symmetricCurlSystem_of_sublinear_second_deriv`):**
   For *any* `C¹` divergence-free vector field `F` on `ball 0 R` (`0 < R`) that is `C²` on the
   punctured ball `ball 0 R \ {0}` and satisfies the sublinear second-derivative condition
   `‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial (fun w => F w m) y j) z‖ → 0` as `z → 0`,
   the classical radial-homotopy Poincaré potential `G(x) = ∫_0^1 t (F(t • x) × x) dt` belongs
   to `C²(ball 0 R)` and satisfies `curl G = F` on `ball 0 R` (hence `SymmetricCurlSystem (ball 0 R) F`).
   This rules out the **entire class** of single-point sublinear-Hessian / radial-modulus
   candidates `F(x) = ψ(‖x‖) V(x / ‖x‖) + W(x)` with smooth `V` and `r ψ'(r) → 0, r² ψ''(r) → 0`:
   any genuine counterexample to Rudin 10.43 MUST violate `‖z - z₀‖ · ‖D²F(z)‖ → 0` (requiring
   rapid radial/angular oscillation or multiscale concentration).

3. **Gauge-Invariant Fourth-Order Planar Duality Identity & Bound
   (`planar_c2_div_fourth_order_duality`, `planar_c2_div_fourth_order_bound`):**
   For *any* `C²` planar vector field `V = (V₁, V₂)` solving `planarDivergence V = h` (with NO `C³`
   assumption on `V`) and any `C⁵` test function `w` vanishing to order 4 on the boundary of a
   rectangle `[a, b] × [c, d]`,
   `∫_c^d ∫_a^b h (∂_x² ∂_y² w) dx dy = -∫_c^d ∫_a^b ((∂_y² V₁)(∂_x³ w) + (∂_x² V₂)(∂_y³ w)) dx dy`,
   isolating the exact all-gauge duality pairing between `h ∈ C¹` and `(∂_x³ w, ∂_y³ w) ∈ L¹`.
-/

/-- Homogeneous cubic polynomial `(1/6) ∑_{i,j,k} C_{ijk} x_i x_j x_k` associated with any
constant rank-3 tensor `C`. -/
def cubicOfTensor (C : Fin 3 → Fin 3 → Fin 3 → ℝ) (x : Euclidean 3) : ℝ :=
  (1 / 6 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, C i j k * (x i * x j * x k)

private lemma coordinatePartial_coord_fin3 (m a : Fin 3) (x : Euclidean 3) :
    coordinatePartial (fun y : Euclidean 3 => y m) x a = kronecker3 m a := by
  have hd : HasFDerivAt (fun y : Euclidean 3 => y m)
      (EuclideanSpace.proj m : Euclidean 3 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj m : Euclidean 3 →L[ℝ] ℝ).hasFDerivAt
  rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv]
  cases m using fin3_cases <;> cases a using fin3_cases <;>
    norm_num [EuclideanSpace.coe_proj, coordinateVector, EuclideanSpace.basisFun_apply,
      kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]

private lemma coordinatePartial_quad_fin3 (i j a : Fin 3) (x : Euclidean 3) :
    coordinatePartial (fun y : Euclidean 3 => y i * y j) x a =
      kronecker3 i a * x j + x i * kronecker3 j a := by
  have hi : DifferentiableAt ℝ (fun y : Euclidean 3 => y i) x :=
    (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).differentiableAt
  have hj : DifferentiableAt ℝ (fun y : Euclidean 3 => y j) x :=
    (EuclideanSpace.proj j : Euclidean 3 →L[ℝ] ℝ).differentiableAt
  rw [coordinatePartial_mul hi hj a, coordinatePartial_coord_fin3, coordinatePartial_coord_fin3]

private lemma coordinatePartial_cubic_fin3 (i j k a : Fin 3) (x : Euclidean 3) :
    coordinatePartial (fun y : Euclidean 3 => y i * y j * y k) x a =
      (kronecker3 i a * x j + x i * kronecker3 j a) * x k +
        (x i * x j) * kronecker3 k a := by
  have hij : DifferentiableAt ℝ (fun y : Euclidean 3 => y i * y j) x :=
    (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).differentiableAt.mul
      (EuclideanSpace.proj j : Euclidean 3 →L[ℝ] ℝ).differentiableAt
  have hk : DifferentiableAt ℝ (fun y : Euclidean 3 => y k) x :=
    (EuclideanSpace.proj k : Euclidean 3 →L[ℝ] ℝ).differentiableAt
  rw [coordinatePartial_mul hij hk a, coordinatePartial_quad_fin3, coordinatePartial_coord_fin3]

private lemma scalarLaplacian3_coord_mul3 (i j k : Fin 3) (x : Euclidean 3) :
    scalarLaplacian3 (fun z : Euclidean 3 => z i * z j * z k) x =
      2 * (kronecker3 i j * x k + kronecker3 i k * x j + kronecker3 j k * x i) := by
  unfold scalarLaplacian3
  have hterm : ∀ b : Fin 3,
      fderiv ℝ (fun y : Euclidean 3 =>
        fderiv ℝ (fun z : Euclidean 3 => z i * z j * z k) y (coordinateVector 3 b)) x
          (coordinateVector 3 b) =
      ((kronecker3 i b * kronecker3 j b + kronecker3 i b * kronecker3 j b) * x k +
        (kronecker3 i b * x j + x i * kronecker3 j b) * kronecker3 k b) +
        (kronecker3 i b * x j + x i * kronecker3 j b) * kronecker3 k b := by
    intro b
    have h1 : (fun y : Euclidean 3 =>
        fderiv ℝ (fun z : Euclidean 3 => z i * z j * z k) y (coordinateVector 3 b)) =
        fun y : Euclidean 3 =>
          (kronecker3 i b * y j + y i * kronecker3 j b) * y k +
            (y i * y j) * kronecker3 k b := by
      funext y
      rw [← coordinatePartial_eq_fderiv (by fun_prop) b, coordinatePartial_cubic_fin3]
    rw [h1, ← coordinatePartial_eq_fderiv (by fun_prop) b,
      coordinatePartial_add (by fun_prop) (by fun_prop),
      coordinatePartial_mul (by fun_prop) (by fun_prop),
      coordinatePartial_add (by fun_prop) (by fun_prop),
      coordinatePartial_const_mul (by fun_prop),
      coordinatePartial_mul_const (by fun_prop),
      coordinatePartial_mul_const (by fun_prop),
      coordinatePartial_quad_fin3,
      coordinatePartial_coord_fin3, coordinatePartial_coord_fin3, coordinatePartial_coord_fin3]
  simp only [hterm, Fin.sum_univ_three]
  cases i using fin3_cases <;> cases j using fin3_cases <;> cases k using fin3_cases <;>
    norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two] <;>
    ring

/-- **Universal `Sym³₀(ℝ³) = H₃(ℝ³)` Harmonic Trap:**
For *every* symmetric trace-free constant 3-tensor `C` on `ℝ³`, `cubicOfTensor C` is globally
harmonic (`scalarLaplacian3 (cubicOfTensor C) x = 0`) and its third coordinate partials recover
`C a b c` identically. Hence `G6` fails for *every* non-oscillatory trace-free rank-3 blow-up. -/
theorem traceFree_sym3_cubic_harmonic
    (C : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hsym12 : ∀ i j k : Fin 3, C i j k = C j i k)
    (hsym23 : ∀ i j k : Fin 3, C i j k = C i k j)
    (htrace : ∀ k : Fin 3, (∑ i : Fin 3, C i i k) = 0) :
    (∀ x : Euclidean 3, scalarLaplacian3 (cubicOfTensor C) x = 0) ∧
      (∀ (x : Euclidean 3) (a b c : Fin 3),
        coordinatePartial (fun w =>
          coordinatePartial (fun z =>
            coordinatePartial (cubicOfTensor C) z c) w b) x a = C a b c) := by
  -- Canonical sorted-index reductions for all 17 non-sorted triples
  have e010 : C 0 1 0 = C 0 0 1 := hsym23 0 1 0
  have e100 : C 1 0 0 = C 0 0 1 := (hsym12 1 0 0).trans (hsym23 0 1 0)
  have e020 : C 0 2 0 = C 0 0 2 := hsym23 0 2 0
  have e200 : C 2 0 0 = C 0 0 2 := (hsym12 2 0 0).trans (hsym23 0 2 0)
  have e101 : C 1 0 1 = C 0 1 1 := hsym12 1 0 1
  have e110 : C 1 1 0 = C 0 1 1 := (hsym23 1 1 0).trans (hsym12 1 0 1)
  have e202 : C 2 0 2 = C 0 2 2 := hsym12 2 0 2
  have e220 : C 2 2 0 = C 0 2 2 := (hsym23 2 2 0).trans (hsym12 2 0 2)
  have e121 : C 1 2 1 = C 1 1 2 := hsym23 1 2 1
  have e211 : C 2 1 1 = C 1 1 2 := (hsym12 2 1 1).trans (hsym23 1 2 1)
  have e212 : C 2 1 2 = C 1 2 2 := hsym12 2 1 2
  have e221 : C 2 2 1 = C 1 2 2 := (hsym23 2 2 1).trans (hsym12 2 1 2)
  have e021 : C 0 2 1 = C 0 1 2 := hsym23 0 2 1
  have e102 : C 1 0 2 = C 0 1 2 := hsym12 1 0 2
  have e120 : C 1 2 0 = C 0 1 2 := (hsym23 1 2 0).trans (hsym12 1 0 2)
  have e201 : C 2 0 1 = C 0 1 2 := (hsym12 2 0 1).trans (hsym23 0 2 1)
  have e210 : C 2 1 0 = C 0 1 2 := (hsym12 2 1 0).trans ((hsym23 1 2 0).trans (hsym12 1 0 2))
  have htr0 := htrace 0; have htr1 := htrace 1; have htr2 := htrace 2
  simp only [Fin.sum_univ_three] at htr0 htr1 htr2
  have e000 : C 0 0 0 = -C 0 1 1 - C 0 2 2 := by linarith [htr0, e110, e220]
  have e111 : C 1 1 1 = -C 0 0 1 - C 1 2 2 := by linarith [htr1, e221]
  have e222 : C 2 2 2 = -C 0 0 2 - C 1 1 2 := by linarith [htr2]
  constructor
  · intro x
    have heq : cubicOfTensor C = fun z : Euclidean 3 =>
        (1 / 6 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, C i j k * (z i * z j * z k) := rfl
    rw [heq]
    simp only [Fin.sum_univ_three]
    simp (disch := fun_prop) only [scalarLaplacian3_const_mul, scalarLaplacian3_add,
      scalarLaplacian3_coord_mul3]
    norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    simp only [e010, e100, e020, e200, e101, e110, e202, e220, e121, e211, e212, e221,
      e000, e111, e222]
    ring
  · intro x a b c
    have hd1 : ∀ z : Euclidean 3,
        coordinatePartial (cubicOfTensor C) z c =
          (1 / 6 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            C i j k * ((kronecker3 i c * z j + z i * kronecker3 j c) * z k +
              (z i * z j) * kronecker3 k c) := by
      intro z
      unfold cubicOfTensor
      rw [coordinatePartial_const_mul (by fun_prop)]
      congr 1
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coordinatePartial_const_mul (by fun_prop), coordinatePartial_cubic_fin3]
    have hd2 : ∀ w : Euclidean 3,
        coordinatePartial (fun z => coordinatePartial (cubicOfTensor C) z c) w b =
          (1 / 6 : ℝ) * ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            C i j k *
              (((kronecker3 i c * kronecker3 j b + kronecker3 i b * kronecker3 j c) * w k +
                  (kronecker3 i c * w j + w i * kronecker3 j c) * kronecker3 k b) +
                (kronecker3 i b * w j + w i * kronecker3 j b) * kronecker3 k c) := by
      intro w
      simp only [hd1]
      rw [coordinatePartial_const_mul (by fun_prop)]
      congr 1
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coordinatePartial_const_mul (by fun_prop)]
      congr 1
      rw [coordinatePartial_add (by fun_prop) (by fun_prop),
        coordinatePartial_mul (by fun_prop) (by fun_prop),
        coordinatePartial_add (by fun_prop) (by fun_prop),
        coordinatePartial_const_mul (by fun_prop),
        coordinatePartial_mul_const (by fun_prop),
        coordinatePartial_mul_const (by fun_prop),
        coordinatePartial_quad_fin3,
        coordinatePartial_coord_fin3, coordinatePartial_coord_fin3, coordinatePartial_coord_fin3]
    simp only [hd2]
    rw [coordinatePartial_const_mul (by fun_prop)]
    have hsum :
        coordinatePartial (fun w : Euclidean 3 =>
          ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
            C i j k *
              (((kronecker3 i c * kronecker3 j b + kronecker3 i b * kronecker3 j c) * w k +
                  (kronecker3 i c * w j + w i * kronecker3 j c) * kronecker3 k b) +
                (kronecker3 i b * w j + w i * kronecker3 j b) * kronecker3 k c)) x a =
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3,
          C i j k *
            (((kronecker3 i c * kronecker3 j b + kronecker3 i b * kronecker3 j c) * kronecker3 k a +
                (kronecker3 i c * kronecker3 j a + kronecker3 i a * kronecker3 j c) * kronecker3 k b) +
              (kronecker3 i b * kronecker3 j a + kronecker3 i a * kronecker3 j b) * kronecker3 k c) := by
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [coordinatePartial_sum (fun _ => by fun_prop)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coordinatePartial_const_mul (by fun_prop)]
      congr 1
      rw [coordinatePartial_add (by fun_prop) (by fun_prop),
        coordinatePartial_add (by fun_prop) (by fun_prop),
        coordinatePartial_const_mul (by fun_prop),
        coordinatePartial_mul_const (by fun_prop),
        coordinatePartial_mul_const (by fun_prop),
        coordinatePartial_add (by fun_prop) (by fun_prop),
        coordinatePartial_add (by fun_prop) (by fun_prop),
        coordinatePartial_const_mul (by fun_prop),
        coordinatePartial_const_mul (by fun_prop),
        coordinatePartial_mul_const (by fun_prop),
        coordinatePartial_mul_const (by fun_prop),
        coordinatePartial_coord_fin3, coordinatePartial_coord_fin3, coordinatePartial_coord_fin3]
    rw [hsum]
    simp only [Fin.sum_univ_three]
    set_option linter.unusedSimpArgs false in
    cases a using fin3_cases <;> cases b using fin3_cases <;> cases c using fin3_cases <;>
      · norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
        try simp only [e010, e100, e020, e200, e101, e110, e202, e220, e121, e211, e212, e221,
          e021, e102, e120, e201, e210]
        ring

/-- Scalar radial moment integral `M_i(g)(x) = ∫_0^1 t * x_i * g(t • x) dt`. -/
def rayMomentIntegral (i : Fin 3) (g : Euclidean 3 → ℝ) (x : Euclidean 3) : ℝ :=
  ∫ t in (0 : ℝ)..1, t * x i * g (t • x)

/-- Classical radial-homotopy Poincaré vector potential `G(x) = ∫_0^1 t (F(t • x) × x) dt`. -/
def poincareVectorPotential (F : VectorField) : VectorField :=
  fun x => coordEquivEuclidean 3
    (fin3Vec
      (rayMomentIntegral 2 (fun y => F y 1) x - rayMomentIntegral 1 (fun y => F y 2) x)
      (rayMomentIntegral 0 (fun y => F y 2) x - rayMomentIntegral 2 (fun y => F y 0) x)
      (rayMomentIntegral 1 (fun y => F y 0) x - rayMomentIntegral 0 (fun y => F y 1) x))

private lemma prod_Icc_ball_subset_preimage {R : ℝ} :
    Icc (0 : ℝ) 1 ×ˢ Metric.ball (0 : Euclidean 3) R ⊆
      (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' Metric.ball (0 : Euclidean 3) R := by
  rintro ⟨t, x⟩ ⟨ht, hx⟩
  change t • x ∈ Metric.ball (0 : Euclidean 3) R
  rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
  calc
    t * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)
    _ = ‖x‖ := one_mul ‖x‖
    _ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx

private lemma contDiffOn_one_rayLinear {U : Set (Euclidean 3)} (i : Fin 3)
    {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g U) :
    ContDiffOn ℝ 1 (fun q : ℝ × Euclidean 3 => q.1 * q.2 i * g (q.1 • q.2))
      ((fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U) := by
  have hw : ContDiff ℝ 1 (fun q : ℝ × Euclidean 3 => q.1 * q.2 i) :=
    contDiff_fst.mul ((EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).contDiff.comp contDiff_snd)
  exact hw.contDiffOn.mul (hg.comp (contDiff_fst.smul contDiff_snd).contDiffOn fun _ h => h)

private lemma contDiffOn_one_rayMomentIntegral_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    (i : Fin 3) {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g U) :
    ContDiffOn ℝ 1 (rayMomentIntegral i g) U :=
  contDiffOn_parameter_integral
    (hU.preimage (continuous_fst.smul continuous_snd)) hU hstar
    (contDiffOn_one_rayLinear i hg)

lemma contDiffOn_one_rayMomentIntegral {R : ℝ} (i : Fin 3)
    {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g (Metric.ball (0 : Euclidean 3) R)) :
    ContDiffOn ℝ 1 (rayMomentIntegral i g) (Metric.ball (0 : Euclidean 3) R) :=
  contDiffOn_one_rayMomentIntegral_of_star Metric.isOpen_ball prod_Icc_ball_subset_preimage i hg

private lemma coordinatePartial_smul_arg {g : Euclidean 3 → ℝ} {x : Euclidean 3} {t : ℝ}
    (hg : DifferentiableAt ℝ g (t • x)) (j : Fin 3) :
    coordinatePartial (fun y : Euclidean 3 => g (t • y)) x j =
      t * coordinatePartial g (t • x) j := by
  have hsmul : HasFDerivAt (fun y : Euclidean 3 => t • y)
      (t • ContinuousLinearMap.id ℝ (Euclidean 3)) x :=
    (hasFDerivAt_id x).const_smul t
  have hcomp : HasFDerivAt (fun y : Euclidean 3 => g (t • y))
      ((fderiv ℝ g (t • x)).comp (t • ContinuousLinearMap.id ℝ (Euclidean 3))) x :=
    hg.hasFDerivAt.comp x hsmul
  rw [coordinatePartial_eq_fderiv hcomp.differentiableAt, hcomp.fderiv,
    coordinatePartial_eq_fderiv hg]
  simp [smul_eq_mul]

private lemma coordinatePartial_rayMomentIntegral_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    (i j : Fin 3) {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g U)
    {x : Euclidean 3} (hx : x ∈ U) :
    coordinatePartial (rayMomentIntegral i g) x j =
      ∫ t in (0 : ℝ)..1,
        (t * kronecker3 i j * g (t • x) + t ^ 2 * x i * coordinatePartial g (t • x) j) := by
  have hW : IsOpen ((fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U) :=
    hU.preimage (continuous_fst.smul continuous_snd)
  have hH := contDiffOn_one_rayLinear i hg
  change coordinatePartial
    (fun y => ∫ t in (0 : ℝ)..1, (fun q : ℝ × Euclidean 3 => q.1 * q.2 i * g (q.1 • q.2)) (t, y))
      x j = _
  rw [coordinatePartial_parameter_integral hW hU hstar hH hx j]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have htx : t • x ∈ U := Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht' hx))
  have hgd : DifferentiableAt ℝ g (t • x) :=
    hg.differentiableOn_one.differentiableAt (hU.mem_nhds htx)
  have hw : DifferentiableAt ℝ (fun y : Euclidean 3 => t * y i) x :=
    ((EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).differentiableAt).const_mul t
  have hgs : DifferentiableAt ℝ (fun y : Euclidean 3 => g (t • y)) x :=
    hgd.comp x ((differentiableAt_id).const_smul t)
  change coordinatePartial (fun y : Euclidean 3 => (t * y i) * g (t • y)) x j = _
  rw [coordinatePartial_mul hw hgs j,
    coordinatePartial_const_mul (by fun_prop : DifferentiableAt ℝ (fun y : Euclidean 3 => y i) x) t j,
    coordinatePartial_coord_fin3, coordinatePartial_smul_arg hgd j]
  ring

lemma coordinatePartial_rayMomentIntegral {R : ℝ} (i j : Fin 3)
    {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g (Metric.ball (0 : Euclidean 3) R))
    {x : Euclidean 3} (hx : x ∈ Metric.ball (0 : Euclidean 3) R) :
    coordinatePartial (rayMomentIntegral i g) x j =
      ∫ t in (0 : ℝ)..1,
        (t * kronecker3 i j * g (t • x) + t ^ 2 * x i * coordinatePartial g (t • x) j) :=
  coordinatePartial_rayMomentIntegral_of_star Metric.isOpen_ball
    prod_Icc_ball_subset_preimage i j hg hx

private lemma coordinatePartial_sub_fin3 {f₁ f₂ : Euclidean 3 → ℝ} {x : Euclidean 3}
    (hd₁ : DifferentiableAt ℝ f₁ x) (hd₂ : DifferentiableAt ℝ f₂ x) (j : Fin 3) :
    coordinatePartial (fun y => f₁ y - f₂ y) x j =
      coordinatePartial f₁ x j - coordinatePartial f₂ x j := by
  have hneg : coordinatePartial (fun y => (-1 : ℝ) * f₂ y) x j = -coordinatePartial f₂ x j := by
    simpa using coordinatePartial_const_mul hd₂ (-1) j
  have hrew : (fun y => f₁ y - f₂ y) = fun y => f₁ y + (-1 : ℝ) * f₂ y := by
    funext y; ring
  rw [hrew, coordinatePartial_add hd₁ (hd₂.const_mul (-1)) j, hneg, sub_eq_add_neg]

private lemma poincare_ray_ftc_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g U)
    {x : Euclidean 3} (hx : x ∈ U) :
    (∫ t in (0 : ℝ)..1,
      (2 * t * g (t • x) +
        t ^ 2 * (x 0 * coordinatePartial g (t • x) 0 +
          x 1 * coordinatePartial g (t • x) 1 +
          x 2 * coordinatePartial g (t • x) 2))) = g x := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => s ^ 2 * g (s • x))
        (2 * t * g (t • x) +
          t ^ 2 * (x 0 * coordinatePartial g (t • x) 0 +
            x 1 * coordinatePartial g (t • x) 1 +
            x 2 * coordinatePartial g (t • x) 2)) t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have htx : t • x ∈ U := Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht' hx))
    have hgd : DifferentiableAt ℝ g (t • x) :=
      hg.differentiableOn_one.differentiableAt (hU.mem_nhds htx)
    have hline : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa [one_smul] using (hasDerivAt_id t).smul_const x
    have hcomp : HasDerivAt (fun s : ℝ => g (s • x)) (fderiv ℝ g (t • x) x) t :=
      hgd.hasFDerivAt.comp_hasDerivAt t hline
    have hlin : fderiv ℝ g (t • x) x =
        x 0 * coordinatePartial g (t • x) 0 +
          x 1 * coordinatePartial g (t • x) 1 +
          x 2 * coordinatePartial g (t • x) 2 := by
      rw [linear_apply_eq_sum_coordinates, Fin.sum_univ_three,
        ← coordinatePartial_eq_fderiv hgd 0,
        ← coordinatePartial_eq_fderiv hgd 1,
        ← coordinatePartial_eq_fderiv hgd 2]
      ring
    rw [hlin] at hcomp
    have hpow : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      have hsq : (fun s : ℝ => s ^ 2) = fun s : ℝ => s * s := funext sq
      rw [hsq]
      exact ((hasDerivAt_id' t).mul (hasDerivAt_id' t)).congr_deriv (by ring)
    exact hpow.mul hcomp
  have hcont : ContinuousOn
      (fun t : ℝ =>
        2 * t * g (t • x) +
          t ^ 2 * (x 0 * coordinatePartial g (t • x) 0 +
            x 1 * coordinatePartial g (t • x) 1 +
            x 2 * coordinatePartial g (t • x) 2))
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    have hmap : MapsTo (fun t : ℝ => t • x) (Icc (0 : ℝ) 1) U :=
      fun t ht => Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht hx))
    have hcg : ContinuousOn (fun t : ℝ => g (t • x)) (Icc (0 : ℝ) 1) :=
      hg.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hmap
    have hcp : ∀ j : Fin 3,
        ContinuousOn (fun t : ℝ => coordinatePartial g (t • x) j) (Icc (0 : ℝ) 1) :=
      fun j => (continuousOn_coordinatePartial hU hg j).comp
        (continuous_id.smul continuous_const).continuousOn hmap
    exact (((continuousOn_const.mul continuousOn_id).mul hcg).add
      ((continuousOn_id.pow 2).mul
        (((continuousOn_const.mul (hcp 0)).add (continuousOn_const.mul (hcp 1))).add
          (continuousOn_const.mul (hcp 2)))))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable
  simpa [one_pow, one_smul, zero_pow (by norm_num : 2 ≠ 0), zero_mul] using hftc

private lemma poincare_slice_intervalIntegrable_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    (i j : Fin 3) {g : Euclidean 3 → ℝ} (hg : ContDiffOn ℝ 1 g U)
    {x : Euclidean 3} (hx : x ∈ U) :
    IntervalIntegrable
      (fun t : ℝ =>
        t * kronecker3 i j * g (t • x) +
          t ^ 2 * x i * coordinatePartial g (t • x) j)
      volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le zero_le_one]
  have hmap : MapsTo (fun t : ℝ => t • x) (Icc (0 : ℝ) 1) U :=
    fun t ht => Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht hx))
  exact (((continuousOn_id.mul continuousOn_const).mul
    (hg.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hmap)).add
    (((continuousOn_id.pow 2).mul continuousOn_const).mul
      ((continuousOn_coordinatePartial hU hg j).comp
        (continuous_id.smul continuous_const).continuousOn hmap)))

private lemma intervalIntegral_sub_sub {f₁ f₂ f₃ f₄ : ℝ → ℝ}
    (h₁ : IntervalIntegrable f₁ volume 0 1) (h₂ : IntervalIntegrable f₂ volume 0 1)
    (h₃ : IntervalIntegrable f₃ volume 0 1) (h₄ : IntervalIntegrable f₄ volume 0 1) :
    ((∫ t in (0 : ℝ)..1, f₁ t) - ∫ t in (0 : ℝ)..1, f₂ t) -
      ((∫ t in (0 : ℝ)..1, f₃ t) - ∫ t in (0 : ℝ)..1, f₄ t) =
      ∫ t in (0 : ℝ)..1, ((f₁ t - f₂ t) - (f₃ t - f₄ t)) := by
  rw [← intervalIntegral.integral_sub h₁ h₂, ← intervalIntegral.integral_sub h₃ h₄,
    ← intervalIntegral.integral_sub (h₁.sub h₂) (h₃.sub h₄)]

private lemma curl_poincareVectorPotential_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F U)
    (hdiv : EqOn (divergence F) 0 U) :
    EqOn (curl (poincareVectorPotential F)) F U := by
  intro x hx
  have hFc : ∀ m : Fin 3, ContDiffOn ℝ 1 (fun y => F y m) U :=
    fun m => contDiffOn_map_coordinate hF m
  have hMc : ∀ i m : Fin 3,
      DifferentiableAt ℝ (rayMomentIntegral i (fun y => F y m)) x := fun i m =>
    (contDiffOn_one_rayMomentIntegral_of_star hU hstar i (hFc m)).differentiableOn_one.differentiableAt
      (hU.mem_nhds hx)
  ext m
  cases m using fin3_cases
  · simp only [curl, poincareVectorPotential, coordEquivEuclidean_apply_coordinate,
      Matrix.cons_val_zero, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    rw [coordinatePartial_sub_fin3 (hMc 1 0) (hMc 0 1) 1,
      coordinatePartial_sub_fin3 (hMc 0 2) (hMc 2 0) 2,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 1 1 (hFc 0) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 0 1 (hFc 1) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 0 2 (hFc 2) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 2 2 (hFc 0) hx,
      intervalIntegral_sub_sub
        (poincare_slice_intervalIntegrable_of_star hU hstar 1 1 (hFc 0) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 0 1 (hFc 1) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 0 2 (hFc 2) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 2 2 (hFc 0) hx),
      ← poincare_ray_ftc_of_star hU hstar (hFc 0) hx]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hdiv_tx : divergence F (t • x) = 0 :=
      hdiv (Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht' hx)))
    simp only [divergence, Fin.sum_univ_three] at hdiv_tx
    have hdiv0 : coordinatePartial (fun y => F y 0) (t • x) 0 =
        -coordinatePartial (fun y => F y 1) (t • x) 1 -
          coordinatePartial (fun y => F y 2) (t • x) 2 := by linarith
    norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    rw [hdiv0]
    ring
  · simp only [curl, poincareVectorPotential, coordEquivEuclidean_apply_coordinate,
      Matrix.cons_val_zero, Matrix.cons_val_one, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    rw [coordinatePartial_sub_fin3 (hMc 2 1) (hMc 1 2) 2,
      coordinatePartial_sub_fin3 (hMc 1 0) (hMc 0 1) 0,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 2 2 (hFc 1) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 1 2 (hFc 2) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 1 0 (hFc 0) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 0 0 (hFc 1) hx,
      intervalIntegral_sub_sub
        (poincare_slice_intervalIntegrable_of_star hU hstar 2 2 (hFc 1) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 1 2 (hFc 2) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 1 0 (hFc 0) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 0 0 (hFc 1) hx),
      ← poincare_ray_ftc_of_star hU hstar (hFc 1) hx]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hdiv_tx : divergence F (t • x) = 0 :=
      hdiv (Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht' hx)))
    simp only [divergence, Fin.sum_univ_three] at hdiv_tx
    have hdiv1 : coordinatePartial (fun y => F y 1) (t • x) 1 =
        -coordinatePartial (fun y => F y 0) (t • x) 0 -
          coordinatePartial (fun y => F y 2) (t • x) 2 := by linarith
    norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    rw [hdiv1]
    ring
  · simp only [curl, poincareVectorPotential, coordEquivEuclidean_apply_coordinate,
      Matrix.cons_val_two, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    rw [coordinatePartial_sub_fin3 (hMc 0 2) (hMc 2 0) 0,
      coordinatePartial_sub_fin3 (hMc 2 1) (hMc 1 2) 1,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 0 0 (hFc 2) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 2 0 (hFc 0) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 2 1 (hFc 1) hx,
      coordinatePartial_rayMomentIntegral_of_star hU hstar 1 1 (hFc 2) hx,
      intervalIntegral_sub_sub
        (poincare_slice_intervalIntegrable_of_star hU hstar 0 0 (hFc 2) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 2 0 (hFc 0) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 2 1 (hFc 1) hx)
        (poincare_slice_intervalIntegrable_of_star hU hstar 1 1 (hFc 2) hx),
      ← poincare_ray_ftc_of_star hU hstar (hFc 2) hx]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
    have hdiv_tx : divergence F (t • x) = 0 :=
      hdiv (Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht' hx)))
    simp only [divergence, Fin.sum_univ_three] at hdiv_tx
    have hdiv2 : coordinatePartial (fun y => F y 2) (t • x) 2 =
        -coordinatePartial (fun y => F y 0) (t • x) 0 -
          coordinatePartial (fun y => F y 1) (t • x) 1 := by linarith
    norm_num [kronecker3, fin3Mat_apply, fin3Vec_zero, fin3Vec_one, fin3Vec_two]
    rw [hdiv2]
    ring

/-- On `ball 0 R`, `poincareVectorPotential F` is a classical curl potential of any `C¹`
divergence-free field `F`. -/
theorem curl_poincareVectorPotential {R : ℝ} {F : VectorField}
    (hF : ContDiffOn ℝ 1 F (Metric.ball (0 : Euclidean 3) R))
    (hdiv : EqOn (divergence F) 0 (Metric.ball (0 : Euclidean 3) R)) :
    EqOn (curl (poincareVectorPotential F)) F (Metric.ball (0 : Euclidean 3) R) :=
  curl_poincareVectorPotential_of_star Metric.isOpen_ball prod_Icc_ball_subset_preimage hF hdiv

private def rayQuadKernel (i : Fin 3) (h : Euclidean 3 → ℝ)
    (q : ℝ × Euclidean 3) : Euclidean 3 →L[ℝ] ℝ :=
  (q.1 ^ 2 * h (q.1 • q.2)) • (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ) +
    (q.1 ^ 2) • (if q.1 • q.2 = 0 then (0 : Euclidean 3 →L[ℝ] ℝ)
      else ((q.1 • q.2) i) • fderiv ℝ h (q.1 • q.2))

private lemma hasFDerivAt_rayQuadIntegral_zero_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U) (h0U : (0 : Euclidean 3) ∈ U) (i : Fin 3)
    {h : Euclidean 3 → ℝ}
    (hh0 : ContinuousOn h U)
    (hH_cont : ContinuousOn (fun q : ℝ × Euclidean 3 => q.1 ^ 2 * q.2 i * h (q.1 • q.2))
      (Icc (0 : ℝ) 1 ×ˢ U))
    (hK_cont : ContinuousOn (rayQuadKernel i h) (Icc (0 : ℝ) 1 ×ˢ U)) :
    HasFDerivAt (fun y : Euclidean 3 => ∫ t in (0 : ℝ)..1, t ^ 2 * y i * h (t • y))
      (∫ t in (0 : ℝ)..1, rayQuadKernel i h (t, 0)) 0 := by
  have hval0 : (∫ t in (0 : ℝ)..1, t ^ 2 * (0 : Euclidean 3) i * h (t • 0)) = 0 := by simp
  have hK0_apply : ∀ y : Euclidean 3,
      (∫ t in (0 : ℝ)..1, rayQuadKernel i h (t, 0)) y =
        ∫ t in (0 : ℝ)..1, t ^ 2 * y i * h 0 := by
    intro y
    rw [ContinuousLinearMap.intervalIntegral_apply
      (parameter_slice_intervalIntegrable hK_cont h0U)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp [rayQuadKernel, mul_comm, mul_left_comm, mul_assoc]
  rw [hasFDerivAt_iff_tendsto, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r₀, hr₀, hball_sub⟩ := Metric.isOpen_iff.mp hU 0 h0U
  have hh_at0 : ContinuousAt h 0 := hh0.continuousAt (hU.mem_nhds h0U)
  obtain ⟨δ₁, hδ₁, hclose⟩ := Metric.continuousAt_iff.mp hh_at0 (ε / 2) (half_pos hε)
  let δ := min δ₁ r₀
  have hδ : 0 < δ := lt_min hδ₁ hr₀
  filter_upwards [Metric.ball_mem_nhds (0 : Euclidean 3) hδ] with y hy
  rw [Real.dist_eq, sub_zero]
  have hy_δ : ‖y‖ < δ := by simpa [Metric.mem_ball, dist_zero_right] using hy
  have hy_lt_δ₁ : ‖y‖ < δ₁ := hy_δ.trans_le (min_le_left _ _)
  have hy_U : y ∈ U := hball_sub (by
    rw [Metric.mem_ball, dist_zero_right]
    exact hy_δ.trans_le (min_le_right _ _))
  by_cases hy0 : y = 0
  · subst hy0
    simpa [norm_zero, inv_zero, zero_mul] using hε
  · simp only [sub_zero, hval0, hK0_apply]
    have hint1 : IntervalIntegrable (fun t : ℝ => t ^ 2 * y i * h (t • y)) volume 0 1 :=
      parameter_slice_intervalIntegrable hH_cont hy_U
    have hint2 : IntervalIntegrable (fun t : ℝ => t ^ 2 * y i * h 0) volume 0 1 :=
      (((continuous_id.pow 2).mul continuous_const).mul continuous_const).intervalIntegrable 0 1
    rw [← intervalIntegral.integral_sub hint1 hint2]
    have hbound_int :
        ‖∫ t in (0 : ℝ)..1, (t ^ 2 * y i * h (t • y) - t ^ 2 * y i * h 0)‖ ≤
          (ε / 2) * ‖y‖ := by
      have hle : ∀ t ∈ uIoc (0 : ℝ) 1,
          ‖t ^ 2 * y i * h (t • y) - t ^ 2 * y i * h 0‖ ≤ (ε / 2) * ‖y‖ := by
        intro t ht
        rw [uIoc_of_le zero_le_one] at ht
        have ht0 : 0 ≤ t := ht.1.le
        have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
        have hty_norm : dist (t • y) 0 < δ₁ := by
          rw [dist_zero_right, norm_smul, Real.norm_of_nonneg ht0]
          calc
            t * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg y)
            _ = ‖y‖ := one_mul ‖y‖
            _ < δ₁ := hy_lt_δ₁
        have hh_diff : ‖h (t • y) - h 0‖ ≤ ε / 2 := by
          simpa [Real.dist_eq] using (hclose hty_norm).le
        have hrew : t ^ 2 * y i * h (t • y) - t ^ 2 * y i * h 0 =
            t ^ 2 * y i * (h (t • y) - h 0) := by ring
        rw [hrew, norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg t)]
        calc
          t ^ 2 * ‖y i‖ * ‖h (t • y) - h 0‖
              ≤ 1 * ‖y‖ * (ε / 2) := by
                gcongr
                exact PiLp.norm_apply_le y i
          _ = (ε / 2) * ‖y‖ := by ring
      simpa using intervalIntegral.norm_integral_le_of_norm_le_const hle
    have hy_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hy_pos.le) (norm_nonneg _))]
    calc
      ‖y‖⁻¹ * ‖∫ t in (0 : ℝ)..1, (t ^ 2 * y i * h (t • y) - t ^ 2 * y i * h 0)‖
          ≤ ‖y‖⁻¹ * ((ε / 2) * ‖y‖) :=
            mul_le_mul_of_nonneg_left hbound_int (inv_nonneg.mpr hy_pos.le)
      _ = ε / 2 := by field_simp [hy_pos.ne']
      _ < ε := half_lt_self hε

private lemma hasFDerivAt_rayQuadIntegral_ne_zero {U V : Set (Euclidean 3)}
    (hU : IsOpen U) (hV : IsOpen V) (hVU : V ⊆ U) (h0V : (0 : Euclidean 3) ∉ V)
    (hstarV : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ y ∈ V, t • y ∈ V)
    (i : Fin 3) {h : Euclidean 3 → ℝ}
    (hh1 : ContDiffOn ℝ 1 h V)
    (hH_cont : ContinuousOn (fun q : ℝ × Euclidean 3 => q.1 ^ 2 * q.2 i * h (q.1 • q.2))
      (Icc (0 : ℝ) 1 ×ˢ U))
    (hK_cont : ContinuousOn (rayQuadKernel i h) (Icc (0 : ℝ) 1 ×ˢ U))
    {x : Euclidean 3} (hxV : x ∈ V) :
    HasFDerivAt (fun y : Euclidean 3 => ∫ t in (0 : ℝ)..1, t ^ 2 * y i * h (t • y))
      (∫ t in (0 : ℝ)..1, rayQuadKernel i h (t, x)) x := by
  have hxU : x ∈ U := hVU hxV
  have hK_V : ContinuousOn (rayQuadKernel i h) (Icc (0 : ℝ) 1 ×ˢ V) :=
    hK_cont.mono (prod_mono Subset.rfl hVU)
  obtain ⟨r, hr, hsub_r, C, hC⟩ := compact_parameter_local_bound hV hK_V hxV
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (F' := fun y t => rayQuadKernel i h (t, y))
    (s := Metric.closedBall x r) (bound := fun _ => C) (Metric.closedBall_mem_nhds x hr)
  · filter_upwards [hU.mem_nhds hxU] with y hy
    simpa only [uIoc_of_le zero_le_one] using
      (parameter_slice_intervalIntegrable hH_cont hy).1.aestronglyMeasurable
  · exact parameter_slice_intervalIntegrable hH_cont hxU
  · simpa only [uIoc_of_le zero_le_one] using
      (parameter_slice_intervalIntegrable hK_cont hxU).1.aestronglyMeasurable
  · apply ae_restrict_of_forall_mem measurableSet_uIoc
    intro t ht y hy
    exact hC t (Ioc_subset_Icc_self
      (by simpa only [uIoc_of_le zero_le_one] using ht)) y hy
  · exact intervalIntegrable_const
  · apply ae_restrict_of_forall_mem measurableSet_uIoc
    intro t ht y hy
    have ht_ioc : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    have hyV : y ∈ V := hsub_r hy
    have hty_V : t • y ∈ V := hstarV t ht_ioc y hyV
    have hty_ne : t • y ≠ 0 := fun h0 => h0V (h0 ▸ hty_V)
    have hdh : DifferentiableAt ℝ h (t • y) :=
      hh1.differentiableOn_one.differentiableAt (hV.mem_nhds hty_V)
    have hd1 : HasFDerivAt (fun w : Euclidean 3 => t ^ 2 * w i)
        ((t ^ 2) • (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ)) y :=
      (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).hasFDerivAt.const_mul (t ^ 2)
    have hd2 : HasFDerivAt (fun w : Euclidean 3 => h (t • w))
        ((fderiv ℝ h (t • y)).comp (t • ContinuousLinearMap.id ℝ (Euclidean 3))) y :=
      hdh.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul t)
    change HasFDerivAt (fun w : Euclidean 3 => (t ^ 2 * w i) * h (t • w))
      (rayQuadKernel i h (t, y)) y
    convert hd1.mul hd2 using 1
    ext v
    simp [rayQuadKernel, hty_ne, smul_eq_mul]
    ring

private lemma contDiffOn_one_rayQuadIntegral_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U) (h0U : (0 : Euclidean 3) ∈ U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    (i : Fin 3) {h : Euclidean 3 → ℝ}
    (hh0 : ContinuousOn h U)
    (hh1 : ContDiffOn ℝ 1 h (U \ {0}))
    (hsub : Filter.Tendsto (fun z => ‖z‖ * ‖fderiv ℝ h z‖) (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 1 (fun x => ∫ t in (0 : ℝ)..1, t ^ 2 * x i * h (t • x)) U := by
  have hU₀ : IsOpen (U \ {(0 : Euclidean 3)}) := hU.sdiff isClosed_singleton
  let Ψ : Euclidean 3 → (Euclidean 3 →L[ℝ] ℝ) :=
    fun z => if z = 0 then 0 else (z i) • fderiv ℝ h z
  have hΨ_zero : ContinuousAt Ψ 0 := by
    rw [continuousAt_iff_punctured_nhds]
    have h0 : Ψ 0 = 0 := by simp [Ψ]
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hsub
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzne : z ≠ 0 := hz
    simp only [Ψ, hzne, ↓reduceIte, norm_smul]
    exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le z i) (norm_nonneg _)
  have hΨ_U₀ : ContinuousOn Ψ (U \ {0}) := by
    have hc : ContinuousOn (fun z : Euclidean 3 => (z i) • fderiv ℝ h z) (U \ {0}) :=
      ((EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).continuous.continuousOn).smul
        (hh1.continuousOn_fderiv_of_isOpen hU₀ le_rfl)
    exact hc.congr fun z hz => by
      have hzne : z ≠ 0 := hz.2
      simp [Ψ, hzne]
  have hΨ : ContinuousOn Ψ U := by
    intro z hz
    by_cases hz0 : z = 0
    · subst hz0; exact hΨ_zero.continuousWithinAt
    · exact (hΨ_U₀.continuousAt (hU₀.mem_nhds ⟨hz, hz0⟩)).continuousWithinAt
  have hH_cont : ContinuousOn (fun q : ℝ × Euclidean 3 => q.1 ^ 2 * q.2 i * h (q.1 • q.2))
      (Icc (0 : ℝ) 1 ×ˢ U) :=
    ((continuous_fst.pow 2).mul
      ((EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).continuous.comp continuous_snd)).continuousOn.mul
      (hh0.comp (continuous_fst.smul continuous_snd).continuousOn hstar)
  have hK_eq : rayQuadKernel i h = fun q : ℝ × Euclidean 3 =>
      (q.1 ^ 2 * h (q.1 • q.2)) • (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ) +
        (q.1 ^ 2) • Ψ (q.1 • q.2) := rfl
  have hK_cont : ContinuousOn (rayQuadKernel i h) (Icc (0 : ℝ) 1 ×ˢ U) := by
    rw [hK_eq]
    exact (((continuous_fst.pow 2).continuousOn.mul
      (hh0.comp (continuous_fst.smul continuous_snd).continuousOn hstar)).smul
      continuousOn_const).add
      ((continuous_fst.pow 2).continuousOn.smul
        (hΨ.comp (continuous_fst.smul continuous_snd).continuousOn hstar))
  have hhas : ∀ x ∈ U, HasFDerivAt (fun y => ∫ t in (0 : ℝ)..1, t ^ 2 * y i * h (t • y))
      (∫ t in (0 : ℝ)..1, rayQuadKernel i h (t, x)) x := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      exact hasFDerivAt_rayQuadIntegral_zero_of_star hU h0U i hh0 hH_cont hK_cont
    · exact hasFDerivAt_rayQuadIntegral_ne_zero hU hU₀ Set.sdiff_subset
        (fun hmem => hmem.2 rfl)
        (fun t ht y hy =>
          ⟨Set.mem_preimage.mp (hstar (Set.mk_mem_prod (Ioc_subset_Icc_self ht) hy.1)),
            smul_ne_zero ht.1.ne' hy.2⟩)
        i hh1 hH_cont hK_cont ⟨hx, hx0⟩
  apply (c1On_iff_contDiffOn hU).mp
  refine ⟨fun x hx => (hhas x hx).differentiableAt, ?_⟩
  exact (continuousOn_parameter_integral hU hK_cont).congr fun x hx => (hhas x hx).fderiv

/-- Key punctured-ball parametric `C¹` lifting lemma: if `h` is continuous on `ball 0 R`, `C¹` on
`ball 0 R \ {0}`, and satisfies `‖z‖ * ‖fderiv ℝ h z‖ → 0` as `z → 0` (`z ≠ 0`), then the quadratic
radial moment `x ↦ ∫_0^1 t² x_i h(t • x) dt` is `C¹` across the origin on all of `ball 0 R`. -/
lemma contDiffOn_one_rayQuadIntegral {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {h : Euclidean 3 → ℝ}
    (hh0 : ContinuousOn h (Metric.ball (0 : Euclidean 3) R))
    (hh1 : ContDiffOn ℝ 1 h (Metric.ball (0 : Euclidean 3) R \ {0}))
    (hsub : Filter.Tendsto (fun z => ‖z‖ * ‖fderiv ℝ h z‖) (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 1 (fun x => ∫ t in (0 : ℝ)..1, t ^ 2 * x i * h (t • x))
      (Metric.ball (0 : Euclidean 3) R) :=
  contDiffOn_one_rayQuadIntegral_of_star Metric.isOpen_ball (Metric.mem_ball_self hR)
    prod_Icc_ball_subset_preimage i hh0 hh1 hsub

private lemma contDiffOn_two_rayMomentIntegral_of_star {U : Set (Euclidean 3)}
    (hU : IsOpen U) (h0U : (0 : Euclidean 3) ∈ U)
    (hstar : Icc (0 : ℝ) 1 ×ˢ U ⊆ (fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U)
    (i : Fin 3) {g : Euclidean 3 → ℝ}
    (hg1 : ContDiffOn ℝ 1 g U)
    (hg2 : ContDiffOn ℝ 2 g (U \ {0}))
    (hsub : ∀ j : Fin 3,
      Filter.Tendsto (fun z => ‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial g y j) z‖)
        (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 2 (rayMomentIntegral i g) U := by
  have hU₀ : IsOpen (U \ {(0 : Euclidean 3)}) := hU.sdiff isClosed_singleton
  apply contDiffOn_two_of_coordinatePartials hU
    (contDiffOn_one_rayMomentIntegral_of_star hU hstar i hg1)
  intro j
  have h1 : ContDiffOn ℝ 1
      (fun x : Euclidean 3 => ∫ t in (0 : ℝ)..1, t * kronecker3 i j * g (t • x)) U := by
    have hHg : ContDiffOn ℝ 1
        (fun q : ℝ × Euclidean 3 => q.1 * kronecker3 i j * g (q.1 • q.2))
        ((fun q : ℝ × Euclidean 3 => q.1 • q.2) ⁻¹' U) :=
      (contDiff_fst.mul contDiff_const).contDiffOn.mul
        (hg1.comp (contDiff_fst.smul contDiff_snd).contDiffOn fun _ h => h)
    exact contDiffOn_parameter_integral
      (hU.preimage (continuous_fst.smul continuous_snd)) hU hstar hHg
  have hh0 : ContinuousOn (fun z => coordinatePartial g z j) U :=
    continuousOn_coordinatePartial hU hg1 j
  have hh1 : ContDiffOn ℝ 1 (fun z => coordinatePartial g z j) (U \ {0}) :=
    contDiffOn_coordinatePartial (r := 1) hU₀ hg2 j
  have h2 : ContDiffOn ℝ 1
      (fun x : Euclidean 3 => ∫ t in (0 : ℝ)..1, t ^ 2 * x i * coordinatePartial g (t • x) j) U :=
    contDiffOn_one_rayQuadIntegral_of_star hU h0U hstar i hh0 hh1 (hsub j)
  refine (h1.add h2).congr fun x hx => ?_
  rw [coordinatePartial_rayMomentIntegral_of_star hU hstar i j hg1 hx]
  have hmap : MapsTo (fun t : ℝ => t • x) (Icc (0 : ℝ) 1) U :=
    fun t ht => Set.mem_preimage.mp (hstar (Set.mk_mem_prod ht hx))
  have hi1 : IntervalIntegrable (fun t : ℝ => t * kronecker3 i j * g (t • x)) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact (continuousOn_id.mul continuousOn_const).mul
      (hg1.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hmap)
  have hi2 : IntervalIntegrable
      (fun t : ℝ => t ^ 2 * x i * coordinatePartial g (t • x) j) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    exact ((continuousOn_id.pow 2).mul continuousOn_const).mul
      (hh0.comp (continuous_id.smul continuous_const).continuousOn hmap)
  exact intervalIntegral.integral_add hi1 hi2

/-- **General Sublinear-Hessian `C²` Regularity of `rayMomentIntegral`:**
If `g ∈ C¹(ball 0 R) ∩ C²(ball 0 R \ {0})` satisfies
`‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial g y j) z‖ → 0` as `z → 0` (`z ≠ 0`) for every `j`,
then `rayMomentIntegral i g ∈ C²(ball 0 R)`. -/
theorem contDiffOn_two_rayMomentIntegral {R : ℝ} (hR : 0 < R) (i : Fin 3)
    {g : Euclidean 3 → ℝ}
    (hg1 : ContDiffOn ℝ 1 g (Metric.ball (0 : Euclidean 3) R))
    (hg2 : ContDiffOn ℝ 2 g (Metric.ball (0 : Euclidean 3) R \ {0}))
    (hsub : ∀ j : Fin 3,
      Filter.Tendsto (fun z => ‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial g y j) z‖)
        (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 2 (rayMomentIntegral i g) (Metric.ball (0 : Euclidean 3) R) :=
  contDiffOn_two_rayMomentIntegral_of_star Metric.isOpen_ball (Metric.mem_ball_self hR)
    prod_Icc_ball_subset_preimage i hg1 hg2 hsub

/-- **General Sublinear-Hessian `C²` Regularity of the Poincaré Vector Potential:**
Any `F ∈ C¹(ball 0 R) ∩ C²(ball 0 R \ {0})` satisfying
`‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial (fun w => F w m) y j) z‖ → 0` as `z → 0` (`z ≠ 0`)
has `poincareVectorPotential F ∈ C²(ball 0 R)`. -/
theorem contDiffOn_two_poincareVectorPotential {R : ℝ} (hR : 0 < R)
    {F : VectorField}
    (hF1 : ContDiffOn ℝ 1 F (Metric.ball (0 : Euclidean 3) R))
    (hF2 : ContDiffOn ℝ 2 F (Metric.ball (0 : Euclidean 3) R \ {0}))
    (hsub : ∀ m j : Fin 3,
      Filter.Tendsto
        (fun z => ‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial (fun w => F w m) y j) z‖)
        (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 2 (poincareVectorPotential F) (Metric.ball (0 : Euclidean 3) R) := by
  have hM : ∀ i m : Fin 3,
      ContDiffOn ℝ 2 (rayMomentIntegral i (fun y => F y m)) (Metric.ball (0 : Euclidean 3) R) :=
    fun i m => contDiffOn_two_rayMomentIntegral hR i
      (contDiffOn_map_coordinate hF1 m)
      (contDiffOn_map_coordinate hF2 m)
      (hsub m)
  apply contDiffOn_vector_of_coordinates
  intro k
  cases k using fin3_cases
  · simpa [poincareVectorPotential, fin3Vec_zero] using (hM 2 1).sub (hM 1 2)
  · simpa [poincareVectorPotential, fin3Vec_one] using (hM 0 2).sub (hM 2 0)
  · simpa [poincareVectorPotential, fin3Vec_two] using (hM 1 0).sub (hM 0 1)

/-- Any `C²` curl potential on an open set `E` immediately yields `SymmetricCurlSystem E F`. -/
theorem symmetricCurlSystem_of_c2_vectorPotential {E : Set (Euclidean 3)}
    (hE : IsOpen E) {F G : VectorField}
    (hF : ContDiffOn ℝ 1 F E) (hdiv : EqOn (divergence F) 0 E)
    (hG : ContDiffOn ℝ 2 G E) (hcurl : EqOn (curl G) F E) :
    SymmetricCurlSystem E F := by
  have hcomp : CompatibleCurlRows E F :=
    ⟨fun i => gradient (fun x => G x i),
      fun i => contDiffOn_gradient hE (contDiffOn_map_coordinate hG i),
      fun i => curl_gradient_eq_zero hE (contDiffOn_map_coordinate hG i),
      hcurl⟩
  exact (symmetricCurlCorrection_iff_system hE hF hdiv).mp
    ((compatibleCurlRows_iff_symmetricCurlCorrection hF).mp hcomp)

/-- **Dead-Class Theorem for Single-Point Sublinear-Hessian Candidates:**
Every `C¹` divergence-free field `F` on `ball 0 R` (`0 < R`) that is `C²` on `ball 0 R \ {0}`
with `‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial (fun w => F w m) y j) z‖ → 0` as `z → 0`
satisfies `SymmetricCurlSystem (ball 0 R) F`. In particular, no radial-logarithmic ansatz
`F(x) = ψ(‖x‖) V(x / ‖x‖) + W(x)` with smooth `V` and sublinear Hessian can disprove Rudin 10.43. -/
theorem symmetricCurlSystem_of_sublinear_second_deriv {R : ℝ} (hR : 0 < R)
    {F : VectorField}
    (hF1 : ContDiffOn ℝ 1 F (Metric.ball (0 : Euclidean 3) R))
    (hdiv : EqOn (divergence F) 0 (Metric.ball (0 : Euclidean 3) R))
    (hF2 : ContDiffOn ℝ 2 F (Metric.ball (0 : Euclidean 3) R \ {0}))
    (hsub : ∀ m j : Fin 3,
      Filter.Tendsto
        (fun z => ‖z‖ * ‖fderiv ℝ (fun y => coordinatePartial (fun w => F w m) y j) z‖)
        (𝓝[≠] 0) (𝓝 0)) :
    SymmetricCurlSystem (Metric.ball (0 : Euclidean 3) R) F :=
  symmetricCurlSystem_of_c2_vectorPotential Metric.isOpen_ball hF1 hdiv
    (contDiffOn_two_poincareVectorPotential hR hF1 hF2 hsub)
    (curl_poincareVectorPotential hF1 hdiv)

private def fin2Vec (a b : ℝ) : Fin 2 → ℝ :=
  fun i => match i.1 with
    | 0 => a
    | _ => b

@[simp] private lemma fin2Vec_zero (a b : ℝ) : fin2Vec a b 0 = a := rfl
@[simp] private lemma fin2Vec_one (a b : ℝ) : fin2Vec a b 1 = b := rfl

/-- Planar point `(x, y)` in `Euclidean 2`. -/
def planarPt (x y : ℝ) : Euclidean 2 :=
  coordEquivEuclidean 2 (fin2Vec x y)

/-- Iterated planar `x`-partial `∂_x` on `Euclidean 2`. -/
def planarDx (f : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  coordinatePartial f p 0

/-- Iterated planar `y`-partial `∂_y` on `Euclidean 2`. -/
def planarDy (f : Euclidean 2 → ℝ) (p : Euclidean 2) : ℝ :=
  coordinatePartial f p 1

private lemma hasDerivAt_planarPt_x {f : Euclidean 2 → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun s : ℝ => f (planarPt s y)) (planarDx f (planarPt x y)) x := by
  have hpt : HasDerivAt (fun s : ℝ => planarPt s y) (coordinateVector 2 0) x := by
    have hrew : (fun s : ℝ => planarPt s y) =
        fun s : ℝ => planarPt 0 y + s • coordinateVector 2 0 := by
      funext s; ext i; fin_cases i <;>
        simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    rw [hrew]
    simpa [one_smul] using
      ((hasDerivAt_id x).smul_const (coordinateVector 2 0)).const_add (planarPt 0 y)
  have hcomp := (hf (planarPt x y)).hasFDerivAt.comp_hasDerivAt x hpt
  rwa [planarDx, coordinatePartial_eq_fderiv (hf (planarPt x y))]

private lemma hasDerivAt_planarPt_y {f : Euclidean 2 → ℝ} (hf : Differentiable ℝ f) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => f (planarPt x t)) (planarDy f (planarPt x y)) y := by
  have hpt : HasDerivAt (fun t : ℝ => planarPt x t) (coordinateVector 2 1) y := by
    have hrew : (fun t : ℝ => planarPt x t) =
        fun t : ℝ => planarPt x 0 + t • coordinateVector 2 1 := by
      funext t; ext i; fin_cases i <;>
        simp [planarPt, coordinateVector, EuclideanSpace.basisFun_apply]
    rw [hrew]
    simpa [one_smul] using
      ((hasDerivAt_id y).smul_const (coordinateVector 2 1)).const_add (planarPt x 0)
  have hcomp := (hf (planarPt x y)).hasFDerivAt.comp_hasDerivAt y hpt
  rwa [planarDy, coordinatePartial_eq_fderiv (hf (planarPt x y))]

private lemma contDiff_planarDx {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) :
    ContDiff ℝ (r : ℕ) (planarDx f) :=
  contDiffOn_univ.mp (contDiffOn_coordinatePartial (r := r) isOpen_univ hf.contDiffOn 0)

private lemma contDiff_planarDy {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) :
    ContDiff ℝ (r : ℕ) (planarDy f) :=
  contDiffOn_univ.mp (contDiffOn_coordinatePartial (r := r) isOpen_univ hf.contDiffOn 1)

private lemma planarDx_planarDy_comm {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 2 : ℕ) f) (q : Euclidean 2) :
    planarDx (planarDy f) q = planarDy (planarDx f) q :=
  coordinatePartial_commute isOpen_univ
    (hf.contDiffOn.of_le (by norm_cast; omega)) (mem_univ q) 1 0

private lemma planarDivergence_eq_planarDx_add_planarDy
    (V : PlanarVectorField) (q : Euclidean 2) :
    planarDivergence V q =
      planarDx (fun p => V p 0) q + planarDy (fun p => V p 1) q := rfl

attribute [irreducible] planarDx planarDy

private lemma diff_of_contDiff_succ {r : ℕ} {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ (r + 1 : ℕ) f) : Differentiable ℝ f :=
  hf.differentiable (by norm_cast)

private lemma cont_planarPt_uncurry {f : Euclidean 2 → ℝ} (hf : Continuous f) :
    Continuous (Function.uncurry fun x y : ℝ => f (planarPt x y)) := by
  have hp : Continuous (fun q : ℝ × ℝ => planarPt q.1 q.2) := by
    have hv : Continuous (fun q : ℝ × ℝ => fin2Vec q.1 q.2) :=
      continuous_pi fun i => by
        fin_cases i
        · exact continuous_fst
        · exact continuous_snd
    exact (coordEquivEuclidean 2).continuous.comp hv
  exact hf.comp hp

private lemma cont_planarPt_mul {f g : Euclidean 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Function.uncurry fun x y : ℝ => f (planarPt x y) * g (planarPt x y)) :=
  cont_planarPt_uncurry (hf.mul hg)

private lemma planar_prod_integrableOn {a b c d : ℝ} {G : ℝ → ℝ → ℝ}
    (hG : Continuous (Function.uncurry G)) :
    IntegrableOn (Function.uncurry G) (uIoc a b ×ˢ uIoc c d) :=
  (hG.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
    (Set.prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

private lemma ibp_1d_zero_boundary {a b : ℝ} {u v u' v' : ℝ → ℝ}
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

private lemma planar_ibp_piece1 {a b c d : ℝ}
    {v₀ w : Euclidean 2 → ℝ} (hV0 : ContDiff ℝ (2 : ℕ) v₀) (hw : ContDiff ℝ (5 : ℕ) w)
    (hx_bdry : ∀ y : ℝ,
      planarDy (planarDy (planarDx (planarDx w))) (planarPt a y) = 0 ∧
      planarDy (planarDy (planarDx (planarDx w))) (planarPt b y) = 0)
    (hy_bdry : ∀ x : ℝ,
      planarDy (planarDx (planarDx (planarDx w))) (planarPt x c) = 0 ∧
      planarDy (planarDx (planarDx (planarDx w))) (planarPt x d) = 0 ∧
      planarDx (planarDx (planarDx w)) (planarPt x c) = 0 ∧
      planarDx (planarDx (planarDx w)) (planarPt x d) = 0) :
    (∫ y in c..d, ∫ x in a..b,
      planarDx v₀ (planarPt x y) *
        planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
    -(∫ y in c..d, ∫ x in a..b,
      planarDy (planarDy v₀) (planarPt x y) *
        planarDx (planarDx (planarDx w)) (planarPt x y)) := by
  have hw_x1 : ContDiff ℝ (4 : ℕ) (planarDx w) := contDiff_planarDx (r := 4) hw
  have hw_x2 : ContDiff ℝ (3 : ℕ) (planarDx (planarDx w)) := contDiff_planarDx (r := 3) hw_x1
  have hw_x3 : ContDiff ℝ (2 : ℕ) (planarDx (planarDx (planarDx w))) :=
    contDiff_planarDx (r := 2) hw_x2
  have hw_x3y1 : ContDiff ℝ (1 : ℕ) (planarDy (planarDx (planarDx (planarDx w)))) :=
    contDiff_planarDy (r := 1) hw_x3
  have hw_x3y2 : ContDiff ℝ (0 : ℕ) (planarDy (planarDy (planarDx (planarDx (planarDx w))))) :=
    contDiff_planarDy (r := 0) hw_x3y1
  have hw_x2y1 : ContDiff ℝ (2 : ℕ) (planarDy (planarDx (planarDx w))) :=
    contDiff_planarDy (r := 2) hw_x2
  have hw_x2y2 : ContDiff ℝ (1 : ℕ) (planarDy (planarDy (planarDx (planarDx w)))) :=
    contDiff_planarDy (r := 1) hw_x2y1
  have hv₀_y1 : ContDiff ℝ (1 : ℕ) (planarDy v₀) := contDiff_planarDy (r := 1) hV0
  have hv₀_y2 : ContDiff ℝ (0 : ℕ) (planarDy (planarDy v₀)) := contDiff_planarDy (r := 0) hv₀_y1
  have hv₀_x1 : ContDiff ℝ (1 : ℕ) (planarDx v₀) := contDiff_planarDx (r := 1) hV0
  have heq_x2y2_dx : planarDx (planarDy (planarDy (planarDx (planarDx w)))) =
      planarDy (planarDy (planarDx (planarDx (planarDx w)))) := by
    funext q
    rw [planarDx_planarDy_comm (r := 0) hw_x2y1 q]
    have hinner : planarDx (planarDy (planarDx (planarDx w))) =
        planarDy (planarDx (planarDx (planarDx w))) :=
      funext fun p => planarDx_planarDy_comm (r := 1) hw_x2 p
    rw [hinner]
  have hibp_x : ∀ y : ℝ,
      (∫ x in a..b,
        planarDx v₀ (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
      -(∫ x in a..b,
        v₀ (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx (planarDx w)))) (planarPt x y)) := by
    intro y
    rw [← heq_x2y2_dx]
    exact ibp_1d_zero_boundary
      (fun x _ => hasDerivAt_planarPt_x (diff_of_contDiff_succ (r := 1) hV0) x y)
      (fun x _ => hasDerivAt_planarPt_x (diff_of_contDiff_succ (r := 0) hw_x2y2) x y)
      ((cont_planarPt_uncurry hV0.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hw_x2y2.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hv₀_x1.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry (heq_x2y2_dx.symm ▸ hw_x3y2.continuous)).comp
        (continuous_id.prodMk continuous_const))
      (hx_bdry y).1 (hx_bdry y).2
  simp_rw [hibp_x, intervalIntegral.integral_neg]
  congr 1
  rw [← MeasureTheory.intervalIntegral_intervalIntegral_swap
    (planar_prod_integrableOn (cont_planarPt_mul hV0.continuous hw_x3y2.continuous))]
  have hibp_y2 : ∀ x : ℝ,
      (∫ y in c..d,
        v₀ (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx (planarDx w)))) (planarPt x y)) =
      ∫ y in c..d,
        planarDy (planarDy v₀) (planarPt x y) *
          planarDx (planarDx (planarDx w)) (planarPt x y) := by
    intro x
    have h1 := ibp_1d_zero_boundary
      (u := fun y => v₀ (planarPt x y))
      (v := fun y => planarDy (planarDx (planarDx (planarDx w))) (planarPt x y))
      (u' := fun y => planarDy v₀ (planarPt x y))
      (v' := fun y => planarDy (planarDy (planarDx (planarDx (planarDx w)))) (planarPt x y))
      (fun y _ => hasDerivAt_planarPt_y (diff_of_contDiff_succ (r := 1) hV0) x y)
      (fun y _ => hasDerivAt_planarPt_y (diff_of_contDiff_succ (r := 0) hw_x3y1) x y)
      ((cont_planarPt_uncurry hV0.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hw_x3y1.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hv₀_y1.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hw_x3y2.continuous).comp (continuous_const.prodMk continuous_id))
      (hy_bdry x).1 (hy_bdry x).2.1
    have h2 := ibp_1d_zero_boundary
      (fun y _ => hasDerivAt_planarPt_y (diff_of_contDiff_succ (r := 0) hv₀_y1) x y)
      (fun y _ => hasDerivAt_planarPt_y (diff_of_contDiff_succ (r := 1) hw_x3) x y)
      ((cont_planarPt_uncurry hv₀_y1.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hw_x3.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hv₀_y2.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hw_x3y1.continuous).comp (continuous_const.prodMk continuous_id))
      (hy_bdry x).2.2.1 (hy_bdry x).2.2.2
    have hc1 : (∫ y in c..d,
        v₀ (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx (planarDx w)))) (planarPt x y)) =
        ∫ y in c..d,
          planarDy (planarDy (planarDx (planarDx (planarDx w)))) (planarPt x y) *
            v₀ (planarPt x y) :=
      intervalIntegral.integral_congr fun _ _ => mul_comm _ _
    have hc2 : (∫ y in c..d,
        planarDy v₀ (planarPt x y) *
          planarDy (planarDx (planarDx (planarDx w))) (planarPt x y)) =
        ∫ y in c..d,
          planarDy (planarDx (planarDx (planarDx w))) (planarPt x y) *
            planarDy v₀ (planarPt x y) :=
      intervalIntegral.integral_congr fun _ _ => mul_comm _ _
    linarith
  simp_rw [hibp_y2]
  exact MeasureTheory.intervalIntegral_intervalIntegral_swap
    (planar_prod_integrableOn (cont_planarPt_mul hv₀_y2.continuous hw_x3.continuous))

private lemma planar_ibp_piece2 {a b c d : ℝ}
    {v₁ w : Euclidean 2 → ℝ} (hV1 : ContDiff ℝ (2 : ℕ) v₁) (hw : ContDiff ℝ (5 : ℕ) w)
    (hx_bdry : ∀ y : ℝ,
      planarDy (planarDy (planarDy w)) (planarPt a y) = 0 ∧
      planarDy (planarDy (planarDy w)) (planarPt b y) = 0 ∧
      planarDx (planarDy (planarDy (planarDy w))) (planarPt a y) = 0 ∧
      planarDx (planarDy (planarDy (planarDy w))) (planarPt b y) = 0)
    (hy_bdry : ∀ x : ℝ,
      planarDy (planarDy (planarDx (planarDx w))) (planarPt x c) = 0 ∧
      planarDy (planarDy (planarDx (planarDx w))) (planarPt x d) = 0) :
    (∫ y in c..d, ∫ x in a..b,
      planarDy v₁ (planarPt x y) *
        planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
    -(∫ y in c..d, ∫ x in a..b,
      planarDx (planarDx v₁) (planarPt x y) *
        planarDy (planarDy (planarDy w)) (planarPt x y)) := by
  have hw_x1 : ContDiff ℝ (4 : ℕ) (planarDx w) := contDiff_planarDx (r := 4) hw
  have hw_x2 : ContDiff ℝ (3 : ℕ) (planarDx (planarDx w)) := contDiff_planarDx (r := 3) hw_x1
  have hw_x2y1 : ContDiff ℝ (2 : ℕ) (planarDy (planarDx (planarDx w))) :=
    contDiff_planarDy (r := 2) hw_x2
  have hw_x2y2 : ContDiff ℝ (1 : ℕ) (planarDy (planarDy (planarDx (planarDx w)))) :=
    contDiff_planarDy (r := 1) hw_x2y1
  have hw_x2y3 : ContDiff ℝ (0 : ℕ) (planarDy (planarDy (planarDy (planarDx (planarDx w))))) :=
    contDiff_planarDy (r := 0) hw_x2y2
  have hw_y1 : ContDiff ℝ (4 : ℕ) (planarDy w) := contDiff_planarDy (r := 4) hw
  have hw_y2 : ContDiff ℝ (3 : ℕ) (planarDy (planarDy w)) := contDiff_planarDy (r := 3) hw_y1
  have hw_y3 : ContDiff ℝ (2 : ℕ) (planarDy (planarDy (planarDy w))) :=
    contDiff_planarDy (r := 2) hw_y2
  have hw_y3x1 : ContDiff ℝ (1 : ℕ) (planarDx (planarDy (planarDy (planarDy w)))) :=
    contDiff_planarDx (r := 1) hw_y3
  have hw_y3x2 : ContDiff ℝ (0 : ℕ) (planarDx (planarDx (planarDy (planarDy (planarDy w))))) :=
    contDiff_planarDx (r := 0) hw_y3x1
  have hv₁_y1 : ContDiff ℝ (1 : ℕ) (planarDy v₁) := contDiff_planarDy (r := 1) hV1
  have hv₁_x1 : ContDiff ℝ (1 : ℕ) (planarDx v₁) := contDiff_planarDx (r := 1) hV1
  have hv₁_x2 : ContDiff ℝ (0 : ℕ) (planarDx (planarDx v₁)) := contDiff_planarDx (r := 0) hv₁_x1
  have heq_x2y3 : planarDy (planarDy (planarDy (planarDx (planarDx w)))) =
      planarDx (planarDx (planarDy (planarDy (planarDy w)))) := by
    have s1 : planarDy (planarDx (planarDx w)) = planarDx (planarDy (planarDx w)) :=
      funext fun p => (planarDx_planarDy_comm (r := 2) hw_x1 p).symm
    have s2 : planarDy (planarDx w) = planarDx (planarDy w) :=
      funext fun p => (planarDx_planarDy_comm (r := 3) hw p).symm
    rw [s2] at s1
    have s3 : planarDy (planarDy (planarDx (planarDx w))) =
        planarDx (planarDx (planarDy (planarDy w))) := by
      rw [s1]
      funext p
      rw [(planarDx_planarDy_comm (r := 1) (contDiff_planarDx (r := 3) hw_y1) p).symm]
      have hmid : planarDy (planarDx (planarDy w)) = planarDx (planarDy (planarDy w)) :=
        funext fun r => (planarDx_planarDy_comm (r := 2) hw_y1 r).symm
      rw [hmid]
    rw [s3]
    funext p
    rw [(planarDx_planarDy_comm (r := 0) (contDiff_planarDx (r := 2) hw_y2) p).symm]
    have hmid2 : planarDy (planarDx (planarDy (planarDy w))) =
        planarDx (planarDy (planarDy (planarDy w))) :=
      funext fun r => (planarDx_planarDy_comm (r := 1) hw_y2 r).symm
    rw [hmid2]
  rw [← MeasureTheory.intervalIntegral_intervalIntegral_swap
    (planar_prod_integrableOn (cont_planarPt_mul hv₁_y1.continuous hw_x2y2.continuous))]
  have hibp_y : ∀ x : ℝ,
      (∫ y in c..d,
        planarDy v₁ (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
      -(∫ y in c..d,
        v₁ (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (planarDy w)))) (planarPt x y)) := by
    intro x
    rw [← heq_x2y3]
    exact ibp_1d_zero_boundary
      (fun y _ => hasDerivAt_planarPt_y (diff_of_contDiff_succ (r := 1) hV1) x y)
      (fun y _ => hasDerivAt_planarPt_y (diff_of_contDiff_succ (r := 0) hw_x2y2) x y)
      ((cont_planarPt_uncurry hV1.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hw_x2y2.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hv₁_y1.continuous).comp (continuous_const.prodMk continuous_id))
      ((cont_planarPt_uncurry hw_x2y3.continuous).comp (continuous_const.prodMk continuous_id))
      (hy_bdry x).1 (hy_bdry x).2
  simp_rw [hibp_y, intervalIntegral.integral_neg]
  congr 1
  rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
    (planar_prod_integrableOn (cont_planarPt_mul hV1.continuous hw_y3x2.continuous))]
  have hibp_x2 : ∀ y : ℝ,
      (∫ x in a..b,
        v₁ (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (planarDy w)))) (planarPt x y)) =
      ∫ x in a..b,
        planarDx (planarDx v₁) (planarPt x y) *
          planarDy (planarDy (planarDy w)) (planarPt x y) := by
    intro y
    have h1 := ibp_1d_zero_boundary
      (u := fun x => v₁ (planarPt x y))
      (v := fun x => planarDx (planarDy (planarDy (planarDy w))) (planarPt x y))
      (u' := fun x => planarDx v₁ (planarPt x y))
      (v' := fun x => planarDx (planarDx (planarDy (planarDy (planarDy w)))) (planarPt x y))
      (fun x _ => hasDerivAt_planarPt_x (diff_of_contDiff_succ (r := 1) hV1) x y)
      (fun x _ => hasDerivAt_planarPt_x (diff_of_contDiff_succ (r := 0) hw_y3x1) x y)
      ((cont_planarPt_uncurry hV1.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hw_y3x1.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hv₁_x1.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hw_y3x2.continuous).comp (continuous_id.prodMk continuous_const))
      (hx_bdry y).2.2.1 (hx_bdry y).2.2.2
    have h2 := ibp_1d_zero_boundary
      (fun x _ => hasDerivAt_planarPt_x (diff_of_contDiff_succ (r := 0) hv₁_x1) x y)
      (fun x _ => hasDerivAt_planarPt_x (diff_of_contDiff_succ (r := 1) hw_y3) x y)
      ((cont_planarPt_uncurry hv₁_x1.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hw_y3.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hv₁_x2.continuous).comp (continuous_id.prodMk continuous_const))
      ((cont_planarPt_uncurry hw_y3x1.continuous).comp (continuous_id.prodMk continuous_const))
      (hx_bdry y).1 (hx_bdry y).2.1
    have hc1 : (∫ x in a..b,
        v₁ (planarPt x y) *
          planarDx (planarDx (planarDy (planarDy (planarDy w)))) (planarPt x y)) =
        ∫ x in a..b,
          planarDx (planarDx (planarDy (planarDy (planarDy w)))) (planarPt x y) *
            v₁ (planarPt x y) :=
      intervalIntegral.integral_congr fun _ _ => mul_comm _ _
    have hc2 : (∫ x in a..b,
        planarDx v₁ (planarPt x y) *
          planarDx (planarDy (planarDy (planarDy w))) (planarPt x y)) =
        ∫ x in a..b,
          planarDx (planarDy (planarDy (planarDy w))) (planarPt x y) *
            planarDx v₁ (planarPt x y) :=
      intervalIntegral.integral_congr fun _ _ => mul_comm _ _
    linarith
  simp_rw [hibp_x2]

/-- **Gauge-Invariant Fourth-Order Planar Duality Identity (`C²` Potentials):**
For *any* `C²` planar vector field `V` (with NO `C³` hypothesis on `V`) and any `C⁵` test function
`w : Euclidean 2 → ℝ` whose relevant mixed partials vanish on the boundary of `[a, b] × [c, d]`,
the fourth-order pairing of `planarDivergence V` against `∂_x² ∂_y² w` satisfies
`∫_c^d ∫_a^b (planarDivergence V)(x,y) (∂_x² ∂_y² w)(x,y) dx dy`
`  = -∫_c^d ∫_a^b ((∂_y² V₀)(x,y)(∂_x³ w)(x,y) + (∂_x² V₁)(x,y)(∂_y³ w)(x,y)) dx dy`. -/
theorem planar_c2_div_fourth_order_duality
    {a b c d : ℝ} {V : PlanarVectorField} (hV : ContDiff ℝ (2 : ℕ) V)
    {w : Euclidean 2 → ℝ} (hw : ContDiff ℝ (5 : ℕ) w)
    (hx_bdry : ∀ y : ℝ,
      planarDy (planarDy (planarDx (planarDx w))) (planarPt a y) = 0 ∧
      planarDy (planarDy (planarDx (planarDx w))) (planarPt b y) = 0 ∧
      planarDy (planarDy (planarDy w)) (planarPt a y) = 0 ∧
      planarDy (planarDy (planarDy w)) (planarPt b y) = 0 ∧
      planarDx (planarDy (planarDy (planarDy w))) (planarPt a y) = 0 ∧
      planarDx (planarDy (planarDy (planarDy w))) (planarPt b y) = 0)
    (hy_bdry : ∀ x : ℝ,
      planarDy (planarDy (planarDx (planarDx w))) (planarPt x c) = 0 ∧
      planarDy (planarDy (planarDx (planarDx w))) (planarPt x d) = 0 ∧
      planarDy (planarDx (planarDx (planarDx w))) (planarPt x c) = 0 ∧
      planarDy (planarDx (planarDx (planarDx w))) (planarPt x d) = 0 ∧
      planarDx (planarDx (planarDx w)) (planarPt x c) = 0 ∧
      planarDx (planarDx (planarDx w)) (planarPt x d) = 0) :
    (∫ y in c..d, ∫ x in a..b,
      planarDivergence V (planarPt x y) *
        planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
    -(∫ y in c..d, ∫ x in a..b,
      (planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
          planarDx (planarDx (planarDx w)) (planarPt x y) +
        planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
          planarDy (planarDy (planarDy w)) (planarPt x y))) := by
  have hV0 : ContDiff ℝ (2 : ℕ) (fun q => V q 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hV1 : ContDiff ℝ (2 : ℕ) (fun q => V q 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hv₀_x1 : ContDiff ℝ (1 : ℕ) (planarDx (fun q => V q 0)) := contDiff_planarDx (r := 1) hV0
  have hv₁_y1 : ContDiff ℝ (1 : ℕ) (planarDy (fun q => V q 1)) := contDiff_planarDy (r := 1) hV1
  have hv₀_y2 : ContDiff ℝ (0 : ℕ) (planarDy (planarDy (fun q => V q 0))) :=
    contDiff_planarDy (r := 0) (contDiff_planarDy (r := 1) hV0)
  have hv₁_x2 : ContDiff ℝ (0 : ℕ) (planarDx (planarDx (fun q => V q 1))) :=
    contDiff_planarDx (r := 0) (contDiff_planarDx (r := 1) hV1)
  have hw_x1 : ContDiff ℝ (4 : ℕ) (planarDx w) := contDiff_planarDx (r := 4) hw
  have hw_x2 : ContDiff ℝ (3 : ℕ) (planarDx (planarDx w)) := contDiff_planarDx (r := 3) hw_x1
  have hw_x3 : ContDiff ℝ (2 : ℕ) (planarDx (planarDx (planarDx w))) :=
    contDiff_planarDx (r := 2) hw_x2
  have hw_x2y1 : ContDiff ℝ (2 : ℕ) (planarDy (planarDx (planarDx w))) :=
    contDiff_planarDy (r := 2) hw_x2
  have hw_x2y2 : ContDiff ℝ (1 : ℕ) (planarDy (planarDy (planarDx (planarDx w)))) :=
    contDiff_planarDy (r := 1) hw_x2y1
  have hw_y1 : ContDiff ℝ (4 : ℕ) (planarDy w) := contDiff_planarDy (r := 4) hw
  have hw_y2 : ContDiff ℝ (3 : ℕ) (planarDy (planarDy w)) := contDiff_planarDy (r := 3) hw_y1
  have hw_y3 : ContDiff ℝ (2 : ℕ) (planarDy (planarDy (planarDy w))) :=
    contDiff_planarDy (r := 2) hw_y2
  have hpiece1 := planar_ibp_piece1 (a := a) (b := b) (c := c) (d := d) hV0 hw
    (fun y => ⟨(hx_bdry y).1, (hx_bdry y).2.1⟩)
    (fun x => ⟨(hy_bdry x).2.2.1, (hy_bdry x).2.2.2.1,
      (hy_bdry x).2.2.2.2.1, (hy_bdry x).2.2.2.2.2⟩)
  have hpiece2 := planar_ibp_piece2 (a := a) (b := b) (c := c) (d := d) hV1 hw
    (fun y => ⟨(hx_bdry y).2.2.1, (hx_bdry y).2.2.2.1,
      (hx_bdry y).2.2.2.2.1, (hx_bdry y).2.2.2.2.2⟩)
    (fun x => ⟨(hy_bdry x).1, (hy_bdry x).2.1⟩)
  have hc_int : ∀ F : ℝ → ℝ → ℝ, Continuous (Function.uncurry F) →
      Continuous (fun y : ℝ => ∫ x in a..b, F x y) := fun F hF =>
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y x => F x y) (hF.comp continuous_swap) a b
  have hsplit_lhs :
      (∫ y in c..d, ∫ x in a..b,
        planarDivergence V (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
      (∫ y in c..d, ∫ x in a..b,
        planarDx (fun q => V q 0) (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) +
      (∫ y in c..d, ∫ x in a..b,
        planarDy (fun q => V q 1) (planarPt x y) *
          planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) := by
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          planarDivergence V (planarPt x y) *
            planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
        (∫ x in a..b,
          planarDx (fun q => V q 0) (planarPt x y) *
            planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) +
        (∫ x in a..b,
          planarDy (fun q => V q 1) (planarPt x y) *
            planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) := by
      intro y
      have hrew : (fun x : ℝ =>
          planarDivergence V (planarPt x y) *
            planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)) =
          fun x : ℝ =>
            planarDx (fun q => V q 0) (planarPt x y) *
              planarDy (planarDy (planarDx (planarDx w))) (planarPt x y) +
            planarDy (fun q => V q 1) (planarPt x y) *
              planarDy (planarDy (planarDx (planarDx w))) (planarPt x y) := by
        funext x; rw [planarDivergence_eq_planarDx_add_planarDy, add_mul]
      rw [hrew]
      exact intervalIntegral.integral_add
        (((cont_planarPt_uncurry (hv₀_x1.continuous.mul hw_x2y2.continuous)).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
        (((cont_planarPt_uncurry (hv₁_y1.continuous.mul hw_x2y2.continuous)).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    simp_rw [hinner]
    exact intervalIntegral.integral_add
      ((hc_int _ (cont_planarPt_uncurry
        (hv₀_x1.continuous.mul hw_x2y2.continuous))).intervalIntegrable c d)
      ((hc_int _ (cont_planarPt_uncurry
        (hv₁_y1.continuous.mul hw_x2y2.continuous))).intervalIntegrable c d)
  have hsplit_rhs :
      (∫ y in c..d, ∫ x in a..b,
        (planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
            planarDx (planarDx (planarDx w)) (planarPt x y) +
          planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
            planarDy (planarDy (planarDy w)) (planarPt x y))) =
      (∫ y in c..d, ∫ x in a..b,
        planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
          planarDx (planarDx (planarDx w)) (planarPt x y)) +
      (∫ y in c..d, ∫ x in a..b,
        planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
          planarDy (planarDy (planarDy w)) (planarPt x y)) := by
    have hinner : ∀ y : ℝ,
        (∫ x in a..b,
          (planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
              planarDx (planarDx (planarDx w)) (planarPt x y) +
            planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
              planarDy (planarDy (planarDy w)) (planarPt x y))) =
        (∫ x in a..b,
          planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
            planarDx (planarDx (planarDx w)) (planarPt x y)) +
        (∫ x in a..b,
          planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
            planarDy (planarDy (planarDy w)) (planarPt x y)) := fun y =>
      intervalIntegral.integral_add
        (((cont_planarPt_uncurry (hv₀_y2.continuous.mul hw_x3.continuous)).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
        (((cont_planarPt_uncurry (hv₁_x2.continuous.mul hw_y3.continuous)).comp
          (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    simp_rw [hinner]
    exact intervalIntegral.integral_add
      ((hc_int _ (cont_planarPt_uncurry
        (hv₀_y2.continuous.mul hw_x3.continuous))).intervalIntegrable c d)
      ((hc_int _ (cont_planarPt_uncurry
        (hv₁_x2.continuous.mul hw_y3.continuous))).intervalIntegrable c d)
  rw [hsplit_lhs, hpiece1, hpiece2, hsplit_rhs]
  ring

/-- **Gauge-Invariant Fourth-Order Planar `L∞–L¹` Duality Bound:**
If `V ∈ C²` has `|∂_y² V₀| ≤ M` and `|∂_x² V₁| ≤ M` on `[a, b] × [c, d]`, then for every `C⁵`
test function `w` satisfying the boundary conditions of `planar_c2_div_fourth_order_duality`,
`|∫_c^d ∫_a^b (planarDivergence V)(x,y) (∂_x² ∂_y² w)(x,y) dx dy|`
`  ≤ M * ∫_c^d ∫_a^b (|∂_x³ w(x,y)| + |∂_y³ w(x,y)|) dx dy`.
Hence any sequence of test functions `w_k` whose ratio `|∫ h ∂_x²∂_y² w_k| / ∫(|∂_x³ w_k| + |∂_y³ w_k|)`
diverges rules out ALL `C²` solutions `V` of `planarDivergence V = h` simultaneously. -/
theorem planar_c2_div_fourth_order_bound
    {a b c d M : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {V : PlanarVectorField} (hV : ContDiff ℝ (2 : ℕ) V)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc c d,
      |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| ≤ M ∧
      |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| ≤ M)
    {w : Euclidean 2 → ℝ} (hw : ContDiff ℝ (5 : ℕ) w)
    (hx_bdry : ∀ y : ℝ,
      planarDy (planarDy (planarDx (planarDx w))) (planarPt a y) = 0 ∧
      planarDy (planarDy (planarDx (planarDx w))) (planarPt b y) = 0 ∧
      planarDy (planarDy (planarDy w)) (planarPt a y) = 0 ∧
      planarDy (planarDy (planarDy w)) (planarPt b y) = 0 ∧
      planarDx (planarDy (planarDy (planarDy w))) (planarPt a y) = 0 ∧
      planarDx (planarDy (planarDy (planarDy w))) (planarPt b y) = 0)
    (hy_bdry : ∀ x : ℝ,
      planarDy (planarDy (planarDx (planarDx w))) (planarPt x c) = 0 ∧
      planarDy (planarDy (planarDx (planarDx w))) (planarPt x d) = 0 ∧
      planarDy (planarDx (planarDx (planarDx w))) (planarPt x c) = 0 ∧
      planarDy (planarDx (planarDx (planarDx w))) (planarPt x d) = 0 ∧
      planarDx (planarDx (planarDx w)) (planarPt x c) = 0 ∧
      planarDx (planarDx (planarDx w)) (planarPt x d) = 0) :
    |∫ y in c..d, ∫ x in a..b,
      planarDivergence V (planarPt x y) *
        planarDy (planarDy (planarDx (planarDx w))) (planarPt x y)| ≤
    M * ∫ y in c..d, ∫ x in a..b,
      (|planarDx (planarDx (planarDx w)) (planarPt x y)| +
        |planarDy (planarDy (planarDy w)) (planarPt x y)|) := by
  rw [planar_c2_div_fourth_order_duality hV hw hx_bdry hy_bdry, abs_neg]
  have hV0 : ContDiff ℝ (2 : ℕ) (fun q => V q 0) :=
    (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hV1 : ContDiff ℝ (2 : ℕ) (fun q => V q 1) :=
    (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hV
  have hv₀_y2 : ContDiff ℝ (0 : ℕ) (planarDy (planarDy (fun q => V q 0))) :=
    contDiff_planarDy (r := 0) (contDiff_planarDy (r := 1) hV0)
  have hv₁_x2 : ContDiff ℝ (0 : ℕ) (planarDx (planarDx (fun q => V q 1))) :=
    contDiff_planarDx (r := 0) (contDiff_planarDx (r := 1) hV1)
  have hw_x3 : ContDiff ℝ (2 : ℕ) (planarDx (planarDx (planarDx w))) :=
    contDiff_planarDx (r := 2) (contDiff_planarDx (r := 3) (contDiff_planarDx (r := 4) hw))
  have hw_y3 : ContDiff ℝ (2 : ℕ) (planarDy (planarDy (planarDy w))) :=
    contDiff_planarDy (r := 2) (contDiff_planarDy (r := 3) (contDiff_planarDy (r := 4) hw))
  let F : ℝ → ℝ → ℝ := fun x y =>
    planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
        planarDx (planarDx (planarDx w)) (planarPt x y) +
      planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
        planarDy (planarDy (planarDy w)) (planarPt x y)
  let W : ℝ → ℝ → ℝ := fun x y =>
    |planarDx (planarDx (planarDx w)) (planarPt x y)| +
      |planarDy (planarDy (planarDy w)) (planarPt x y)|
  have hcF : Continuous (Function.uncurry F) :=
    cont_planarPt_uncurry
      ((hv₀_y2.continuous.mul hw_x3.continuous).add
        (hv₁_x2.continuous.mul hw_y3.continuous))
  have hcW : Continuous (Function.uncurry W) :=
    cont_planarPt_uncurry (hw_x3.continuous.abs.add hw_y3.continuous.abs)
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
      obtain ⟨hb0, hb1⟩ := hbound x hx y hy
      calc
        |F x y|
            ≤ |planarDy (planarDy (fun q => V q 0)) (planarPt x y) *
                  planarDx (planarDx (planarDx w)) (planarPt x y)| +
                |planarDx (planarDx (fun q => V q 1)) (planarPt x y) *
                  planarDy (planarDy (planarDy w)) (planarPt x y)| := abs_add_le _ _
        _ = |planarDy (planarDy (fun q => V q 0)) (planarPt x y)| *
                |planarDx (planarDx (planarDx w)) (planarPt x y)| +
              |planarDx (planarDx (fun q => V q 1)) (planarPt x y)| *
                |planarDy (planarDy (planarDy w)) (planarPt x y)| := by
              rw [abs_mul, abs_mul]
        _ ≤ M * |planarDx (planarDx (planarDx w)) (planarPt x y)| +
              M * |planarDy (planarDy (planarDy w)) (planarPt x y)| := by
              gcongr
        _ = M * W x y := by dsimp [W]; ring
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

end Rudin.PMA.Chapter10

/-! Audit every declaration owned by this module, including private helpers and generated lemmas. -/
run_cmd do
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10.FtildeCZPrep
    #[`Rudin.PMA.Chapter10.integral_sphere_monomial,
      `Rudin.PMA.Chapter10.odd_stream_completion_cz_vanishes,
      `Rudin.PMA.Chapter10.ftilde_dipole_angular_identification,
      `Rudin.PMA.Chapter10.ftilde_angular_identification_a2,
      `Rudin.PMA.Chapter10.ftildeSymbolMean_nonzero_witness,
      `Rudin.PMA.Chapter10.ftildeBase_dipole_angular_eq_zero,
      `Rudin.PMA.Chapter10.ftildeBase_row0_dipole_020,
      `Rudin.PMA.Chapter10.korn_second_partial_identity,
      `Rudin.PMA.Chapter10.sym3_gauge_orthogonality,
      `Rudin.PMA.Chapter10.integral_ftildePsi_div_self,
      `Rudin.PMA.Chapter10.integral_ftildePsi_sq_div_self_bounds,
      `Rudin.PMA.Chapter10.l10_not_c1_of_log_log_symGrad,
      `Rudin.PMA.Chapter10.traceFree_sym3_cubic_harmonic,
      `Rudin.PMA.Chapter10.curl_poincareVectorPotential,
      `Rudin.PMA.Chapter10.contDiffOn_two_poincareVectorPotential,
      `Rudin.PMA.Chapter10.symmetricCurlSystem_of_sublinear_second_deriv,
      `Rudin.PMA.Chapter10.planar_c2_div_fourth_order_duality,
      `Rudin.PMA.Chapter10.planar_c2_div_fourth_order_bound]
