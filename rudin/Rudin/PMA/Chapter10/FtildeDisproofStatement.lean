/-
  Statement draft for rudin-lean issue #29 (SymmetricDerivativeLifting).
  PLACED 2026-10-31 ~17:53 PDT by the math orchestrator under Derek's
  2026-10-31 ~17:30 PDT standing-delegation clarification (routine
  pipeline placement + typecheck, not a new direction).
  STATUS: DRAFT WIP. The Stage 1 tensor, radial, and divergence-profile
  lemmas below are Lean-checked. The (A) witness lemma `ftilde_witness`
  still carries one `sorry` for its three analytic clauses; neither it nor
  its downstream consequences is a completed result. The pin manifest is
  frozen and no dependency pins are changed by this proof work.
  Source: desk draft v3 (sha256
  4392009bf437d79067c3509bcc268064cfce87043879170f042cf11990974978).
  The original statement is unchanged; proof lemmas and the domain part of
  the witness proof were added during Stage 1.
-/

-- Interval-integral notation arrives transitively via Integration.lean's
-- imports (this Mathlib rev has no Mathlib.MeasureTheory.Integral.IntervalIntegral
-- module file; the notation lives in IntervalIntegral/Basic.lean).
import Rudin.PMA.Chapter10.VectorFields
import Rudin.PMA.Chapter10.ExactnessTransport
import Rudin.PMA.Chapter10.Integration
import Rudin.PMA.Chapter10.Prerequisites
import Rudin.Research.PMA1043ProofAttack

namespace Rudin.PMA.Chapter10

open Set Function Metric
open scoped Topology BigOperators
noncomputable section

/-- The unit ball B ⊂ ℝ³: the convex domain of the #29 witness. -/
def ftildeBall : Set (Euclidean 3) := Metric.ball 0 1

/-- (V1, 15:23 run) The identity C2DomainEquivalence on B. Ambient extensions
    need not be inverse outside the domains (ExactnessTransport.lean
    comment, lines 18-19), so id/id is admitted; both C² fields are
    contDiffOn_id. Repo precedent: univIdentityEquivalence
    (PlanarVectorPotentialResearch.lean 175-184, private, for univ). -/
def ballIdentityEquivalence : C2DomainEquivalence ftildeBall ftildeBall where
  forward := id
  inverse := id
  forward_mapsTo := fun _ hx => hx
  inverse_mapsTo := fun _ hx => hx
  left_inverse := fun _ _ => rfl
  right_inverse := fun _ _ => rfl
  forward_c2 := contDiffOn_id
  inverse_c2 := contDiffOn_id

/-- Direction θ = x / ‖x‖ for x ≠ 0. -/
def ftildeDir (x : Euclidean 3) : Euclidean 3 := ‖x‖⁻¹ • x

/-- ψ(r) = 1 / |log r| for 0 < r < 1, ψ(0) = 0. (Manifest §1; ψ′ = ψ²/r.) -/
def ftildePsi (r : ℝ) : ℝ := if r = 0 then 0 else 1 / |Real.log r|

lemma ftildePsi_eq_neg_inv_log {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ftildePsi r = -(Real.log r)⁻¹ := by
  rw [ftildePsi, if_neg hr.ne', abs_of_neg (Real.log_neg hr hr1), one_div, inv_neg]

lemma hasDerivAt_ftildePsi {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt ftildePsi (ftildePsi r ^ 2 / r) r := by
  have hlog : Real.log r < 0 := Real.log_neg hr hr1
  have h := (Real.hasDerivAt_inv_log hr.ne' (ne_of_lt hr1) (by linarith)).neg
  have heq : ftildePsi =ᶠ[𝓝 r] fun x : ℝ => -(Real.log x)⁻¹ := by
    filter_upwards [Ioo_mem_nhds hr hr1] with x hx
    exact ftildePsi_eq_neg_inv_log hx.1 hx.2
  convert h.congr_of_eventuallyEq heq using 1
  rw [ftildePsi_eq_neg_inv_log hr hr1]
  field_simp [hr.ne', hlog.ne]

lemma tendsto_ftildePsi_nhdsNE_zero :
    Filter.Tendsto ftildePsi (𝓝[≠] 0) (𝓝 0) := by
  have hlog : Filter.Tendsto (fun r : ℝ => |Real.log r|) (𝓝[≠] 0) Filter.atTop :=
    Filter.tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsNE_zero
  apply hlog.inv_tendsto_atTop.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : r ≠ 0 := hr
  simp only [ftildePsi, if_neg hr0, one_div, Pi.inv_apply]

lemma continuousAt_ftildePsi_zero : ContinuousAt ftildePsi 0 := by
  rw [continuousAt_iff_punctured_nhds]
  simpa [ftildePsi] using tendsto_ftildePsi_nhdsNE_zero

/-- b(u) = u + u³/2 − u⁵/4 (0253 closed form); b′ alongside. -/
def ftildeB (u : ℝ) : ℝ := u + u ^ 3 / 2 - u ^ 5 / 4
def ftildeB' (u : ℝ) : ℝ := 1 + 3 * u ^ 2 / 2 - 5 * u ^ 4 / 4

/-- Coordinate helpers: θᵢ(x) for a direction θ. -/
def ftildeTh (i : Fin 3) (θ : Euclidean 3) : ℝ := θ i

/-- V rows, homogeneous degree 1 (manifest §1 + 14:53 §3 + V2, 15:23 run).
    First row (V2, exact): V₁(x) = r·θ₁⁶θ₂ = x₁⁶x₂/r⁶ for x ≠ 0.
    Transverse rows: potential compensation f₂, f₃ plus the case-A stream
    shift (c = θ₂⁴), all extended as homogeneous degree-1 rows. -/
def ftildeV₁ (x : Euclidean 3) : ℝ :=
  if x = 0 then 0 else ‖x‖ * (ftildeTh 0 (ftildeDir x)) ^ 6 * ftildeTh 1 (ftildeDir x)
def ftildeV₂ (x : Euclidean 3) : ℝ :=
  if x = 0 then 0 else
    let θ := ftildeDir x
    let u := ftildeTh 0 θ; let v := ftildeTh 1 θ; let w := ftildeTh 2 θ
    ‖x‖ * ((ftildeB u * (1 + v ^ 2) - u * v ^ 2 * ftildeB' u) + 2 * v ^ 4 * w)
def ftildeV₃ (x : Euclidean 3) : ℝ :=
  if x = 0 then 0 else
    let θ := ftildeDir x
    let u := ftildeTh 0 θ; let v := ftildeTh 1 θ; let w := ftildeTh 2 θ
    ‖x‖ * ((v * w * (ftildeB u - u * ftildeB' u)) + 2 * v ^ 3 * (2 - v ^ 2))

/-- The combined field V, assembled coordinate-wise. The exact vector
    constructor follows the repo's coordinate conventions at typecheck time. -/
def ftildeV : VectorField :=
  fun x => coordEquivEuclidean 3 ![ftildeV₁ x, ftildeV₂ x, ftildeV₃ x]

/-- F = ψV on the punctured ball, F(0) = 0. -/
def ftildeF : VectorField :=
  fun x => if x = 0 then 0 else ftildePsi ‖x‖ • ftildeV x

/-- Derivative profiles D_{a,n}: the Jacobian profile of the homogeneous
    rows, as a function of θ (degree-0, hence well-defined on the sphere).
    CLOSED 16:53 run: fderiv D == 0653 code sphere-gradient D on the sphere
    (homogeneity identity + FD check, REPORT.md). -/
def ftildeD (a n : Fin 3) (θ : Euclidean 3) : ℝ :=
  fderiv ℝ (fun x => (ftildeV x) n) θ (coordinateVector 3 a)

/-- The nonzero branches of the three homogeneous rows. -/
def core₁ (x : Euclidean 3) : ℝ :=
  ‖x‖ * (ftildeTh 0 (ftildeDir x)) ^ 6 * ftildeTh 1 (ftildeDir x)

def core₂ (x : Euclidean 3) : ℝ :=
  let θ := ftildeDir x
  let u := ftildeTh 0 θ; let v := ftildeTh 1 θ; let w := ftildeTh 2 θ
  ‖x‖ * ((ftildeB u * (1 + v ^ 2) - u * v ^ 2 * ftildeB' u) + 2 * v ^ 4 * w)

def core₃ (x : Euclidean 3) : ℝ :=
  let θ := ftildeDir x
  let u := ftildeTh 0 θ; let v := ftildeTh 1 θ; let w := ftildeTh 2 θ
  ‖x‖ * ((v * w * (ftildeB u - u * ftildeB' u)) + 2 * v ^ 3 * (2 - v ^ 2))

lemma ftildeV₁_eq_core {x : Euclidean 3} (hx : x ≠ 0) : ftildeV₁ x = core₁ x := by
  simp only [ftildeV₁, core₁, if_neg hx]

lemma ftildeV₂_eq_core {x : Euclidean 3} (hx : x ≠ 0) : ftildeV₂ x = core₂ x := by
  simp only [ftildeV₂, core₂, if_neg hx]

lemma ftildeV₃_eq_core {x : Euclidean 3} (hx : x ≠ 0) : ftildeV₃ x = core₃ x := by
  simp only [ftildeV₃, core₃, if_neg hx]

lemma differentiableAt_core₁ {x : Euclidean 3} (hx : x ≠ 0) : DifferentiableAt ℝ core₁ x := by
  have hnorm : DifferentiableAt ℝ (fun y : Euclidean 3 => ‖y‖) x :=
    (differentiableAt_id (x := x)).norm ℝ hx
  unfold core₁ ftildeDir ftildeTh
  fun_prop (disch := aesop)

lemma differentiableAt_core₂ {x : Euclidean 3} (hx : x ≠ 0) : DifferentiableAt ℝ core₂ x := by
  have hnorm : DifferentiableAt ℝ (fun y : Euclidean 3 => ‖y‖) x :=
    (differentiableAt_id (x := x)).norm ℝ hx
  unfold core₂ ftildeDir ftildeTh ftildeB ftildeB'
  fun_prop (disch := aesop)

lemma differentiableAt_core₃ {x : Euclidean 3} (hx : x ≠ 0) : DifferentiableAt ℝ core₃ x := by
  have hnorm : DifferentiableAt ℝ (fun y : Euclidean 3 => ‖y‖) x :=
    (differentiableAt_id (x := x)).norm ℝ hx
  unfold core₃ ftildeDir ftildeTh ftildeB ftildeB'
  fun_prop (disch := aesop)

lemma differentiableAt_ftildeV₁ {x : Euclidean 3} (hx : x ≠ 0) : DifferentiableAt ℝ ftildeV₁ x := by
  apply (differentiableAt_core₁ hx).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact ftildeV₁_eq_core hy

lemma differentiableAt_ftildeV₂ {x : Euclidean 3} (hx : x ≠ 0) : DifferentiableAt ℝ ftildeV₂ x := by
  apply (differentiableAt_core₂ hx).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact ftildeV₂_eq_core hy

lemma differentiableAt_ftildeV₃ {x : Euclidean 3} (hx : x ≠ 0) : DifferentiableAt ℝ ftildeV₃ x := by
  apply (differentiableAt_core₃ hx).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  exact ftildeV₃_eq_core hy

lemma differentiableAt_ftildeV_coordinate {x : Euclidean 3} (hx : x ≠ 0) (n : Fin 3) :
    DifferentiableAt ℝ (fun y => ftildeV y n) x := by
  fin_cases n
  · simpa [ftildeV] using differentiableAt_ftildeV₁ hx
  · simpa [ftildeV] using differentiableAt_ftildeV₂ hx
  · simpa [ftildeV] using differentiableAt_ftildeV₃ hx

lemma ftildeD_trace_eq_divergence {θ : Euclidean 3} (hθ : θ ≠ 0) :
    ∑ a : Fin 3, ftildeD a a θ = divergence ftildeV θ := by
  rw [divergence]
  apply Finset.sum_congr rfl
  intro a ha
  rw [coordinatePartial_eq_fderiv (differentiableAt_ftildeV_coordinate hθ a)]
  rfl

lemma hasFDerivAt_norm_euclidean {θ : Euclidean 3} (hθ : θ ≠ 0) :
    HasFDerivAt (fun x : Euclidean 3 => ‖x‖) (‖θ‖⁻¹ • innerSL ℝ θ) θ := by
  have h := (hasStrictFDerivAt_norm_sq θ).hasFDerivAt.sqrt
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hθ))
  simp only [Real.sqrt_sq (norm_nonneg _)] at h
  convert h using 1
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hθ]
  ring

lemma fderiv_norm_euclidean {θ : Euclidean 3} (hθ : θ ≠ 0) (a : Fin 3) :
    fderiv ℝ (fun x : Euclidean 3 => ‖x‖) θ (coordinateVector 3 a) = θ a / ‖θ‖ := by
  rw [(hasFDerivAt_norm_euclidean hθ).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply_apply,
    coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
    map_one, one_mul, conj_trivial]
  ring

lemma fderiv_dir_coordinate_of_unit {θ : Euclidean 3} (hθ : θ ≠ 0)
    (hnorm : ‖θ‖ = 1) (i a : Fin 3) :
    fderiv ℝ (fun x => ftildeTh i (ftildeDir x)) θ (coordinateVector 3 a) =
      (if i = a then 1 else 0) - θ i * θ a := by
  have hN := hasFDerivAt_norm_euclidean hθ
  have hI := (hasDerivAt_id ‖θ‖).inv (norm_ne_zero_iff.mpr hθ) |>.comp_hasFDerivAt θ hN
  have hc : HasFDerivAt (fun x : Euclidean 3 => x i) (EuclideanSpace.proj (𝕜 := ℝ) i) θ := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := θ)
  have h := hI.mul hc
  have he := congrArg (fun L : Euclidean 3 →L[ℝ] ℝ => L (coordinateVector 3 a)) h.fderiv
  have hf : (fun x => ftildeTh i (ftildeDir x)) =
      (id⁻¹ ∘ (norm : Euclidean 3 → ℝ) * fun x => x i) := by
    funext x
    simp [ftildeTh, ftildeDir, Function.comp_def, Pi.mul_apply, Pi.inv_apply,
      id_eq, smul_eq_mul]
  rw [hf]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Function.comp_def, id_eq, Pi.inv_apply, PiLp.proj_apply,
    PiLp.single_apply, innerSL_apply_apply, coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right,
    map_one, one_mul, conj_trivial] at he
  rw [hnorm] at he
  simp only [inv_one, one_smul, one_mul, one_div, one_pow] at he
  have hvec : coordinateVector 3 a = EuclideanSpace.single a 1 := by
    ext j
    simp [coordinateVector, EuclideanSpace.basisFun_apply]
  rw [hvec]
  change fderiv ℝ ((fun x : Euclidean 3 => ‖x‖⁻¹) * fun x => x i) θ
    (EuclideanSpace.single a 1) = _
  by_cases hia : i = a
  · subst a
    simp only [if_pos rfl] at he ⊢
    convert he using 1 <;> ring
  · simp only [if_neg hia] at he ⊢
    convert he using 1 <;> ring

lemma fderiv_core₁_of_unit {θ : Euclidean 3} (hθ : θ ≠ 0) (hnorm : ‖θ‖ = 1)
    (a : Fin 3) :
    fderiv ℝ core₁ θ (coordinateVector 3 a) =
      θ a * (θ 0 ^ 6 * θ 1) +
        (6 * θ 0 ^ 5 * θ 1) * ((if 0 = a then 1 else 0) - θ 0 * θ a) +
        θ 0 ^ 6 * ((if 1 = a then 1 else 0) - θ 1 * θ a) := by
  have hr : DifferentiableAt ℝ (fun y : Euclidean 3 => ‖y‖) θ :=
    (differentiableAt_id (x := θ)).norm ℝ hθ
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun x => ftildeTh i (ftildeDir x)) θ := by
    unfold ftildeTh ftildeDir
    fun_prop (disch := aesop)
  unfold core₁
  simp (disch := fun_prop) only [fderiv_fun_mul, fderiv_fun_pow,
    add_apply, smul_apply, smul_eq_mul, nsmul_eq_mul]
  rw [fderiv_norm_euclidean hθ, fderiv_dir_coordinate_of_unit hθ hnorm,
    fderiv_dir_coordinate_of_unit hθ hnorm]
  simp only [ftildeTh, ftildeDir, hnorm, inv_one, one_smul, one_div]
  ring

lemma fderiv_ftildeV_zero_eq_core {θ : Euclidean 3} (hθ : θ ≠ 0) :
    fderiv ℝ (fun y => ftildeV y 0) θ = fderiv ℝ core₁ θ := by
  have heq : (fun y => ftildeV y 0) =ᶠ[𝓝 θ] core₁ := by
    filter_upwards [eventually_ne_nhds hθ] with y hy
    simpa [ftildeV] using ftildeV₁_eq_core hy
  exact heq.fderiv_eq

lemma fderiv_ftildeV_one_eq_core {θ : Euclidean 3} (hθ : θ ≠ 0) :
    fderiv ℝ (fun y => ftildeV y 1) θ = fderiv ℝ core₂ θ := by
  have heq : (fun y => ftildeV y 1) =ᶠ[𝓝 θ] core₂ := by
    filter_upwards [eventually_ne_nhds hθ] with y hy
    simpa [ftildeV] using ftildeV₂_eq_core hy
  exact heq.fderiv_eq

lemma fderiv_ftildeV_two_eq_core {θ : Euclidean 3} (hθ : θ ≠ 0) :
    fderiv ℝ (fun y => ftildeV y 2) θ = fderiv ℝ core₃ θ := by
  have heq : (fun y => ftildeV y 2) =ᶠ[𝓝 θ] core₃ := by
    filter_upwards [eventually_ne_nhds hθ] with y hy
    simpa [ftildeV] using ftildeV₃_eq_core hy
  exact heq.fderiv_eq

lemma unit_sum_sq {θ : Euclidean 3} (hnorm : ‖θ‖ = 1) :
    θ 0 ^ 2 + θ 1 ^ 2 + θ 2 ^ 2 = 1 := by
  have h := EuclideanSpace.norm_sq_eq θ
  rw [hnorm] at h
  simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using h.symm

lemma divergence_ftildeV_of_unit {θ : Euclidean 3} (hθ : θ ≠ 0) (hnorm : ‖θ‖ = 1) :
    divergence ftildeV θ = 0 := by
  have hr : DifferentiableAt ℝ (fun y : Euclidean 3 => ‖y‖) θ :=
    (differentiableAt_id (x := θ)).norm ℝ hθ
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun x => ftildeTh i (ftildeDir x)) θ := by
    unfold ftildeTh ftildeDir
    fun_prop (disch := aesop)
  have hs := unit_sum_sq hnorm
  simp only [divergence, Fin.sum_univ_three]
  rw [coordinatePartial_eq_fderiv (differentiableAt_ftildeV_coordinate hθ 0),
    coordinatePartial_eq_fderiv (differentiableAt_ftildeV_coordinate hθ 1),
    coordinatePartial_eq_fderiv (differentiableAt_ftildeV_coordinate hθ 2),
    fderiv_ftildeV_zero_eq_core hθ, fderiv_ftildeV_one_eq_core hθ,
    fderiv_ftildeV_two_eq_core hθ]
  unfold core₁ core₂ core₃ ftildeB ftildeB'
  simp (disch := fun_prop) only [div_eq_mul_inv, fderiv_fun_mul, fderiv_fun_pow,
    fderiv_fun_add, fderiv_fun_sub, fderiv_const_mul, fderiv_mul_const,
    fderiv_const, add_apply, smul_apply, sub_apply, smul_eq_mul, nsmul_eq_mul]
  simp only [fderiv_dir_coordinate_of_unit hθ hnorm, fderiv_norm_euclidean hθ]
  simp only [ftildeTh, ftildeDir, hnorm, inv_one, one_smul, one_div]
  norm_num
  linear_combination (θ 0 ^ 3 * θ 1 * (4 - 6 * θ 0 ^ 2)) * hs

lemma ftildeD_trace_of_unit {θ : Euclidean 3} (hθ : θ ≠ 0) (hnorm : ‖θ‖ = 1) :
    ∑ a : Fin 3, ftildeD a a θ = 0 := by
  rw [ftildeD_trace_eq_divergence hθ, divergence_ftildeV_of_unit hθ hnorm]

/-- v_n(θ) = Σ_a θ_a D_{a,n}(θ); q(θ) = θ · v(θ). max|q| = 1.369 (0923 §4). -/
def ftildeQ (θ : Euclidean 3) : ℝ :=
  ∑ n : Fin 3, θ n * (∑ a : Fin 3, θ a * ftildeD a n θ)

/-- The exact leading-order tensor from the 0653/1223 computation, in zero-based
coordinates. -/
def ftildeC (i j k : Fin 3) : ℝ :=
  ![![![-8 / 35, 0, 0], ![0, 32 / 105, 0], ![0, 0, -8 / 105]],
    ![![0, 32 / 105, 0], ![32 / 105, 0, 0], ![0, 0, 0]],
    ![![0, 0, -8 / 105], ![0, 0, 0], ![-8 / 105, 0, 0]]] i j k

/-- Φᵢⱼ(θ) = Σₖ Cᵢⱼₖθₖ. -/
def ftildePhi (θ : Euclidean 3) (i j : Fin 3) : ℝ :=
  ∑ k : Fin 3, ftildeC i j k * θ k

/-- The squared Frobenius norm of Φ(θ). -/
def ftildePhiNormSq (θ : Euclidean 3) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ftildePhi θ i j ^ 2

/-- The Frobenius norm used in the uniform ray obstruction L9. -/
def ftildePhiNorm (θ : Euclidean 3) : ℝ := √(ftildePhiNormSq θ)

lemma ftildeC_swap_left (i j k : Fin 3) : ftildeC i j k = ftildeC j i k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [ftildeC]

lemma ftildeC_swap_right (i j k : Fin 3) : ftildeC i j k = ftildeC i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [ftildeC]

lemma ftildeC_trace (k : Fin 3) : ∑ i : Fin 3, ftildeC i i k = 0 := by
  fin_cases k <;> norm_num [ftildeC, Fin.sum_univ_three]

lemma ftildePhiNormSq_eq (θ : Euclidean 3) :
    ftildePhiNormSq θ =
      (1664 * θ 0 ^ 2 + 2048 * θ 1 ^ 2 + 128 * θ 2 ^ 2) / 11025 := by
  simp [ftildePhiNormSq, ftildePhi, ftildeC, Fin.sum_univ_three]
  ring

lemma ftildePhiNormSq_lower {θ : Euclidean 3} (hθ : ∑ i : Fin 3, θ i ^ 2 = 1) :
    128 / 11025 ≤ ftildePhiNormSq θ := by
  rw [ftildePhiNormSq_eq]
  simp only [Fin.sum_univ_three] at hθ
  norm_num at *
  nlinarith [sq_nonneg (θ 0), sq_nonneg (θ 1)]

lemma ftildePhiNorm_lower {θ : Euclidean 3} (hθ : ∑ i : Fin 3, θ i ^ 2 = 1) :
    8 * √2 / 105 ≤ ftildePhiNorm θ := by
  have h := ftildePhiNormSq_lower hθ
  have hs : (8 * √2 / 105 : ℝ) ^ 2 = 128 / 11025 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hn : (0 : ℝ) ≤ 8 * √2 / 105 := by positivity
  calc
    8 * √2 / 105 = √((8 * √2 / 105 : ℝ) ^ 2) := (Real.sqrt_sq hn).symm
    _ ≤ √(ftildePhiNormSq θ) := Real.sqrt_le_sqrt (hs ▸ h)
    _ = ftildePhiNorm θ := rfl

lemma ftildePhi_ne_zero {θ : Euclidean 3} (hθ : ∑ i : Fin 3, θ i ^ 2 = 1) :
    ftildePhi θ ≠ 0 := by
  intro hzero
  have hsq : ftildePhiNormSq θ = 0 := by simp [ftildePhiNormSq, hzero]
  have h := ftildePhiNormSq_lower hθ
  rw [hsq] at h
  norm_num at h

/-- J(r) = ∫₀^r ψ²(t)·t² dt. -/
def ftildeJ (r : ℝ) : ℝ := ∫ t in (0)..r, ftildePsi t ^ 2 * t ^ 2

lemma continuousOn_ftildePsi_Ioo : ContinuousOn ftildePsi (Ioo 0 1) := by
  intro r hr
  exact (hasDerivAt_ftildePsi hr.1 hr.2).continuousAt.continuousWithinAt

lemma continuousOn_ftildePsi_Icc {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ContinuousOn ftildePsi (Icc 0 r) := by
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    exact continuousAt_ftildePsi_zero.continuousWithinAt
  · exact (hasDerivAt_ftildePsi (lt_of_le_of_ne ht.1 (Ne.symm ht0))
      (lt_of_le_of_lt ht.2 hr1)).continuousAt.continuousWithinAt

lemma intervalIntegrable_ftildePsi_sq_mul_sq {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    IntervalIntegrable (fun t => ftildePsi t ^ 2 * t ^ 2) MeasureTheory.volume 0 r := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hr.le]
  exact ((continuousOn_ftildePsi_Icc hr hr1).pow 2).mul (continuousOn_id.pow 2)

lemma continuousOn_ftildePsi_sq_mul_sq_Ioo :
    ContinuousOn (fun t => ftildePsi t ^ 2 * t ^ 2) (Ioo 0 1) :=
  (continuousOn_ftildePsi_Ioo.pow 2).mul (continuousOn_id.pow 2)

lemma hasDerivAt_ftildeJ {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt ftildeJ (ftildePsi r ^ 2 * r ^ 2) r := by
  have hc : ContinuousAt (fun t => ftildePsi t ^ 2 * t ^ 2) r :=
    ((hasDerivAt_ftildePsi hr hr1).continuousAt.pow 2).mul (continuousAt_id.pow 2)
  have hm : StronglyMeasurableAtFilter (fun t => ftildePsi t ^ 2 * t ^ 2)
      (𝓝 r) MeasureTheory.volume :=
    continuousOn_ftildePsi_sq_mul_sq_Ioo.stronglyMeasurableAtFilter
      isOpen_Ioo r ⟨hr, hr1⟩
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_ftildePsi_sq_mul_sq hr hr1) hm hc

/-- The scalar radial factor in the divergence repair. -/
def ftildeRadialRepair (q r : ℝ) : ℝ := -q * ftildeJ r / r ^ 2

lemma hasDerivAt_ftildeRadialRepair (q : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun t => ftildeRadialRepair q t)
      (-q * (ftildePsi r ^ 2 - 2 * ftildeJ r / r ^ 3)) r := by
  have hJ := (hasDerivAt_ftildeJ hr hr1).const_mul (-q)
  have hr2 := (hasDerivAt_id r).pow 2
  have hdiv := hJ.div hr2 (pow_ne_zero 2 hr.ne')
  change HasDerivAt (fun t => -q * ftildeJ t / t ^ 2) _ r
  convert hdiv using 1
  · funext t
    simp [div_eq_mul_inv, mul_comm]
  · simp only [id_eq, Pi.pow_apply, Pi.div_apply, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, mul_one]
    field_simp [hr.ne']
    ring

lemma ftildeRadialRepair_deriv (q : ℝ) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    deriv (fun t => ftildeRadialRepair q t) r =
      -q * (ftildePsi r ^ 2 - 2 * ftildeJ r / r ^ 3) :=
  (hasDerivAt_ftildeRadialRepair q hr hr1).deriv

/-- Repair: w(r,θ) = −q(θ)·J(r)/r²; W = w·θ; F̃ = F + W (0923 §3, 0953 §1).
    F̃ is the falsifying field; the literally-defined ψV field is NOT
    div-free (L3: div F = ψ²q). -/
def ftildeW : VectorField :=
  fun x => if x = 0 then 0 else
    (-(ftildeQ (ftildeDir x)) * ftildeJ ‖x‖ / ‖x‖ ^ 2) • ftildeDir x
def ftildeField : VectorField :=
  fun x => ftildeF x + ftildeW x

/-- (A) WITNESS LEMMA (the Lean target, in repo vocabulary; 14:53 §1).
    The domain clauses are proved below. The single remaining sorry covers
    the C¹, divergence-free, and no-symmetric-system clauses (stages 2–4). -/
theorem ftilde_witness :
    IsOpen ftildeBall ∧ Convex ℝ ftildeBall ∧
    ContDiffOn ℝ 1 ftildeField ftildeBall ∧
    EqOn (divergence ftildeField) 0 ftildeBall ∧
    ¬ SymmetricCurlSystem ftildeBall ftildeField := by
  refine ⟨Metric.isOpen_ball, convex_ball 0 1, ?_⟩
  sorry

/-- (B) MAIN THEOREM: ¬ SymmetricDerivativeLifting, by negating the
    universal at the (A) witness; hence ¬ pma10_43_contract by the PR #28
    iff. The proof is logic over (A), is written out (not sorry), and
    typechecks; it still depends on (A)'s `sorryAx`. -/
theorem ftilde_disproves_lifting : ¬ SymmetricDerivativeLifting := by
  intro h
  obtain ⟨_, _, hC1, hDiv, hNo⟩ := ftilde_witness
  exact hNo (h ftildeBall ftildeBall ballIdentityEquivalence ftildeField
    (by exact Metric.isOpen_ball) (by exact Metric.isOpen_ball)
    (by exact convex_ball 0 1) hC1 hDiv)

theorem ftilde_disproves_pma10_43 : ¬ pma10_43_contract := by
  intro h
  exact ftilde_disproves_lifting
    (pma10_43_contract_iff_symmetricDerivativeLifting.mp h)

end
end Rudin.PMA.Chapter10
