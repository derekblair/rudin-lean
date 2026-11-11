/-
  Statement draft for rudin-lean issue #29 (SymmetricDerivativeLifting).
  PLACED 2026-10-31 ~17:53 PDT by the math orchestrator under Derek's
  2026-10-31 ~17:30 PDT standing-delegation clarification (routine
  pipeline placement + typecheck, not a new direction).
  STATUS: DRAFT WIP. The Stage 1 tensor, radial, and divergence-profile
  lemmas and the Stage 2 C¹ and repaired-divergence theorems below are
  Lean-checked. The (A) witness lemma `ftilde_witness` still carries one
  `sorry` for its remaining no-symmetric-system clause; neither it nor its
  downstream consequences is a completed result. The pin manifest is frozen
  and no dependency pins are changed by this proof work.
  Source: desk draft v3 (sha256
  4392009bf437d79067c3509bcc268064cfce87043879170f042cf11990974978).
  The original statement is unchanged; proof lemmas and the domain, C¹, and
  divergence-free clauses of the witness proof were added during Stages 1–2.
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

/-! ### Stage 2: homogeneity, L2–L4 repaired divergence, and C¹ regularity -/

lemma norm_ftildeDir {x : Euclidean 3} (hx : x ≠ 0) : ‖ftildeDir x‖ = 1 := by
  rw [ftildeDir, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

lemma ftildeDir_ne_zero {x : Euclidean 3} (hx : x ≠ 0) : ftildeDir x ≠ 0 := by
  intro h0
  have h1 := norm_ftildeDir hx
  rw [h0, norm_zero] at h1
  exact zero_ne_one h1

lemma norm_smul_ftildeDir (x : Euclidean 3) : ‖x‖ • ftildeDir x = x := by
  by_cases hx : x = 0
  · simp [hx, ftildeDir]
  · rw [ftildeDir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

lemma ftildeDir_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) :
    ftildeDir (t • x) = ftildeDir x := by
  by_cases hx : x = 0
  · simp [hx, ftildeDir]
  · rw [ftildeDir, ftildeDir, norm_smul, Real.norm_eq_abs, abs_of_pos ht,
      mul_inv_rev, smul_smul]
    congr 1
    field_simp [ht.ne', norm_ne_zero_iff.mpr hx]

lemma ftildeDir_of_unit {θ : Euclidean 3} (hnorm : ‖θ‖ = 1) : ftildeDir θ = θ := by
  simp [ftildeDir, hnorm]

lemma abs_ftildeDir_le_one {x : Euclidean 3} (hx : x ≠ 0) (i : Fin 3) :
    |ftildeDir x i| ≤ 1 := by
  have hs := unit_sum_sq (norm_ftildeDir hx)
  have hsq : ftildeDir x i ^ 2 ≤ 1 := by
    fin_cases i <;> dsimp <;>
      nlinarith [sq_nonneg (ftildeDir x 0), sq_nonneg (ftildeDir x 1), sq_nonneg (ftildeDir x 2)]
  exact abs_le_one_iff_mul_self_le_one.mpr (by simpa only [sq] using hsq)

lemma ftildeV₁_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) :
    ftildeV₁ (t • x) = t * ftildeV₁ x := by
  by_cases hx : x = 0
  · simp [hx, ftildeV₁]
  · have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
    simp only [ftildeV₁, ite_eq_right hx, ite_eq_right htx, ftildeDir_smul_pos ht,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring

lemma ftildeV₂_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) :
    ftildeV₂ (t • x) = t * ftildeV₂ x := by
  by_cases hx : x = 0
  · simp [hx, ftildeV₂]
  · have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
    simp only [ftildeV₂, ite_eq_right hx, ite_eq_right htx, ftildeDir_smul_pos ht,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring

lemma ftildeV₃_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) :
    ftildeV₃ (t • x) = t * ftildeV₃ x := by
  by_cases hx : x = 0
  · simp [hx, ftildeV₃]
  · have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
    simp only [ftildeV₃, ite_eq_right hx, ite_eq_right htx, ftildeDir_smul_pos ht,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    ring

lemma ftildeV_coordinate_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) (n : Fin 3) :
    ftildeV (t • x) n = t * ftildeV x n := by
  fin_cases n
  · simpa [ftildeV] using ftildeV₁_smul_pos ht x
  · simpa [ftildeV] using ftildeV₂_smul_pos ht x
  · simpa [ftildeV] using ftildeV₃_smul_pos ht x

lemma ftildeV_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) :
    ftildeV (t • x) = t • ftildeV x := by
  ext n
  simpa [PiLp.smul_apply, smul_eq_mul] using ftildeV_coordinate_smul_pos ht x n

lemma ftildeV_coordinate_eq_norm_mul_dir {x : Euclidean 3} (hx : x ≠ 0) (n : Fin 3) :
    ftildeV x n = ‖x‖ * ftildeV (ftildeDir x) n := by
  conv_lhs => rw [← norm_smul_ftildeDir x]
  exact ftildeV_coordinate_smul_pos (norm_pos_iff.mpr hx) (ftildeDir x) n

lemma ftildeV_eq_norm_smul_dir {x : Euclidean 3} (hx : x ≠ 0) :
    ftildeV x = ‖x‖ • ftildeV (ftildeDir x) := by
  conv_lhs => rw [← norm_smul_ftildeDir x]
  exact ftildeV_smul_pos (norm_pos_iff.mpr hx) (ftildeDir x)

lemma hasFDerivAt_of_homog_one {g : Euclidean 3 → ℝ}
    (hg : ∀ {t : ℝ}, 0 < t → ∀ y, g (t • y) = t * g y)
    {y : Euclidean 3} {A : Euclidean 3 →L[ℝ] ℝ} (hA : HasFDerivAt g A y)
    {t : ℝ} (ht : 0 < t) :
    HasFDerivAt g A (t • y) := by
  have hinv : 0 < t⁻¹ := inv_pos.mpr ht
  have hlin : HasFDerivAt (fun z : Euclidean 3 => t⁻¹ • z)
      (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3)) (t • y) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3)).hasFDerivAt
  have hy : t⁻¹ • (t • y) = y := inv_smul_smul₀ ht.ne' y
  have hcomp : HasFDerivAt (fun z => g (t⁻¹ • z))
      (A.comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3))) (t • y) :=
    (hy ▸ hA).comp (t • y) hlin
  have hmul := hcomp.const_mul t
  have hfun : (fun z => t * g (t⁻¹ • z)) = g := by
    funext z
    rw [← hg ht (t⁻¹ • z), smul_inv_smul₀ ht.ne']
  have hclm : t • A.comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3)) = A := by
    ext v
    simp [mul_inv_cancel_left₀ ht.ne']
  simpa only [hfun, hclm] using hmul

lemma hasFDerivAt_of_homog_zero {g : Euclidean 3 → ℝ}
    (hg : ∀ {t : ℝ}, 0 < t → ∀ y, g (t • y) = g y)
    {y : Euclidean 3} {A : Euclidean 3 →L[ℝ] ℝ} (hA : HasFDerivAt g A y)
    {t : ℝ} (ht : 0 < t) :
    HasFDerivAt g (t⁻¹ • A) (t • y) := by
  have hlin : HasFDerivAt (fun z : Euclidean 3 => t⁻¹ • z)
      (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3)) (t • y) :=
    (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3)).hasFDerivAt
  have hy : t⁻¹ • (t • y) = y := inv_smul_smul₀ ht.ne' y
  have hcomp : HasFDerivAt (fun z => g (t⁻¹ • z))
      (A.comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3))) (t • y) :=
    (hy ▸ hA).comp (t • y) hlin
  have hfun : (fun z => g (t⁻¹ • z)) = g := by
    funext z
    exact hg (inv_pos.mpr ht) z
  have hclm : A.comp (t⁻¹ • ContinuousLinearMap.id ℝ (Euclidean 3)) = t⁻¹ • A := by
    ext v
    simp
  simpa only [hfun, hclm] using hcomp

lemma euler_homog_one {g : Euclidean 3 → ℝ}
    (hg : ∀ {t : ℝ}, 0 < t → ∀ y, g (t • y) = t * g y)
    {y : Euclidean 3} (hd : DifferentiableAt ℝ g y) :
    ∑ a : Fin 3, y a * fderiv ℝ g y (coordinateVector 3 a) = g y := by
  have hcurve : HasDerivAt (fun t : ℝ => t • y) y 1 := by
    convert (hasDerivAt_id' (1 : ℝ)).smul_const y using 1
    exact (one_smul ℝ y).symm
  have hA : HasFDerivAt g (fderiv ℝ g y) ((1 : ℝ) • y) := by
    simpa only [one_smul] using hd.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => g (t • y)) ((fderiv ℝ g y) y) 1 :=
    hA.comp_hasDerivAt 1 hcurve
  have heq : (fun t : ℝ => g (t • y)) =ᶠ[𝓝 (1 : ℝ)] (fun t : ℝ => t * g y) := by
    filter_upwards [Ioi_mem_nhds zero_lt_one] with t ht
    exact hg ht y
  have h2 : HasDerivAt (fun t : ℝ => g (t • y)) (g y) 1 := by
    have hmul : HasDerivAt (fun t : ℝ => t * g y) (g y) 1 := by
      convert (hasDerivAt_id' (1 : ℝ)).mul_const (g y) using 1
      exact (one_mul (g y)).symm
    exact hmul.congr_of_eventuallyEq heq
  have hu := h1.unique h2
  rw [linear_apply_eq_sum_coordinates] at hu
  simpa only [mul_comm] using hu

lemma coordinatePartial_ftildeV_eq_ftildeD {x : Euclidean 3} (hx : x ≠ 0) (n a : Fin 3) :
    coordinatePartial (fun z => ftildeV z n) x a = ftildeD a n (ftildeDir x) := by
  have hθ : ftildeDir x ≠ 0 := ftildeDir_ne_zero hx
  have hdθ := (differentiableAt_ftildeV_coordinate hθ n).hasFDerivAt
  have hdx := hasFDerivAt_of_homog_one
    (fun ht y => ftildeV_coordinate_smul_pos ht y n) hdθ (norm_pos_iff.mpr hx)
  rw [norm_smul_ftildeDir] at hdx
  rw [coordinatePartial_eq_fderiv hdx.differentiableAt, hdx.fderiv]
  rfl

lemma ftildeD_euler {y : Euclidean 3} (hy : y ≠ 0) (n : Fin 3) :
    ∑ a : Fin 3, y a * ftildeD a n y = ftildeV y n :=
  euler_homog_one (fun ht z => ftildeV_coordinate_smul_pos ht z n)
    (differentiableAt_ftildeV_coordinate hy n)

lemma ftildeQ_eq_sum_ftildeV {y : Euclidean 3} (hy : y ≠ 0) :
    ftildeQ y = ∑ n : Fin 3, y n * ftildeV y n := by
  unfold ftildeQ
  apply Finset.sum_congr rfl
  intro n _
  rw [ftildeD_euler hy n]

lemma differentiableAt_ftildeDir_coordinate {x : Euclidean 3} (hx : x ≠ 0) (i : Fin 3) :
    DifferentiableAt ℝ (fun z => ftildeDir z i) x := by
  have hN := hasFDerivAt_norm_euclidean hx
  have hI := (hasDerivAt_id ‖x‖).inv (norm_ne_zero_iff.mpr hx) |>.comp_hasFDerivAt x hN
  have hc : HasFDerivAt (fun z : Euclidean 3 => z i) (EuclideanSpace.proj (𝕜 := ℝ) i) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := x)
  exact (hI.mul hc).differentiableAt

lemma coordinatePartial_ftildeDir {x : Euclidean 3} (hx : x ≠ 0) (i a : Fin 3) :
    coordinatePartial (fun z => ftildeDir z i) x a =
      ‖x‖⁻¹ * ((if i = a then 1 else 0) - ftildeDir x i * ftildeDir x a) := by
  have hθ : ftildeDir x ≠ 0 := ftildeDir_ne_zero hx
  have hnorm : ‖ftildeDir x‖ = 1 := norm_ftildeDir hx
  have hdθ := (differentiableAt_ftildeDir_coordinate hθ i).hasFDerivAt
  have hdx := hasFDerivAt_of_homog_zero
    (fun ht y => congrArg (fun v : Euclidean 3 => v i) (ftildeDir_smul_pos ht y))
    hdθ (norm_pos_iff.mpr hx)
  rw [norm_smul_ftildeDir] at hdx
  rw [coordinatePartial_eq_fderiv hdx.differentiableAt, hdx.fderiv, smul_apply, smul_eq_mul]
  congr 1
  exact fderiv_dir_coordinate_of_unit hθ hnorm i a

lemma sum_coordinatePartial_ftildeDir {x : Euclidean 3} (hx : x ≠ 0) :
    ∑ n : Fin 3, coordinatePartial (fun z => ftildeDir z n) x n = 2 / ‖x‖ := by
  have hs := unit_sum_sq (norm_ftildeDir hx)
  simp only [Fin.sum_univ_three, coordinatePartial_ftildeDir hx, ↓reduceIte, div_eq_mul_inv]
  linear_combination -‖x‖⁻¹ * hs

lemma ftildePsi_nonneg (t : ℝ) : 0 ≤ ftildePsi t := by
  by_cases ht : t = 0
  · simp [ftildePsi, ht]
  · rw [ftildePsi, ite_eq_right ht]
    positivity

lemma ftildePsi_le_of_mem_Icc {r t : ℝ} (hr : 0 < r) (hr1 : r < 1) (ht : t ∈ Icc 0 r) :
    ftildePsi t ≤ ftildePsi r := by
  by_cases ht0 : t = 0
  · subst t
    simpa [ftildePsi] using ftildePsi_nonneg r
  · have htp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have ht1 : t < 1 := lt_of_le_of_lt ht.2 hr1
    have hlog_le : Real.log t ≤ Real.log r := Real.log_le_log htp ht.2
    have hlog_r : Real.log r < 0 := Real.log_neg hr hr1
    rw [ftildePsi_eq_neg_inv_log htp ht1, ftildePsi_eq_neg_inv_log hr hr1,
      ← inv_neg, ← inv_neg]
    exact inv_anti₀ (by linarith) (by linarith)

lemma ftildeJ_nonneg {r : ℝ} (hr : 0 < r) : 0 ≤ ftildeJ r := by
  apply intervalIntegral.integral_nonneg hr.le
  intro t _
  positivity

lemma ftildeJ_le_psi_sq_mul_cube {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ftildeJ r ≤ ftildePsi r ^ 2 * r ^ 3 := by
  have hmono : ftildeJ r ≤ ∫ _ in (0)..r, ftildePsi r ^ 2 * r ^ 2 := by
    apply intervalIntegral.integral_mono_on hr.le
      (intervalIntegrable_ftildePsi_sq_mul_sq hr hr1) intervalIntegrable_const
    intro t ht
    have hpsi : ftildePsi t ^ 2 ≤ ftildePsi r ^ 2 :=
      pow_le_pow_left₀ (ftildePsi_nonneg t) (ftildePsi_le_of_mem_Icc hr hr1 ht) 2
    have ht2 : t ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ht.1 ht.2 2
    exact mul_le_mul hpsi ht2 (sq_nonneg t) (sq_nonneg (ftildePsi r))
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  linarith

lemma hasFDerivAt_ftildePsi_norm {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    HasFDerivAt (fun y : Euclidean 3 => ftildePsi ‖y‖)
      ((ftildePsi ‖x‖ ^ 2 / ‖x‖) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
  (hasDerivAt_ftildePsi (norm_pos_iff.mpr hx) hx1).comp_hasFDerivAt x
    (hasFDerivAt_norm_euclidean hx)

lemma coordinatePartial_ftildePsi_norm {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1)
    (a : Fin 3) :
    coordinatePartial (fun y : Euclidean 3 => ftildePsi ‖y‖) x a =
      (ftildePsi ‖x‖ ^ 2 / ‖x‖) * ftildeDir x a := by
  have h := hasFDerivAt_ftildePsi_norm hx hx1
  rw [coordinatePartial_eq_fderiv h.differentiableAt, h.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    ftildeDir, PiLp.smul_apply]

lemma differentiableAt_ftildeF_coordinate {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1)
    (i : Fin 3) :
    DifferentiableAt ℝ (fun y => ftildeF y i) x := by
  have hprod : DifferentiableAt ℝ (fun y : Euclidean 3 => ftildePsi ‖y‖ * ftildeV y i) x :=
    (hasFDerivAt_ftildePsi_norm hx hx1).differentiableAt.mul
      (differentiableAt_ftildeV_coordinate hx i)
  apply hprod.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [ftildeF, ite_eq_right hy, PiLp.smul_apply, smul_eq_mul]

lemma coordinatePartial_ftildeF {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1)
    (i a : Fin 3) :
    coordinatePartial (fun y => ftildeF y i) x a =
      ftildePsi ‖x‖ ^ 2 * ftildeDir x a * ftildeV (ftildeDir x) i +
        ftildePsi ‖x‖ * ftildeD a i (ftildeDir x) := by
  have heq : EqOn (fun y => ftildeF y i) (fun y => ftildePsi ‖y‖ * ftildeV y i) {0}ᶜ := by
    intro y hy
    simp [ftildeF, ite_eq_right (mem_compl_singleton_iff.mp hy), PiLp.smul_apply, smul_eq_mul]
  rw [coordinatePartial_congr_of_eqOn isOpen_compl_singleton heq hx a,
    coordinatePartial_mul (hasFDerivAt_ftildePsi_norm hx hx1).differentiableAt
      (differentiableAt_ftildeV_coordinate hx i) a,
    coordinatePartial_ftildePsi_norm hx hx1 a,
    coordinatePartial_ftildeV_eq_ftildeD hx i a,
    ftildeV_coordinate_eq_norm_mul_dir hx i]
  have hnr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnr]

lemma divergence_ftildeF_of_ne_zero {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    divergence ftildeF x = ftildePsi ‖x‖ ^ 2 * ftildeQ (ftildeDir x) := by
  have hθ : ftildeDir x ≠ 0 := ftildeDir_ne_zero hx
  have hnorm : ‖ftildeDir x‖ = 1 := norm_ftildeDir hx
  rw [divergence]
  have hsum : ∑ i : Fin 3, coordinatePartial (fun y => ftildeF y i) x i =
      ftildePsi ‖x‖ ^ 2 * (∑ i : Fin 3, ftildeDir x i * ftildeV (ftildeDir x) i) +
        ftildePsi ‖x‖ * (∑ i : Fin 3, ftildeD i i (ftildeDir x)) := by
    simp_rw [coordinatePartial_ftildeF hx hx1, mul_assoc]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [hsum, ftildeD_trace_of_unit hθ hnorm, mul_zero, add_zero, ← ftildeQ_eq_sum_ftildeV hθ]

/-- Scalar radial-angular factor in W(x) = w(x) • θ(x) away from the origin. -/
def ftildeWScalar (x : Euclidean 3) : ℝ :=
  -ftildeQ (ftildeDir x) * ftildeJ ‖x‖ / ‖x‖ ^ 2

lemma differentiableAt_ftildeQ {y : Euclidean 3} (hy : y ≠ 0) :
    DifferentiableAt ℝ ftildeQ y := by
  have hsum : DifferentiableAt ℝ (fun z : Euclidean 3 => ∑ n : Fin 3, z n * ftildeV z n) y := by
    apply DifferentiableAt.fun_sum
    intro n _
    have hc : DifferentiableAt ℝ (fun z : Euclidean 3 => z n) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) n).differentiableAt
    exact hc.mul (differentiableAt_ftildeV_coordinate hy n)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hy] with z hz
  exact ftildeQ_eq_sum_ftildeV hz

lemma differentiableAt_ftildeDir {x : Euclidean 3} (hx : x ≠ 0) :
    DifferentiableAt ℝ ftildeDir x := by
  rw [differentiableAt_piLp]
  intro i
  exact differentiableAt_ftildeDir_coordinate hx i

lemma differentiableAt_ftildeQ_dir {x : Euclidean 3} (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y => ftildeQ (ftildeDir y)) x :=
  (differentiableAt_ftildeQ (ftildeDir_ne_zero hx)).comp x (differentiableAt_ftildeDir hx)

lemma hasFDerivAt_ftildeJ_norm {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    HasFDerivAt (fun y : Euclidean 3 => ftildeJ ‖y‖)
      ((ftildePsi ‖x‖ ^ 2 * ‖x‖ ^ 2) • (‖x‖⁻¹ • innerSL ℝ x)) x :=
  (hasDerivAt_ftildeJ (norm_pos_iff.mpr hx) hx1).comp_hasFDerivAt x
    (hasFDerivAt_norm_euclidean hx)

lemma differentiableAt_ftildeWScalar {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    DifferentiableAt ℝ ftildeWScalar x := by
  have hq : DifferentiableAt ℝ (fun y : Euclidean 3 => -ftildeQ (ftildeDir y)) x :=
    (differentiableAt_ftildeQ_dir hx).fun_neg
  have hJ : DifferentiableAt ℝ (fun y : Euclidean 3 => ftildeJ ‖y‖) x :=
    (hasFDerivAt_ftildeJ_norm hx hx1).differentiableAt
  have hr2 : DifferentiableAt ℝ (fun y : Euclidean 3 => (‖y‖ ^ 2)⁻¹) x :=
    (((hasFDerivAt_norm_euclidean hx).differentiableAt).fun_pow 2).inv
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  convert (hq.mul hJ).mul hr2 using 1
  funext y
  simp [ftildeWScalar, div_eq_mul_inv]

lemma sum_dir_mul_coordinatePartial_ftildeWScalar {x : Euclidean 3}
    (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    ∑ n : Fin 3, ftildeDir x n * coordinatePartial ftildeWScalar x n =
      -ftildeQ (ftildeDir x) * (ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) := by
  set r := ‖x‖
  set θ := ftildeDir x
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hnorm : ‖θ‖ = 1 := norm_ftildeDir hx
  have hdw : DifferentiableAt ℝ ftildeWScalar x := differentiableAt_ftildeWScalar hx hx1
  have hcurve : HasDerivAt (fun t : ℝ => t • θ) θ r := by
    convert (hasDerivAt_id' r).smul_const θ using 1
    exact (one_smul ℝ θ).symm
  have hA : HasFDerivAt ftildeWScalar (fderiv ℝ ftildeWScalar x) (r • θ) := by
    simpa only [r, θ, norm_smul_ftildeDir] using hdw.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ => ftildeWScalar (t • θ))
      ((fderiv ℝ ftildeWScalar x) θ) r := by
    simpa only [Function.comp_def] using hA.comp_hasDerivAt r hcurve
  have heq : (fun t : ℝ => ftildeWScalar (t • θ)) =ᶠ[𝓝 r]
      (fun t : ℝ => ftildeRadialRepair (ftildeQ θ) t) := by
    filter_upwards [Ioo_mem_nhds hr hx1] with t ht
    simp only [ftildeWScalar, ftildeRadialRepair, ftildeDir_smul_pos ht.1,
      ftildeDir_of_unit hnorm, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1, hnorm, mul_one]
  have h2 := (hasDerivAt_ftildeRadialRepair (ftildeQ θ) hr hx1).congr_of_eventuallyEq heq
  have hu := h1.unique h2
  rw [linear_apply_eq_sum_coordinates] at hu
  calc
    ∑ n : Fin 3, θ n * coordinatePartial ftildeWScalar x n =
        ∑ n : Fin 3, fderiv ℝ ftildeWScalar x (coordinateVector 3 n) * θ n := by
      apply Finset.sum_congr rfl
      intro n _
      rw [coordinatePartial_eq_fderiv hdw, mul_comm]
    _ = -ftildeQ θ * (ftildePsi r ^ 2 - 2 * ftildeJ r / r ^ 3) := hu

lemma differentiableAt_ftildeW_coordinate {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1)
    (i : Fin 3) :
    DifferentiableAt ℝ (fun y => ftildeW y i) x := by
  have hprod : DifferentiableAt ℝ (fun y => ftildeWScalar y * ftildeDir y i) x :=
    (differentiableAt_ftildeWScalar hx hx1).mul (differentiableAt_ftildeDir_coordinate hx i)
  apply hprod.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp [ftildeW, ftildeWScalar, ite_eq_right hy, PiLp.smul_apply, smul_eq_mul]

lemma divergence_ftildeW_of_ne_zero {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    divergence ftildeW x = -ftildeQ (ftildeDir x) * ftildePsi ‖x‖ ^ 2 := by
  rw [divergence]
  have hcongr (i : Fin 3) :
      coordinatePartial (fun y => ftildeW y i) x i =
        coordinatePartial ftildeWScalar x i * ftildeDir x i +
          ftildeWScalar x * coordinatePartial (fun y => ftildeDir y i) x i := by
    have heq : EqOn (fun y => ftildeW y i) (fun y => ftildeWScalar y * ftildeDir y i) {0}ᶜ := by
      intro y hy
      simp [ftildeW, ftildeWScalar, ite_eq_right (mem_compl_singleton_iff.mp hy),
        PiLp.smul_apply, smul_eq_mul]
    rw [coordinatePartial_congr_of_eqOn isOpen_compl_singleton heq hx i,
      coordinatePartial_mul (differentiableAt_ftildeWScalar hx hx1)
        (differentiableAt_ftildeDir_coordinate hx i) i]
  simp_rw [hcongr]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcomm : ∑ i : Fin 3, coordinatePartial ftildeWScalar x i * ftildeDir x i =
      ∑ i : Fin 3, ftildeDir x i * coordinatePartial ftildeWScalar x i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcomm, sum_dir_mul_coordinatePartial_ftildeWScalar hx hx1,
    sum_coordinatePartial_ftildeDir hx]
  simp only [ftildeWScalar]
  have hnr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnr]
  ring

lemma divergence_ftildeField_of_ne_zero {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    divergence ftildeField x = 0 := by
  have hdiv : divergence ftildeField x = divergence ftildeF x + divergence ftildeW x := by
    simp only [divergence, ftildeField, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact coordinatePartial_add (differentiableAt_ftildeF_coordinate hx hx1 i)
      (differentiableAt_ftildeW_coordinate hx hx1 i) i
  rw [hdiv, divergence_ftildeF_of_ne_zero hx hx1, divergence_ftildeW_of_ne_zero hx hx1]
  ring

/-! ### C¹ regularity at the origin and on the punctured ball -/

lemma exists_bound_on_unit_sphere {g : Euclidean 3 → ℝ}
    (hg : ContinuousOn g ({0}ᶜ : Set (Euclidean 3))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : Euclidean 3, ‖θ‖ = 1 → |g θ| ≤ C := by
  have hsub : Metric.sphere (0 : Euclidean 3) 1 ⊆ {0}ᶜ := by
    intro θ hθ h0
    rw [mem_singleton_iff] at h0
    simp [h0] at hθ
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Euclidean 3) 1).exists_bound_of_continuousOn
    (hg.mono hsub)
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro θ hθ
  have hmem : θ ∈ Metric.sphere (0 : Euclidean 3) 1 := by simp [hθ]
  exact (Real.norm_eq_abs (g θ) ▸ hC θ hmem).trans (le_max_left C 0)

lemma norm_euclidean3_le_sum_abs (v : Euclidean 3) :
    ‖v‖ ≤ |v 0| + |v 1| + |v 2| := by
  have hsq : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    simpa [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] using EuclideanSpace.norm_sq_eq v
  have hle : ‖v‖ ^ 2 ≤ (|v 0| + |v 1| + |v 2|) ^ 2 := by
    rw [hsq]
    nlinarith [abs_nonneg (v 0), abs_nonneg (v 1), abs_nonneg (v 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]
  exact le_of_sq_le_sq hle (by positivity)

lemma contDiffOn_norm_compl_zero {r : ℕ} :
    ContDiffOn ℝ r (fun x : Euclidean 3 => ‖x‖) {0}ᶜ := by
  intro x hx
  exact (contDiffAt_id.norm ℝ (mem_compl_singleton_iff.mp hx)).contDiffWithinAt

lemma contDiffOn_ftildeDir_coordinate {r : ℕ} (i : Fin 3) :
    ContDiffOn ℝ r (fun x : Euclidean 3 => ftildeDir x i) {0}ᶜ := by
  have hinv : ContDiffOn ℝ r (fun x : Euclidean 3 => ‖x‖⁻¹) {0}ᶜ :=
    contDiffOn_norm_compl_zero.inv
      (fun _ hx => norm_ne_zero_iff.mpr (mem_compl_singleton_iff.mp hx))
  have hproj : ContDiffOn ℝ r (fun x : Euclidean 3 => x i) {0}ᶜ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.contDiffOn
  exact (hinv.mul hproj).congr (fun x _ => by simp [ftildeDir, PiLp.smul_apply, smul_eq_mul])

lemma contDiffOn_ftildeDir {r : ℕ} : ContDiffOn ℝ r ftildeDir {0}ᶜ :=
  contDiffOn_vector_of_coordinates contDiffOn_ftildeDir_coordinate

lemma contDiff_ftildeB {r : ℕ} : ContDiff ℝ r ftildeB := by
  unfold ftildeB
  exact (contDiff_id.add ((contDiff_id.pow 3).div_const 2)).sub
    ((contDiff_id.pow 5).div_const 4)

lemma contDiff_ftildeB' {r : ℕ} : ContDiff ℝ r ftildeB' := by
  unfold ftildeB'
  exact (contDiff_const.add ((contDiff_const.mul (contDiff_id.pow 2)).div_const 2)).sub
    ((contDiff_const.mul (contDiff_id.pow 4)).div_const 4)

lemma contDiffOn_core₁ {r : ℕ} : ContDiffOn ℝ r core₁ {0}ᶜ := by
  have h0 := contDiffOn_ftildeDir_coordinate (r := r) 0
  have h1 := contDiffOn_ftildeDir_coordinate (r := r) 1
  exact ((contDiffOn_norm_compl_zero.mul (h0.pow 6)).mul h1).congr
    (fun _ _ => by rfl)

lemma contDiffOn_core₂ {r : ℕ} : ContDiffOn ℝ r core₂ {0}ᶜ := by
  have hu := contDiffOn_ftildeDir_coordinate (r := r) 0
  have hv := contDiffOn_ftildeDir_coordinate (r := r) 1
  have hw := contDiffOn_ftildeDir_coordinate (r := r) 2
  have hbu := contDiff_ftildeB.comp_contDiffOn hu
  have hb'u := contDiff_ftildeB'.comp_contDiffOn hu
  exact (contDiffOn_norm_compl_zero.mul
    (((hbu.mul (contDiffOn_const.add (hv.pow 2))).sub ((hu.mul (hv.pow 2)).mul hb'u)).add
      ((contDiffOn_const.mul (hv.pow 4)).mul hw))).congr (fun _ _ => by rfl)

lemma contDiffOn_core₃ {r : ℕ} : ContDiffOn ℝ r core₃ {0}ᶜ := by
  have hu := contDiffOn_ftildeDir_coordinate (r := r) 0
  have hv := contDiffOn_ftildeDir_coordinate (r := r) 1
  have hw := contDiffOn_ftildeDir_coordinate (r := r) 2
  have hbu := contDiff_ftildeB.comp_contDiffOn hu
  have hb'u := contDiff_ftildeB'.comp_contDiffOn hu
  exact (contDiffOn_norm_compl_zero.mul
    (((hv.mul hw).mul (hbu.sub (hu.mul hb'u))).add
      ((contDiffOn_const.mul (hv.pow 3)).mul (contDiffOn_const.sub (hv.pow 2))))).congr
    (fun _ _ => by rfl)

lemma contDiffOn_ftildeV_coordinate {r : ℕ} (i : Fin 3) :
    ContDiffOn ℝ r (fun x => ftildeV x i) {0}ᶜ := by
  fin_cases i
  · exact contDiffOn_core₁.congr (fun x hx => by
      simpa [ftildeV] using ftildeV₁_eq_core (mem_compl_singleton_iff.mp hx))
  · exact contDiffOn_core₂.congr (fun x hx => by
      simpa [ftildeV] using ftildeV₂_eq_core (mem_compl_singleton_iff.mp hx))
  · exact contDiffOn_core₃.congr (fun x hx => by
      simpa [ftildeV] using ftildeV₃_eq_core (mem_compl_singleton_iff.mp hx))

lemma continuousOn_ftildeD (a n : Fin 3) : ContinuousOn (ftildeD a n) {0}ᶜ := by
  apply (continuousOn_coordinatePartial isOpen_compl_singleton
    (contDiffOn_ftildeV_coordinate (r := 1) n) a).congr
  intro θ hθ
  exact (coordinatePartial_eq_fderiv
    (differentiableAt_ftildeV_coordinate (mem_compl_singleton_iff.mp hθ) n) a).symm

lemma contDiffOn_ftildeQ {r : ℕ} : ContDiffOn ℝ r ftildeQ {0}ᶜ := by
  have hsum : ContDiffOn ℝ r (fun y : Euclidean 3 => ∑ n : Fin 3, y n * ftildeV y n) {0}ᶜ :=
    ContDiffOn.sum fun n _ =>
      ((EuclideanSpace.proj (𝕜 := ℝ) n).contDiff.contDiffOn).mul (contDiffOn_ftildeV_coordinate n)
  exact hsum.congr (fun y hy => ftildeQ_eq_sum_ftildeV (mem_compl_singleton_iff.mp hy))

/-- Degree-zero angular factor in W_i(x) = ftildeWAux i x * (J(‖x‖) / ‖x‖²). -/
def ftildeWAux (i : Fin 3) (x : Euclidean 3) : ℝ :=
  -ftildeQ (ftildeDir x) * ftildeDir x i

lemma ftildeWAux_smul_pos {t : ℝ} (ht : 0 < t) (x : Euclidean 3) (i : Fin 3) :
    ftildeWAux i (t • x) = ftildeWAux i x := by
  simp [ftildeWAux, ftildeDir_smul_pos ht]

lemma ftildeWAux_eq_dir {x : Euclidean 3} (hx : x ≠ 0) (i : Fin 3) :
    ftildeWAux i x = ftildeWAux i (ftildeDir x) := by
  conv_lhs => rw [← norm_smul_ftildeDir x]
  exact ftildeWAux_smul_pos (norm_pos_iff.mpr hx) (ftildeDir x) i

lemma contDiffOn_ftildeWAux {r : ℕ} (i : Fin 3) :
    ContDiffOn ℝ r (ftildeWAux i) {0}ᶜ := by
  have hmap : MapsTo ftildeDir {0}ᶜ {0}ᶜ :=
    fun _ hx => ftildeDir_ne_zero (mem_compl_singleton_iff.mp hx)
  exact ((contDiffOn_ftildeQ.comp contDiffOn_ftildeDir hmap).neg).mul
    (contDiffOn_ftildeDir_coordinate i)

lemma differentiableAt_ftildeWAux {x : Euclidean 3} (hx : x ≠ 0) (i : Fin 3) :
    DifferentiableAt ℝ (ftildeWAux i) x :=
  ((contDiffOn_ftildeWAux (r := 1) i).differentiableOn one_ne_zero).differentiableAt
    (isOpen_compl_singleton.mem_nhds hx)

lemma continuousOn_coordinatePartial_ftildeWAux (i a : Fin 3) :
    ContinuousOn (fun x => coordinatePartial (ftildeWAux i) x a) {0}ᶜ :=
  continuousOn_coordinatePartial isOpen_compl_singleton (contDiffOn_ftildeWAux (r := 1) i) a

lemma coordinatePartial_ftildeWAux {x : Euclidean 3} (hx : x ≠ 0) (i a : Fin 3) :
    coordinatePartial (ftildeWAux i) x a =
      ‖x‖⁻¹ * coordinatePartial (ftildeWAux i) (ftildeDir x) a := by
  have hθ : ftildeDir x ≠ 0 := ftildeDir_ne_zero hx
  have hdθ := (differentiableAt_ftildeWAux hθ i).hasFDerivAt
  have hdx := hasFDerivAt_of_homog_zero
    (fun ht y => ftildeWAux_smul_pos ht y i) hdθ (norm_pos_iff.mpr hx)
  rw [norm_smul_ftildeDir] at hdx
  rw [coordinatePartial_eq_fderiv hdx.differentiableAt, hdx.fderiv, smul_apply, smul_eq_mul,
    coordinatePartial_eq_fderiv (differentiableAt_ftildeWAux hθ i)]

lemma hasFDerivAt_ftildeRadialUnit_norm {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1) :
    HasFDerivAt (fun y : Euclidean 3 => ftildeRadialRepair (-1) ‖y‖)
      ((ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) • (‖x‖⁻¹ • innerSL ℝ x)) x := by
  have hd := hasDerivAt_ftildeRadialRepair (-1) (norm_pos_iff.mpr hx) hx1
  simp only [neg_neg, one_mul] at hd
  exact hd.comp_hasFDerivAt x (hasFDerivAt_norm_euclidean hx)

lemma coordinatePartial_ftildeRadialUnit_norm {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1)
    (a : Fin 3) :
    coordinatePartial (fun y : Euclidean 3 => ftildeRadialRepair (-1) ‖y‖) x a =
      (ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) * ftildeDir x a := by
  have h := hasFDerivAt_ftildeRadialUnit_norm hx hx1
  rw [coordinatePartial_eq_fderiv h.differentiableAt, h.fderiv]
  simp only [smul_apply, smul_eq_mul, innerSL_apply_apply, coordinateVector,
    EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right, conj_trivial, one_mul,
    ftildeDir, PiLp.smul_apply]

lemma coordinatePartial_ftildeW {x : Euclidean 3} (hx : x ≠ 0) (hx1 : ‖x‖ < 1)
    (i a : Fin 3) :
    coordinatePartial (fun y => ftildeW y i) x a =
      coordinatePartial (ftildeWAux i) (ftildeDir x) a * (ftildeJ ‖x‖ / ‖x‖ ^ 3) +
        ftildeWAux i (ftildeDir x) *
          (ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) * ftildeDir x a := by
  have heq : EqOn (fun y => ftildeW y i)
      (fun y => ftildeWAux i y * ftildeRadialRepair (-1) ‖y‖) {0}ᶜ := by
    intro y hy
    simp only [ftildeW, ftildeWAux, ftildeRadialRepair,
      ite_eq_right (mem_compl_singleton_iff.mp hy), PiLp.smul_apply, smul_eq_mul]
    ring
  rw [coordinatePartial_congr_of_eqOn isOpen_compl_singleton heq hx a,
    coordinatePartial_mul (differentiableAt_ftildeWAux hx i)
      (hasFDerivAt_ftildeRadialUnit_norm hx hx1).differentiableAt a,
    coordinatePartial_ftildeWAux hx i a,
    coordinatePartial_ftildeRadialUnit_norm hx hx1 a,
    ← ftildeWAux_eq_dir hx i]
  simp only [ftildeRadialRepair]
  have hnr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnr]

lemma tendsto_ftildePsi_norm_nhdsNE_zero :
    Filter.Tendsto (fun x : Euclidean 3 => ftildePsi ‖x‖) (𝓝[≠] 0) (𝓝 0) := by
  have hnorm : Filter.Tendsto (fun x : Euclidean 3 => ‖x‖) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_norm_zero.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact norm_ne_zero_iff.mpr hx
  exact tendsto_ftildePsi_nhdsNE_zero.comp hnorm

lemma tendsto_zero_of_abs_le_psi_nhdsNE_zero {g : Euclidean 3 → ℝ} (C₁ C₂ : ℝ)
    (hg : ∀ x : Euclidean 3, x ≠ 0 → ‖x‖ < 1 →
      |g x| ≤ C₁ * ftildePsi ‖x‖ + C₂ * ftildePsi ‖x‖ ^ 2) :
    Filter.Tendsto g (𝓝[≠] 0) (𝓝 0) := by
  have hu : Filter.Tendsto
      (fun x : Euclidean 3 => C₁ * ftildePsi ‖x‖ + C₂ * ftildePsi ‖x‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
    have hp := tendsto_ftildePsi_norm_nhdsNE_zero
    simpa using (hp.const_mul C₁).add ((hp.pow 2).const_mul C₂)
  have hmem : {x : Euclidean 3 | x ≠ 0} ∩ Metric.ball (0 : Euclidean 3) 1 ∈
      𝓝[≠] (0 : Euclidean 3) :=
    Filter.inter_mem self_mem_nhdsWithin
      (nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 zero_lt_one))
  refine squeeze_zero_norm' ?_ hu
  filter_upwards [hmem] with x hx
  rw [Real.norm_eq_abs]
  exact hg x hx.1 (by simpa using hx.2)

lemma hasFDerivAt_ftildeF_zero :
    HasFDerivAt ftildeF (0 : Euclidean 3 →L[ℝ] Euclidean 3) 0 := by
  rw [← Chapter09.pma9_11, Chapter09.pma9_11_iff_punctured_limit]
  have hf0 : ftildeF 0 = 0 := by simp [ftildeF]
  obtain ⟨C0, hC0, hb0⟩ := exists_bound_on_unit_sphere
    (contDiffOn_ftildeV_coordinate (r := 0) 0).continuousOn
  obtain ⟨C1, hC1, hb1⟩ := exists_bound_on_unit_sphere
    (contDiffOn_ftildeV_coordinate (r := 0) 1).continuousOn
  obtain ⟨C2, hC2, hb2⟩ := exists_bound_on_unit_sphere
    (contDiffOn_ftildeV_coordinate (r := 0) 2).continuousOn
  apply tendsto_zero_of_abs_le_psi_nhdsNE_zero (C0 + C1 + C2) 0
  intro h hh hh1
  have hnorm : ‖ftildeDir h‖ = 1 := norm_ftildeDir hh
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hpsi : 0 ≤ ftildePsi ‖h‖ := ftildePsi_nonneg ‖h‖
  simp only [zero_add, hf0, sub_zero, zero_apply, zero_mul, add_zero]
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le), div_le_iff₀ hpos]
  have hF : ftildeF h = (ftildePsi ‖h‖ * ‖h‖) • ftildeV (ftildeDir h) := by
    rw [ftildeF, ite_eq_right hh, ftildeV_eq_norm_smul_dir hh, smul_smul]
  rw [hF, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hpsi hpos.le)]
  have hv : ‖ftildeV (ftildeDir h)‖ ≤ C0 + C1 + C2 :=
    (norm_euclidean3_le_sum_abs _).trans
      (add_le_add (add_le_add (hb0 _ hnorm) (hb1 _ hnorm)) (hb2 _ hnorm))
  calc
    ftildePsi ‖h‖ * ‖h‖ * ‖ftildeV (ftildeDir h)‖ ≤
        ftildePsi ‖h‖ * ‖h‖ * (C0 + C1 + C2) :=
      mul_le_mul_of_nonneg_left hv (mul_nonneg hpsi hpos.le)
    _ = (C0 + C1 + C2) * ftildePsi ‖h‖ * ‖h‖ := by ring

lemma hasFDerivAt_ftildeW_zero :
    HasFDerivAt ftildeW (0 : Euclidean 3 →L[ℝ] Euclidean 3) 0 := by
  rw [← Chapter09.pma9_11, Chapter09.pma9_11_iff_punctured_limit]
  have hw0 : ftildeW 0 = 0 := by simp [ftildeW]
  obtain ⟨CQ, hCQ, hbQ⟩ := exists_bound_on_unit_sphere
    (contDiffOn_ftildeQ (r := 0)).continuousOn
  apply tendsto_zero_of_abs_le_psi_nhdsNE_zero 0 CQ
  intro h hh hh1
  have hnorm : ‖ftildeDir h‖ = 1 := norm_ftildeDir hh
  have hpos : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hJn : 0 ≤ ftildeJ ‖h‖ := ftildeJ_nonneg hpos
  have hJb : ftildeJ ‖h‖ ≤ ftildePsi ‖h‖ ^ 2 * ‖h‖ ^ 3 :=
    ftildeJ_le_psi_sq_mul_cube hpos hh1
  simp only [zero_add, hw0, sub_zero, zero_apply, zero_mul]
  rw [abs_of_nonneg (div_nonneg (norm_nonneg _) hpos.le), div_le_iff₀ hpos]
  rw [ftildeW, ite_eq_right hh, norm_smul, hnorm, mul_one, Real.norm_eq_abs,
    abs_div, abs_mul, abs_neg, abs_of_nonneg hJn, abs_of_pos (pow_pos hpos 2)]
  have hJr2 : ftildeJ ‖h‖ / ‖h‖ ^ 2 ≤ ftildePsi ‖h‖ ^ 2 * ‖h‖ := by
    rw [div_le_iff₀ (pow_pos hpos 2)]
    linarith
  calc
    |ftildeQ (ftildeDir h)| * ftildeJ ‖h‖ / ‖h‖ ^ 2 =
        |ftildeQ (ftildeDir h)| * (ftildeJ ‖h‖ / ‖h‖ ^ 2) := by ring
    _ ≤ CQ * (ftildePsi ‖h‖ ^ 2 * ‖h‖) :=
      mul_le_mul (hbQ _ hnorm) hJr2 (div_nonneg hJn (sq_nonneg _)) hCQ
    _ = CQ * ftildePsi ‖h‖ ^ 2 * ‖h‖ := by ring

lemma continuousAt_coordinatePartial_ftildeF_of_ne_zero {x : Euclidean 3}
    (hx : x ≠ 0) (hx1 : ‖x‖ < 1) (i a : Fin 3) :
    ContinuousAt (fun z => coordinatePartial (fun y => ftildeF y i) z a) x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hθ : ftildeDir x ≠ 0 := ftildeDir_ne_zero hx
  have hnorm_cont : ContinuousAt (fun z : Euclidean 3 => ‖z‖) x := continuous_norm.continuousAt
  have hpsi_cont : ContinuousAt (fun z : Euclidean 3 => ftildePsi ‖z‖) x :=
    (hasDerivAt_ftildePsi hr hx1).continuousAt.comp hnorm_cont
  have hdir_cont : ContinuousAt ftildeDir x := (differentiableAt_ftildeDir hx).continuousAt
  have hdir_coord_cont : ContinuousAt (fun z : Euclidean 3 => ftildeDir z a) x :=
    (differentiableAt_ftildeDir_coordinate hx a).continuousAt
  have hV_cont : ContinuousAt (fun z : Euclidean 3 => ftildeV (ftildeDir z) i) x :=
    ((contDiffOn_ftildeV_coordinate (r := 0) i).continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds hθ)).comp hdir_cont
  have hD_cont : ContinuousAt (fun z : Euclidean 3 => ftildeD a i (ftildeDir z)) x :=
    ((continuousOn_ftildeD a i).continuousAt (isOpen_compl_singleton.mem_nhds hθ)).comp hdir_cont
  have hrhs : ContinuousAt
      (fun z : Euclidean 3 =>
        ftildePsi ‖z‖ ^ 2 * ftildeDir z a * ftildeV (ftildeDir z) i +
          ftildePsi ‖z‖ * ftildeD a i (ftildeDir z)) x :=
    (((hpsi_cont.pow 2).mul hdir_coord_cont).mul hV_cont).add (hpsi_cont.mul hD_cont)
  apply hrhs.congr_of_eventuallyEq
  have hopen : IsOpen (Metric.ball (0 : Euclidean 3) 1 \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  filter_upwards [hopen.mem_nhds ⟨by simpa using hx1, hx⟩] with z hz
  exact coordinatePartial_ftildeF hz.2 (by simpa using hz.1) i a

lemma continuousAt_coordinatePartial_ftildeW_of_ne_zero {x : Euclidean 3}
    (hx : x ≠ 0) (hx1 : ‖x‖ < 1) (i a : Fin 3) :
    ContinuousAt (fun z => coordinatePartial (fun y => ftildeW y i) z a) x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hθ : ftildeDir x ≠ 0 := ftildeDir_ne_zero hx
  have hnorm_cont : ContinuousAt (fun z : Euclidean 3 => ‖z‖) x := continuous_norm.continuousAt
  have hpsi_cont : ContinuousAt (fun z : Euclidean 3 => ftildePsi ‖z‖) x :=
    (hasDerivAt_ftildePsi hr hx1).continuousAt.comp hnorm_cont
  have hJ_cont : ContinuousAt (fun z : Euclidean 3 => ftildeJ ‖z‖) x :=
    (hasDerivAt_ftildeJ hr hx1).continuousAt.comp hnorm_cont
  have hdir_cont : ContinuousAt ftildeDir x := (differentiableAt_ftildeDir hx).continuousAt
  have hdir_coord_cont : ContinuousAt (fun z : Euclidean 3 => ftildeDir z a) x :=
    (differentiableAt_ftildeDir_coordinate hx a).continuousAt
  have hAux_cont : ContinuousAt (fun z : Euclidean 3 => ftildeWAux i (ftildeDir z)) x :=
    ((contDiffOn_ftildeWAux (r := 0) i).continuousOn.continuousAt
      (isOpen_compl_singleton.mem_nhds hθ)).comp hdir_cont
  have hdAux_cont : ContinuousAt
      (fun z : Euclidean 3 => coordinatePartial (ftildeWAux i) (ftildeDir z) a) x :=
    ((continuousOn_coordinatePartial_ftildeWAux i a).continuousAt
      (isOpen_compl_singleton.mem_nhds hθ)).comp hdir_cont
  have hJr3 : ContinuousAt (fun z : Euclidean 3 => ftildeJ ‖z‖ / ‖z‖ ^ 3) x :=
    hJ_cont.div (hnorm_cont.pow 3) (pow_ne_zero 3 hr.ne')
  have h2Jr3 : ContinuousAt (fun z : Euclidean 3 => 2 * ftildeJ ‖z‖ / ‖z‖ ^ 3) x :=
    (continuousAt_const.mul hJ_cont).div (hnorm_cont.pow 3) (pow_ne_zero 3 hr.ne')
  have hrhs : ContinuousAt
      (fun z : Euclidean 3 =>
        coordinatePartial (ftildeWAux i) (ftildeDir z) a * (ftildeJ ‖z‖ / ‖z‖ ^ 3) +
          ftildeWAux i (ftildeDir z) *
            (ftildePsi ‖z‖ ^ 2 - 2 * ftildeJ ‖z‖ / ‖z‖ ^ 3) * ftildeDir z a) x :=
    (hdAux_cont.mul hJr3).add ((hAux_cont.mul ((hpsi_cont.pow 2).sub h2Jr3)).mul hdir_coord_cont)
  apply hrhs.congr_of_eventuallyEq
  have hopen : IsOpen (Metric.ball (0 : Euclidean 3) 1 \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  filter_upwards [hopen.mem_nhds ⟨by simpa using hx1, hx⟩] with z hz
  exact coordinatePartial_ftildeW hz.2 (by simpa using hz.1) i a

lemma tendsto_coordinatePartial_ftildeF_nhdsNE_zero (i a : Fin 3) :
    Filter.Tendsto (fun z => coordinatePartial (fun y => ftildeF y i) z a) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨CV, hCV, hbV⟩ := exists_bound_on_unit_sphere
    (contDiffOn_ftildeV_coordinate (r := 0) i).continuousOn
  obtain ⟨CD, hCD, hbD⟩ := exists_bound_on_unit_sphere (continuousOn_ftildeD a i)
  apply tendsto_zero_of_abs_le_psi_nhdsNE_zero CD CV
  intro x hx hx1
  have hnorm : ‖ftildeDir x‖ = 1 := norm_ftildeDir hx
  have hpsi : 0 ≤ ftildePsi ‖x‖ := ftildePsi_nonneg ‖x‖
  rw [coordinatePartial_ftildeF hx hx1 i a]
  have h1 : |ftildePsi ‖x‖ ^ 2 * ftildeDir x a * ftildeV (ftildeDir x) i| ≤
      CV * ftildePsi ‖x‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hdir := abs_ftildeDir_le_one hx a
    have hdv : |ftildeDir x a| * |ftildeV (ftildeDir x) i| ≤ 1 * CV :=
      mul_le_mul hdir (hbV _ hnorm) (abs_nonneg _) zero_le_one
    calc
      ftildePsi ‖x‖ ^ 2 * |ftildeDir x a| * |ftildeV (ftildeDir x) i| =
          ftildePsi ‖x‖ ^ 2 * (|ftildeDir x a| * |ftildeV (ftildeDir x) i|) := by ring
      _ ≤ ftildePsi ‖x‖ ^ 2 * (1 * CV) :=
        mul_le_mul_of_nonneg_left hdv (sq_nonneg _)
      _ = CV * ftildePsi ‖x‖ ^ 2 := by ring
  have h2 : |ftildePsi ‖x‖ * ftildeD a i (ftildeDir x)| ≤ CD * ftildePsi ‖x‖ := by
    rw [abs_mul, abs_of_nonneg hpsi, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbD _ hnorm) hpsi
  calc
    |ftildePsi ‖x‖ ^ 2 * ftildeDir x a * ftildeV (ftildeDir x) i +
        ftildePsi ‖x‖ * ftildeD a i (ftildeDir x)| ≤
        |ftildePsi ‖x‖ ^ 2 * ftildeDir x a * ftildeV (ftildeDir x) i| +
          |ftildePsi ‖x‖ * ftildeD a i (ftildeDir x)| := abs_add_le _ _
    _ ≤ CV * ftildePsi ‖x‖ ^ 2 + CD * ftildePsi ‖x‖ := add_le_add h1 h2
    _ = CD * ftildePsi ‖x‖ + CV * ftildePsi ‖x‖ ^ 2 := add_comm _ _

lemma tendsto_coordinatePartial_ftildeW_nhdsNE_zero (i a : Fin 3) :
    Filter.Tendsto (fun z => coordinatePartial (fun y => ftildeW y i) z a) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨CA, hCA, hbA⟩ := exists_bound_on_unit_sphere
    (contDiffOn_ftildeWAux (r := 0) i).continuousOn
  obtain ⟨CdA, hCdA, hbdA⟩ := exists_bound_on_unit_sphere
    (continuousOn_coordinatePartial_ftildeWAux i a)
  apply tendsto_zero_of_abs_le_psi_nhdsNE_zero 0 (CdA + 3 * CA)
  intro x hx hx1
  have hnorm : ‖ftildeDir x‖ = 1 := norm_ftildeDir hx
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hJn : 0 ≤ ftildeJ ‖x‖ := ftildeJ_nonneg hr
  have hJb : ftildeJ ‖x‖ ≤ ftildePsi ‖x‖ ^ 2 * ‖x‖ ^ 3 := ftildeJ_le_psi_sq_mul_cube hr hx1
  have hJr3_nn : 0 ≤ ftildeJ ‖x‖ / ‖x‖ ^ 3 := div_nonneg hJn (pow_nonneg hr.le 3)
  have hJr3_le : ftildeJ ‖x‖ / ‖x‖ ^ 3 ≤ ftildePsi ‖x‖ ^ 2 :=
    (div_le_iff₀ (pow_pos hr 3)).mpr hJb
  rw [coordinatePartial_ftildeW hx hx1 i a]
  have h1 : |coordinatePartial (ftildeWAux i) (ftildeDir x) a * (ftildeJ ‖x‖ / ‖x‖ ^ 3)| ≤
      CdA * ftildePsi ‖x‖ ^ 2 := by
    rw [abs_mul, abs_of_nonneg hJr3_nn]
    exact mul_le_mul (hbdA _ hnorm) hJr3_le hJr3_nn hCdA
  have hrad : |ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3| ≤ 3 * ftildePsi ‖x‖ ^ 2 := by
    have h2 : 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3 = 2 * (ftildeJ ‖x‖ / ‖x‖ ^ 3) := by ring
    rw [h2, abs_le]
    constructor <;> nlinarith [sq_nonneg (ftildePsi ‖x‖)]
  have h2 : |ftildeWAux i (ftildeDir x) *
      (ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) * ftildeDir x a| ≤
      3 * CA * ftildePsi ‖x‖ ^ 2 := by
    rw [abs_mul, abs_mul]
    have hdir := abs_ftildeDir_le_one hx a
    have hm1 : |ftildeWAux i (ftildeDir x)| *
        |ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3| ≤
        CA * (3 * ftildePsi ‖x‖ ^ 2) :=
      mul_le_mul (hbA _ hnorm) hrad (abs_nonneg _) hCA
    calc
      |ftildeWAux i (ftildeDir x)| *
          |ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3| * |ftildeDir x a| ≤
          (CA * (3 * ftildePsi ‖x‖ ^ 2)) * 1 :=
        mul_le_mul hm1 hdir (abs_nonneg _) (by positivity)
      _ = 3 * CA * ftildePsi ‖x‖ ^ 2 := by ring
  calc
    |coordinatePartial (ftildeWAux i) (ftildeDir x) a * (ftildeJ ‖x‖ / ‖x‖ ^ 3) +
        ftildeWAux i (ftildeDir x) *
          (ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) * ftildeDir x a| ≤
        |coordinatePartial (ftildeWAux i) (ftildeDir x) a * (ftildeJ ‖x‖ / ‖x‖ ^ 3)| +
          |ftildeWAux i (ftildeDir x) *
            (ftildePsi ‖x‖ ^ 2 - 2 * ftildeJ ‖x‖ / ‖x‖ ^ 3) * ftildeDir x a| := abs_add_le _ _
    _ ≤ CdA * ftildePsi ‖x‖ ^ 2 + 3 * CA * ftildePsi ‖x‖ ^ 2 := add_le_add h1 h2
    _ = 0 * ftildePsi ‖x‖ + (CdA + 3 * CA) * ftildePsi ‖x‖ ^ 2 := by ring

lemma contDiffOn_ball_of_zero_and_punctured {G : VectorField}
    (hd0 : HasFDerivAt G (0 : Euclidean 3 →L[ℝ] Euclidean 3) 0)
    (hdiff : ∀ x : Euclidean 3, x ≠ 0 → ‖x‖ < 1 →
      ∀ i : Fin 3, DifferentiableAt ℝ (fun y => G y i) x)
    (hcont : ∀ x : Euclidean 3, x ≠ 0 → ‖x‖ < 1 →
      ∀ i a : Fin 3, ContinuousAt (fun z => coordinatePartial (fun y => G y i) z a) x)
    (hlim : ∀ i a : Fin 3,
      Filter.Tendsto (fun z => coordinatePartial (fun y => G y i) z a) (𝓝[≠] 0) (𝓝 0)) :
    ContDiffOn ℝ 1 G ftildeBall := by
  have hopen : IsOpen ftildeBall := Metric.isOpen_ball
  apply (Chapter09.pma9_20 hopen).mp
  apply (Chapter09.pma9_21 hopen).mpr
  refine ⟨?_, ?_⟩
  · intro x hx i a
    by_cases hx0 : x = 0
    · subst x
      exact ⟨0, by simpa using Chapter09.pma9_17 hd0 i a⟩
    · have hx1 : ‖x‖ < 1 := by simpa [ftildeBall] using hx
      have hGx : DifferentiableAt ℝ G x := by
        rw [differentiableAt_piLp]
        exact hdiff x hx0 hx1
      exact ⟨_, Chapter09.pma9_17 hGx.hasFDerivAt i a⟩
  · intro i a x hx
    apply ContinuousAt.continuousWithinAt
    change ContinuousAt (fun z => coordinatePartial (fun y => G y i) z a) x
    by_cases hx0 : x = 0
    · subst x
      have hp0 : coordinatePartial (fun y => G y i) 0 a = 0 := by
        change Chapter09.pma9_16_partial G 0 i a = 0
        simpa using Chapter09.pma9_17_entries hd0 i a
      rw [continuousAt_iff_punctured_nhds, hp0]
      exact hlim i a
    · exact hcont x hx0 (by simpa [ftildeBall] using hx) i a

theorem contDiffOn_ftildeF : ContDiffOn ℝ 1 ftildeF ftildeBall :=
  contDiffOn_ball_of_zero_and_punctured hasFDerivAt_ftildeF_zero
    (fun _ hx hx1 i => differentiableAt_ftildeF_coordinate hx hx1 i)
    (fun _ hx hx1 i a => continuousAt_coordinatePartial_ftildeF_of_ne_zero hx hx1 i a)
    tendsto_coordinatePartial_ftildeF_nhdsNE_zero

theorem contDiffOn_ftildeW : ContDiffOn ℝ 1 ftildeW ftildeBall :=
  contDiffOn_ball_of_zero_and_punctured hasFDerivAt_ftildeW_zero
    (fun _ hx hx1 i => differentiableAt_ftildeW_coordinate hx hx1 i)
    (fun _ hx hx1 i a => continuousAt_coordinatePartial_ftildeW_of_ne_zero hx hx1 i a)
    tendsto_coordinatePartial_ftildeW_nhdsNE_zero

theorem contDiffOn_ftildeField : ContDiffOn ℝ 1 ftildeField ftildeBall :=
  contDiffOn_ftildeF.add contDiffOn_ftildeW

lemma divergence_ftildeField_zero : divergence ftildeField 0 = 0 := by
  have hd0 : HasFDerivAt ftildeField (0 : Euclidean 3 →L[ℝ] Euclidean 3) 0 := by
    have hadd := hasFDerivAt_ftildeF_zero.add hasFDerivAt_ftildeW_zero
    rw [add_zero] at hadd
    exact hadd
  rw [divergence]
  apply Finset.sum_eq_zero
  intro i _
  change Chapter09.pma9_16_partial ftildeField 0 i i = 0
  simpa using Chapter09.pma9_17_entries hd0 i i

theorem divergence_ftildeField_eqOn_zero :
    EqOn (divergence ftildeField) 0 ftildeBall := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    exact divergence_ftildeField_zero
  · exact divergence_ftildeField_of_ne_zero hx0 (by simpa [ftildeBall] using hx)

/-- (A) WITNESS LEMMA (the Lean target, in repo vocabulary; 14:53 §1).
    The domain, C¹, and divergence-free clauses are proved below (Stages 1–2).
    The single remaining sorry covers the no-symmetric-system clause (Stages 3–4). -/
theorem ftilde_witness :
    IsOpen ftildeBall ∧ Convex ℝ ftildeBall ∧
    ContDiffOn ℝ 1 ftildeField ftildeBall ∧
    EqOn (divergence ftildeField) 0 ftildeBall ∧
    ¬ SymmetricCurlSystem ftildeBall ftildeField := by
  refine ⟨Metric.isOpen_ball, convex_ball 0 1,
    contDiffOn_ftildeField, divergence_ftildeField_eqOn_zero, ?_⟩
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
