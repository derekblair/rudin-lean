/-
  Statement draft for rudin-lean issue #29 (SymmetricDerivativeLifting).
  PLACED 2026-10-31 ~17:53 PDT by the math orchestrator under Derek's
  2026-10-31 ~17:30 PDT standing-delegation clarification (routine
  pipeline placement + typecheck, not a new direction).
  STATUS: DRAFT, statement only. The (A) witness lemma `ftilde_witness`
  carries a `sorry` placeholder: that is the formalization work
  (stages 1-4), never a result. Nothing here is proved, and the pin
  manifest ~/workspace/math-fleet/pins/rudin29-ftilde-disproof.md stays
  DRAFT v0.1 until this file typechecks and its path + sha256 + commit
  are recorded there.
  Source: desk draft v3 (sha256
  4392009bf437d79067c3509bcc268064cfce87043879170f042cf11990974978),
  v2 + the single `open scoped BigOperators` placement line. Body
  unchanged from v3 except the import block below (v3 listed imports
  only as comments) and this header.
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
open scoped BigOperators
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

/-- v_n(θ) = Σ_a θ_a D_{a,n}(θ); q(θ) = θ · v(θ). max|q| = 1.369 (0923 §4). -/
def ftildeQ (θ : Euclidean 3) : ℝ :=
  ∑ n : Fin 3, θ n * (∑ a : Fin 3, θ a * ftildeD a n θ)

/-- J(r) = ∫₀^r ψ²(t)·t² dt. -/
def ftildeJ (r : ℝ) : ℝ := ∫ t in (0)..r, ftildePsi t ^ 2 * t ^ 2

/-- Repair: w(r,θ) = −q(θ)·J(r)/r²; W = w·θ; F̃ = F + W (0923 §3, 0953 §1).
    F̃ is the falsifying field; the literally-defined ψV field is NOT
    div-free (L3: div F = ψ²q). -/
def ftildeW : VectorField :=
  fun x => if x = 0 then 0 else
    (-(ftildeQ (ftildeDir x)) * ftildeJ ‖x‖ / ‖x‖ ^ 2) • ftildeDir x
def ftildeField : VectorField :=
  fun x => ftildeF x + ftildeW x

/-- (A) WITNESS LEMMA (the Lean target, in repo vocabulary; 14:53 §1).
    Stated, NOT proved: the sorry below is the formalization work
    (L1–L10, stages 1–4), never a result. -/
theorem ftilde_witness :
    IsOpen ftildeBall ∧ Convex ℝ ftildeBall ∧
    ContDiffOn ℝ 1 ftildeField ftildeBall ∧
    EqOn (divergence ftildeField) 0 ftildeBall ∧
    ¬ SymmetricCurlSystem ftildeBall ftildeField := by
  sorry

/-- (B) MAIN THEOREM: ¬ SymmetricDerivativeLifting, by negating the
    universal at the (A) witness; hence ¬ pma10_43_contract by the PR #28
    iff. The proof is logic over (A) once (A) is proved; it is written out
    (not sorry) so the layering is checkable, but it is UNTYPECHECKED. -/
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
