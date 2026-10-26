import Rudin.PMA.Chapter10Audit
import Rudin.PMA.Chapter10.SecondHalfAudit
import Rudin.PMA.AxiomAudit
import Rudin.PMA.Chapter09
import Rudin.PMA.Chapter09.SecondHalf

/-!
Integration gate for Chapter 10 against the merged Chapter 8/9 tree.
All 51 numbered contracts must be present, but only 50 principal theorems:
10.43's final C² vector-potential clause is explicitly unproved. Its proved
forward identities, C² scalar converse, and weaker C¹ vector-potential theorem
are retained and audited without claiming the missing clause.

The two imported audits retain all principal-to-contract comparisons. This
additional gate checks their combined module closure and audits every chapter
module by source ownership, including generated and private declarations.
-/

namespace Rudin.PMA.Chapter10.IntegrationContractComparators
open Chapter09 Set Function

-- Keep the missing C² vector-potential conclusion explicit without asserting it.
example : pma10_43_contract ↔
    (∀ (E : Set (Euclidean 3)) (u : Euclidean 3 → ℝ),
      IsOpen E → ContDiffOn ℝ 2 u E → EqOn (curl (gradient u)) 0 E) ∧
    (∀ (E : Set (Euclidean 3)) (G : VectorField),
      IsOpen E → ContDiffOn ℝ 2 G E → EqOn (divergence (curl G)) 0 E) ∧
    (∀ (U E : Set (Euclidean 3)) (e : C2DomainEquivalence U E) (F : VectorField),
      IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E → EqOn (curl F) 0 E →
        ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) F E) ∧
    (∀ (U E : Set (Euclidean 3)) (e : C2DomainEquivalence U E) (F : VectorField),
      IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E → EqOn (divergence F) 0 E →
        ∃ G : VectorField, ContDiffOn ℝ 2 G E ∧ EqOn (curl G) F E) := Iff.rfl

example :
    (∀ (E : Set (Euclidean 3)) (u : Euclidean 3 → ℝ),
      IsOpen E → ContDiffOn ℝ 2 u E → EqOn (curl (gradient u)) 0 E) ∧
    (∀ (E : Set (Euclidean 3)) (G : VectorField),
      IsOpen E → ContDiffOn ℝ 2 G E → EqOn (divergence (curl G)) 0 E) :=
  pma10_43_forward

example : ∀ (U E : Set (Euclidean 3)) (e : C2DomainEquivalence U E) (F : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E → EqOn (curl F) 0 E →
      ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) F E :=
  pma10_43_scalar_converse

-- This comparison intentionally checks C¹ output, not the unresolved C² clause.
example {U E : Set (Euclidean 3)} (e : C2DomainEquivalence U E)
    (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U) {F : VectorField}
    (hF : ContDiffOn ℝ 1 F E) (hz : EqOn (divergence F) 0 E) :
    ∃ G : VectorField, ContDiffOn ℝ 1 G E ∧ EqOn (curl G) F E :=
  vectorPotential_c1_of_equivalent_convex e hU hE hc hF hz

end Rudin.PMA.Chapter10.IntegrationContractComparators

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut required : Array Name := #[]
  for i in List.range 51 do
    let node := i + 1
    let contract := Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString node ++ "_contract")
    match env.find? contract with
    | some (.defnInfo _) => required := required.push contract
    | _ => throwError "Missing Chapter 10 numbered contract: {contract}"
    let principal := Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString node)
    if node == 43 then
      if (env.find? principal).isSome then
        throwError "PMA 10.43 is incomplete: its principal must remain absent."
    else
      match env.find? principal with
      | some (.thmInfo _) => required := required.push principal
      | _ => throwError "Missing Chapter 10 principal theorem: {principal}"
  for name in #[`Rudin.PMA.Chapter10.pma10_43_forward,
      `Rudin.PMA.Chapter10.pma10_43_scalar_converse,
      `Rudin.PMA.Chapter10.vectorPotential_c1_of_equivalent_convex,
      `Rudin.PMA.Chapter10.pma10_8_complex_corollary,
      `Rudin.PMA.Chapter10.pma10_12_geometry,
      `Rudin.PMA.Chapter10.pma10_19_xdy_derivative,
      `Rudin.PMA.Chapter10.pma10_19_dxdy_not_formEqOn_zero,
      `Rudin.PMA.Chapter10.pma10_26_relativeOrientation] do
    match env.find? name with
    | some (.thmInfo _) => required := required.push name
    | _ => throwError "Missing retained Chapter 10 partial or supplementary theorem: {name}"
  required := required.push `Rudin.PMA.Chapter10.pma10_26_relativeOrientation_contract
  let probes := #[
    `Rudin.PMA.Chapter10.BoundaryExamplesProbes,
    `Rudin.PMA.Chapter10.CellTriangulationProbes,
    `Rudin.PMA.Chapter10.ChangeOfVariablesProbes,
    `Rudin.PMA.Chapter10.ClassicalCalculusProbes,
    `Rudin.PMA.Chapter10.ClosedFormProbes,
    `Rudin.PMA.Chapter10.ConvexExactnessProbes,
    `Rudin.PMA.Chapter10.ConvexPrimitiveProbes,
    `Rudin.PMA.Chapter10.ExteriorDerivativeProbes,
    `Rudin.PMA.Chapter10.FormAlgebraProbes,
    `Rudin.PMA.Chapter10.FormProbes,
    `Rudin.PMA.Chapter10.IntegrationProbes,
    `Rudin.PMA.Chapter10.PartitionProbes,
    `Rudin.PMA.Chapter10.PositiveBoundaryProbes,
    `Rudin.PMA.Chapter10.PrimitiveProbes,
    `Rudin.PMA.Chapter10.PullbackProbes,
    `Rudin.PMA.Chapter10.PuncturedProbes,
    `Rudin.PMA.Chapter10.ScalarPotentialProbes,
    `Rudin.PMA.Chapter10.SimplexChainProbes,
    `Rudin.PMA.Chapter10.SimplexProbes,
    `Rudin.PMA.Chapter10.SphereExampleProbes,
    `Rudin.PMA.Chapter10.StokesProbes,
    `Rudin.PMA.Chapter10.TorusProbes,
    `Rudin.PMA.Chapter10.VectorFieldProbes,
    `Rudin.PMA.Chapter10.VectorIntegrationProbes,
    `Rudin.PMA.Chapter10.VolumeAreaProbes]
  for probe in probes do
    if (env.getModuleIdx? probe).isNone then
      throwError "Missing Chapter 10 probe module: {probe}"
  logInfo m!"Chapter 10 integration coverage: 51 contracts, 50 principal theorems, {probes.size} probe modules; 10.43 final C² clause incomplete."
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10 required
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10Audit (allowEmpty := true)

-- Supplement the merged chapter's legacy namespace audits without changing its source.
run_cmd do
  Lean.logInfo "Supplementary merged Chapter 9 production audit by source-module ownership."
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter09
    #[`Rudin.PMA.Chapter09.pma9_1_span_iff,
      `Rudin.PMA.Chapter09.pma9_22,
      `Rudin.PMA.Chapter09.pma9_43]
