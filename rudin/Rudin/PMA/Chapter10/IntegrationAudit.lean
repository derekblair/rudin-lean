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
  -- Retain an owned declaration from every contributing proof/probe module.
  required := required ++ #[
    `Rudin.PMA.Chapter10.AffineSimplexIn,
    `Rudin.PMA.Chapter10.standardFaceAffine,
    `Rudin.PMA.Chapter10.HasAffineRelativeOrientation,
    `Rudin.PMA.Chapter10.vertexLinear,
    `Rudin.PMA.Chapter10.puncturedSpace_isOpen,
    `Rudin.PMA.Chapter10.cross3,
    `Rudin.PMA.Chapter10.pma10_31_contract,
    `Rudin.PMA.Chapter10.FidelityProbes.sphere_continuous_absolute_coefficient,
    `Rudin.PMA.Chapter10.Cell.delete,
    `Rudin.PMA.Chapter10.cellFaceLinear,
    `Rudin.PMA.Chapter10.surfaceIntegral_density_eq_image_of_interior_inj,
    `Rudin.PMA.Chapter10.cellNormalize_image,
    `Rudin.PMA.Chapter10.cellNormalize,
    `Rudin.PMA.Chapter10.cellStaircase_affine,
    `Rudin.PMA.Chapter10.FidelityProbes.collapsed_cell_staircase_chain_zero,
    `Rudin.PMA.Chapter10.affineMap_euclidean_contDiff,
    `Rudin.PMA.Chapter10.pma10_33,
    `Rudin.PMA.Chapter10.coordinateJacobian,
    `Rudin.PMA.Chapter10.FidelityProbes.reflection_negative_jacobian,
    `Rudin.PMA.Chapter10.directionWithFallback,
    `Rudin.PMA.Chapter10.FidelityProbes.rank_one_cell_boundary_circulation,
    `Rudin.PMA.Chapter10.chainCirculation,
    `Rudin.PMA.Chapter10.IsExactOn,
    `Rudin.PMA.Chapter10.pma10_35_contract,
    `Rudin.PMA.Chapter10.FidelityProbes.C1_primitive_surface_boundary_integral,
    `Rudin.PMA.Chapter10.coefficientIntegral,
    `Rudin.PMA.Chapter10.contractCoordinate,
    `Rudin.PMA.Chapter10.coefficientsDifferentiableAt_linearMap,
    `Rudin.PMA.Chapter10.FidelityProbes.convex_closed_two_form_cycle_zero,
    `Rudin.PMA.Chapter10.exists_contDiffOn_linear_section,
    `Rudin.PMA.Chapter10.sectionSegment,
    `Rudin.PMA.Chapter10.FidelityProbes.slantedStrip,
    `Rudin.PMA.Chapter10.pma10_38_contract,
    `Rudin.PMA.Chapter10.exists_contDiffOn_convex_section,
    `Rudin.PMA.Chapter10.coordinatePartial_const,
    `Rudin.PMA.Chapter10.cellRIntegral_congr,
    `Rudin.PMA.Chapter10.cumulativeCoordinates,
    `Rudin.PMA.Chapter10.pma10_40_contract,
    `Rudin.PMA.Chapter10.exteriorDerivative_vectorTwoForm_density,
    `Rudin.PMA.Chapter10.exteriorDerivative_coordinateOneForm,
    `Rudin.PMA.Chapter10.ParameterDomain.one_integral_eq_intervalIntegral,
    `Rudin.PMA.Chapter10.ClosedFormsExactOn,
    `Rudin.PMA.Chapter10.exteriorDerivative,
    `Rudin.PMA.Chapter10.FidelityProbes.scalar_differential_on_mixed_tangent,
    `Rudin.PMA.Chapter10.CoefficientsDifferentiableAt,
    `Rudin.PMA.Chapter10.surfaceUnitNormal,
    `Rudin.PMA.Chapter10.FidelityProbes.nonsorted_two_form_product,
    `Rudin.PMA.Chapter10.smooth_approximation_on_compact,
    `Rudin.PMA.Chapter10.ParameterDomain.Integrable,
    `Rudin.PMA.Chapter10.ellipseScaling,
    `Rudin.PMA.Chapter10.coordinateOneForm,
    `Rudin.PMA.Chapter10.Surface.coefficientWeight,
    `Rudin.PMA.Chapter10.ParameterDomain.isClosed,
    `Rudin.PMA.Chapter10.FidelityProbes.point_zero_form_nonzero_value,
    `Rudin.PMA.Chapter10.formCoefficient_fromCoefficients,
    `Rudin.PMA.Chapter10.pma10_15_contract,
    `Rudin.PMA.Chapter10.StandardIndex,
    `Rudin.PMA.Chapter10.CotangentExterior,
    `Rudin.PMA.Chapter10.Coord,
    `Rudin.PMA.Chapter10.Cell.measure,
    `Rudin.PMA.Chapter10.FidelityProbes.collapsed_first_side_integral,
    `Rudin.PMA.Chapter10.Cell.isCompact_carrier,
    `Rudin.PMA.Chapter10.iteratedRIntegral_pos,
    `Rudin.PMA.Chapter10.exteriorBasis_singleton,
    `Rudin.PMA.Chapter10.compact_parameter_local_bound,
    `Rudin.PMA.Chapter10.pma10_8_contract,
    `Rudin.PMA.Chapter10.pma10_8_complex_corollary,
    `Rudin.PMA.Chapter10.FidelityProbes.empty_cover_partition,
    `Rudin.PMA.Chapter10.regionIntegral,
    `Rudin.PMA.Chapter10.pma10_39_contract,
    `Rudin.PMA.Chapter10.PositiveSimplex.boundary,
    `Rudin.PMA.Chapter10.FidelityProbes.cubic_positive_boundary_with_singular_endpoint,
    `Rudin.PMA.Chapter10.PositiveSimplex.coordinateCarrier_preimage,
    `Rudin.PMA.Chapter10.standardSimplex_interior_nonempty,
    `Rudin.PMA.Chapter10.contDiffOn_two_of_coordinatePartials,
    `Rudin.PMA.Chapter10.prefixIndex,
    `Rudin.PMA.Chapter10.Euclidean,
    `Rudin.PMA.Chapter10.primitiveMap,
    `Rudin.PMA.Chapter10.FidelityProbes.dimension_one_has_no_flip,
    `Rudin.PMA.Chapter10.covectorPullback,
    `Rudin.PMA.Chapter10.pma10_21,
    `Rudin.PMA.Chapter10.exteriorDerivative_congr_of_eqOn,
    `Rudin.PMA.Chapter10.evaluateForm_pullback,
    `Rudin.PMA.Chapter10.FidelityProbes.constant_pullback_one_form_and_scalar,
    `Rudin.PMA.Chapter10.IsCFormOn.congr,
    `Rudin.PMA.Chapter10.pma10_21_contract,
    `Rudin.PMA.Chapter10.puncturedSpace,
    `Rudin.PMA.Chapter10.puncturedCircleMap_contDiff,
    `Rudin.PMA.Chapter10.FidelityProbes.nonzero_circle_multiplicity_not_boundary,
    `Rudin.PMA.Chapter10.sphereRectangleMap_norm,
    `Rudin.PMA.Chapter10.radial_denominator_eq_rpow,
    `Rudin.PMA.Chapter10.radialHomotopyIntegrand,
    `Rudin.PMA.Chapter10.intervalIntegrable_linear_exteriorDerivative,
    `Rudin.PMA.Chapter10.squareTriangleMap_contDiff_order,
    `Rudin.PMA.Chapter10.rectangleEdgeCell,
    `Rudin.PMA.Chapter10.cellRIntegral_two_eq_doubleIntegral,
    `Rudin.PMA.Chapter10.exteriorBasis_empty,
    `Rudin.PMA.Chapter10.FidelityProbes.scalar_potential_C2_hessian,
    `Rudin.PMA.Chapter10.stoppedSlice_setIntegral,
    `Rudin.PMA.Chapter10.C2Simplex.face,
    `Rudin.PMA.Chapter10.C2Simplex.face_face,
    `Rudin.PMA.Chapter10.FidelityProbes.origin_moving_transposition_reverses_integral,
    `Rudin.PMA.Chapter10.C2Simplex,
    `Rudin.PMA.Chapter10.simplexRIntegral_comp_of_abs_det_one,
    `Rudin.PMA.Chapter10.mem_standardSimplex_insertNth,
    `Rudin.PMA.Chapter10.evaluateForm_dx_coordinateWedge,
    `Rudin.PMA.Chapter10.simplexVertexPermutation,
    `Rudin.PMA.Chapter10.FidelityProbes.simplex_extension_boundary_jump,
    `Rudin.PMA.Chapter10.simplexSeparation_contract,
    `Rudin.PMA.Chapter10.rIntegrable_congr,
    `Rudin.PMA.Chapter10.standardSimplexStokes_contract,
    `Rudin.PMA.Chapter10.sphereRectangleCell,
    `Rudin.PMA.Chapter10.FidelityProbes.sphere_boundary_identification,
    `Rudin.PMA.Chapter10.contDiff_sphericalMap,
    `Rudin.PMA.Chapter10.squareTriangleMap,
    `Rudin.PMA.Chapter10.squareRIntegral_eq_doubleIntegral,
    `Rudin.PMA.Chapter10.coordinatePermutation,
    `Rudin.PMA.Chapter10.staircaseChamber_isCompact,
    `Rudin.PMA.Chapter10.rawTwoForm,
    `Rudin.PMA.Chapter10.standardC2Simplex,
    `Rudin.PMA.Chapter10.omittedCoefficient,
    `Rudin.PMA.Chapter10.FidelityProbes.stokes_folded_triangle_negative_multiplicity,
    `Rudin.PMA.Chapter10.C2Simplex.euclideanNeighborhood,
    `Rudin.PMA.Chapter10.Surface.asSimplex,
    `Rudin.PMA.Chapter10.surfaceDomain_standardSimplex_subset_unit,
    `Rudin.PMA.Chapter10.Surface.targetNeighborhood,
    `Rudin.PMA.Chapter10.Surface.precompose,
    `Rudin.PMA.Chapter10.pma10_23,
    `Rudin.PMA.Chapter10.ParameterDomain,
    `Rudin.PMA.Chapter10.torusCell,
    `Rudin.PMA.Chapter10.cellFaceMap_three_zero,
    `Rudin.PMA.Chapter10.torusSolidSurface_isC2,
    `Rudin.PMA.Chapter10.torus_revolution_radius_pos,
    `Rudin.PMA.Chapter10.FidelityProbes.inner_torus_face_absolute_coefficient,
    `Rudin.PMA.Chapter10.pma10_47,
    `Rudin.PMA.Chapter10.densityForm_one_three,
    `Rudin.PMA.Chapter10.FidelityProbes.cyclic_middle_form_positive_vector,
    `Rudin.PMA.Chapter10.VectorField,
    `Rudin.PMA.Chapter10.vectorOneForm_gradient,
    `Rudin.PMA.Chapter10.FidelityProbes.stationary_curve_weighted_integral,
    `Rudin.PMA.Chapter10.pma10_43_contract,
    `Rudin.PMA.Chapter10.FidelityProbes.image_indicator_native_volume,
    `Rudin.PMA.Chapter10.standardVolume,
    `Rudin.PMA.Chapter10.crossInversionCount]
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10 required
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10Audit (allowEmpty := true)

-- Supplement the merged chapter's legacy namespace audits without changing its source.
run_cmd do
  Lean.logInfo "Supplementary merged Chapter 9 production audit by source-module ownership."
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter09
    #[`Rudin.PMA.Chapter09.pma9_1_span_iff,
      `Rudin.PMA.Chapter09.pma9_22,
      `Rudin.PMA.Chapter09.pma9_43]
