import Rudin.PMA.Chapter10.SecondHalf
import Rudin.PMA.Chapter10.SimplexChainProbes
import Rudin.PMA.Chapter10.BoundaryExamplesProbes
import Rudin.PMA.Chapter10.PositiveBoundaryProbes
import Rudin.PMA.Chapter10.StokesProbes
import Rudin.PMA.Chapter10.ClosedFormProbes
import Rudin.PMA.Chapter10.PuncturedProbes
import Rudin.PMA.Chapter10.ConvexPrimitiveProbes
import Rudin.PMA.Chapter10.ConvexExactnessProbes
import Rudin.PMA.Chapter10.CellTriangulationProbes
import Rudin.PMA.Chapter10.VectorFieldProbes
import Rudin.PMA.Chapter10.ScalarPotentialProbes
import Rudin.PMA.Chapter10.VolumeAreaProbes
import Rudin.PMA.Chapter10.TorusProbes
import Rudin.PMA.Chapter10.VectorIntegrationProbes
import Rudin.PMA.Chapter10.ClassicalCalculusProbes
import Rudin.PMA.AxiomAudit

set_option autoImplicit false

/-! Checks recovered second-half contracts and recursively audits all imported
Chapter 10 declarations. Node 10.43 is explicitly incomplete. -/

open Rudin.PMA.Chapter10
namespace Rudin.PMA.Chapter10.SecondHalfContractComparators
example : pma10_27_contract := pma10_27
example : pma10_28_contract := pma10_28
example : pma10_29_contract := pma10_29
example : pma10_30_contract := pma10_30
example : pma10_31_contract := pma10_31
example : pma10_32_contract := pma10_32
example : pma10_33_contract := pma10_33
example : pma10_34_contract := pma10_34
example : pma10_35_contract := pma10_35
example : pma10_36_contract := pma10_36
example : pma10_37_contract := pma10_37
example : pma10_38_contract := pma10_38
example : pma10_39_contract := pma10_39
example : pma10_40_contract := pma10_40
example : pma10_41_contract := pma10_41
example : pma10_42_contract := pma10_42
example : pma10_44_contract := pma10_44
example : pma10_45_contract := pma10_45
example : pma10_46_contract := pma10_46
example : pma10_47_contract := pma10_47
example : pma10_48_contract := pma10_48
example : pma10_49_contract := pma10_49
example : pma10_50_contract := pma10_50
example : pma10_51_contract := pma10_51
end Rudin.PMA.Chapter10.SecondHalfContractComparators

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for i in [27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 45, 46, 47, 48, 49, 50, 51] do
    let name := Lean.Name.str `Rudin.PMA.Chapter10 ("pma10_" ++ toString i)
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Missing second-half principal theorem: {name}"
  if (env.find? `Rudin.PMA.Chapter10.pma10_43).isSome then
    throwError "Unresolved PMA 10.43 must not be marked complete."
  logInfo "Second-half coverage: 24 principal theorems and contract comparisons; 10.43 incomplete."
  -- Source-module ownership also covers declarations emitted outside the chapter namespace.
  Rudin.PMA.Audit.checkModuleAxioms `Rudin.PMA.Chapter10 #[
    `Rudin.PMA.Chapter10.AffineSimplexIn,
    `Rudin.PMA.Chapter10.standardFaceAffine,
    `Rudin.PMA.Chapter10.pma10_26_relativeOrientation,
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
    `Rudin.PMA.Chapter10.pma10_19_xdy_derivative,
    `Rudin.PMA.Chapter10.ParameterDomain.one_integral_eq_intervalIntegral,
    `Rudin.PMA.Chapter10.ClosedFormsExactOn,
    `Rudin.PMA.Chapter10.exteriorDerivative,
    `Rudin.PMA.Chapter10.CoefficientsDifferentiableAt,
    `Rudin.PMA.Chapter10.surfaceUnitNormal,
    `Rudin.PMA.Chapter10.smooth_approximation_on_compact,
    `Rudin.PMA.Chapter10.ParameterDomain.Integrable,
    `Rudin.PMA.Chapter10.pma10_12_geometry,
    `Rudin.PMA.Chapter10.coordinateOneForm,
    `Rudin.PMA.Chapter10.Surface.coefficientWeight,
    `Rudin.PMA.Chapter10.ParameterDomain.isClosed,
    `Rudin.PMA.Chapter10.formCoefficient_fromCoefficients,
    `Rudin.PMA.Chapter10.pma10_15_contract,
    `Rudin.PMA.Chapter10.StandardIndex,
    `Rudin.PMA.Chapter10.CotangentExterior,
    `Rudin.PMA.Chapter10.Coord,
    `Rudin.PMA.Chapter10.Cell.measure,
    `Rudin.PMA.Chapter10.Cell.isCompact_carrier,
    `Rudin.PMA.Chapter10.iteratedRIntegral_pos,
    `Rudin.PMA.Chapter10.exteriorBasis_singleton,
    `Rudin.PMA.Chapter10.compact_parameter_local_bound,
    `Rudin.PMA.Chapter10.pma10_8_contract,
    `Rudin.PMA.Chapter10.pma10_8_complex_corollary,
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
    `Rudin.PMA.Chapter10.covectorPullback,
    `Rudin.PMA.Chapter10.pma10_21,
    `Rudin.PMA.Chapter10.exteriorDerivative_congr_of_eqOn,
    `Rudin.PMA.Chapter10.evaluateForm_pullback,
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
    `Rudin.PMA.Chapter10.simplexSeparation_contract,
    `Rudin.PMA.Chapter10.rIntegrable_congr,
    `Rudin.PMA.Chapter10.standardSimplexStokes_contract,
    `Rudin.PMA.Chapter10.sphereRectangleCell,
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
    `Rudin.PMA.Chapter10.pma10_43_forward,
    `Rudin.PMA.Chapter10.FidelityProbes.image_indicator_native_volume,
    `Rudin.PMA.Chapter10.standardVolume,
    `Rudin.PMA.Chapter10.crossInversionCount]
