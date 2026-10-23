import Rudin.PMA.Chapter10.Flux

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def lineCollapse : Coord 2 →L[ℝ] Euclidean 3 :=
  ((ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ) +
    ContinuousLinearMap.proj 1).smulRight (coordinateVector 3 0)

private lemma lineCollapse_normal_zero (C : Cell 2) (p : Euclidean 3) (u : Coord 2) :
    surfaceNormal (affineRectangleSurface C p lineCollapse) u = 0 := by
  rw [surfaceNormal_affineRectangle]
  ext i
  fin_cases i <;> simp [lineCollapse, cross3, ContinuousLinearMap.smulRight_apply,
    coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply]

private def stationaryCurve (c : Euclidean 3) : Surface 1 3 univ where
  domain := .cell (Cell.unit 1)
  map := fun _ => c
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := contDiffOn_const
  mapsTo := mapsTo_univ _ _

/-- At zero speed the normalized tangent still exists, but both weighted
circulation and Chapter6 length vanish. No ambient regularity of F is used. -/
theorem stationary_curve_weighted_integral (c : Euclidean 3) (F : VectorField) :
    (stationaryCurve c).domain.Integrable (fun u =>
      inner ℝ (F c) (curveUnitTangent (stationaryCurve c) u) *
        ‖curveVelocity (stationaryCurve c) u‖) ∧
    circulation (stationaryCurve c) F = 0 ∧
    Chapter06.CurveLength (stationaryCurve c).toCurve.map 0 1 = 0 := by
  have hc : ContinuousOn F ((stationaryCurve c).map '' (stationaryCurve c).domain.carrier) := by
    apply (continuousOn_const (c := F c)).congr
    rintro x ⟨u, hu, rfl⟩
    rfl
  have h := pma10_48.2.1 univ (stationaryCurve c) F hc
  have hv : curveVelocity (stationaryCurve c) = fun _ => (0 : Euclidean 3) := by
    funext u
    simp [curveVelocity, stationaryCurve]
  have hz : (stationaryCurve c).domain.integral (fun _ => (0 : ℝ)) = 0 := by
    rw [ParameterDomain.integral_eq_setIntegral continuousOn_const]
    simp
  refine ⟨h.2.2.2.2.1, ?_, ?_⟩
  · unfold circulation circulationIntegrand
    rw [hv]
    simpa using hz
  · have hl := (pma10_48.2.2 univ (stationaryCurve c) (Cell.unit 1) rfl).2
    rw [hv] at hl
    change Chapter06.CurveLength (stationaryCurve c).toCurve.map 0 1 = _ at hl
    simpa only [norm_zero, hz, ENNReal.ofReal_zero] using hl

/-- The rank-one surface has zero actual native flux for every field
continuous on its image; a unit fallback cannot create spurious flux. -/
theorem line_collapse_native_flux_zero (C : Cell 2) (p : Euclidean 3)
    (F : VectorField)
    (hF : ContinuousOn F ((affineRectangleSurface C p lineCollapse).map ''
      (affineRectangleSurface C p lineCollapse).domain.carrier)) :
    (affineRectangleSurface C p lineCollapse).domain.Integrable
      (fluxIntegrand (affineRectangleSurface C p lineCollapse) F) ∧
    flux (affineRectangleSurface C p lineCollapse) F = 0 := by
  have h := pma10_49 univ (affineRectangleSurface C p lineCollapse) F hF
  refine ⟨h.2.2.1, ?_⟩
  have hz : fluxIntegrand (affineRectangleSurface C p lineCollapse) F = fun _ => 0 := by
    funext u
    simp [fluxIntegrand, lineCollapse_normal_zero]
  unfold flux
  rw [hz, ParameterDomain.integral_eq_setIntegral continuousOn_const]
  simp

end Rudin.PMA.Chapter10.FidelityProbes
