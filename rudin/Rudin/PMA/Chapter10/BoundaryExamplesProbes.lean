import Rudin.PMA.Chapter10.SphereBoundary
import Rudin.PMA.Chapter10.SquareBoundaries

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def absoluteHeightForm : FormField 3 := fun x => |x 0| • dx 2

private lemma absoluteHeightForm_continuous : IsFormOn univ 1 absoluteHeightForm := by
  constructor
  · intro x hx
    apply Submodule.smul_mem
    rw [dx_eq_coordinateWedge]
    exact coordinateWedge_mem _
  · intro S
    change ContinuousOn (fun x : Euclidean 3 =>
      (exteriorBasis 3).repr (|x 0| • dx 2) S) univ
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (EuclideanSpace.proj 0 : Euclidean 3 →L[ℝ] ℝ).continuous.abs.continuousOn.mul
      continuousOn_const

/-- The sphere cancellation accepts the nonsmooth coefficient |x|. Its
one-form is nonzero, so this does not test cancellation on the zero form. -/
theorem sphere_continuous_absolute_coefficient :
    evaluateForm 1 (fun _ => coordinateVector 3 2)
      (absoluteHeightForm (coordinateVector 3 0)) = 1 ∧
    (∀ i : Fin 4, IteratedRIntegrable (rectangleEdgeCell sphereRectangleCell i)
      (surfaceIntegrand (rectangleEdgeSurface
        (sphereRectangleSurface (mapsTo_univ _ _)) sphereRectangleCell rfl i)
        absoluteHeightForm)) ∧
    rectangleBoundaryIntegral (sphereRectangleSurface (mapsTo_univ _ _))
      sphereRectangleCell rfl absoluteHeightForm = 0 := by
  have h := (pma10_32.2 univ (mapsTo_univ _ _)).2.2.2.2
    absoluteHeightForm absoluteHeightForm_continuous
  refine ⟨?_, h.1, h.2.2.2.2⟩
  simp [absoluteHeightForm, evaluateForm_dx, coordinateVector,
    EuclideanSpace.basisFun_apply]

private def C1Square (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) : Surface 2 3 univ where
  domain := .cell (Cell.unit 2)
  map u := f (u 0) • coordinateVector 3 0 + u 1 • coordinateVector 3 2
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := ((hf.comp (contDiff_apply ℝ ℝ (0 : Fin 2))).smul contDiff_const |>.add
    ((contDiff_apply ℝ ℝ (1 : Fin 2)).smul contDiff_const)).contDiffOn
  mapsTo := mapsTo_univ _ _

/-- A nonlinear square surface needs only C1 regularity. The diagonal
cancellation and the actual four-side formula also accept a merely
continuous coefficient form. No C2 premise is available in this client. -/
theorem C1_square_absolute_coefficient (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    surfaceIntegral (squareTriangleFaceSurface (C1Square f hf) rfl 0 0)
        absoluteHeightForm +
      surfaceIntegral (squareTriangleFaceSurface (C1Square f hf) rfl 1 0)
        absoluteHeightForm = 0 ∧
    squareTriangularBoundaryIntegral (C1Square f hf) rfl absoluteHeightForm =
      rectangleBoundaryIntegral (C1Square f hf) (Cell.unit 2) rfl absoluteHeightForm := by
  have h := (squareBoundary.2.2 3 univ (C1Square f hf) rfl).2
    absoluteHeightForm absoluteHeightForm_continuous
  exact ⟨h.2.2.1, h.2.2.2⟩

end Rudin.PMA.Chapter10.FidelityProbes
