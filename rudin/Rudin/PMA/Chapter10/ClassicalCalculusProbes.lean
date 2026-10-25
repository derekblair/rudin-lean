import Rudin.PMA.Chapter10.DivergenceTheorem

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def collapsedLinear : Coord 2 →L[ℝ] Euclidean 3 :=
  ((ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ) +
    ContinuousLinearMap.proj 1).smulRight (coordinateVector 3 0)

private lemma collapsed_surface_isC2 (C : Cell 2) (p : Euclidean 3) :
    (affineRectangleSurface C p collapsedLinear).IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _,
    (contDiff_const.add collapsedLinear.contDiff).contDiffOn⟩

private lemma collapsed_surface_normal (C : Cell 2) (p : Euclidean 3) (u : Coord 2) :
    surfaceNormal (affineRectangleSurface C p collapsedLinear) u = 0 := by
  rw [surfaceNormal_affineRectangle]
  ext i
  fin_cases i <;> simp [collapsedLinear, cross3, ContinuousLinearMap.smulRight_apply,
    coordinateVector, EuclideanSpace.basisFun_apply]

/-- Classical Stokes handles a nonconstant rank-one cell parametrization:
its actual induced boundary has zero circulation for every C1 field. -/
theorem rank_one_cell_boundary_circulation (C : Cell 2) (p : Euclidean 3)
    (F : VectorField) (hF : ContDiff ℝ 1 F) :
    chainCirculation F ((affineRectangleSurface C p collapsedLinear).boundaryChain
      (collapsed_surface_isC2 C p)) = 0 := by
  have h := (pma10_50 univ isOpen_univ (affineRectangleSurface C p collapsedLinear)
    (collapsed_surface_isC2 C p) F hF.contDiffOn).1
  rw [← h]
  have hz : fluxIntegrand (affineRectangleSurface C p collapsedLinear) (curl F) =
      fun _ => (0 : ℝ) := by
    funext u
    simp [fluxIntegrand, collapsed_surface_normal]
  unfold flux
  rw [hz, ParameterDomain.integral_eq_setIntegral continuousOn_const]
  simp

/-- The identity vector field has divergence three. The ordinary region
volume therefore determines the outward boundary flux with positive sign. -/
theorem identity_field_boundary_flux {E : Set (Euclidean 3)} (hE : IsOpen E)
    (R : PositiveRegion 3 E) :
    IntegrableOn (fun _ : Euclidean 3 => (3 : ℝ)) R.carrier ∧
      chainFlux (fun x => x) R.boundary = 3 * (volume R.carrier).toReal := by
  have h := pma10_51 E hE R (fun x => x) contDiffOn_id
  have hd : divergence (fun x : Euclidean 3 => x) = fun _ => (3 : ℝ) := by
    funext x
    simp [divergence, coordinatePartial_coordinate, Fin.sum_univ_three]
  refine ⟨?_, ?_⟩
  · simpa only [hd] using h.1
  · simpa only [hd, regionIntegral_const, mul_comm] using h.2.2.1.symm

end Rudin.PMA.Chapter10.FidelityProbes
