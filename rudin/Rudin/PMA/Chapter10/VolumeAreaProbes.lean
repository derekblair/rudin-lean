import Rudin.PMA.Chapter10.PlanarGreen
import Rudin.PMA.Chapter10.AreaElements

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- The image indicator is a valid density although it need not be continuous
on the ambient space. Its native volume integral is the ordinary image volume. -/
theorem image_indicator_native_volume {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface n n E) (hi : InjOn Φ.map Φ.domain.carrier)
    (hp : ∀ u ∈ Φ.domain.carrier, 0 < coordinateJacobian Φ.coordinateMap u) :
    Φ.domain.Integrable
      (surfaceIntegrand Φ (densityForm (Φ.image.indicator (fun _ => (1 : ℝ))))) ∧
    surfaceIntegral Φ (densityForm (Φ.image.indicator (fun _ => (1 : ℝ)))) =
      (volume Φ.image).toReal := by
  classical
  have hc : ContinuousOn (Φ.image.indicator (fun _ => (1 : ℝ))) Φ.image := by
    apply (continuousOn_const (c := (1 : ℝ))).congr
    intro x hx
    simp [hx]
  refine ⟨(pma10_44.1 n E Φ _ hc).1, ?_⟩
  rw [(pma10_44.2 n E Φ hi hp).1 _ hc]
  have he : (∫ x in Φ.image, Φ.image.indicator (fun _ => (1 : ℝ)) x) =
      ∫ _x in Φ.image, (1 : ℝ) := by
    apply setIntegral_congr_fun Φ.isCompact_image.measurableSet
    intro x hx
    simp [hx]
  rw [he]
  simp [measureReal_def]

/-- Positive planar orientation makes y dx the negative area form. This
checks the off-diagonal sign in Green's density independently of x dy. -/
theorem ydx_is_negative_area {E : Set (Euclidean 2)} (hE : IsOpen E)
    (R : PositiveRegion 2 E) :
    chainIntegral (planarOneForm (fun x => x 1) (fun _ => 0)) R.boundary =
      -(volume R.carrier).toReal := by
  have h := ((pma10_45 E R hE).1 (fun x => x 1) (fun _ => 0)
    (EuclideanSpace.proj 1 : Euclidean 2 →L[ℝ] ℝ).contDiff.contDiffOn
    contDiffOn_const).1
  simpa only [coordinatePartial_const, coordinatePartial_coordinate, ite_true,
    zero_sub, regionIntegral_const, mul_neg_one] using h

private def lineCollapse : Coord 2 →L[ℝ] Euclidean 3 :=
  ((ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ) +
    ContinuousLinearMap.proj 1).smulRight (coordinateVector 3 0)

private lemma lineCollapse_normal_zero (C : Cell 2) (p : Euclidean 3) (u : Coord 2) :
    surfaceNormal (affineRectangleSurface C p lineCollapse) u = 0 := by
  rw [surfaceNormal_affineRectangle]
  ext i
  fin_cases i <;> simp [lineCollapse, cross3, ContinuousLinearMap.smulRight_apply,
    coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply]

/-- A nonconstant rank-one affine parametrization has zero surface area on
every rectangle, including rectangles with two positive side lengths. -/
theorem affine_line_collapse_has_zero_area (C : Cell 2) (p : Euclidean 3) :
    surfaceArea (affineRectangleSurface C p lineCollapse) = 0 := by
  have hz := lineCollapse_normal_zero C p 0
  rw [surfaceNormal_affineRectangle] at hz
  rw [(pma10_46.2 C p lineCollapse).2.1, hz, norm_zero, zero_mul]

end Rudin.PMA.Chapter10.FidelityProbes
