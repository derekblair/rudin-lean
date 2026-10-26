import Rudin.PMA.Chapter10.TorusProof
import Rudin.PMA.Chapter10.ClosedFormConsequences

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def absoluteValueField : VectorField := fun x => |x 1| • coordinateVector 3 0

/-- An absolute-value coefficient needs only continuity. The radius-zero
face is a nonconstant circle with a redundant parameter, yet its actual
native two-form integral vanishes. -/
theorem inner_torus_face_absolute_coefficient (a b : ℝ) (ha : 0 < a) :
    let Φ := cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 0 0
    Φ.domain.Integrable (surfaceIntegrand Φ (vectorTwoForm absoluteValueField)) ∧
      surfaceIntegral Φ (vectorTwoForm absoluteValueField) = 0 := by
  have hc : Continuous absoluteValueField :=
    (EuclideanSpace.proj 1 : Euclidean 3 →L[ℝ] ℝ).continuous.abs.smul continuous_const
  have hω : IsFormOn univ 2 (vectorTwoForm absoluteValueField) :=
    isFormOn_vectorTwoForm hc.continuousOn
  exact ⟨ParameterDomain.integrable_of_continuousOn
    ((cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 0 0).continuousOn_integrand hω),
    torusFace_inner_zero a b ha hω⟩

/-- The actual solid-torus chain makes every closed two-form integrate to
zero on its outer surface, without assuming a primitive for that form. -/
theorem closed_form_outer_torus_integral {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {ω : FormField 3} (hω : IsClosedOn univ 2 ω) :
    surfaceIntegral (torusOuterSurface a b) ω = 0 := by
  rcases pma10_47 a b ha hab with
    ⟨_, _, _, _, _, _, _, _, _, _, hΓ, _⟩
  obtain ⟨Γ, _, hboundary⟩ := hΓ
  rw [← hboundary ω hω.1.isFormOn]
  exact closed_chainIntegral_boundary_eq_zero isOpen_univ hω Γ

/-- At the parameter corner u=v=0 the ordered normal points along positive
x, independently checking the source orientation away from its top-z example. -/
theorem torus_corner_normal {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    surfaceNormal (torusOuterSurface a b) (0 : Coord 2) =
      (a * b) • coordinateVector 3 0 := by
  rcases pma10_47 a b ha hab with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hnormal, _⟩
  have hzero : (0 : Coord 2) ∈ torusOuterCell.carrier := by
    rw [Cell.mem_carrier]
    intro i
    exact ⟨le_rfl, by change (0 : ℝ) ≤ 2 * Real.pi; positivity⟩
  have h := (hnormal 0 hzero).1
  rw [h]
  ext i
  fin_cases i <;> simp [torusUnitNormal, coordinateVector, EuclideanSpace.basisFun_apply,
    PiLp.smul_apply, smul_eq_mul]

end Rudin.PMA.Chapter10.FidelityProbes
