import Rudin.PMA.Chapter10.ExactOneForms
import Rudin.PMA.Chapter10.ExteriorDerivativeRules

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- Evaluation of df uses the tangent vector, including its negative
coordinate; it is not the sum of the coordinate derivative values. -/
theorem scalar_differential_on_mixed_tangent :
    evaluateForm 1 (fun _ =>
      (3 : ℝ) • coordinateVector 2 0 - (4 : ℝ) • coordinateVector 2 1)
      (scalarDifferential (fun x : Euclidean 2 => x 0 + 2 * x 1) 0) = -5 := by
  let L : Euclidean 2 →L[ℝ] ℝ := EuclideanSpace.proj 0 + (2 : ℝ) • EuclideanSpace.proj 1
  have h := pma10_18.2.2 2 univ L isOpen_univ L.contDiff.contDiffOn
    0 (mem_univ _) (fun _ =>
      (3 : ℝ) • coordinateVector 2 0 - (4 : ℝ) • coordinateVector 2 1)
  rw [L.hasFDerivAt.fderiv] at h
  have hL : (L : Euclidean 2 → ℝ) = fun x => x 0 + 2 * x 1 := by
    funext x
    rfl
  rw [hL] at h
  norm_num [L, coordinateVector, EuclideanSpace.basisFun_apply] at h
  simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using h

private def asymmetricCurveCell : Cell 1 where
  lower := fun _ => -1
  upper := fun _ => 2
  lower_le_upper := fun _ => by norm_num

private def polynomialCurve : Surface 1 2 univ where
  domain := .cell asymmetricCurveCell
  map u := (u 0)^2 • coordinateVector 2 0 + (u 0)^3 • coordinateVector 2 1
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2).smul contDiff_const |>.add
    (((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 3).smul contDiff_const)).contDiffOn
  mapsTo := mapsTo_univ _ _

/-- A nonlinear curve on [-1,2] exercises the source endpoint theorem
outside the unit parameter interval. Its potential is the product xy. -/
theorem nonlinear_curve_native_endpoint_value :
    polynomialCurve.domain.Integrable (surfaceIntegrand polynomialCurve
      (scalarDifferential (fun x : Euclidean 2 => x 0 * x 1))) ∧
    surfaceIntegral polynomialCurve
      (scalarDifferential (fun x : Euclidean 2 => x 0 * x 1)) = 33 := by
  have hf : ContDiff ℝ 1 (fun x : Euclidean 2 => x 0 * x 1) :=
    (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).contDiff.mul
      (EuclideanSpace.proj 1 : Euclidean 2 →L[ℝ] ℝ).contDiff
  have h := pma10_19.1 2 univ _ isOpen_univ hf.contDiffOn polynomialCurve
  refine ⟨h.1, ?_⟩
  rw [h.2]
  change
    (((2 : ℝ)^2 • coordinateVector 2 0 + (2 : ℝ)^3 • coordinateVector 2 1) 0 *
      ((2 : ℝ)^2 • coordinateVector 2 0 + (2 : ℝ)^3 • coordinateVector 2 1) 1) -
    (((-1 : ℝ)^2 • coordinateVector 2 0 + (-1 : ℝ)^3 • coordinateVector 2 1) 0 *
      ((-1 : ℝ)^2 • coordinateVector 2 0 + (-1 : ℝ)^3 • coordinateVector 2 1) 1) = 33
  norm_num [coordinateVector, EuclideanSpace.basisFun_apply]

/-- For a merely C1 one-form, the product rule's odd sign cancels the two
terms in d(omega wedge omega); no C2 premise is needed. -/
theorem C1_one_form_self_product_derivative {n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsCFormOn 1 E 1 ω) :
    EqOn (exteriorDerivative (wedge ω ω)) 0 E := by
  have hd : IsFormOn E 2 (exteriorDerivative ω) :=
    (pma10_18.1 n 1 E ω hE hω).1
  have hc := pma10_17.2.2.2 n 2 1 E (exteriorDerivative ω) ω hd hω.isFormOn
  have hp := pma10_20.1 n 1 1 E ω ω hE hω hω
  intro x hx
  have hc' : wedge (exteriorDerivative ω) ω x = wedge ω (exteriorDerivative ω) x := by
    simpa using hc hx
  simpa [hc'] using hp hx

end Rudin.PMA.Chapter10.FidelityProbes
