import Rudin.PMA.Chapter10.RadialForm
import Rudin.PMA.Chapter10.RectangleChains

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma sphereRectangleMap_norm (u : Coord 2) : ‖sphereRectangleMap u‖ = 1 :=
  sphericalMap_norm (by norm_num : 0 ≤ (![1, u 0, u 1] : Coord 3) 0)

lemma sphereRectangleMap_punctured :
    MapsTo sphereRectangleMap sphereRectangleCell.carrier (puncturedSpace 3) := by
  intro u hu hz
  have h := sphereRectangleMap_norm u
  rw [hz, norm_zero] at h
  norm_num at h

def puncturedSphereSurface : Surface 2 3 (puncturedSpace 3) :=
  sphereRectangleSurface sphereRectangleMap_punctured

lemma sphereRectangleMap_contDiff_order (r : WithTop ENat) :
    ContDiff ℝ r sphereRectangleMap := by
  have he : sphereRectangleMap = fun u : Coord 2 => (coordEquivEuclidean 3)
      ![Real.sin (u 0) * Real.cos (u 1),
        Real.sin (u 0) * Real.sin (u 1), Real.cos (u 0)] :=
    funext sphereRectangleMap_formula
  rw [he]
  apply (coordEquivEuclidean 3).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  have h0 : ContDiff ℝ r (fun u : Coord 2 => u 0) := contDiff_apply ℝ ℝ 0
  have h1 : ContDiff ℝ r (fun u : Coord 2 => u 1) := contDiff_apply ℝ ℝ 1
  fin_cases i
  · exact h0.sin.mul h1.cos
  · exact h0.sin.mul h1.sin
  · exact h0.cos

lemma puncturedSphereSurface_isC2 : puncturedSphereSurface.IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _, (sphereRectangleMap_contDiff_order 2).contDiffOn⟩

lemma evaluateForm_dx_pair {n : ℕ} (v : Fin 2 → Euclidean n) (i j : Fin n) :
    evaluateForm 2 v (dx i * dx j) = v 0 i * v 1 j - v 1 i * v 0 j := by
  have he : dx i * dx j = coordinateWedge ![i, j] := by
    simp [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply,
      Matrix.vecTail, Function.comp_def]
  rw [he, evaluateForm_coordinateWedge]
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun a b => v b (![i, j] a)
  change Matrix.det M = _
  rw [Matrix.det_fin_two]
  rfl

/-- The numerator is the signed volume of the position vector and the two
parameter tangent vectors, in this column order. -/
lemma evaluateForm_radial (x : Euclidean 3) (v : Fin 2 → Euclidean 3) :
    evaluateForm 2 v (radialForm x) = (‖x‖ ^ 3)⁻¹ *
      (x 0 * (v 0 1 * v 1 2 - v 1 1 * v 0 2) +
        x 1 * (v 0 2 * v 1 0 - v 1 2 * v 0 0) +
        x 2 * (v 0 0 * v 1 1 - v 1 0 * v 0 1)) := by
  simp only [radialForm, map_smul, map_add, smul_eq_mul, evaluateForm_dx_pair]

def sphereRectangleDerivative (u : Coord 2) : Coord 2 →L[ℝ] Euclidean 3 :=
  (coordEquivEuclidean 3 : Coord 3 →L[ℝ] Euclidean 3).comp
    (ContinuousLinearMap.pi ![
      (Real.cos (u 0) * Real.cos (u 1)) • ContinuousLinearMap.proj 0 -
        (Real.sin (u 0) * Real.sin (u 1)) • ContinuousLinearMap.proj 1,
      (Real.cos (u 0) * Real.sin (u 1)) • ContinuousLinearMap.proj 0 +
        (Real.sin (u 0) * Real.cos (u 1)) • ContinuousLinearMap.proj 1,
      (-Real.sin (u 0)) • ContinuousLinearMap.proj 0])

lemma sphereRectangleMap_hasFDerivAt (u : Coord 2) :
    HasFDerivAt sphereRectangleMap (sphereRectangleDerivative u) u := by
  have he : sphereRectangleMap = fun u : Coord 2 => (coordEquivEuclidean 3)
      ![Real.sin (u 0) * Real.cos (u 1),
        Real.sin (u 0) * Real.sin (u 1), Real.cos (u 0)] :=
    funext sphereRectangleMap_formula
  rw [he]
  have h0 := (ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h1 := (ContinuousLinearMap.proj 1 : Coord 2 →L[ℝ] ℝ).hasFDerivAt (x := u)
  apply (coordEquivEuclidean 3).hasFDerivAt.comp u
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert h0.sin.mul h1.cos using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring
  · convert h0.sin.mul h1.sin using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        smul_eq_mul] <;> ring
  · exact h0.cos

lemma puncturedSphere_radial_integrand (u : Coord 2) :
    surfaceIntegrand puncturedSphereSurface radialForm u = Real.sin (u 0) := by
  change evaluateForm 2 (fun j => fderiv ℝ sphereRectangleMap u (Pi.single j 1))
    (radialForm (sphereRectangleMap u)) = _
  rw [evaluateForm_radial, sphereRectangleMap_norm, one_pow, inv_one, one_mul,
    (sphereRectangleMap_hasFDerivAt u).fderiv, sphereRectangleMap_formula]
  simp only [sphereRectangleDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.pi_apply, coordEquivEuclidean_apply_coordinate,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, smul_eq_mul]
  norm_num
  calc
    _ = Real.sin (u 0) * (Real.sin (u 0) ^ 2 + Real.cos (u 0) ^ 2) *
      (Real.sin (u 1) ^ 2 + Real.cos (u 1) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

lemma sphereRectangle_sin_integral :
    iteratedRIntegral sphereRectangleCell (fun u => Real.sin (u 0)) = 4 * Real.pi := by
  have hc : Continuous (fun u : Coord 2 => Real.sin (u 0)) :=
    Real.continuous_sin.comp (continuous_apply 0)
  rw [cellRIntegral_two_eq_doubleIntegral sphereRectangleCell hc]
  simp only [sphereRectangleCell, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp only [Real.cos_zero, Real.cos_pi]
  ring

lemma puncturedSphere_radial_integral :
    surfaceIntegral puncturedSphereSurface radialForm = 4 * Real.pi := by
  change iteratedRIntegral sphereRectangleCell (surfaceIntegrand puncturedSphereSurface radialForm) = _
  rw [funext puncturedSphere_radial_integrand]
  exact sphereRectangle_sin_integral

def puncturedSphereChain : SimplexChain 2 3 (puncturedSpace 3) :=
  puncturedSphereSurface.rectangleChain sphereRectangleCell rfl puncturedSphereSurface_isC2

lemma puncturedSphereChain_integral {ω : FormField 3}
    (hω : IsFormOn (puncturedSpace 3) 2 ω) :
    chainIntegral ω puncturedSphereChain = surfaceIntegral puncturedSphereSurface ω :=
  rectangleChain_integral puncturedSphereSurface sphereRectangleCell rfl
    puncturedSphereSurface_isC2 hω

lemma puncturedSphereChain_cycle : ChainEq (chainBoundary puncturedSphereChain) 0 := by
  apply rectangleChain_cycle puncturedSphereSurface sphereRectangleCell rfl puncturedSphereSurface_isC2
  intro ω hω
  exact ((pma10_32.2 (puncturedSpace 3) sphereRectangleMap_punctured).2.2.2.2 ω hω).2.2.2.2

/-- Source 10.37 uses the native spherical rectangle integral. The two-simplex
chain is its explicit normalized triangulation, equivalent for every continuous
form; its zero boundary and nonbounding conclusion use functional chain equality. -/
theorem pma10_37 : pma10_37_contract := by
  have hne : chainIntegral radialForm puncturedSphereChain ≠ 0 := by
    rw [puncturedSphereChain_integral radialForm_closed.1.isFormOn, puncturedSphere_radial_integral]
    positivity
  refine ⟨radial_denominator_eq_rpow, radialForm_closed, ?_, puncturedSphereSurface,
    rfl, rfl, fun u _ => puncturedSphere_radial_integrand u,
    ParameterDomain.integrable_of_continuousOn
      (puncturedSphereSurface.continuousOn_integrand radialForm_closed.1.isFormOn),
    puncturedSphere_radial_integral, ?_, puncturedSphereChain,
    fun _ hω => puncturedSphereChain_integral hω, puncturedSphereChain_cycle, ?_⟩
  · exact not_exact_of_nonzero_cycle_integral (puncturedSpace_isOpen 3) radialForm_closed.1.isFormOn
      puncturedSphereChain puncturedSphereChain_cycle hne
  · rw [puncturedSphere_radial_integral]
    positivity
  · exact not_boundary_of_closed_integral_ne_zero (puncturedSpace_isOpen 3) radialForm_closed
      puncturedSphereChain hne

end Rudin.PMA.Chapter10
