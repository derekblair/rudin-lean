import Rudin.PMA.Chapter10.ContractionAlgebra
import Rudin.PMA.Chapter10.StokesCoefficients
import Rudin.PMA.Chapter10.PullbackDifferentiation

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

lemma coefficientsDifferentiableAt_linearMap {n : ℕ} {ω : FormField n} {x : Euclidean n}
    (hω : CoefficientsDifferentiableAt ω x) (L : CotangentExterior n →ₗ[ℝ] CotangentExterior n) :
    CoefficientsDifferentiableAt (fun y => L (ω y)) x := by
  intro S
  let A : CotangentExterior n →ₗ[ℝ] ℝ :=
    ((exteriorBasis n).coord S).comp L
  have he : formCoefficient (fun y => L (ω y)) S = fun y =>
      ∑ T : Finset (Fin n), formCoefficient ω T y * A (exteriorBasis n T) := by
    funext y
    exact linear_formEvaluation_expansion A ω y
  rw [he]
  exact DifferentiableAt.fun_sum fun T _ => (hω T).mul_const _

lemma coefficientDerivative_linearMap {n : ℕ} {ω : FormField n} {x : Euclidean n}
    (hω : CoefficientsDifferentiableAt ω x)
    (L : CotangentExterior n →ₗ[ℝ] CotangentExterior n) (j : Fin n) :
    coefficientDerivative (fun y => L (ω y)) j x = L (coefficientDerivative ω j x) := by
  have he : (fun y => L (ω y)) = fun y =>
      ∑ S : Finset (Fin n), formCoefficient ω S y • L (exteriorBasis n S) := by
    funext y
    rw [formField_expansion ω y, map_sum]
    simp only [map_smul]
  rw [he, coefficientDerivative_sum_smul _ _ hω]
  simp only [coefficientDerivative, map_sum, map_smul]

lemma coefficientsDifferentiableAt_function_smul {n : ℕ} {ω : FormField n}
    {f : Euclidean n → ℝ} {x : Euclidean n} (hf : DifferentiableAt ℝ f x)
    (hω : CoefficientsDifferentiableAt ω x) :
    CoefficientsDifferentiableAt (fun y => f y • ω y) x := by
  intro S
  change DifferentiableAt ℝ (fun y => (exteriorBasis n).repr (f y • ω y) S) x
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact hf.mul (hω S)

lemma coefficientDerivative_function_smul {n : ℕ} {ω : FormField n}
    {f : Euclidean n → ℝ} {x : Euclidean n} (hf : DifferentiableAt ℝ f x)
    (hω : CoefficientsDifferentiableAt ω x) (j : Fin n) :
    coefficientDerivative (fun y => f y • ω y) j x =
      coordinatePartial f x j • ω x + f x • coefficientDerivative ω j x := by
  classical
  have he : (fun y => f y • ω y) = fun y => ∑ S : Finset (Fin n),
      (f y * formCoefficient ω S y) • exteriorBasis n S := by
    funext y
    rw [formField_expansion ω y, Finset.smul_sum]
    simp only [mul_smul]
  have hp (S : Finset (Fin n)) : DifferentiableAt ℝ
      (fun y => f y * formCoefficient ω S y) x := hf.mul (hω S)
  rw [he, coefficientDerivative_sum_smul
    (fun S y => f y * formCoefficient ω S y) (exteriorBasis n) hp]
  simp only [coordinatePartial_mul hf (hω _), add_smul, mul_smul,
    Finset.sum_add_distrib, ← Finset.smul_sum, ← formField_expansion, coefficientDerivative]

/-- The coefficient form of Cartan's contraction identity at a closed form. -/
lemma contraction_closed_identity {n : ℕ} {ω : FormField n} {x : Euclidean n}
    (hclosed : exteriorDerivative ω x = 0) (i : Fin n) :
    (∑ j : Fin n, dx j * contractCoordinate i (coefficientDerivative ω j x)) =
      coefficientDerivative ω i x := by
  classical
  have he := congrArg (contractCoordinate i) hclosed
  simp only [exteriorDerivative_eq_sum, map_sum, contractCoordinate_dx_mul,
    Finset.sum_sub_distrib, map_zero] at he
  have hs : (∑ j : Fin n, if i = j then coefficientDerivative ω j x else 0) =
      coefficientDerivative ω i x := by simp
  rw [hs] at he
  exact (sub_eq_zero.mp he).symm

/-- Radial interpolation has a scalar multiple of the identity as its spatial derivative. -/
def radialPoint {n : ℕ} (a : Euclidean n) (q : ℝ × Euclidean n) : Euclidean n :=
  a + q.1 • (q.2 - a)

lemma contDiff_radialPoint {n : ℕ} (a : Euclidean n) : ContDiff ℝ 1 (radialPoint a) := by
  change ContDiff ℝ 1 (fun q : ℝ × Euclidean n => a + q.1 • (q.2-a))
  fun_prop

lemma hasFDerivAt_radialPoint {n : ℕ} (a x : Euclidean n) (t : ℝ) :
    HasFDerivAt (fun y => radialPoint a (t, y))
      (t • ContinuousLinearMap.id ℝ (Euclidean n)) x := by
  exact (((hasFDerivAt_id x).sub_const a).const_smul t).const_add a

lemma coefficientsDifferentiableAt_radial {n : ℕ} {ω : FormField n}
    (a x : Euclidean n) (t : ℝ)
    (hω : CoefficientsDifferentiableAt ω (radialPoint a (t, x))) :
    CoefficientsDifferentiableAt (fun y => ω (radialPoint a (t, y))) x := by
  intro S
  exact (hω S).comp x (hasFDerivAt_radialPoint a x t).differentiableAt

lemma coefficientDerivative_radial {n : ℕ} {ω : FormField n}
    (a x : Euclidean n) (t : ℝ)
    (hω : CoefficientsDifferentiableAt ω (radialPoint a (t, x))) (j : Fin n) :
    coefficientDerivative (fun y => ω (radialPoint a (t, y))) j x =
      t • coefficientDerivative ω j (radialPoint a (t, x)) := by
  classical
  rw [coefficientDerivative, coefficientDerivative, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hd := (hω S).hasFDerivAt.comp x (hasFDerivAt_radialPoint a x t)
  have he : coordinatePartial (fun y => formCoefficient ω S (radialPoint a (t, y))) x j =
      t * coordinatePartial (formCoefficient ω S) (radialPoint a (t, x)) j := by
    change coordinatePartial (formCoefficient ω S ∘ fun y => radialPoint a (t,y)) x j = _
    rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv,
      coordinatePartial_eq_fderiv (hω S)]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  change coordinatePartial (fun y => formCoefficient ω S (radialPoint a (t, y))) x j • _ = _
  rw [he, mul_smul]

end Rudin.PMA.Chapter10
