import Rudin.PMA.Chapter10.ContractionCalculus
import Rudin.PMA.Chapter10.CoefficientIntegrals
import Rudin.PMA.Chapter10.ClosedExact

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators Topology Interval

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The radial contraction integrand for a form of degree k+1. -/
def radialHomotopyIntegrand {n : ℕ} (k : ℕ) (a : Euclidean n) (ω : FormField n)
    (q : ℝ × Euclidean n) : CotangentExterior n :=
  ∑ i : Fin n, (q.1 ^ k * (q.2 i - a i)) • contractCoordinate i (ω (radialPoint a q))

lemma radialHomotopyIntegrand_mem {n k : ℕ} {a x : Euclidean n} {t : ℝ} {ω : FormField n}
    (hω : ω (radialPoint a (t, x)) ∈ (⋀[ℝ]^(k+1) (Coord n))) :
    radialHomotopyIntegrand k a ω (t, x) ∈ (⋀[ℝ]^k (Coord n)) := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (contractCoordinate_mem i hω)

lemma radialHomotopyIntegrand_coeff_regular {n k : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hω : IsCFormOn 1 E (k+1) ω) (a : Euclidean n)
    (S : Finset (Fin n)) :
    ContDiffOn ℝ 1 (fun q => (exteriorBasis n).repr (radialHomotopyIntegrand k a ω q) S)
      (radialPoint a ⁻¹' E) := by
  classical
  have he : (fun q => (exteriorBasis n).repr (radialHomotopyIntegrand k a ω q) S) =
      fun q => ∑ i : Fin n, (q.1 ^ k * (q.2 i - a i)) *
        (((exteriorBasis n).coord S).comp (contractCoordinate i)) (ω (radialPoint a q)) := by
    funext q
    simp only [radialHomotopyIntegrand, map_sum, map_smul, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, LinearMap.comp_apply, Basis.coord_apply]
  rw [he]
  apply ContDiffOn.sum
  intro i hi
  have hw : ContDiff ℝ 1 (fun q : ℝ × Euclidean n => q.1 ^ k * (q.2 i - a i)) := by
    have hp : ContDiff ℝ 1 (fun q : ℝ × Euclidean n => q.2 i) :=
      (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).contDiff.comp contDiff_snd
    exact contDiff_fst.pow k |>.mul (hp.sub contDiff_const)
  exact hw.contDiffOn.mul ((contDiffOn_linear_formEvaluation hω _).comp
    (contDiff_radialPoint a).contDiffOn (fun _ h => h))

lemma radial_weight_partial {n : ℕ} (k : ℕ) (a x : Euclidean n) (t : ℝ) (i j : Fin n) :
    coordinatePartial (fun y : Euclidean n => t ^ k * (y i - a i)) x j =
      t ^ k * (if i = j then 1 else 0) := by
  have hd : HasFDerivAt (fun y : Euclidean n => t ^ k * (y i-a i))
      (t ^ k • (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)) x :=
    ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt.sub_const (a i)).const_mul (t ^ k)
  rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv]
  simp [ContinuousLinearMap.smul_apply, EuclideanSpace.coe_proj, coordinateVector,
    EuclideanSpace.basisFun_apply, PiLp.single_apply]

lemma radialHomotopyIntegrand_coeff_differentiable {n : ℕ} (k : ℕ) (a x : Euclidean n)
    (t : ℝ) {ω : FormField n} (hω : CoefficientsDifferentiableAt ω (radialPoint a (t, x))) :
    CoefficientsDifferentiableAt (fun y => radialHomotopyIntegrand k a ω (t, y)) x := by
  intro S
  have he : formCoefficient (fun y => radialHomotopyIntegrand k a ω (t, y)) S =
      fun y => ∑ i : Fin n, formCoefficient
        (fun z => (t^k * (z i-a i)) • contractCoordinate i (ω (radialPoint a (t,z)))) S y := by
    funext y
    simp only [formCoefficient, radialHomotopyIntegrand, map_sum, Finsupp.finsetSum_apply]
  rw [he]
  apply DifferentiableAt.fun_sum
  intro i hi
  apply coefficientsDifferentiableAt_function_smul
  · exact (differentiableAt_const (t^k)).mul
      ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).differentiableAt.sub_const _)
  · exact coefficientsDifferentiableAt_linearMap
      (coefficientsDifferentiableAt_radial a x t hω) (contractCoordinate i)

lemma exteriorDerivative_radialHomotopyIntegrand {n k : ℕ} (a x : Euclidean n) (t : ℝ)
    {ω : FormField n} (hω : CoefficientsDifferentiableAt ω (radialPoint a (t, x)))
    (hg : ω (radialPoint a (t, x)) ∈ (⋀[ℝ]^(k+1) (Coord n)))
    (hz : exteriorDerivative ω (radialPoint a (t, x)) = 0) :
    exteriorDerivative (fun y => radialHomotopyIntegrand k a ω (t, y)) x =
      (t^k * (k+1 : ℕ)) • ω (radialPoint a (t, x)) +
        t^(k+1) • ∑ i : Fin n, (x i-a i) • coefficientDerivative ω i (radialPoint a (t, x)) := by
  classical
  let y := radialPoint a (t, x)
  have hd (i : Fin n) := coefficientsDifferentiableAt_linearMap
    (coefficientsDifferentiableAt_radial a x t hω) (contractCoordinate i)
  have hw (i : Fin n) : DifferentiableAt ℝ (fun z : Euclidean n => t^k*(z i-a i)) x :=
    (differentiableAt_const (t^k)).mul ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).differentiableAt.sub_const _)
  have hcd (j : Fin n) :
      coefficientDerivative (fun z => radialHomotopyIntegrand k a ω (t,z)) j x =
        ∑ i : Fin n, ((t^k*(if i=j then 1 else 0)) • contractCoordinate i (ω y) +
          (t^(k+1)*(x i-a i)) • contractCoordinate i (coefficientDerivative ω j y)) := by
    change coefficientDerivative (fun z => ∑ i : Fin n,
      (t^k*(z i-a i)) • contractCoordinate i (ω (radialPoint a (t,z)))) j x = _
    rw [coefficientDerivative_sum (fun i => coefficientsDifferentiableAt_function_smul (hw i) (hd i))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coefficientDerivative_function_smul (hw i) (hd i), radial_weight_partial,
      coefficientDerivative_linearMap (coefficientsDifferentiableAt_radial a x t hω),
      coefficientDerivative_radial a x t hω, map_smul, smul_smul]
    congr 2
    rw [pow_succ]
    ring
  simp only [exteriorDerivative_eq_sum, hcd, Finset.mul_sum, mul_add, mul_smul_comm,
    Finset.sum_add_distrib]
  have hfirst : (∑ j : Fin n, ∑ i : Fin n,
      (t^k*(if i=j then 1 else 0)) • (dx j * contractCoordinate i (ω y))) =
      (t^k*(k+1 : ℕ)) • ω y := by
    calc
      _ = t^k • ∑ j : Fin n, dx j * contractCoordinate j (ω y) := by
        simp [mul_smul, Finset.smul_sum]
      _ = _ := by rw [contraction_euler hg, smul_smul]
  rw [hfirst]
  congr 1
  rw [Finset.sum_comm, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.smul_sum, contraction_closed_identity hz i, smul_smul]

end Rudin.PMA.Chapter10
