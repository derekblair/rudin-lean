import Rudin.PMA.Chapter10.ExteriorDerivativeRules
import Rudin.PMA.Chapter10.SimplexFTC

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The coefficient of the coordinate form omitting coordinate i, expressed as
an evaluation so no choice of a complementary finite-set index is involved. -/
def omittedCoefficient {d : ℕ} (ω : FormField (d + 1)) (i : Fin (d + 1)) :
    Euclidean (d + 1) → ℝ := fun x =>
  evaluateForm d (fun j => coordinateVector (d + 1) (i.succAbove j)) (ω x)

lemma linear_formEvaluation_expansion {n : ℕ} (L : CotangentExterior n →ₗ[ℝ] ℝ)
    (ω : FormField n) (x : Euclidean n) :
    L (ω x) = ∑ S : Finset (Fin n), formCoefficient ω S x * L (exteriorBasis n S) := by
  rw [formField_expansion ω x]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma contDiffOn_linear_formEvaluation {n k r : ℕ} {U : Set (Euclidean n)}
    {ω : FormField n} (hω : IsCFormOn r U k ω) (L : CotangentExterior n →ₗ[ℝ] ℝ) :
    ContDiffOn ℝ r (fun x => L (ω x)) U := by
  have he := funext (linear_formEvaluation_expansion L ω)
  rw [he]
  exact ContDiffOn.sum (fun S _ => (hω.2 S).mul contDiffOn_const)

lemma coordinatePartial_linear_formEvaluation {n : ℕ} {ω : FormField n} {x : Euclidean n}
    (hω : CoefficientsDifferentiableAt ω x) (L : CotangentExterior n →ₗ[ℝ] ℝ) (i : Fin n) :
    coordinatePartial (fun y => L (ω y)) x i = L (coefficientDerivative ω i x) := by
  have he := funext (linear_formEvaluation_expansion L ω)
  rw [he, coordinatePartial_sum (fun S => (hω S).mul_const _)]
  simp only [coordinatePartial_mul_const (hω _) _, coefficientDerivative,
    map_sum, map_smul, smul_eq_mul]

lemma contDiffOn_omittedCoefficient {d r : ℕ} {U : Set (Euclidean (d + 1))}
    {ω : FormField (d + 1)} (hω : IsCFormOn r U d ω) (i : Fin (d + 1)) :
    ContDiffOn ℝ r (omittedCoefficient ω i) U :=
  contDiffOn_linear_formEvaluation hω _

@[simp] lemma coordEquivEuclidean_single {n : ℕ} (i : Fin n) :
    coordEquivEuclidean n (Pi.single i 1) = coordinateVector n i := by
  ext j
  simp [coordEquivEuclidean_apply_coordinate, coordinateVector,
    EuclideanSpace.basisFun_apply, Pi.single_apply]

lemma simplexCoordinateDerivative_comp_coordEquiv {n : ℕ} {f : Euclidean n → ℝ}
    {u : Coord n} (hf : DifferentiableAt ℝ f (coordEquivEuclidean n u)) (i : Fin n) :
    simplexCoordinateDerivative (f ∘ coordEquivEuclidean n) i u =
      coordinatePartial f (coordEquivEuclidean n u) i := by
  have hd := hf.hasFDerivAt.comp u (coordEquivEuclidean n).hasFDerivAt
  rw [simplexCoordinateDerivative, hd.fderiv, coordinatePartial_eq_fderiv hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    coordEquivEuclidean_single]

end Rudin.PMA.Chapter10
