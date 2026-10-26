import Rudin.PMA.Chapter10.Integration
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating

/-! Coordinate exterior algebra used to represent forms. Equality of integration
functionals is a separate relation, with a separation theorem; algebraic equality
alone does not stand for Rudin's functional definition. -/
noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

abbrev CotangentExterior (n : ℕ) := ExteriorAlgebra ℝ (Coord n)
abbrev FormField (n : ℕ) := Euclidean n → CotangentExterior n

/-- Coordinate covectors, identified with their coefficient vectors. -/
def covectorBasis (n : ℕ) : Basis (Fin n) ℝ (Coord n) := Pi.basisFun ℝ (Fin n)

def exteriorBasis (n : ℕ) : Basis (Finset (Fin n)) ℝ (CotangentExterior n) :=
  (covectorBasis n).ExteriorAlgebra

def dx {n : ℕ} (i : Fin n) : CotangentExterior n :=
  ExteriorAlgebra.ι ℝ (covectorBasis n i)

def coordinateWedge {n k : ℕ} (I : Fin k → Fin n) : CotangentExterior n :=
  ExteriorAlgebra.ιMulti ℝ k (fun j => covectorBasis n (I j))

def formCoefficient {n : ℕ} (ω : FormField n) (S : Finset (Fin n)) : Euclidean n → ℝ :=
  fun x => (exteriorBasis n).repr (ω x) S

/-- Source regularity is regularity of all scalar coefficients. -/
def IsFormOn {n : ℕ} (E : Set (Euclidean n)) (k : ℕ) (ω : FormField n) : Prop :=
  (∀ x ∈ E, ω x ∈ (⋀[ℝ]^k (Coord n))) ∧
    ∀ S, ContinuousOn (formCoefficient ω S) E

def IsCFormOn {n : ℕ} (r : ℕ) (E : Set (Euclidean n)) (k : ℕ)
    (ω : FormField n) : Prop :=
  (∀ x ∈ E, ω x ∈ (⋀[ℝ]^k (Coord n))) ∧
    ∀ S, ContDiffOn ℝ r (formCoefficient ω S) E

def wedge {n : ℕ} (ω η : FormField n) : FormField n := fun x => ω x * η x

/-- Evaluate one covector on each of the supplied tangent vectors. -/
def covectorEvaluation {n k : ℕ} (v : Fin k → Euclidean n) : Coord n →ₗ[ℝ] Coord k where
  toFun a j := ∑ i, a i * v j i
  map_add' a b := by ext j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext j; simp [Finset.mul_sum, mul_assoc]

def determinantEvaluation {n k : ℕ} (v : Fin k → Euclidean n) :
    (Coord n) [⋀^Fin k]→ₗ[ℝ] ℝ :=
  Matrix.detRowAlternating.compLinearMap (covectorEvaluation v)

/-- Evaluate the degree-k component of an exterior-algebra element.
The other homogeneous components are sent to zero. -/
def evaluateForm {n : ℕ} (k : ℕ) (v : Fin k → Euclidean n) :
    CotangentExterior n →ₗ[ℝ] ℝ :=
  ExteriorAlgebra.liftAlternating (fun d =>
    if h : d = k then by subst d; exact determinantEvaluation v else 0)

@[simp] theorem covectorEvaluation_basis {n k : ℕ} (v : Fin k → Euclidean n)
    (i : Fin n) (j : Fin k) : covectorEvaluation v (covectorBasis n i) j = v j i := by
  simp [covectorEvaluation, covectorBasis, Pi.basisFun_apply, Pi.single_apply]

/-- The determinant in the surface integral has selected output rows and
parameter columns; transpose invariance aligns the alternating evaluation. -/
theorem evaluateForm_coordinateWedge {n k : ℕ} (I : Fin k → Fin n)
    (v : Fin k → Euclidean n) :
    evaluateForm k v (coordinateWedge I) = Matrix.det (fun i j => v j (I i)) := by
  simp only [evaluateForm, coordinateWedge, ExteriorAlgebra.liftAlternating_apply_ιMulti,
    dite_true]
  change Matrix.det (fun i => covectorEvaluation v (covectorBasis n (I i))) = _
  congr 1
  ext i j
  exact covectorEvaluation_basis v (I i) j

@[simp] theorem coordinateWedge_zero {n : ℕ} (I : Fin 0 → Fin n) :
    coordinateWedge I = 1 := ExteriorAlgebra.ιMulti_zero_apply _

theorem coordinateWedge_repeat {n k : ℕ} (I : Fin k → Fin n) (i j : Fin k)
    (hij : i ≠ j) (h : I i = I j) : coordinateWedge I = 0 :=
  (ExteriorAlgebra.ιMulti ℝ k).map_eq_zero_of_eq _ (by rw [h]) hij

theorem dx_mul_dx {n : ℕ} (i : Fin n) : dx i * dx i = 0 :=
  ExteriorAlgebra.ι_sq_zero _

theorem dx_mul_swap {n : ℕ} (i j : Fin n) : dx i * dx j = -(dx j * dx i) :=
  eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)

theorem wedge_assoc {n : ℕ} (ω η θ : FormField n) :
    wedge (wedge ω η) θ = wedge ω (wedge η θ) := by
  funext x
  exact mul_assoc _ _ _

theorem wedge_add_left {n : ℕ} (ω η θ : FormField n) :
    wedge (ω + η) θ = wedge ω θ + wedge η θ := by
  funext x
  exact add_mul _ _ _

theorem wedge_add_right {n : ℕ} (ω η θ : FormField n) :
    wedge ω (η + θ) = wedge ω η + wedge ω θ := by
  funext x
  exact mul_add _ _ _

end Rudin.PMA.Chapter10
