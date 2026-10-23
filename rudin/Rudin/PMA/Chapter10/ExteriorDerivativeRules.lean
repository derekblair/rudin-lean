import Rudin.PMA.Chapter10.ExteriorDerivative

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

/-- All coefficient functions are differentiable at the given point. -/
def CoefficientsDifferentiableAt {n : ℕ} (ω : FormField n) (x : Euclidean n) : Prop :=
  ∀ S : Finset (Fin n), DifferentiableAt ℝ (formCoefficient ω S) x

theorem IsCFormOn.coefficientsDifferentiableAt {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsCFormOn 1 E k ω) (hE : IsOpen E) {x : Euclidean n} (hx : x ∈ E) :
    CoefficientsDifferentiableAt ω x := fun S =>
  (hω.2 S).differentiableOn_one.differentiableAt (hE.mem_nhds hx)

theorem wedge_expansion_all {n : ℕ} (ω η : FormField n) :
    wedge ω η = fun y => ∑ p : Finset (Fin n) × Finset (Fin n),
      (formCoefficient ω p.1 y * formCoefficient η p.2 y) •
        (exteriorBasis n p.1 * exteriorBasis n p.2) := by
  funext y
  change ω y * η y = _
  rw [formField_expansion ω y, formField_expansion η y]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- The coefficient derivative obeys the ordinary product rule in the finite
exterior algebra; the graded sign enters only when dx is commuted past a form. -/
theorem coefficientDerivative_wedge {n : ℕ} {ω η : FormField n} {x : Euclidean n}
    (hω : CoefficientsDifferentiableAt ω x) (hη : CoefficientsDifferentiableAt η x) (i : Fin n) :
    coefficientDerivative (wedge ω η) i x =
      coefficientDerivative ω i x * η x + ω x * coefficientDerivative η i x := by
  classical
  have hd := coefficientDerivative_sum_smul
    (fun (p : Finset (Fin n) × Finset (Fin n)) (y : Euclidean n) =>
      formCoefficient ω p.1 y * formCoefficient η p.2 y)
    (fun p : Finset (Fin n) × Finset (Fin n) => exteriorBasis n p.1 * exteriorBasis n p.2)
    (fun p => (hω p.1).mul (hη p.2)) i
  rw [wedge_expansion_all ω η, hd]
  simp only [coordinatePartial_mul (hω _) (hη _), Fintype.sum_prod_type,
    add_smul, Finset.sum_add_distrib]
  rw [formField_expansion η x, formField_expansion ω x]
  simp only [coefficientDerivative, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  congr 1 <;> exact Finset.sum_comm

theorem exteriorDerivative_wedge {n k m : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hE : IsOpen E) (hω : IsCFormOn 1 E k ω) (hη : IsCFormOn 1 E m η)
    {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative (wedge ω η) x =
      wedge (exteriorDerivative ω) η x + ((-1 : ℝ)^k) • wedge ω (exteriorDerivative η) x := by
  classical
  have hcomm (i : Fin n) : dx i * ω x = (-1 : ℝ)^k • (ω x * dx i) := by
    have hdx : dx i ∈ (⋀[ℝ]^1 (Coord n)) := by
      rw [dx_eq_coordinateWedge]
      exact coordinateWedge_mem _
    simpa only [Nat.one_mul] using homogeneous_mul_anticomm hdx (hω.1 x hx)
  simp only [exteriorDerivative_eq_sum, wedge]
  simp_rw [coefficientDerivative_wedge (hω.coefficientsDifferentiableAt hE hx)
    (hη.coefficientsDifferentiableAt hE hx), mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    exact (mul_assoc _ _ _).symm
  · apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, hcomm, smul_mul_assoc, mul_assoc]

/-- Explicit second exterior derivative before antisymmetric cancellation. -/
theorem exteriorDerivative_twice_formula {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsCFormOn 2 E k ω) {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative (exteriorDerivative ω) x =
      ∑ j : Fin n, ∑ i : Fin n, ∑ S : Finset (Fin n),
        coordinatePartial (fun y => coordinatePartial (formCoefficient ω S) y i) x j •
          (dx j * (dx i * exteriorBasis n S)) := by
  classical
  have he : exteriorDerivative ω = fun y => ∑ p : Fin n × Finset (Fin n),
      coordinatePartial (formCoefficient ω p.2) y p.1 • (dx p.1 * exteriorBasis n p.2) := by
    funext y
    simp only [exteriorDerivative, Fintype.sum_prod_type]
  rw [exteriorDerivative_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he]
  have hd (p : Fin n × Finset (Fin n)) :
      DifferentiableAt ℝ (fun y => coordinatePartial (formCoefficient ω p.2) y p.1) x :=
    (contDiffOn_coordinatePartial (r := 1) hE (hω.2 p.2) p.1).differentiableOn_one.differentiableAt
      (hE.mem_nhds hx)
  rw [coefficientDerivative_sum_smul _ _ hd]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, mul_smul_comm]

theorem exteriorDerivative_twice_eq_zero {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsCFormOn 2 E k ω) {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative (exteriorDerivative ω) x = 0 := by
  classical
  let A (i j : Fin n) : CotangentExterior n := ∑ S : Finset (Fin n),
    coordinatePartial (fun y => coordinatePartial (formCoefficient ω S) y i) x j •
      (dx j * (dx i * exteriorBasis n S))
  have ha (i j : Fin n) : A i j = -A j i := by
    dsimp [A]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    rw [coordinatePartial_commute hE (hω.2 S) hx i j,
      ← mul_assoc, dx_mul_swap j i, neg_mul, mul_assoc, smul_neg]
  have he : exteriorDerivative (exteriorDerivative ω) x = ∑ i, ∑ j, A i j := by
    rw [exteriorDerivative_twice_formula hE hω hx]
    exact Finset.sum_comm
  have hn : (∑ i, ∑ j, A i j) = -(∑ i, ∑ j, A i j) := by
    calc
      _ = ∑ j, ∑ i, A i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -A j i := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        exact ha i j
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have hz : (2 : ℝ) • (∑ i, ∑ j, A i j) = 0 := by
    rw [two_smul]
    exact eq_neg_iff_add_eq_zero.mp hn
  rw [he]
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

theorem pma10_20 : pma10_20_contract := by
  constructor
  · intro n k m E ω η hE hω hη x hx
    exact exteriorDerivative_wedge hE hω hη hx
  · intro n k E ω hE hω
    exact ⟨isCFormOn_exteriorDerivative (r := 1) hE hω,
      fun x hx => exteriorDerivative_twice_eq_zero hE hω hx⟩

end Rudin.PMA.Chapter10
