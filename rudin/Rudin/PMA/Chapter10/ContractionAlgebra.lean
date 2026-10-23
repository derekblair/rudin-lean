import Rudin.PMA.Chapter10.WedgeProducts
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Contraction by the i-th coordinate tangent vector. -/
def contractCoordinate {n : ℕ} (i : Fin n) :
    CotangentExterior n →ₗ[ℝ] CotangentExterior n :=
  CliffordAlgebra.contractLeft (LinearMap.proj i)

@[simp] lemma contractCoordinate_one {n : ℕ} (i : Fin n) :
    contractCoordinate i 1 = 0 := CliffordAlgebra.contractLeft_one _ _

lemma contractCoordinate_dx_mul {n : ℕ} (i j : Fin n) (a : CotangentExterior n) :
    contractCoordinate i (dx j * a) = (if i = j then a else 0) - dx j * contractCoordinate i a := by
  have h := CliffordAlgebra.contractLeft_ι_mul
    (Q := (0 : QuadraticForm ℝ (Coord n))) (LinearMap.proj i) (covectorBasis n j) a
  simpa only [contractCoordinate, dx, covectorBasis, Pi.basisFun_apply,
    LinearMap.proj_apply, Pi.single_apply, ite_smul, one_smul, zero_smul, eq_comm] using h

lemma coordinateWedge_succ {n k : ℕ} (I : Fin (k+1) → Fin n) :
    coordinateWedge I = dx (I 0) * coordinateWedge (fun j => I j.succ) := by
  exact ExteriorAlgebra.ιMulti_succ_apply _

lemma dx_mem {n : ℕ} (i : Fin n) : dx i ∈ (⋀[ℝ]^1 (Coord n)) := by
  simpa only [ExteriorAlgebra.exteriorPower, pow_one, dx] using
    (LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ) (covectorBasis n i))

lemma contractCoordinate_wedge_mem {n k : ℕ} (i : Fin n) (I : Fin (k+1) → Fin n) :
    contractCoordinate i (coordinateWedge I) ∈ (⋀[ℝ]^k (Coord n)) := by
  induction k with
  | zero =>
    rw [coordinateWedge_succ, coordinateWedge_zero, contractCoordinate_dx_mul,
      contractCoordinate_one, mul_zero, sub_zero]
    split_ifs
    · exact coordinateWedge_mem (fun j : Fin 0 => I j.succ)
    · exact Submodule.zero_mem _
  | succ k ih =>
    rw [coordinateWedge_succ, contractCoordinate_dx_mul]
    apply Submodule.sub_mem
    · split_ifs
      · exact coordinateWedge_mem _
      · exact Submodule.zero_mem _
    · simpa only [Nat.add_comm 1 k] using homogeneous_mul_mem (dx_mem (I 0))
        (ih (fun j => I j.succ))

lemma contractCoordinate_mem {n k : ℕ} (i : Fin n) {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^(k+1) (Coord n))) :
    contractCoordinate i a ∈ (⋀[ℝ]^k (Coord n)) := by
  rw [standard_expansion a ha, map_sum]
  apply Submodule.sum_mem
  intro S hS
  rw [map_smul, standardWedge_eq_coordinateWedge]
  exact Submodule.smul_mem _ _ (contractCoordinate_wedge_mem i _)

/-- The degree operator expressed through coordinate contraction. -/
def degreeOperator (n : ℕ) : CotangentExterior n →ₗ[ℝ] CotangentExterior n :=
  ∑ i : Fin n, (LinearMap.mulLeft ℝ (dx i)).comp (contractCoordinate i)

lemma degreeOperator_apply {n : ℕ} (a : CotangentExterior n) :
    degreeOperator n a = ∑ i, dx i * contractCoordinate i a := by
  simp [degreeOperator]

lemma degreeOperator_dx_mul {n : ℕ} (j : Fin n) (a : CotangentExterior n) :
    degreeOperator n (dx j * a) = dx j * a + dx j * degreeOperator n a := by
  classical
  simp only [degreeOperator_apply, contractCoordinate_dx_mul, mul_sub, Finset.sum_sub_distrib]
  have hs : (∑ i : Fin n, dx i * (if i = j then a else 0)) = dx j * a := by
    simp
  rw [hs]
  have he : (∑ i : Fin n, dx i * (dx j * contractCoordinate i a)) =
      -(dx j * ∑ i : Fin n, dx i * contractCoordinate i a) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← mul_assoc, dx_mul_swap i j, neg_mul, mul_assoc]
  rw [he, sub_neg_eq_add]

lemma degreeOperator_coordinateWedge {n k : ℕ} (I : Fin k → Fin n) :
    degreeOperator n (coordinateWedge I) = (k : ℝ) • coordinateWedge I := by
  induction k with
  | zero => simp [coordinateWedge_zero, degreeOperator_apply]
  | succ k ih =>
    rw [coordinateWedge_succ, degreeOperator_dx_mul, ih, mul_smul_comm]
    rw [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    exact add_comm _ _

/-- Euler's identity on every homogeneous exterior component, including degree zero. -/
lemma contraction_euler {n k : ℕ} {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) :
    (∑ i : Fin n, dx i * contractCoordinate i a) = (k : ℝ) • a := by
  rw [← degreeOperator_apply, standard_expansion a ha, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [map_smul, standardWedge_eq_coordinateWedge, degreeOperator_coordinateWedge,
    smul_comm]

end Rudin.PMA.Chapter10
