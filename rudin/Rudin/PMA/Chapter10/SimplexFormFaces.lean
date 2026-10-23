import Rudin.PMA.Chapter10.SimplexOrientation

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

private lemma basisVector_component {n : ℕ} (i j : Fin n) :
    coordinateVector n i j = if j = i then 1 else 0 := by
  simp [coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]

lemma evaluateForm_dx_coordinateWedge {d : ℕ} (i : Fin (d + 1)) (I : Fin d → Fin (d + 1)) :
    evaluateForm (d + 1) (fun j => coordinateVector (d + 1) j) (dx i * coordinateWedge I) =
      (-1 : ℝ)^i.val *
        evaluateForm d (fun j => coordinateVector (d + 1) (i.succAbove j)) (coordinateWedge I) := by
  have he : dx i * coordinateWedge I = coordinateWedge (Fin.cons i I) := by
    simp [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, Function.comp_def]
  rw [he, evaluateForm_coordinateWedge, evaluateForm_coordinateWedge]
  let M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
    fun r c => coordinateVector (d + 1) c ((Fin.cons i I : Fin (d + 1) → Fin (d + 1)) r)
  let N : Matrix (Fin d) (Fin d) ℝ :=
    fun r c => coordinateVector (d + 1) (i.succAbove c) (I r)
  change M.det = (-1 : ℝ)^i.val * N.det
  have hM (j : Fin (d + 1)) : M 0 j = if i = j then 1 else 0 := by
    simp [M, basisVector_component]
  rw [Matrix.det_succ_row_zero]
  simp only [hM]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, mul_one]
    congr 1
  · intro j hj hji
    rw [if_neg hji.symm]
    simp
  · simp

/-- Cofactor sign of a coordinate differential, with the remaining coordinates
kept in their original increasing order. The zero-degree case is included. -/
lemma evaluateForm_dx_standard {d : ℕ} (i : Fin (d + 1)) {a : CotangentExterior (d + 1)}
    (ha : a ∈ (⋀[ℝ]^d (Coord (d + 1)))) :
    evaluateForm (d + 1) (fun j => coordinateVector (d + 1) j) (dx i * a) =
      (-1 : ℝ)^i.val * evaluateForm d (fun j => coordinateVector (d + 1) (i.succAbove j)) a := by
  rw [standard_expansion a ha]
  simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro S hS
  rw [standardWedge_eq_coordinateWedge, evaluateForm_dx_coordinateWedge]
  ring

lemma determinant_edge_alternating_faces {d : ℕ} (p : Fin (d + 1) → Coord d) :
    Matrix.det (fun i j : Fin d => p j.succ i - p 0 i) =
      ∑ l : Fin (d + 1), (-1 : ℝ)^l.val * Matrix.det (fun i j : Fin d => p (l.succAbove j) i) := by
  have hm : LinearMap.toMatrix' (vertexLinear p).toLinearMap =
      (fun i j : Fin d => p j.succ i - p 0 i) := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    exact congrArg (fun v : Coord d => v i) (vertexLinear_single p j)
  rw [← hm, LinearMap.det_toMatrix', vertexLinear_det_eq_augmented, Matrix.det_succ_column_zero]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [augmentedVertexMatrix, Fin.cons_zero, mul_one]
  congr 1
  rw [← Matrix.det_transpose]
  congr 1

lemma evaluateForm_upper_coordinateWedge {d : ℕ} (I : Fin d → Fin (d + 1)) :
    evaluateForm d (fun j => coordinateVector (d + 1) j.succ - coordinateVector (d + 1) 0)
      (coordinateWedge I) =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        evaluateForm d (fun j => coordinateVector (d + 1) (i.succAbove j)) (coordinateWedge I) := by
  simp only [evaluateForm_coordinateWedge, PiLp.sub_apply]
  exact determinant_edge_alternating_faces (fun j l => coordinateVector (d + 1) j (I l))

/-- The oriented tangent frame of the face opposite the zero vertex expands as
an alternating sum of the coordinate faces. This is an identity of evaluations. -/
lemma evaluateForm_upper_standard {d : ℕ} {a : CotangentExterior (d + 1)}
    (ha : a ∈ (⋀[ℝ]^d (Coord (d + 1)))) :
    evaluateForm d (fun j => coordinateVector (d + 1) j.succ - coordinateVector (d + 1) 0) a =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        evaluateForm d (fun j => coordinateVector (d + 1) (i.succAbove j)) a := by
  rw [standard_expansion a ha]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [standardWedge_eq_coordinateWedge, evaluateForm_upper_coordinateWedge]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end Rudin.PMA.Chapter10
