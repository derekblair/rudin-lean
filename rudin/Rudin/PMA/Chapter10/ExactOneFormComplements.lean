import Rudin.PMA.Chapter10.ExteriorDerivative

set_option autoImplicit false
noncomputable section
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The exterior derivative of a coordinate one-form, supplying the explicit
calculation used in the concluding remark of PMA 10.19. -/
theorem exteriorDerivative_coordinateOneForm {n : ℕ} (i j : Fin n) (x : Euclidean n) :
    exteriorDerivative (coordinateOneForm i j) x = dx i * dx j := by
  have hd : DifferentiableAt ℝ (fun y : Euclidean n => y i) x :=
    (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).differentiableAt
  have hc (k : Fin n) : coefficientDerivative (coordinateOneForm i j) k x =
      coordinatePartial (fun y : Euclidean n => y i) x k • dx j := by
    change coefficientDerivative (fun y : Euclidean n => y i • dx j) k x = _
    simpa only [Fintype.sum_unique] using
      coefficientDerivative_sum_smul (fun _ : Unit => fun y : Euclidean n => y i)
        (fun _ : Unit => dx j) (fun _ => hd) k
  have hp (k : Fin n) : coordinatePartial (fun y : Euclidean n => y i) x k =
      if k = i then 1 else 0 := by
    rw [coordinatePartial_eq_fderiv hd]
    have he : HasFDerivAt (fun y : Euclidean n => y i)
        (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt
    rw [he.fderiv]
    simp [coordinateVector, EuclideanSpace.basisFun_apply, eq_comm]
  rw [exteriorDerivative_eq_sum]
  simp [hc, hp]

/-- PMA 10.19: the displayed derivative `d(x dy) = dx ∧ dy` is nonzero.
The earlier module proves nonexactness by integrating around the unit circle;
this supplement also proves the printed exterior-derivative calculation. -/
theorem pma10_19_xdy_derivative (x : Euclidean 2) :
    exteriorDerivative (coordinateOneForm (0 : Fin 2) 1) x = dx (0 : Fin 2) * dx 1 ∧
      dx (0 : Fin 2) * dx 1 ≠ 0 := by
  refine ⟨exteriorDerivative_coordinateOneForm 0 1 x, ?_⟩
  have hw : dx (0 : Fin 2) * dx 1 = coordinateWedge (![0, 1] : Fin 2 → Fin 2) := by
    simp [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply,
      Matrix.vecTail, Function.comp_def]
  intro hz
  have he := congrArg (evaluateForm 2 (fun i : Fin 2 => coordinateVector 2 i)) hz
  rw [hw, evaluateForm_coordinateWedge] at he
  have hidentity : (fun i j : Fin 2 => coordinateVector 2 j (![0, 1] i)) =
      (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coordinateVector, EuclideanSpace.basisFun_apply]
  rw [hidentity, Matrix.det_one, map_zero] at he
  norm_num at he

/-- PMA 10.19: `dx ∧ dy` is nonzero also in Rudin's operational sense of
form equality, which compares every admissible surface integral. The proved
10.15 separation theorem transfers the algebraic calculation to that sense. -/
theorem pma10_19_dxdy_not_formEqOn_zero :
    ¬ FormEqOn (Set.univ : Set (Euclidean 2)) 2
      (fun _ => dx (0 : Fin 2) * dx 1) 0 := by
  have hw : dx (0 : Fin 2) * dx 1 = coordinateWedge (![0, 1] : Fin 2 → Fin 2) := by
    simp [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply,
      Matrix.vecTail, Function.comp_def]
  have hform : IsFormOn (Set.univ : Set (Euclidean 2)) 2
      (fun _ => dx (0 : Fin 2) * dx 1) := by
    refine ⟨fun _ _ => ?_, fun _ => continuousOn_const⟩
    rw [hw]
    exact coordinateWedge_mem _
  intro h
  have he := (formEqOn_iff_eqOn isOpen_univ hform (isFormOn_zero univ)).mp h
  exact (pma10_19_xdy_derivative 0).2 (he (mem_univ (0 : Euclidean 2)))

end Rudin.PMA.Chapter10
