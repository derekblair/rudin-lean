import Rudin.PMA.Chapter09.Linear

set_option autoImplicit false
noncomputable section
open Set Module
open scoped BigOperators
namespace Rudin.PMA.Chapter09.FidelityProbes

/-- The empty family spans the zero vector, including in a nonzero ambient space. -/
theorem empty_span (x : ℝ) :
    x ∈ Submodule.span ℝ (range (fun i : Fin 0 => Fin.elim0 i : Fin 0 → ℝ)) ↔ x = 0 := by
  have h := (pma9_1.{0,0}.1 ℝ).2.1 0 (fun i : Fin 0 => Fin.elim0 i) x
  simpa using h

/-- Empty sets do not become linear subspaces merely by vacuous closure. -/
theorem empty_not_subspace : ¬ IsLinearSubspace (∅ : Set ℝ) := by
  intro h
  exact Set.not_nonempty_empty h.1

/-- Dimension zero is represented faithfully. -/
theorem dimension_zero : HasDimension (Euclidean 0) 0 := pma9_2.{0}.2 0

theorem real_dimension_one : HasDimension ℝ 1 := by
  apply (hasDimension_iff_finrank 1).mpr
  simp

/-- A singular endomorphism is rejected by the invertibility characterization. -/
theorem zero_plane_not_unit : ¬ IsUnit (0 : Operator 2 2) := by
  rw [(pma9_8 2).1]
  intro h
  have hz := h.1 (a₁ := standardBasis 2 0) (a₂ := 0) (by simp)
  have he := congrArg (fun x : Euclidean 2 => x 0) hz
  simpa using he

/-- In dimension zero the zero operator is also the invertible identity. -/
theorem zero_dimension_unit : IsUnit (0 : Operator 0 0) := by
  apply ((pma9_8 0).1 0).mpr
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

theorem noncommuting_plane_operators :
    ∃ A B : Operator 2 2, A.comp B ≠ B.comp A := pma9_6.2.2.1

theorem negative_scalar_norm (A : Operator 2 3) : ‖(-2 : ℝ) • A‖ = 2 * ‖A‖ := by
  simpa using (pma9_7.2.1 2 3 A 0 (-2)).2.2.2.1

/-- Frobenius control includes the rectangular zero-row case. -/
theorem zero_target_norm (A : Operator 3 0) : ‖A‖ = 0 := by
  have h := pma9_9.{0,0,0,0}.2.1 3 0 A
  have hz : ‖A‖ ≤ 0 := by simpa using h
  exact le_antisymm hz (norm_nonneg _)

end Rudin.PMA.Chapter09.FidelityProbes
