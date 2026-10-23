import Rudin.PMA.Chapter10.Primitive

set_option autoImplicit false
noncomputable section
open Set

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- At dimension one the factorization has no flip at all, leaving one actual
primitive on an open neighborhood of zero. -/
theorem dimension_one_has_no_flip (E : Set (Euclidean 1))
    (F : Euclidean 1 → Euclidean 1) (hE : IsOpen E) (h0E : (0 : Euclidean 1) ∈ E)
    (hF : C1On F E) (h0 : F 0 = 0) (hi : (fderiv ℝ F 0).IsInvertible) :
    ∃ (g : Euclidean 1 → Euclidean 1) (U : Set (Euclidean 1)),
      PrimitiveNearZero g ∧ IsOpen U ∧ (0 : Euclidean 1) ∈ U ∧ U ⊆ E ∧ EqOn F g U := by
  obtain ⟨G, B, U, hGlen, hBlen, hG, _, hU, h0U, hUE, he⟩ :=
    pma10_7 1 (by decide) E F hE h0E hF h0 hi
  obtain ⟨g, rfl⟩ := List.length_eq_one_iff.mp hGlen
  have hB : B = [] := List.length_eq_zero_iff.mp (by simpa using hBlen)
  subst B
  refine ⟨g, U, hG g (by simp), hU, h0U, hUE, ?_⟩
  intro x hx
  simpa only [List.map_nil, List.nil_append, composeMaps_cons, composeMaps_nil] using he hx

/-- The plane flip has a zero first diagonal derivative, so an elimination
argument that assumes a nonzero diagonal pivot would miss this input. -/
theorem plane_flip_requires_off_diagonal_pivot :
    (operatorMatrix (flipOperator (0 : Fin 2) 1)) 0 0 = 0 ∧
    (operatorMatrix (flipOperator (0 : Fin 2) 1)) 1 0 = 1 ∧
    (flipOperator (0 : Fin 2) 1).IsInvertible := by
  refine ⟨?_, ?_, flipOperator_isInvertible 0 1⟩ <;>
    simp [operatorMatrix_apply]

/-- The full nonlinear theorem accepts that off-diagonal invertible example
and returns precisely two primitive factors and one flip-or-identity factor. -/
theorem plane_flip_has_two_primitive_factors :
    ∃ (g₁ g₂ : Euclidean 2 → Euclidean 2) (b : Operator 2 2)
      (U : Set (Euclidean 2)),
      PrimitiveNearZero g₁ ∧ PrimitiveNearZero g₂ ∧
      (IsFlip b ∨ b = ContinuousLinearMap.id ℝ (Euclidean 2)) ∧
      IsOpen U ∧ (0 : Euclidean 2) ∈ U ∧
      EqOn (flipOperator (0 : Fin 2) 1) (fun x => b (g₂ (g₁ x))) U := by
  let F : Euclidean 2 → Euclidean 2 := flipOperator (0 : Fin 2) 1
  have hF : C1On F univ :=
    (c1On_iff_contDiffOn isOpen_univ).mpr
      (flipOperator (0 : Fin 2) 1).contDiff.contDiffOn
  have hd : HasFDerivAt F (flipOperator (0 : Fin 2) 1) 0 :=
    (flipOperator (0 : Fin 2) 1).hasFDerivAt
  have hi : (fderiv ℝ F 0).IsInvertible := by
    rw [hd.fderiv]
    exact flipOperator_isInvertible 0 1
  obtain ⟨G, B, U, hGlen, hBlen, hG, hB, hU, h0U, _, he⟩ :=
    pma10_7 2 (by decide) univ F isOpen_univ (mem_univ _) hF
      (map_zero (flipOperator (0 : Fin 2) 1)) hi
  obtain ⟨g₂, g₁, rfl⟩ := List.length_eq_two.mp hGlen
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hBlen)
  refine ⟨g₁, g₂, b, U, hG g₁ (by simp), hG g₂ (by simp),
    hB b (by simp), hU, h0U, ?_⟩
  intro x hx
  simpa only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    composeMaps_cons, composeMaps_nil] using he hx

end Rudin.PMA.Chapter10.FidelityProbes
