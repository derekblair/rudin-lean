import Rudin.PMA.Chapter09.LinearProbes
import Rudin.PMA.Chapter09.Rank
import Rudin.PMA.Chapter09.Determinants

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace Rudin.PMA.Chapter09.FidelityProbes

theorem repeated_integer_tuple_sign : tupleSign (![7,7,-3] : Fin 3 → ℤ) = 0 := by
  exact pma9_33.2.2.1 3 _ 0 1 (by decide) (by norm_num)

theorem transposed_sign (t : Fin 2 → ℤ) : tupleSign (t ∘ Equiv.swap 0 1) = -tupleSign t :=
  pma9_33.2.1 2 t 0 1 (by decide)

/-- The all-tuple convention retains the empty determinant equal to one. -/
theorem empty_all_tuple_determinant :
    (∑ t : Fin 0 → Fin 0,
      (tupleSign (fun i => ((t i).val : ℤ)) : ℝ) * ∏ i, (0 : Matrix (Fin 0) (Fin 0) ℝ) i (t i)) = 1 := by
  rw [← pma9_33.2.2.2.2.1 0 0]
  simp

theorem nonzero_singular_determinant :
    (operatorMatrix (0 : Operator 2 2)).det = 0 := by
  by_contra h
  exact zero_plane_not_unit ((pma9_36 2 0).mpr h)

/-- A projection is allowed to be oblique. -/
def obliqueProjection : Operator 2 2 :=
  ((EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ) + EuclideanSpace.proj 1).smulRight
    (coordinateVector 2 0)

theorem oblique_is_projection : IsProjection obliqueProjection.toLinearMap := by
  ext x i
  fin_cases i <;> simp [IsProjection, obliqueProjection, coordinateVector,
    EuclideanSpace.basisFun_apply]

theorem oblique_moves_second_axis : obliqueProjection (coordinateVector 2 1) = coordinateVector 2 0 := by
  simp [obliqueProjection, coordinateVector, EuclideanSpace.basisFun_apply]

/-- Rank zero retains an arbitrary constant image, rather than forcing that image to be zero. -/
theorem constant_map_has_rank_normal_form (c : Euclidean 3) :
    Nonempty (RankNormalForm (fun _ : Euclidean 2 => c) univ 0 0) := by
  have hc : C1On (fun _ : Euclidean 2 => c) univ :=
    (c1On_iff_contDiffOn isOpen_univ).mpr contDiff_const.contDiffOn
  have hr : ∀ x ∈ (univ : Set (Euclidean 2)),
      operatorRank (fderiv ℝ (fun _ : Euclidean 2 => c) x) = 0 := by
    intro x _
    simp [operatorRank]
  obtain ⟨N,_⟩ := pma9_32 2 3 0 univ (fun _ : Euclidean 2 => c) 0 0
    isOpen_univ (mem_univ _) hc hr (by ext; simp [IsProjection]) (by simp)
  exact ⟨N⟩

end Rudin.PMA.Chapter09.FidelityProbes
