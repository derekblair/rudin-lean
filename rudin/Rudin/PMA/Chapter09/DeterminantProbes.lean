import Rudin.PMA.Chapter09.Determinants

/-! Independent clients of the literal all-tuple determinant definition. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators Matrix

namespace Rudin.PMA.Chapter09.FidelityProbes

theorem all_tuple_two_by_two_value :
    (∑ t : Fin 2 → Fin 2,
      (tupleSign (fun i => ((t i).val : ℤ)) : ℝ) *
        ∏ i, (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) ℝ) i (t i)) = -2 := by
  rw [← pma9_33.2.2.2.2.1 2]
  norm_num [Matrix.det_fin_two]

end Rudin.PMA.Chapter09.FidelityProbes
