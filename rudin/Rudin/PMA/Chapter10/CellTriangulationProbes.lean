import Rudin.PMA.Chapter10.CellTriangulation

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def thinCell : Cell 2 where
  lower := ![2, -1]
  upper := ![2, 3]
  lower_le_upper := by intro i; fin_cases i <;> norm_num

/-- The native simplex-chain integral of a collapsed rectangle vanishes
even for a map which varies along the remaining parameter direction. -/
theorem collapsed_cell_staircase_chain_zero {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (hD : Φ.domain = .cell thinCell) (h₂ : Φ.IsC2)
    {ω : FormField n} (hω : IsFormOn E 2 ω) :
    chainIntegral ω (Φ.staircaseChain thinCell hD h₂) = 0 := by
  rw [pma10_41.2.2.1 2 n E Φ thinCell hD h₂ ω hω]
  unfold surfaceIntegral
  rw [hD]
  change Chapter06.RIntegral _ 2 2 = 0
  exact (Chapter06.rsIntegral_same_endpoint _ id 2).2

/-- The zero-dimensional cell has one simplex with evaluation mass one;
it does not behave like a collapsed positive-dimensional rectangle. -/
theorem zero_dimensional_staircase_chain_evaluation {n : ℕ}
    {E : Set (Euclidean n)} (Φ : Surface 0 n E) (C : Cell 0)
    (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) (f : Euclidean n → ℝ)
    (hf : ContinuousOn f E) :
    chainIntegral (scalarForm f) (Φ.staircaseChain C hD h₂) = f (Φ.map 0) := by
  rw [pma10_41.2.2.1 0 n E Φ C hD h₂ (scalarForm f)
    (isFormOn_scalarForm hf)]
  exact pma10_11.2.2.2.2.2 n E Φ f

end Rudin.PMA.Chapter10.FidelityProbes
