import Rudin.PMA.Chapter10.CoordinateDifferentiation
import Rudin.PMA.Chapter10.PrefixCoordinates
import Rudin.PMA.Chapter10.ConvexPrimitiveIntegral

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Source10.38: a coordinate primitive on an arbitrary convex open domain.
Vanishing later coordinate partials is preserved; no product-domain or fixed
fiber basepoint hypothesis is imposed. -/
def pma10_38_contract : Prop :=
  ∀ (n : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ) (p : Fin n),
    IsOpen E → Convex ℝ E → ContDiffOn ℝ 1 f E →
      (∀ x ∈ E, ∀ j : Fin n, p < j → coordinatePartial f x j = 0) →
      ∃ F : Euclidean n → ℝ, ContDiffOn ℝ 1 F E ∧
        (∀ x ∈ E, coordinatePartial F x p = f x) ∧
        (∀ x ∈ E, ∀ j : Fin n, p < j → coordinatePartial F x j = 0)

theorem pma10_38 : pma10_38_contract := by
  intro n E f p hE hc hf hz
  obtain ⟨a, ha, ham, hap, haz⟩ := exists_prefix_retraction hE hc p
  exact exists_coordinate_primitive_of_retraction hE hc hf p hz ha ham hap haz

end Rudin.PMA.Chapter10
