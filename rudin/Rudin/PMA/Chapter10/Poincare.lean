import Rudin.PMA.Chapter10.ClosedFormConsequences
import Rudin.PMA.Chapter10.ConvexPrimitives
import Rudin.PMA.Chapter10.RadialPrimitive

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Source10.39: every closed C¹ form of positive degree on a convex open set
has a global C¹ primitive. No potential is assumed in the hypotheses. -/
def pma10_39_contract : Prop :=
  ∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → Convex ℝ E → IsClosedOn E (k + 1) ω → IsExactOn E (k + 1) ω

theorem pma10_39 : pma10_39_contract := by
  intro k n E ω hE hc hω
  exact closed_exact_on_convex hE hc hω

end Rudin.PMA.Chapter10
