import Rudin.PMA.Chapter10.ExactnessTransport
import Rudin.PMA.Chapter10.Poincare

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Exactness in a fixed positive degree is invariant under an actual
C² equivalence of open domains. Convex open domains supply the property. -/
def pma10_40_contract : Prop :=
  (∀ (n m k : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
      (e : C2DomainEquivalence E V), IsOpen E → IsOpen V →
    ClosedFormsExactOn E k → ClosedFormsExactOn V k) ∧
  (∀ (n m : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
      (e : C2DomainEquivalence E V), IsOpen E → IsOpen V → Convex ℝ E →
    AllClosedFormsExactOn V)

theorem pma10_40 : pma10_40_contract := by
  refine ⟨fun n m k E V e hE hV h => e.transports_degree_exactness hE hV h, ?_⟩
  intro n m E V e hE hV hc
  apply e.transports_exactness hE hV
  intro k ω hω
  exact closed_exact_on_convex hE hc hω

end Rudin.PMA.Chapter10
