import Rudin.PMA.Chapter10.DiffeomorphicExactness

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- A closed C1 two-form on a convex domain vanishes on every functional
cycle, without requiring that cycle to be supplied as a chain boundary. -/
theorem convex_closed_two_form_cycle_zero {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (hc : Convex ℝ E) {ω : FormField n}
    (hω : IsClosedOn E 2 ω) (Γ : SimplexChain 2 n E)
    (hΓ : ChainEq (chainBoundary Γ) 0) : chainIntegral ω Γ = 0 := by
  have he : IsExactOn E 2 ω := pma10_39 1 n E ω hE hc hω
  exact pma10_35.2.2.2.1 1 n E ω hE hω.1.isFormOn he Γ hΓ

/-- Exactness is transported in just the requested degree. Neither convexity
nor exactness in any other degree is assumed on the starting domain. -/
theorem fixed_degree_transport_cycle_zero {n m k : ℕ}
    {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    (hE : IsOpen E) (hV : IsOpen V) (e : C2DomainEquivalence E V)
    (h : ClosedFormsExactOn E k) {ω : FormField m}
    (hω : IsClosedOn V (k + 1) ω) (Γ : SimplexChain (k + 1) m V)
    (hΓ : ChainEq (chainBoundary Γ) 0) : chainIntegral ω Γ = 0 := by
  have he := pma10_40.1 n m k E V e hE hV h ω hω
  exact pma10_35.2.2.2.1 k m V ω hV hω.1.isFormOn he Γ hΓ

end Rudin.PMA.Chapter10.FidelityProbes
