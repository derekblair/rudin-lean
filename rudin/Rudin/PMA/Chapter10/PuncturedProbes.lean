import Rudin.PMA.Chapter10.PuncturedPlane
import Rudin.PMA.Chapter10.PuncturedSphere

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- Negative as well as positive nonzero integer multiplicities retain the
circle obstruction. Its radius remains arbitrary and its map is explicit. -/
theorem nonzero_circle_multiplicity_not_boundary (r : ℝ) (hr : 0 < r)
    (z : ℤ) (hz : z ≠ 0) :
    ∃ σ : C2Simplex 1 2 (puncturedSpace 2),
      σ.map = (fun u => puncturedCircleMap r (fun _ => 2 * Real.pi * u 0)) ∧
      chainIntegral angularForm (Finsupp.single σ z) = (z : ℝ) * (2 * Real.pi) ∧
      ¬ ∃ Δ : SimplexChain 2 2 (puncturedSpace 2),
        ChainEq (chainBoundary Δ) (Finsupp.single σ z) := by
  obtain ⟨γ, _, _, _, _, hI, _, σ, hm, htransport, _, _⟩ := pma10_36.2.2 r hr
  have hc := pma10_36.1
  have hb : surfaceIntegral σ.toSurface angularForm = 2 * Real.pi := by
    have h := (htransport angularForm hc.1.isFormOn).trans hI
    simpa only [chainIntegral_single, Int.cast_one, one_mul] using h
  have hi : chainIntegral angularForm (Finsupp.single σ z) = (z : ℝ) * (2 * Real.pi) := by
    rw [chainIntegral_single, hb]
  refine ⟨σ, hm, hi, ?_⟩
  apply not_boundary_of_closed_integral_ne_zero (puncturedSpace_isOpen 2) hc
  rw [hi]
  exact mul_ne_zero (Int.cast_ne_zero.mpr hz) (by positivity)

/-- Adding any actual three-chain boundary to the spherical cycle preserves
its nonzero radial integral and its obstruction to being a boundary. -/
theorem sphere_obstruction_survives_boundary_addition :
    ∃ Γ : SimplexChain 2 3 (puncturedSpace 3),
      ChainEq (chainBoundary Γ) 0 ∧
      ∀ Δ : SimplexChain 3 3 (puncturedSpace 3),
        chainIntegral radialForm (Γ + chainBoundary Δ) = 4 * Real.pi ∧
        ¬ ∃ Λ : SimplexChain 3 3 (puncturedSpace 3),
          ChainEq (chainBoundary Λ) (Γ + chainBoundary Δ) := by
  obtain ⟨Φ, _, _, _, _, hI, _, Γ, htransport, hcycle, _⟩ := pma10_37.2.2.2
  have hc := pma10_37.2.1
  have hb : chainIntegral radialForm Γ = 4 * Real.pi :=
    (htransport radialForm hc.1.isFormOn).trans hI
  refine ⟨Γ, hcycle, fun Δ => ?_⟩
  have hd : chainIntegral radialForm (chainBoundary Δ) = 0 :=
    pma10_35.2.2.2.2.1 2 3 (puncturedSpace 3) radialForm (puncturedSpace_isOpen 3) hc Δ
  have hi : chainIntegral radialForm (Γ + chainBoundary Δ) = 4 * Real.pi := by
    rw [map_add, hb, hd, add_zero]
  refine ⟨hi, ?_⟩
  apply not_boundary_of_closed_integral_ne_zero (puncturedSpace_isOpen 3) hc
  rw [hi]
  positivity

end Rudin.PMA.Chapter10.FidelityProbes
