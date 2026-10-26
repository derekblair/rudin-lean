import Rudin.PMA.Chapter10.ClosedFormConsequences
import Rudin.PMA.Chapter10.SphereBoundary
import Rudin.PMA.Chapter10.SquareBoundaries

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def puncturedSpace (n : ℕ) : Set (Euclidean n) := {0}ᶜ

/-- The literal angular one-form (x dy − y dx)/(x²+y²). -/
def angularForm : FormField 2 := fun x =>
  (x 0 ^ 2 + x 1 ^ 2)⁻¹ • (x 0 • dx 1 - x 1 • dx 0)

def puncturedCircleMap (r : ℝ) (u : Coord 1) : Euclidean 2 :=
  (coordEquivEuclidean 2) ![r * Real.cos (u 0), r * Real.sin (u 0)]

/-- The denominator ‖x‖³ is (x²+y²+z²)^(3/2); the contract below
includes the explicit real-power identity fixing this convention. -/
def radialForm : FormField 3 := fun x =>
  (‖x‖ ^ 3)⁻¹ • (x 0 • (dx 1 * dx 2) + x 1 • (dx 2 * dx 0) +
    x 2 • (dx 0 * dx 1))

def pma10_36_contract : Prop :=
  IsClosedOn (puncturedSpace 2) 1 angularForm ∧
  ¬ IsExactOn (puncturedSpace 2) 1 angularForm ∧
  ∀ r : ℝ, 0 < r → ∃ γ : Surface 1 2 (puncturedSpace 2),
    γ.domain = .cell ellipseCell ∧ γ.map = puncturedCircleMap r ∧
    γ.map 0 = γ.map (fun _ => 2 * Real.pi) ∧
    γ.domain.Integrable (surfaceIntegrand γ angularForm) ∧
    surfaceIntegral γ angularForm = 2 * Real.pi ∧ surfaceIntegral γ angularForm ≠ 0 ∧
    ∃ σ : C2Simplex 1 2 (puncturedSpace 2),
      σ.map = (fun u => puncturedCircleMap r (fun _ => 2 * Real.pi * u 0)) ∧
      (∀ ω : FormField 2, IsFormOn (puncturedSpace 2) 1 ω →
        chainIntegral ω (Finsupp.single σ 1) = surfaceIntegral γ ω) ∧
      ChainEq (chainBoundary (Finsupp.single σ 1)) 0 ∧
      ¬ ∃ Δ : SimplexChain 2 2 (puncturedSpace 2),
        ChainEq (chainBoundary Δ) (Finsupp.single σ 1)

def pma10_37_contract : Prop :=
  (∀ x : Euclidean 3, ‖x‖ ^ 3 =
    Real.rpow (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) (3 / 2 : ℝ)) ∧
  IsClosedOn (puncturedSpace 3) 2 radialForm ∧
  ¬ IsExactOn (puncturedSpace 3) 2 radialForm ∧
  ∃ Φ : Surface 2 3 (puncturedSpace 3),
    Φ.domain = .cell sphereRectangleCell ∧ Φ.map = sphereRectangleMap ∧
    (∀ u ∈ sphereRectangleCell.carrier, surfaceIntegrand Φ radialForm u = Real.sin (u 0)) ∧
    Φ.domain.Integrable (surfaceIntegrand Φ radialForm) ∧
    surfaceIntegral Φ radialForm = 4 * Real.pi ∧ surfaceIntegral Φ radialForm ≠ 0 ∧
    ∃ Γ : SimplexChain 2 3 (puncturedSpace 3),
      (∀ ω : FormField 3, IsFormOn (puncturedSpace 3) 2 ω →
        chainIntegral ω Γ = surfaceIntegral Φ ω) ∧
      ChainEq (chainBoundary Γ) 0 ∧
      ¬ ∃ Δ : SimplexChain 3 3 (puncturedSpace 3), ChainEq (chainBoundary Δ) Γ

end Rudin.PMA.Chapter10
