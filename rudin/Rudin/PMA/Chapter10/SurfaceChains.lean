import Rudin.PMA.Chapter10.CellTriangulation

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def Surface.asSimplex {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (hD : Φ.domain = .simplex) (h₂ : Φ.IsC2) : C2Simplex k n E where
  map := Φ.map
  regularity := by simpa only [Surface.IsC2, hD, ParameterDomain.carrier] using h₂
  mapsTo := by simpa only [hD, ParameterDomain.carrier] using Φ.mapsTo

/-- The actual chain of a C2 surface: one simplex, or the finite affine cell subdivision. -/
def Surface.integralChain {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (h₂ : Φ.IsC2) : SimplexChain k n E :=
  match hD : Φ.domain with
  | .cell C => Φ.staircaseChain C hD h₂
  | .simplex => Finsupp.single (Φ.asSimplex hD h₂) 1

def Surface.boundaryChain {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface (k+1) n E)
    (h₂ : Φ.IsC2) : SimplexChain k n E := chainBoundary (Φ.integralChain h₂)

lemma Surface.integralChain_integral {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (h₂ : Φ.IsC2) {ω : FormField n} (hω : IsFormOn E k ω) :
    chainIntegral ω (Φ.integralChain h₂) = surfaceIntegral Φ ω := by
  unfold Surface.integralChain
  split
  · exact staircaseChain_integral Φ _ _ h₂ hω
  · rename_i hD
    rw [chainIntegral_single, Int.cast_one, one_mul]
    apply surfaceIntegral_congr_map
    · exact hD.symm
    · rfl

lemma Surface.stokes {k n : ℕ} {E : Set (Euclidean n)} (hE : IsOpen E)
    (Φ : Surface (k+1) n E) (h₂ : Φ.IsC2) {ω : FormField n} (hω : IsCFormOn 1 E k ω) :
    surfaceIntegral Φ (exteriorDerivative ω) = chainIntegral ω (Φ.boundaryChain h₂) := by
  rw [← Φ.integralChain_integral h₂ (pma10_18.1 _ _ _ _ hE hω).1]
  exact pma10_33 _ _ _ _ _ hE hω

end Rudin.PMA.Chapter10
