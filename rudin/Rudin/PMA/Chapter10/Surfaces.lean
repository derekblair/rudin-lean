import Rudin.PMA.Chapter10.FormsCore

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The two parameter domains admitted in the source development. -/
inductive ParameterDomain (k : ℕ)
  | cell (C : Cell k)
  | simplex

def ParameterDomain.carrier {k : ℕ} : ParameterDomain k → Set (Coord k)
  | .cell C => C.carrier
  | .simplex => standardSimplex k

def ParameterDomain.integral {k : ℕ} (D : ParameterDomain k) (f : Coord k → ℝ) : ℝ :=
  match D with
  | .cell C => iteratedRIntegral C f
  | .simplex => simplexRIntegral f

/-- A parametrized surface is a map, with no injectivity or immersion requirement.
Regularity on its compact domain means an extension to an open neighborhood. -/
structure Surface (k n : ℕ) (E : Set (Euclidean n)) where
  domain : ParameterDomain k
  map : Coord k → Euclidean n
  neighborhood : Set (Coord k)
  open_neighborhood : IsOpen neighborhood
  domain_subset : domain.carrier ⊆ neighborhood
  regularity : ContDiffOn ℝ 1 map neighborhood
  mapsTo : MapsTo map domain.carrier E

def Surface.IsC2 {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) : Prop :=
  ∃ U : Set (Coord k), IsOpen U ∧ Φ.domain.carrier ⊆ U ∧ ContDiffOn ℝ 2 Φ.map U

def surfaceIntegrand {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (ω : FormField n) (u : Coord k) : ℝ :=
  evaluateForm k (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (ω (Φ.map u))

def surfaceIntegral {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (ω : FormField n) : ℝ := Φ.domain.integral (surfaceIntegrand Φ ω)

/-- Rudin's equality of forms is equality of all their integration functionals.
Its equivalence to pointwise equality requires the separation theorem 10.15. -/
def FormEqOn {n : ℕ} (E : Set (Euclidean n)) (k : ℕ) (ω η : FormField n) : Prop :=
  ∀ Φ : Surface k n E, surfaceIntegral Φ ω = surfaceIntegral Φ η

/-- The source's redundant expansion over all ordered coordinate tuples. -/
def formFromCoefficients {n k : ℕ} (a : (Fin k → Fin n) → Euclidean n → ℝ) :
    FormField n := fun x => ∑ I, a I x • coordinateWedge I

/-- A scalar function viewed as a degree-zero exterior-algebra field. -/
def scalarForm {n : ℕ} (f : Euclidean n → ℝ) : FormField n :=
  fun x => algebraMap ℝ (CotangentExterior n) (f x)

end Rudin.PMA.Chapter10
