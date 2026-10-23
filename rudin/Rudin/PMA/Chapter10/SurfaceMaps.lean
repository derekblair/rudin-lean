import Rudin.PMA.Chapter10.PullbackAlgebra

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- A surface's regularity neighborhood can be restricted to the preimage of its
open target set; its ambient extension is not assumed to land there globally. -/
def Surface.targetNeighborhood {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) :
    Set (Coord k) := Φ.neighborhood ∩ Φ.map ⁻¹' E

lemma Surface.targetNeighborhood_isOpen {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (hE : IsOpen E) : IsOpen Φ.targetNeighborhood :=
  Φ.regularity.continuousOn.isOpen_inter_preimage Φ.open_neighborhood hE

lemma Surface.domain_subset_targetNeighborhood {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) : Φ.domain.carrier ⊆ Φ.targetNeighborhood :=
  fun _ hu => ⟨Φ.domain_subset hu, Φ.mapsTo hu⟩

def Surface.mapBy {k n m : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    (Φ : Surface k n E) (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 1 T E) (hTV : MapsTo T E V) : Surface k m V where
  domain := Φ.domain
  map := T ∘ Φ.map
  neighborhood := Φ.targetNeighborhood
  open_neighborhood := Φ.targetNeighborhood_isOpen hE
  domain_subset := Φ.domain_subset_targetNeighborhood
  regularity := hT.comp (Φ.regularity.mono inter_subset_left) (fun _ hu => hu.2)
  mapsTo := hTV.comp Φ.mapsTo

/-- The identity parametrization in the Euclidean model has the original native
coordinate domain and the norm-changing linear equivalence as its map. -/
def identityParameterSurface {k : ℕ} (D : ParameterDomain k) : Surface k k univ where
  domain := D
  map := coordEquivEuclidean k
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (coordEquivEuclidean k).contDiff.contDiffOn
  mapsTo := mapsTo_univ _ _

def Surface.euclideanMap {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) :
    Euclidean k → Euclidean n := Φ.map ∘ (coordEquivEuclidean k).symm

lemma Surface.euclideanMap_parameter {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (u : Coord k) :
    Φ.euclideanMap ((identityParameterSurface Φ.domain).map u) = Φ.map u := by
  simp [Surface.euclideanMap, identityParameterSurface]

end Rudin.PMA.Chapter10
