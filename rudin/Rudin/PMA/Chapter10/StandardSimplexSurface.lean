import Rudin.PMA.Chapter10.SimplexChains

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The standard simplex as a genuine C² simplex in any ambient open parameter
neighborhood containing it. Its map is the fixed coordinate-to-Euclidean map. -/
def standardC2Simplex {k : ℕ} (U : Set (Euclidean k))
    (hSU : MapsTo (coordEquivEuclidean k) (standardSimplex k) U) : C2Simplex k k U where
  map := coordEquivEuclidean k
  regularity := ⟨univ, isOpen_univ, subset_univ _, (coordEquivEuclidean k).contDiff.contDiffOn⟩
  mapsTo := hSU

end Rudin.PMA.Chapter10
