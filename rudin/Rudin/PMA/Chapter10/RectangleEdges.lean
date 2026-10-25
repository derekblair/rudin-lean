import Rudin.PMA.Chapter10.SurfacePrecomposition

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The four counterclockwise sides, each on its actual coordinate interval. -/
def rectangleEdgeCell (C : Cell 2) : Fin 4 → Cell 1 :=
  ![intervalCell (C.lower 0) (C.upper 0) (C.lower_le_upper 0),
    intervalCell (C.lower 1) (C.upper 1) (C.lower_le_upper 1),
    intervalCell (C.lower 0) (C.upper 0) (C.lower_le_upper 0),
    intervalCell (C.lower 1) (C.upper 1) (C.lower_le_upper 1)]

def rectangleEdgeMap (C : Cell 2) : Fin 4 → Coord 1 → Coord 2 :=
  ![fun u => ![u 0, C.lower 1],
    fun u => ![C.upper 0, u 0],
    fun u => ![C.lower 0 + C.upper 0 - u 0, C.upper 1],
    fun u => ![C.lower 0, C.lower 1 + C.upper 1 - u 0]]

lemma rectangleEdgeMap_contDiff (C : Cell 2) (i : Fin 4) :
    ContDiff ℝ 1 (rectangleEdgeMap C i) := by
  have hc : ContDiff ℝ 1 (fun u : Coord 1 => u 0) := contDiff_apply ℝ ℝ 0
  have hpair {f g : Coord 1 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
      ContDiff ℝ 1 (fun u => (![f u, g u] : Coord 2)) := by
    apply contDiff_pi.mpr
    intro j
    fin_cases j
    · exact hf
    · exact hg
  fin_cases i
  · exact hpair hc contDiff_const
  · exact hpair contDiff_const hc
  · exact hpair (contDiff_const.sub hc) contDiff_const
  · exact hpair contDiff_const (contDiff_const.sub hc)

lemma rectangleEdgeMap_mapsTo (C : Cell 2) (i : Fin 4) :
    MapsTo (rectangleEdgeMap C i) (rectangleEdgeCell C i).carrier C.carrier := by
  intro u hu
  have ht := (Cell.mem_carrier.mp hu) 0
  rw [Cell.mem_carrier]
  fin_cases i
  · change C.lower 0 ≤ u 0 ∧ u 0 ≤ C.upper 0 at ht
    intro j
    fin_cases j
    · exact ht
    · exact ⟨le_rfl, C.lower_le_upper 1⟩
  · change C.lower 1 ≤ u 0 ∧ u 0 ≤ C.upper 1 at ht
    intro j
    fin_cases j
    · exact ⟨C.lower_le_upper 0, le_rfl⟩
    · exact ht
  · change C.lower 0 ≤ u 0 ∧ u 0 ≤ C.upper 0 at ht
    intro j
    fin_cases j
    · change C.lower 0 ≤ C.lower 0 + C.upper 0 - u 0 ∧
        C.lower 0 + C.upper 0 - u 0 ≤ C.upper 0
      constructor <;> linarith
    · exact ⟨C.lower_le_upper 1, le_rfl⟩
  · change C.lower 1 ≤ u 0 ∧ u 0 ≤ C.upper 1 at ht
    intro j
    fin_cases j
    · exact ⟨le_rfl, C.lower_le_upper 0⟩
    · change C.lower 1 ≤ C.lower 1 + C.upper 1 - u 0 ∧
        C.lower 1 + C.upper 1 - u 0 ≤ C.upper 1
      constructor <;> linarith

def rectangleEdgeSurface {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (C : Cell 2) (hD : Φ.domain = .cell C) (i : Fin 4) : Surface 1 n E :=
  Φ.precompose (.cell (rectangleEdgeCell C i)) (rectangleEdgeMap C i)
    (rectangleEdgeMap_contDiff C i)
    (by rw [hD]; exact rectangleEdgeMap_mapsTo C i)

def rectangleBoundaryIntegral {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (C : Cell 2) (hD : Φ.domain = .cell C) (ω : FormField n) : ℝ :=
  ∑ i : Fin 4, surfaceIntegral (rectangleEdgeSurface Φ C hD i) ω

lemma rectangleEdgeSurface_integrable {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C)
    {ω : FormField n} (hω : IsFormOn E 1 ω) (i : Fin 4) :
    IteratedRIntegrable (rectangleEdgeCell C i)
      (surfaceIntegrand (rectangleEdgeSurface Φ C hD i) ω) :=
  iteratedRIntegrable_of_continuousOn
    ((rectangleEdgeSurface Φ C hD i).continuousOn_integrand hω)

end Rudin.PMA.Chapter10
