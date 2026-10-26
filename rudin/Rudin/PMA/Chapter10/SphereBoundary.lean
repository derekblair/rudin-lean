import Rudin.PMA.Chapter10.RectangleEdges
import Rudin.PMA.Chapter10.SphereExamples

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def sphereRectangleCell : Cell 2 where
  lower := 0
  upper := ![Real.pi, 2 * Real.pi]
  lower_le_upper := by intro i; fin_cases i <;> simp <;> positivity

/-- The literal spherical parametrization of 10.32, on [0,π] × [0,2π]. -/
def sphereRectangleMap (u : Coord 2) : Euclidean 3 :=
  sphericalMap ![1, u 0, u 1]

lemma sphereRectangleMap_formula (u : Coord 2) :
    sphereRectangleMap u = (coordEquivEuclidean 3)
      ![Real.sin (u 0) * Real.cos (u 1),
        Real.sin (u 0) * Real.sin (u 1), Real.cos (u 0)] := by
  simp [sphereRectangleMap, sphericalMap]

lemma sphereRectangleMap_contDiff : ContDiff ℝ 1 sphereRectangleMap := by
  apply contDiff_sphericalMap.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

def sphereRectangleSurface {E : Set (Euclidean 3)}
    (hE : MapsTo sphereRectangleMap sphereRectangleCell.carrier E) : Surface 2 3 E where
  domain := .cell sphereRectangleCell
  map := sphereRectangleMap
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := sphereRectangleMap_contDiff.contDiffOn
  mapsTo := hE

/-- Source 10.32: the poles are constant curves, and the two meridians have
opposite traversals. The cancellation applies to every continuous one-form. -/
def pma10_32_contract : Prop :=
  sphereRectangleMap '' sphereRectangleCell.carrier = Metric.sphere (0 : Euclidean 3) 1 ∧
  (∀ (E : Set (Euclidean 3)) (hE : MapsTo sphereRectangleMap sphereRectangleCell.carrier E),
    let Φ := sphereRectangleSurface hE
    (rectangleEdgeSurface Φ sphereRectangleCell rfl 0).map =
      (fun u => (coordEquivEuclidean 3) ![Real.sin (u 0), 0, Real.cos (u 0)]) ∧
    (rectangleEdgeSurface Φ sphereRectangleCell rfl 1).map =
      (fun _ => (coordEquivEuclidean 3) ![0, 0, -1]) ∧
    (rectangleEdgeSurface Φ sphereRectangleCell rfl 2).map =
      (fun u => (coordEquivEuclidean 3) ![Real.sin (u 0), 0, -Real.cos (u 0)]) ∧
    (rectangleEdgeSurface Φ sphereRectangleCell rfl 3).map =
      (fun _ => (coordEquivEuclidean 3) ![0, 0, 1]) ∧
    ∀ ω : FormField 3, IsFormOn E 1 ω →
      (∀ i : Fin 4, IteratedRIntegrable (rectangleEdgeCell sphereRectangleCell i)
        (surfaceIntegrand (rectangleEdgeSurface Φ sphereRectangleCell rfl i) ω)) ∧
      surfaceIntegral (rectangleEdgeSurface Φ sphereRectangleCell rfl 1) ω = 0 ∧
      surfaceIntegral (rectangleEdgeSurface Φ sphereRectangleCell rfl 3) ω = 0 ∧
      surfaceIntegral (rectangleEdgeSurface Φ sphereRectangleCell rfl 2) ω =
        -surfaceIntegral (rectangleEdgeSurface Φ sphereRectangleCell rfl 0) ω ∧
      rectangleBoundaryIntegral Φ sphereRectangleCell rfl ω = 0)

lemma sphereRectangleMap_image :
    sphereRectangleMap '' sphereRectangleCell.carrier = Metric.sphere (0 : Euclidean 3) 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right]
    exact sphericalMap_norm (by norm_num : 0 ≤ (![1, u 0, u 1] : Coord 3) 0)
  · intro hx
    have hxnorm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hxb : x ∈ Metric.closedBall (0 : Euclidean 3) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right, hxnorm, le_refl]
    rw [← sphericalMap_image] at hxb
    obtain ⟨u, hu, rfl⟩ := hxb
    have hr : u 0 = 1 := by
      rw [sphericalMap_norm ((Cell.mem_carrier.mp hu) 0).1] at hxnorm
      exact hxnorm
    refine ⟨![u 1, u 2], ?_, ?_⟩
    · rw [Cell.mem_carrier]
      intro i
      fin_cases i
      · exact (Cell.mem_carrier.mp hu) 1
      · exact (Cell.mem_carrier.mp hu) 2
    · unfold sphereRectangleMap
      congr 1
      ext i
      fin_cases i <;> simp [hr]

lemma sphereRectangle_edge_formulas {E : Set (Euclidean 3)}
    (hE : MapsTo sphereRectangleMap sphereRectangleCell.carrier E) :
    (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 0).map =
      (fun u => (coordEquivEuclidean 3) ![Real.sin (u 0), 0, Real.cos (u 0)]) ∧
    (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 1).map =
      (fun _ => (coordEquivEuclidean 3) ![0, 0, -1]) ∧
    (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 2).map =
      (fun u => (coordEquivEuclidean 3) ![Real.sin (u 0), 0, -Real.cos (u 0)]) ∧
    (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 3).map =
      (fun _ => (coordEquivEuclidean 3) ![0, 0, 1]) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext u <;>
    simp [rectangleEdgeSurface, Surface.precompose, sphereRectangleSurface,
      rectangleEdgeMap, sphereRectangleCell, Function.comp_def, sphereRectangleMap,
      sphericalMap, Real.sin_sub, Real.cos_sub]

lemma sphereRectangle_meridian_reverse {E : Set (Euclidean 3)}
    (hE : MapsTo sphereRectangleMap sphereRectangleCell.carrier E) (ω : FormField 3)
    (hω : IsFormOn E 1 ω) :
    surfaceIntegral (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 2) ω =
      -surfaceIntegral (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 0) ω := by
  let γ := rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 0
  let C := rectangleEdgeCell sphereRectangleCell 0
  have he := sphereRectangle_edge_formulas hE
  calc
    _ = surfaceIntegral (γ.reverse C rfl) ω := by
      refine surfaceIntegral_congr_map
        (Φ := rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 2)
        (Ψ := γ.reverse C rfl) ?_ ?_ ω
      · change ParameterDomain.cell (rectangleEdgeCell sphereRectangleCell 2) = .cell C
        rfl
      funext u
      change (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 2).map u =
        γ.map (intervalReverse C u)
      rw [he.2.2.1]
      change _ = (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 0).map _
      rw [he.1]
      simp [intervalReverse, C, rectangleEdgeCell, sphereRectangleCell, intervalCell,
        Real.sin_sub, Real.cos_sub]
    _ = _ := surfaceIntegral_reverse γ C rfl hω

theorem pma10_32 : pma10_32_contract := by
  refine ⟨sphereRectangleMap_image, ?_⟩
  intro E hE
  have he := sphereRectangle_edge_formulas hE
  refine ⟨he.1, he.2.1, he.2.2.1, he.2.2.2, ?_⟩
  intro ω hω
  have h1 := surfaceIntegral_constant_map
    (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 1) he.2.1 hω
  have h3 := surfaceIntegral_constant_map
    (rectangleEdgeSurface (sphereRectangleSurface hE) sphereRectangleCell rfl 3) he.2.2.2 hω
  have hr := sphereRectangle_meridian_reverse hE ω hω
  refine ⟨rectangleEdgeSurface_integrable _ _ rfl hω, h1, h3, hr, ?_⟩
  simp only [rectangleBoundaryIntegral, Fin.sum_univ_four, h1, h3, hr]
  ring

end Rudin.PMA.Chapter10
