import Rudin.PMA.Chapter10.RectangleEdges
import Rudin.PMA.Chapter10.SquareIntegral

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def squareTriangleMap : Fin 2 → Coord 2 → Coord 2 := ![id, fun u => 1 - u]

lemma squareTriangleMap_contDiff (i : Fin 2) : ContDiff ℝ 1 (squareTriangleMap i) := by
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const.sub contDiff_id

lemma squareTriangleMap_mapsTo (i : Fin 2) :
    MapsTo (squareTriangleMap i) (standardSimplex 2) (Cell.unit 2).carrier := by
  intro u hu
  have h := standardSimplex_subset_unit 2 hu
  fin_cases i
  · exact h
  · rw [Cell.mem_carrier] at h ⊢
    intro j
    have hj := h j
    change 0 ≤ u j ∧ u j ≤ 1 at hj
    change 0 ≤ 1 - u j ∧ 1 - u j ≤ 1
    constructor <;> linarith

def squareTriangleSurface {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (hD : Φ.domain = .cell (Cell.unit 2)) (i : Fin 2) : Surface 2 n E :=
  Φ.precompose .simplex (squareTriangleMap i) (squareTriangleMap_contDiff i)
    (by rw [hD]; exact squareTriangleMap_mapsTo i)

/-- A one-simplex has precisely the same native interval as the unit 1-cell. -/
def squareTriangleFaceMap (i : Fin 2) (j : Fin 3) : Coord 1 → Coord 2 :=
  squareTriangleMap i ∘ standardFaceMap j

lemma squareTriangleFaceMap_contDiff (i : Fin 2) (j : Fin 3) :
    ContDiff ℝ 1 (squareTriangleFaceMap i j) :=
  (squareTriangleMap_contDiff i).comp (standardFaceMap_contDiff j 1)

lemma squareTriangleFaceMap_mapsTo (i : Fin 2) (j : Fin 3) :
    MapsTo (squareTriangleFaceMap i j) (Cell.unit 1).carrier (Cell.unit 2).carrier := by
  apply (squareTriangleMap_mapsTo i).comp
  intro u hu
  apply standardFaceMap_mapsTo j
  have ht := (Cell.mem_carrier.mp hu) 0
  simpa [standardSimplex, Cell.unit] using ht

def squareTriangleFaceSurface {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (hD : Φ.domain = .cell (Cell.unit 2)) (i : Fin 2) (j : Fin 3) : Surface 1 n E :=
  Φ.precompose (.cell (Cell.unit 1)) (squareTriangleFaceMap i j)
    (squareTriangleFaceMap_contDiff i j)
    (by rw [hD]; exact squareTriangleFaceMap_mapsTo i j)

def squareTriangularBoundaryIntegral {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (hD : Φ.domain = .cell (Cell.unit 2)) (ω : FormField n) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 3, (-1 : ℝ)^j.val *
    surfaceIntegral (squareTriangleFaceSurface Φ hD i j) ω

/-- The C¹ square consequence of 10.31. Both pieces are the actual affine
triangles of the source, and the boundary equality is tested on all continuous
one-forms. The diagonal is retained among the six faces before cancellation. -/
def squareBoundary_contract : Prop :=
  (squareTriangleMap 0 '' standardSimplex 2) ∪
      (squareTriangleMap 1 '' standardSimplex 2) = (Cell.unit 2).carrier ∧
  (∀ (i : Fin 2) (u : Coord 2), LinearMap.det (fderiv ℝ (squareTriangleMap i) u).toLinearMap = 1) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (Φ : Surface 2 n E)
    (hD : Φ.domain = .cell (Cell.unit 2)),
    (∀ ω : FormField n, IsFormOn E 2 ω →
      Φ.domain.Integrable (surfaceIntegrand Φ ω) ∧
      (∀ i : Fin 2, (squareTriangleSurface Φ hD i).domain.Integrable
        (surfaceIntegrand (squareTriangleSurface Φ hD i) ω)) ∧
      surfaceIntegral Φ ω = ∑ i : Fin 2, surfaceIntegral (squareTriangleSurface Φ hD i) ω) ∧
    (∀ ω : FormField n, IsFormOn E 1 ω →
      (∀ (i : Fin 2) (j : Fin 3), (squareTriangleFaceSurface Φ hD i j).domain.Integrable
        (surfaceIntegrand (squareTriangleFaceSurface Φ hD i j) ω)) ∧
      (∀ i : Fin 4, (rectangleEdgeSurface Φ (Cell.unit 2) hD i).domain.Integrable
        (surfaceIntegrand (rectangleEdgeSurface Φ (Cell.unit 2) hD i) ω)) ∧
      surfaceIntegral (squareTriangleFaceSurface Φ hD 0 0) ω +
        surfaceIntegral (squareTriangleFaceSurface Φ hD 1 0) ω = 0 ∧
      squareTriangularBoundaryIntegral Φ hD ω =
        rectangleBoundaryIntegral Φ (Cell.unit 2) hD ω))

lemma squareTriangleMap_cover :
    (squareTriangleMap 0 '' standardSimplex 2) ∪
      (squareTriangleMap 1 '' standardSimplex 2) = (Cell.unit 2).carrier := by
  apply subset_antisymm
  · rintro u (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact squareTriangleMap_mapsTo 0 hv
    · exact squareTriangleMap_mapsTo 1 hv
  · intro u hu
    have h0 := (Cell.mem_carrier.mp hu) 0
    have h1 := (Cell.mem_carrier.mp hu) 1
    by_cases hsum : u 0 + u 1 ≤ 1
    · left
      refine ⟨u, ?_, rfl⟩
      refine ⟨fun i => (Cell.mem_carrier.mp hu i).1, ?_⟩
      simpa only [Fin.sum_univ_two] using hsum
    · right
      refine ⟨1 - u, ?_, ?_⟩
      · constructor
        · intro i
          exact sub_nonneg.mpr ((Cell.mem_carrier.mp hu i).2)
        · simp only [Fin.sum_univ_two, Pi.sub_apply, Pi.one_apply]
          linarith
      · change (1 : Coord 2) - (1 - u) = u
        abel

lemma squareTriangleMap_det (i : Fin 2) (u : Coord 2) :
    LinearMap.det (fderiv ℝ (squareTriangleMap i) u).toLinearMap = 1 := by
  fin_cases i
  · simp [squareTriangleMap, fderiv_id]
  · have hd : HasFDerivAt (squareTriangleMap 1) (-ContinuousLinearMap.id ℝ (Coord 2)) u :=
      (hasFDerivAt_id u).const_sub 1
    change LinearMap.det (fderiv ℝ (squareTriangleMap 1) u).toLinearMap = 1
    rw [hd.fderiv, ← LinearMap.det_toMatrix']
    have he : LinearMap.toMatrix' (-ContinuousLinearMap.id ℝ (Coord 2)).toLinearMap =
        (-1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      simp [LinearMap.toMatrix'_apply, Matrix.one_apply, Pi.single_apply]
    rw [he]
    norm_num [Matrix.det_fin_two, Matrix.one_apply]

lemma squareTriangle_surfaceIntegral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (hD : Φ.domain = .cell (Cell.unit 2)) (i : Fin 2)
    {ω : FormField n} (hω : IsFormOn E 2 ω) :
    surfaceIntegral (squareTriangleSurface Φ hD i) ω =
      simplexRIntegral (fun u => surfaceIntegrand Φ ω (squareTriangleMap i u)) := by
  have hmaps : MapsTo (squareTriangleMap i) (standardSimplex 2) Φ.domain.carrier := by
    rw [hD]
    exact squareTriangleMap_mapsTo i
  apply ParameterDomain.integral_congr (D := .simplex)
    ((squareTriangleSurface Φ hD i).continuousOn_integrand hω)
    ((Φ.continuousOn_integrand hω).comp (squareTriangleMap_contDiff i).continuous.continuousOn hmaps)
  intro u hu
  have he := surfaceIntegrand_precompose Φ .simplex (squareTriangleMap i)
    (squareTriangleMap_contDiff i) hmaps hω hu
  simpa only [squareTriangleSurface, squareTriangleMap_det, one_mul, Function.comp_def] using he

lemma squareTriangle_integral_decomposition {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (hD : Φ.domain = .cell (Cell.unit 2))
    {ω : FormField n} (hω : IsFormOn E 2 ω) :
    surfaceIntegral Φ ω = ∑ i : Fin 2, surfaceIntegral (squareTriangleSurface Φ hD i) ω := by
  rw [Fin.sum_univ_two, squareTriangle_surfaceIntegral Φ hD 0 hω,
    squareTriangle_surfaceIntegral Φ hD 1 hω]
  have hc := Φ.continuousOn_integrand hω
  rw [hD] at hc
  change Φ.domain.integral _ = _
  rw [hD]
  exact squareRIntegral_split hc

lemma squareTriangleFaceMap_formula (i : Fin 2) (j : Fin 3) (u : Coord 1) :
    squareTriangleFaceMap i j u =
      (![![![1 - u 0, u 0], ![0, u 0], ![u 0, 0]],
          ![![u 0, 1 - u 0], ![1, 1 - u 0], ![1 - u 0, 1]]] i j : Coord 2) := by
  fin_cases i <;> fin_cases j <;> ext k <;> fin_cases k <;>
    simp [squareTriangleFaceMap, squareTriangleMap, standardFaceMap, standardFaceAffine,
      affineMapFromVertices_apply, vertexLinear_apply, standardVertex, Fin.sum_univ_one,
      Pi.single_apply, Function.comp_def, Fin.succAbove] <;> ring

lemma unitSurfaceIntegral_reverse {n : ℕ} {E : Set (Euclidean n)}
    (γ η : Surface 1 n E) (hγ : γ.domain = .cell (Cell.unit 1))
    (hη : η.domain = .cell (Cell.unit 1))
    (hm : η.map = fun u => γ.map (1 - u))
    {ω : FormField n} (hω : IsFormOn E 1 ω) : surfaceIntegral η ω = -surfaceIntegral γ ω := by
  calc
    _ = surfaceIntegral (γ.reverse (Cell.unit 1) hγ) ω := by
      apply surfaceIntegral_congr_map hη _ ω
      funext u
      rw [hm]
      change γ.map (1 - u) = γ.map (intervalReverse (Cell.unit 1) u)
      congr 1
      ext i
      simp [intervalReverse, Cell.unit]
    _ = _ := surfaceIntegral_reverse γ (Cell.unit 1) hγ hω

lemma squareTriangle_diagonal_cancel {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (hD : Φ.domain = .cell (Cell.unit 2))
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral (squareTriangleFaceSurface Φ hD 0 0) ω +
      surfaceIntegral (squareTriangleFaceSurface Φ hD 1 0) ω = 0 := by
  have hr := unitSurfaceIntegral_reverse (squareTriangleFaceSurface Φ hD 0 0)
    (squareTriangleFaceSurface Φ hD 1 0) rfl rfl (by
      funext u
      change Φ.map (squareTriangleFaceMap 1 0 u) = Φ.map (squareTriangleFaceMap 0 0 (1 - u))
      congr 1
      simp [squareTriangleFaceMap_formula]) hω
  rw [hr, add_neg_cancel]

lemma squareTriangle_outer_faces {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (hD : Φ.domain = .cell (Cell.unit 2))
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral (squareTriangleFaceSurface Φ hD 0 1) ω =
        -surfaceIntegral (rectangleEdgeSurface Φ (Cell.unit 2) hD 3) ω ∧
    surfaceIntegral (squareTriangleFaceSurface Φ hD 0 2) ω =
        surfaceIntegral (rectangleEdgeSurface Φ (Cell.unit 2) hD 0) ω ∧
    surfaceIntegral (squareTriangleFaceSurface Φ hD 1 1) ω =
        -surfaceIntegral (rectangleEdgeSurface Φ (Cell.unit 2) hD 1) ω ∧
    surfaceIntegral (squareTriangleFaceSurface Φ hD 1 2) ω =
        surfaceIntegral (rectangleEdgeSurface Φ (Cell.unit 2) hD 2) ω := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply unitSurfaceIntegral_reverse _ _ rfl rfl _ hω
    funext u
    change Φ.map (squareTriangleFaceMap 0 1 u) = Φ.map (rectangleEdgeMap (Cell.unit 2) 3 (1 - u))
    congr 1
    simp [squareTriangleFaceMap_formula, rectangleEdgeMap, Cell.unit]
  · refine surfaceIntegral_congr_map
      (Φ := squareTriangleFaceSurface Φ hD 0 2)
      (Ψ := rectangleEdgeSurface Φ (Cell.unit 2) hD 0) ?_ ?_ ω
    · change ParameterDomain.cell (Cell.unit 1) = .cell (rectangleEdgeCell (Cell.unit 2) 0)
      rfl
    funext u
    change Φ.map (squareTriangleFaceMap 0 2 u) = Φ.map (rectangleEdgeMap (Cell.unit 2) 0 u)
    congr 1
    simp [squareTriangleFaceMap_formula, rectangleEdgeMap, Cell.unit]
  · apply unitSurfaceIntegral_reverse _ _ rfl rfl _ hω
    funext u
    change Φ.map (squareTriangleFaceMap 1 1 u) = Φ.map (rectangleEdgeMap (Cell.unit 2) 1 (1 - u))
    congr 1
    simp [squareTriangleFaceMap_formula, rectangleEdgeMap, Cell.unit]
  · refine surfaceIntegral_congr_map
      (Φ := squareTriangleFaceSurface Φ hD 1 2)
      (Ψ := rectangleEdgeSurface Φ (Cell.unit 2) hD 2) ?_ ?_ ω
    · change ParameterDomain.cell (Cell.unit 1) = .cell (rectangleEdgeCell (Cell.unit 2) 2)
      rfl
    funext u
    change Φ.map (squareTriangleFaceMap 1 2 u) = Φ.map (rectangleEdgeMap (Cell.unit 2) 2 u)
    congr 1
    simp [squareTriangleFaceMap_formula, rectangleEdgeMap, Cell.unit]

lemma squareTriangle_boundary_eq_edges {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (hD : Φ.domain = .cell (Cell.unit 2))
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    squareTriangularBoundaryIntegral Φ hD ω = rectangleBoundaryIntegral Φ (Cell.unit 2) hD ω := by
  have hd := squareTriangle_diagonal_cancel Φ hD hω
  rcases squareTriangle_outer_faces Φ hD hω with ⟨h01, h02, h11, h12⟩
  simp only [squareTriangularBoundaryIntegral, rectangleBoundaryIntegral,
    Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_mul]
  rw [h01, h02, h11, h12]
  linarith

theorem squareBoundary : squareBoundary_contract := by
  refine ⟨squareTriangleMap_cover, squareTriangleMap_det, ?_⟩
  intro n E Φ hD
  constructor
  · intro ω hω
    refine ⟨ParameterDomain.integrable_of_continuousOn (Φ.continuousOn_integrand hω),
      fun i => ParameterDomain.integrable_of_continuousOn
        ((squareTriangleSurface Φ hD i).continuousOn_integrand hω),
      squareTriangle_integral_decomposition Φ hD hω⟩
  · intro ω hω
    refine ⟨fun i j => ParameterDomain.integrable_of_continuousOn
      ((squareTriangleFaceSurface Φ hD i j).continuousOn_integrand hω),
      fun i => ParameterDomain.integrable_of_continuousOn
      ((rectangleEdgeSurface Φ (Cell.unit 2) hD i).continuousOn_integrand hω),
      squareTriangle_diagonal_cancel Φ hD hω, squareTriangle_boundary_eq_edges Φ hD hω⟩

end Rudin.PMA.Chapter10
