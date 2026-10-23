import Rudin.PMA.Chapter10.RectangleNormalization
import Rudin.PMA.Chapter10.SimplexBoundaries

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma squareTriangleMap_contDiff_order (i : Fin 2) (r : WithTop ENat) :
    ContDiff ℝ r (squareTriangleMap i) := by
  fin_cases i
  · exact contDiff_id
  · exact contDiff_const.sub contDiff_id

def Surface.rectangleSimplex {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) (i : Fin 2) : C2Simplex 2 n E where
  map := Φ.map ∘ cellNormalize C ∘ squareTriangleMap i
  regularity := by
    obtain ⟨U, hU, hDU, hΦ⟩ := h₂
    have hA : ContDiff ℝ 2 (cellNormalize C ∘ squareTriangleMap i) :=
      (cellNormalize_contDiff C 2).comp (squareTriangleMap_contDiff_order i 2)
    refine ⟨(cellNormalize C ∘ squareTriangleMap i) ⁻¹' U,
      hU.preimage hA.continuous, ?_, hΦ.comp hA.contDiffOn (fun _ hu => hu)⟩
    intro u hu
    apply hDU
    rw [hD]
    exact cellNormalize_mapsTo C (squareTriangleMap_mapsTo i hu)
  mapsTo := by
    intro u hu
    apply Φ.mapsTo
    rw [hD]
    exact cellNormalize_mapsTo C (squareTriangleMap_mapsTo i hu)

def Surface.rectangleChain {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 2 n E)
    (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) : SimplexChain 2 n E :=
  ∑ i : Fin 2, Finsupp.single (Φ.rectangleSimplex C hD h₂ i) 1

lemma rectangleSimplex_surfaceIntegral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    (i : Fin 2) (ω : FormField n) :
    surfaceIntegral (Φ.rectangleSimplex C hD h₂ i).toSurface ω =
      surfaceIntegral (squareTriangleSurface (Φ.normalizeCell C hD) rfl i) ω := by
  exact surfaceIntegral_congr_map
    (Φ := (Φ.rectangleSimplex C hD h₂ i).toSurface)
    (Ψ := squareTriangleSurface (Φ.normalizeCell C hD) rfl i) rfl rfl ω

lemma rectangleChain_integral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    {ω : FormField n} (hω : IsFormOn E 2 ω) :
    chainIntegral ω (Φ.rectangleChain C hD h₂) = surfaceIntegral Φ ω := by
  simp only [Surface.rectangleChain, map_sum, chainIntegral_single, Int.cast_one, one_mul,
    rectangleSimplex_surfaceIntegral]
  rw [← squareTriangle_integral_decomposition (Φ.normalizeCell C hD) rfl hω,
    surfaceIntegral_normalizeRectangle Φ C hD hω]

lemma surfaceIntegral_one_congr {n : ℕ} {E : Set (Euclidean n)}
    (Φ Ψ : Surface 1 n E) (hI : Φ.domain.interval = Ψ.domain.interval)
    (hm : Φ.map = Ψ.map) {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral Φ ω = surfaceIntegral Ψ ω := by
  unfold surfaceIntegral
  rw [ParameterDomain.one_integral_eq_intervalIntegral (Φ.continuousOn_integrand hω),
    ParameterDomain.one_integral_eq_intervalIntegral (Ψ.continuousOn_integrand hω), hI]
  congr 1
  funext t
  unfold surfaceIntegrand
  rw [hm]

lemma rectangleSimplex_face_integral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    (i : Fin 2) (j : Fin 3) {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral ((Φ.rectangleSimplex C hD h₂ i).face j).toSurface ω =
      surfaceIntegral (squareTriangleFaceSurface (Φ.normalizeCell C hD) rfl i j) ω := by
  exact surfaceIntegral_one_congr
    ((Φ.rectangleSimplex C hD h₂ i).face j).toSurface
    (squareTriangleFaceSurface (Φ.normalizeCell C hD) rfl i j) rfl rfl hω

lemma rectangleChain_boundary_integral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    chainIntegral ω (chainBoundary (Φ.rectangleChain C hD h₂)) =
      rectangleBoundaryIntegral Φ C hD ω := by
  have he : chainIntegral ω (chainBoundary (Φ.rectangleChain C hD h₂)) =
      squareTriangularBoundaryIntegral (Φ.normalizeCell C hD) rfl ω := by
    simp only [Surface.rectangleChain, map_sum, chainBoundary_single, one_smul,
      simplexBoundary, map_smul, chainIntegral_single, Int.cast_one, mul_one, one_mul,
      Int.cast_pow, Int.cast_neg, smul_eq_mul, Int.cast_one, zsmul_eq_mul,
      squareTriangularBoundaryIntegral, rectangleSimplex_face_integral Φ C hD h₂ _ _ hω]
  rw [he, squareTriangle_boundary_eq_edges (Φ.normalizeCell C hD) rfl hω,
    rectangleBoundary_normalize_integral Φ C hD hω]

lemma rectangleChain_cycle {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    (hcycle : ∀ ω : FormField n, IsFormOn E 1 ω → rectangleBoundaryIntegral Φ C hD ω = 0) :
    ChainEq (chainBoundary (Φ.rectangleChain C hD h₂)) 0 := by
  intro ω hω
  rw [rectangleChain_boundary_integral Φ C hD h₂ hω, map_zero]
  exact hcycle ω hω

end Rudin.PMA.Chapter10
