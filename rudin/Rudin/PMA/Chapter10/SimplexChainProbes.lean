import Rudin.PMA.Chapter10.SimplexOrientation
import Rudin.PMA.Chapter10.SimplexBoundaries

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- Swapping the base vertex with the last vertex is an affine
reparametrization, rather than a mere permutation of coordinate axes. -/
theorem origin_moving_transposition_reverses_integral {n : ℕ}
    {E : Set (Euclidean n)} (p : Fin 3 → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex 2) E)
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E 2 ω) :
    ∃ hq : MapsTo (affineSimplexMap (p ∘ Equiv.swap 0 2)) (standardSimplex 2) E,
      surfaceIntegral (affineSimplexSurface (p ∘ Equiv.swap 0 2) hq) ω =
        -surfaceIntegral (affineSimplexSurface p hp) ω := by
  obtain ⟨hq, _, _, hsign⟩ := pma10_27 2 n E p hp (Equiv.swap 0 2) ω hE hω
  refine ⟨hq, ?_⟩
  simpa using hsign

/-- Repeated vertices make the same parametrization both equal and opposite
as an integration functional, without an affine-independence hypothesis. -/
theorem repeated_base_vertex_integral_zero {n : ℕ} {E : Set (Euclidean n)}
    (p : Fin 3 → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex 2) E)
    (hrepeated : p 0 = p 2) {ω : FormField n}
    (hE : IsOpen E) (hω : IsFormOn E 2 ω) :
    surfaceIntegral (affineSimplexSurface p hp) ω = 0 := by
  have hswap : p ∘ Equiv.swap 0 2 = p := by
    funext i
    fin_cases i <;> norm_num [Function.comp_def, Equiv.swap_apply_def, hrepeated]
  obtain ⟨hq, hsign⟩ := origin_moving_transposition_reverses_integral p hp hE hω
  have he : surfaceIntegral (affineSimplexSurface p hp) ω =
      -surfaceIntegral (affineSimplexSurface p hp) ω := by
    simpa only [hswap] using hsign
  linarith

/-- The boundary of a segment has the terminal point with positive sign
and the initial point with negative sign, tested on an arbitrary zero-form. -/
theorem segment_boundary_scalar_value {n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn 1 n E) (f : Euclidean n → ℝ) :
    affineChainIntegral (scalarForm f) (affineSimplexBoundary σ) =
      f (σ.vertices 1) - f (σ.vertices 0) := by
  have hpoint (i : Fin 2) :
      surfaceIntegral (affineSimplexSurface (σ.face i).vertices (σ.face i).mapsTo)
        (scalarForm f) = f ((σ.face i).vertices 0) := by
    have h := pma10_26.{0, 0}.2.2.2.2.2.2.2 n E (σ.face i).vertices (σ.face i).mapsTo
      (1 : ℤˣ) f
    simpa only [signedAffineIntegral, Units.val_one, Int.cast_one, one_mul] using h
  simp only [affineSimplexBoundary, map_sum, map_smul, affineChainIntegral_single,
    hpoint, Int.cast_one, one_mul]
  norm_num [Fin.sum_univ_succ, AffineSimplexIn.face, Function.comp_def, sub_eq_add_neg]

end Rudin.PMA.Chapter10.FidelityProbes
