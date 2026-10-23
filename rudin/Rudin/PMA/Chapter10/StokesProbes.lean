import Rudin.PMA.Chapter10.ChainStokes

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def foldedTriangle : C2Simplex 2 3 univ where
  map u := ((u 0)^2 - u 0) • coordinateVector 3 0 + u 1 • coordinateVector 3 1
  regularity := ⟨univ, isOpen_univ, subset_univ _,
    ((((contDiff_apply ℝ ℝ (0 : Fin 2)).pow 2).sub
      (contDiff_apply ℝ ℝ (0 : Fin 2))).smul contDiff_const |>.add
      ((contDiff_apply ℝ ℝ (1 : Fin 2)).smul contDiff_const)).contDiffOn⟩
  mapsTo := mapsTo_univ _ _

/-- A genuinely folded two-simplex in R3 is admissible. The negative
integer multiplicity is retained on both sides of the native Stokes law. -/
theorem stokes_folded_triangle_negative_multiplicity (ω : FormField 3)
    (hω : IsCFormOn 1 univ 1 ω) :
    ¬ InjOn foldedTriangle.map (standardSimplex 2) ∧
    foldedTriangle.toSurface.domain.Integrable
      (surfaceIntegrand foldedTriangle.toSurface (exteriorDerivative ω)) ∧
    (-3 : ℝ) * surfaceIntegral foldedTriangle.toSurface (exteriorDerivative ω) =
      chainIntegral ω ((-3 : ℤ) • simplexBoundary foldedTriangle) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hi
    have h0 : (0 : Coord 2) ∈ standardSimplex 2 := by simp [standardSimplex]
    have h1 : (![1, 0] : Coord 2) ∈ standardSimplex 2 := by
      constructor
      · intro i; fin_cases i <;> norm_num
      · norm_num [Fin.sum_univ_two]
    have hm : foldedTriangle.map 0 = foldedTriangle.map ![1, 0] := by
      norm_num [foldedTriangle]
    have he := congrArg (fun u : Coord 2 => u 0) (hi h0 h1 hm)
    norm_num at he
  · exact ParameterDomain.integrable_of_continuousOn
      (foldedTriangle.toSurface.continuousOn_integrand
        ((pma10_18.1 3 1 univ ω isOpen_univ hω).1))
  · have h := pma10_33 1 3 univ ω (Finsupp.single foldedTriangle (-3)) isOpen_univ hω
    simpa only [chainIntegral_single, chainBoundary_single, Int.cast_neg, Int.cast_ofNat] using h

private def foldedSegment : C2Simplex 1 2 univ where
  map u := ((u 0)^2 - u 0) • coordinateVector 2 0
  regularity := ⟨univ, isOpen_univ, subset_univ _,
    ((((contDiff_apply ℝ ℝ (0 : Fin 1)).pow 2).sub
      (contDiff_apply ℝ ℝ (0 : Fin 1))).smul contDiff_const).contDiffOn⟩
  mapsTo := mapsTo_univ _ _

/-- The two distinct parameter endpoints of the folded segment have the
same image. Its actual zero-dimensional boundary cancels in the free chain. -/
theorem folded_segment_boundary_cancels : simplexBoundary foldedSegment = 0 := by
  have he : foldedSegment.face 0 = foldedSegment.face 1 := by
    apply C2Simplex.ext
    funext u
    change foldedSegment.map (standardFaceMap 0 u) =
      foldedSegment.map (standardFaceMap 1 u)
    simp [foldedSegment, standardFaceMap, standardFaceAffine,
      affineMapFromVertices_apply, vertexLinear_apply, standardVertex]
  simp [simplexBoundary, Fin.sum_univ_two, he]

/-- The degree-zero Stokes case on a nonconstant closed parametrization
gives a zero native integral for every C1 scalar potential. -/
theorem folded_segment_C1_potential (f : Euclidean 2 → ℝ) (hf : ContDiff ℝ 1 f) :
    surfaceIntegral foldedSegment.toSurface (scalarDifferential f) = 0 := by
  have h := pma10_33 0 2 univ (scalarForm f)
    (Finsupp.single foldedSegment 1) isOpen_univ (isCFormOn_scalarForm hf.contDiffOn)
  simpa only [chainIntegral_single, chainBoundary_single, Int.cast_one, one_mul,
    one_smul, exteriorDerivative_scalarForm, folded_segment_boundary_cancels, map_zero] using h

end Rudin.PMA.Chapter10.FidelityProbes
