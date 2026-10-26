import Rudin.PMA.Chapter10.PositiveRegions
import Mathlib.Analysis.Convex.Measure

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory Filter
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma PositiveSimplex.coordinateCarrier_preimage {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) :
    P.coordinateCarrier = (coordEquivEuclidean n) ⁻¹' P.carrier := by
  rw [P.coordinateCarrier_eq]
  exact (coordEquivEuclidean n).toEquiv.image_symm_eq_preimage P.carrier

lemma PositiveSimplex.isCompact_coordinateCarrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : IsCompact P.coordinateCarrier := by
  rw [P.coordinateCarrier_eq]
  exact P.isCompact_carrier.image (coordEquivEuclidean n).symm.continuous

lemma PositiveSimplex.coordinateFrontier_null {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : volume (frontier P.coordinateCarrier) = 0 := by
  have hd : DifferentiableOn ℝ P.simplex.coordinateMap (frontier (standardSimplex n)) := by
    intro u hu
    exact (P.simplex.coordinateMap_c1.1 u (P.simplex.toSurface.domain_subset
      ((isClosed_standardSimplex n).frontier_subset hu))).differentiableWithinAt
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd
    ((convex_standardSimplex n).addHaar_frontier volume)
  apply measure_mono_null _ hz
  intro y hy
  have hyC := P.isCompact_coordinateCarrier.isClosed.frontier_subset hy
  obtain ⟨u, hu, rfl⟩ := hyC
  refine mem_image_of_mem P.simplex.coordinateMap ?_
  rw [(isClosed_standardSimplex n).frontier_eq]
  refine ⟨hu, fun hi => ?_⟩
  have ho : IsOpen (P.simplex.coordinateMap '' interior (standardSimplex n)) := by
    have he : P.simplex.coordinateMap '' interior (standardSimplex n) =
        (coordEquivEuclidean n).symm '' P.openCarrier := by
      simp only [PositiveSimplex.openCarrier, C2Simplex.coordinateMap, image_comp]
    rw [he]
    exact (coordEquivEuclidean n).symm.toHomeomorph.isOpenMap _ P.isOpen_openCarrier
  have hsub : P.simplex.coordinateMap '' interior (standardSimplex n) ⊆
      interior P.coordinateCarrier := ho.subset_interior_iff.mpr (image_mono interior_subset)
  exact hy.2 (hsub (mem_image_of_mem _ hi))

lemma topFormDensity_continuousOn {n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hω : IsFormOn E n ω) :
    ContinuousOn (topFormDensity ω) ((coordEquivEuclidean n) ⁻¹' E) := by
  unfold topFormDensity
  apply continuousOn_formEvaluation
    (v := fun _ => fun j => coordEquivEuclidean n (Pi.single j 1))
    (ω := fun y => ω (coordEquivEuclidean n y)) (fun _ => continuousOn_const)
  intro S
  exact (hω.2 S).comp (coordEquivEuclidean n).continuous.continuousOn (mapsTo_preimage _ _)

lemma PositiveSimplex.density_integrable {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) {ω : FormField n} (hω : IsFormOn E n ω) :
    IntegrableOn (topFormDensity ω) P.coordinateCarrier := by
  apply ContinuousOn.integrableOn_compact P.isCompact_coordinateCarrier
  apply (topFormDensity_continuousOn hω).mono
  rw [P.coordinateCarrier_preimage]
  exact preimage_mono (image_subset_iff.mpr P.simplex.mapsTo)

/-- A finite union with pairwise disjoint interiors; shared boundary points
are retained in every actual closed parametrized piece. -/
structure PositiveRegion (n : ℕ) (E : Set (Euclidean n)) where
  size : ℕ
  piece : Fin size → PositiveSimplex n E
  disjoint : Pairwise (fun i j => Disjoint (interior (piece i).carrier) (interior (piece j).carrier))

def PositiveRegion.carrier {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E) :
    Set (Euclidean n) := ⋃ i, (R.piece i).carrier

def PositiveRegion.coordinateCarrier {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E) :
    Set (Coord n) := ⋃ i, (R.piece i).coordinateCarrier

def PositiveRegion.chain {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E) :
    SimplexChain n n E := ∑ i, Finsupp.single (R.piece i).simplex 1

lemma PositiveRegion.coordinateCarrier_preimage {n : ℕ} {E : Set (Euclidean n)}
    (R : PositiveRegion n E) :
    R.coordinateCarrier = coordEquivEuclidean n ⁻¹' R.carrier := by
  simp only [coordinateCarrier, carrier, PositiveSimplex.coordinateCarrier_preimage, preimage_iUnion]

lemma PositiveRegion.coordinate_interiors_disjoint {n : ℕ} {E : Set (Euclidean n)}
    (R : PositiveRegion n E) :
    Pairwise (fun i j => Disjoint (interior (R.piece i).coordinateCarrier)
      (interior (R.piece j).coordinateCarrier)) := by
  intro i j hij
  rw [(R.piece i).coordinateCarrier_preimage, (R.piece j).coordinateCarrier_preimage]
  change Disjoint (interior ((coordEquivEuclidean n).toHomeomorph ⁻¹' (R.piece i).carrier))
    (interior ((coordEquivEuclidean n).toHomeomorph ⁻¹' (R.piece j).carrier))
  rw [← (coordEquivEuclidean n).toHomeomorph.preimage_interior,
    ← (coordEquivEuclidean n).toHomeomorph.preimage_interior]
  exact (R.disjoint hij).preimage _

lemma PositiveRegion.integral_eq_image {n : ℕ} {E : Set (Euclidean n)}
    (R : PositiveRegion n E) {ω : FormField n} (hω : IsFormOn E n ω) :
    chainIntegral ω R.chain = ∫ y in R.coordinateCarrier, topFormDensity ω y := by
  classical
  have ha := fun i => interior_ae_eq_of_null_frontier (R.piece i).coordinateFrontier_null
  have hU : (⋃ i, interior (R.piece i).coordinateCarrier) =ᵐ[volume] R.coordinateCarrier :=
    EventuallyEqSet.iUnion ha
  have hsum := integral_biUnion_finset (Finset.univ : Finset (Fin R.size))
    (fun i _ => isOpen_interior.measurableSet)
    (fun i _ j _ hij => R.coordinate_interiors_disjoint hij)
    (fun i _ => ((R.piece i).density_integrable hω).mono_set interior_subset)
  have hsum' : (∫ y in ⋃ i, interior (R.piece i).coordinateCarrier, topFormDensity ω y) =
      ∑ i, ∫ y in interior (R.piece i).coordinateCarrier, topFormDensity ω y := by
    simpa only [Finset.mem_univ, iUnion_true] using hsum
  rw [← setIntegral_congr_set hU, hsum']
  simp only [PositiveRegion.chain, map_sum, chainIntegral_single, Int.cast_one, one_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(R.piece i).integral_eq_image hω |>.2, setIntegral_congr_set (ha i)]

lemma PositiveRegion.integral_independent {n : ℕ} {E : Set (Euclidean n)}
    (R T : PositiveRegion n E) (hRT : R.carrier = T.carrier)
    {ω : FormField n} (hω : IsFormOn E n ω) : chainIntegral ω R.chain = chainIntegral ω T.chain := by
  rw [R.integral_eq_image hω, T.integral_eq_image hω,
    R.coordinateCarrier_preimage, T.coordinateCarrier_preimage, hRT]

end Rudin.PMA.Chapter10
