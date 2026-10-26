import Rudin.PMA.Chapter10.VolumeElements
import Mathlib.Analysis.Convex.Measure

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory Filter
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- A cell boundary and its differentiable image are null. Thus the native
change-of-variables formula only requires injectivity in the cell interior. -/
lemma surfaceIntegral_density_eq_image_of_interior_inj {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface n n E) (C : Cell n) (hD : Φ.domain = .cell C)
    (hinj : InjOn Φ.map (interior C.carrier))
    (hnonneg : ∀ u ∈ C.carrier, 0 ≤ coordinateJacobian Φ.coordinateMap u)
    {f : Euclidean n → ℝ} (hf : ContinuousOn f Φ.image) :
    surfaceIntegral Φ (densityForm f) = ∫ x in Φ.image, f x := by
  let T := Φ.coordinateMap
  have hc : ContinuousOn (surfaceIntegrand Φ (densityForm f)) C.carrier := by
    simpa only [hD, ParameterDomain.carrier] using Φ.continuousOn_densityIntegrand hf
  have hd (u : Coord n) (hu : u ∈ C.carrier) : DifferentiableAt ℝ T u :=
    (coordEquivEuclidean n).symm.differentiableAt.comp u
      (Φ.differentiableAt (by simpa only [hD, ParameterDomain.carrier] using hu))
  have hz : volume (frontier C.carrier) = 0 :=
    (convex_Icc C.lower C.upper).addHaar_frontier volume
  have hzimage : volume (T '' frontier C.carrier) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun u hu => (hd u (C.isClosed_carrier.frontier_subset hu)).differentiableWithinAt) hz
  have himage : T '' C.carrier =ᵐ[volume] T '' interior C.carrier := by
    apply ae_eq_set.mpr
    constructor
    · apply measure_mono_null _ hzimage
      rintro y ⟨⟨u, hu, rfl⟩, hy⟩
      apply mem_image_of_mem
      rw [C.isClosed_carrier.frontier_eq]
      exact ⟨hu, fun hi => hy (mem_image_of_mem _ hi)⟩
    · rw [sdiff_eq_empty.mpr (image_mono interior_subset), measure_empty]
  have hcell : interior C.carrier =ᵐ[volume] C.carrier := interior_ae_eq_of_null_frontier hz
  have hi : InjOn T (interior C.carrier) := by
    intro u hu v hv he
    exact hinj hu hv ((coordEquivEuclidean n).symm.injective he)
  have hderiv (u : Coord n) (hu : u ∈ interior C.carrier) :
      HasFDerivWithinAt T (fderiv ℝ T u) (interior C.carrier) u :=
    (hd u (interior_subset hu)).hasFDerivAt.hasFDerivWithinAt
  have hm : Φ.image = coordEquivEuclidean n '' (T '' C.carrier) := by
    simp only [Surface.image, hD, ParameterDomain.carrier, T, Surface.coordinateMap,
      image_image, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
  calc
    surfaceIntegral Φ (densityForm f) = ∫ u in C.carrier, surfaceIntegrand Φ (densityForm f) u := by
      change Φ.domain.integral _ = _
      rw [hD]
      exact iteratedRIntegral_eq_setIntegral hc
    _ = ∫ u in interior C.carrier, surfaceIntegrand Φ (densityForm f) u :=
      setIntegral_congr_set hcell.symm
    _ = ∫ x in T '' interior C.carrier, f (coordEquivEuclidean n x) := by
      rw [integral_image_eq_integral_abs_det_fderiv_smul volume
        isOpen_interior.measurableSet hderiv hi]
      apply setIntegral_congr_fun isOpen_interior.measurableSet
      intro u hu
      rw [surfaceIntegrand_densityForm Φ hf (by simpa only [hD, ParameterDomain.carrier] using interior_subset hu)]
      change f (Φ.map u) * coordinateJacobian T u =
        |coordinateJacobian T u| * f (coordEquivEuclidean n (T u))
      rw [abs_of_nonneg (hnonneg u (interior_subset hu))]
      simp only [T, Surface.coordinateMap, Function.comp_apply,
        ContinuousLinearEquiv.apply_symm_apply, mul_comm]
    _ = ∫ x in T '' C.carrier, f (coordEquivEuclidean n x) :=
      setIntegral_congr_set himage.symm
    _ = ∫ x in Φ.image, f x := by
      rw [hm, (coordEquivEuclidean_measurePreserving n).setIntegral_image_emb
        (coordEquivEuclidean n).toHomeomorph.measurableEmbedding]

end Rudin.PMA.Chapter10
