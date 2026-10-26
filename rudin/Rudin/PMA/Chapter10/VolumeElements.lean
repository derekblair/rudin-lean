import Rudin.PMA.Chapter10.PositiveRegions
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The ordered coordinate volume element in every dimension. -/
def standardVolume (n : ℕ) : CotangentExterior n := coordinateWedge (id : Fin n → Fin n)

def densityForm {n : ℕ} (f : Euclidean n → ℝ) : FormField n := fun x => f x • standardVolume n

lemma isFormOn_densityForm {n : ℕ} {E : Set (Euclidean n)} {f : Euclidean n → ℝ}
    (hf : ContinuousOn f E) : IsFormOn E n (densityForm f) := by
  refine ⟨fun x hx => Submodule.smul_mem _ _ (coordinateWedge_mem id), fun S => ?_⟩
  change ContinuousOn (fun x => (exteriorBasis n).repr (f x • standardVolume n) S) E
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  convert! hf.mul (continuousOn_const (c := (exteriorBasis n).repr (standardVolume n) S)) using 1

def Surface.image {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) : Set (Euclidean n) :=
  Φ.map '' Φ.domain.carrier

lemma Surface.isCompact_image {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) :
    IsCompact Φ.image := Φ.domain.isCompact.image_of_continuousOn
      (Φ.regularity.continuousOn.mono Φ.domain_subset)

def Surface.imageSurface {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) :
    Surface k n Φ.image where
  domain := Φ.domain
  map := Φ.map
  neighborhood := Φ.neighborhood
  open_neighborhood := Φ.open_neighborhood
  domain_subset := Φ.domain_subset
  regularity := Φ.regularity
  mapsTo := fun u hu => mem_image_of_mem _ hu

def Surface.coordinateMap {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface n n E) : Coord n → Coord n :=
  (coordEquivEuclidean n).symm ∘ Φ.map

lemma Surface.top_integrand {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface n n E) {ω : FormField n} (hω : IsFormOn E n ω)
    {u : Coord n} (hu : u ∈ Φ.domain.carrier) :
    surfaceIntegrand Φ ω u = coordinateJacobian Φ.coordinateMap u *
      topFormDensity ω (Φ.coordinateMap u) := by
  let e := coordEquivEuclidean n
  have hd : HasFDerivAt Φ.coordinateMap
      (e.symm.toContinuousLinearMap.comp (fderiv ℝ Φ.map u)) u :=
    e.symm.hasFDerivAt.comp u (Φ.differentiableAt hu).hasFDerivAt
  have hv : (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) =
      fun j => e (fderiv ℝ Φ.coordinateMap u (Pi.single j 1)) := by
    rw [hd.fderiv]
    funext j
    exact (e.apply_symm_apply _).symm
  change evaluateForm n (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (ω (Φ.map u)) = _
  rw [hv]
  simpa only [coordinateJacobian, topFormDensity, Surface.coordinateMap,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using!
    evaluateForm_precompose e.toContinuousLinearMap (fderiv ℝ Φ.coordinateMap u)
      (hω.1 _ (Φ.mapsTo hu))

lemma topFormDensity_densityForm {n : ℕ} (f : Euclidean n → ℝ) (u : Coord n) :
    topFormDensity (densityForm f) u = f (coordEquivEuclidean n u) := by
  simp only [topFormDensity, densityForm, map_smul, smul_eq_mul, standardVolume,
    evaluateForm_coordinateWedge, id_eq]
  have he : (fun i j : Fin n => coordEquivEuclidean n (Pi.single j 1) i) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    change (Pi.single j (1 : ℝ) : Coord n) i = _
    simp [Pi.single_apply, Matrix.one_apply, eq_comm]
  rw [he, Matrix.det_one, mul_one]

lemma Surface.continuousOn_densityIntegrand {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface n n E) {f : Euclidean n → ℝ} (hf : ContinuousOn f Φ.image) :
    ContinuousOn (surfaceIntegrand Φ (densityForm f)) Φ.domain.carrier :=
  Φ.imageSurface.continuousOn_integrand (isFormOn_densityForm hf)

lemma surfaceIntegrand_densityForm {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface n n E) {f : Euclidean n → ℝ} (hf : ContinuousOn f Φ.image)
    {u : Coord n} (hu : u ∈ Φ.domain.carrier) :
    surfaceIntegrand Φ (densityForm f) u = f (Φ.map u) * coordinateJacobian Φ.coordinateMap u := by
  have h := Φ.imageSurface.top_integrand (isFormOn_densityForm hf) hu
  rw [topFormDensity_densityForm] at h
  simpa! only [surfaceIntegrand, Surface.coordinateMap, Surface.imageSurface, Function.comp_apply,
    ContinuousLinearEquiv.apply_symm_apply, mul_comm] using h

lemma coordEquivEuclidean_measurePreserving (n : ℕ) :
    MeasurePreserving (coordEquivEuclidean n) := PiLp.volume_preserving_toLp (Fin n)

lemma surfaceIntegral_density_eq_image {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface n n E) (hinj : InjOn Φ.map Φ.domain.carrier)
    (hpos : ∀ u ∈ Φ.domain.carrier, 0 < coordinateJacobian Φ.coordinateMap u)
    {f : Euclidean n → ℝ} (hf : ContinuousOn f Φ.image) :
    Φ.domain.Integrable (surfaceIntegrand Φ (densityForm f)) ∧
      surfaceIntegral Φ (densityForm f) = ∫ x in Φ.image, f x := by
  have hc := Φ.continuousOn_densityIntegrand hf
  refine ⟨ParameterDomain.integrable_of_continuousOn hc, ?_⟩
  have hm : Φ.image = coordEquivEuclidean n '' (Φ.coordinateMap '' Φ.domain.carrier) := by
    simp only [Surface.image, Surface.coordinateMap, image_image, Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  have hi : InjOn Φ.coordinateMap Φ.domain.carrier := by
    intro u hu v hv he
    exact hinj hu hv ((coordEquivEuclidean n).symm.injective he)
  have hd (u : Coord n) (hu : u ∈ Φ.domain.carrier) :
      HasFDerivWithinAt Φ.coordinateMap (fderiv ℝ Φ.coordinateMap u) Φ.domain.carrier u := by
    exact ((coordEquivEuclidean n).symm.differentiableAt.comp u
      (Φ.differentiableAt hu)).hasFDerivAt.hasFDerivWithinAt
  rw [hm, (coordEquivEuclidean_measurePreserving n).setIntegral_image_emb
    (coordEquivEuclidean n).toHomeomorph.measurableEmbedding]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume Φ.domain.isClosed.measurableSet hd hi,
    surfaceIntegral, ParameterDomain.integral_eq_setIntegral hc]
  apply setIntegral_congr_fun Φ.domain.isClosed.measurableSet
  intro u hu
  rw [surfaceIntegrand_densityForm Φ hf hu]
  change f (Φ.map u) * coordinateJacobian Φ.coordinateMap u =
    |coordinateJacobian Φ.coordinateMap u| * f (coordEquivEuclidean n (Φ.coordinateMap u))
  rw [abs_of_pos (hpos u hu)]
  simp only [Surface.coordinateMap, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
    mul_comm]

/-- The volume-element formula uses only the C¹ regularity of the original
surface and continuity of the density on its actual image. -/
def pma10_44_contract : Prop :=
  (∀ (n : ℕ) (E : Set (Euclidean n)) (Φ : Surface n n E)
      (f : Euclidean n → ℝ), ContinuousOn f Φ.image →
    Φ.domain.Integrable (surfaceIntegrand Φ (densityForm f)) ∧
      ∀ u ∈ Φ.domain.carrier, surfaceIntegrand Φ (densityForm f) u =
        f (Φ.map u) * coordinateJacobian Φ.coordinateMap u) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (Φ : Surface n n E),
    InjOn Φ.map Φ.domain.carrier →
    (∀ u ∈ Φ.domain.carrier, 0 < coordinateJacobian Φ.coordinateMap u) →
    (∀ (f : Euclidean n → ℝ), ContinuousOn f Φ.image →
      surfaceIntegral Φ (densityForm f) = ∫ x in Φ.image, f x) ∧
    surfaceIntegral Φ (densityForm (fun _ => 1)) = (volume Φ.image).toReal)

theorem pma10_44 : pma10_44_contract := by
  refine ⟨?_, ?_⟩
  · intro n E Φ f hf
    exact ⟨ParameterDomain.integrable_of_continuousOn (Φ.continuousOn_densityIntegrand hf),
      fun u hu => surfaceIntegrand_densityForm Φ hf hu⟩
  · intro n E Φ hi hp
    refine ⟨fun f hf => (surfaceIntegral_density_eq_image Φ hi hp hf).2, ?_⟩
    rw [(surfaceIntegral_density_eq_image Φ hi hp continuousOn_const).2]
    simp [measureReal_def]

end Rudin.PMA.Chapter10
