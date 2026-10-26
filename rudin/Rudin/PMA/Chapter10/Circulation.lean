import Rudin.PMA.Chapter10.VectorFields
import Rudin.PMA.Chapter06.Curve

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Normalization with an explicit fallback at the zero vector. -/
def directionWithFallback (v e : Euclidean 3) : Euclidean 3 :=
  if v = 0 then e else ‖v‖⁻¹ • v

def unitDirection (v : Euclidean 3) : Euclidean 3 :=
  directionWithFallback v (coordinateVector 3 0)

def curveVelocity {E : Set (Euclidean 3)} (γ : Surface 1 3 E) (u : Coord 1) : Euclidean 3 :=
  fderiv ℝ γ.map u (Pi.single 0 1)

def curveUnitTangent {E : Set (Euclidean 3)} (γ : Surface 1 3 E) (u : Coord 1) : Euclidean 3 :=
  unitDirection (curveVelocity γ u)

def circulationIntegrand {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    (F : VectorField) (u : Coord 1) : ℝ := inner ℝ (F (γ.map u)) (curveVelocity γ u)

def circulation {E : Set (Euclidean 3)} (γ : Surface 1 3 E) (F : VectorField) : ℝ :=
  γ.domain.integral (circulationIntegrand γ F)

/-- Native circulation with all zero-speed conventions, and the Chapter6 length bridge. -/
def pma10_48_contract : Prop :=
  (∀ (v e : Euclidean 3), ‖e‖ = 1 →
    ‖directionWithFallback v e‖ = 1 ∧ v = ‖v‖ • directionWithFallback v e ∧
    ∀ w : Euclidean 3, inner ℝ w (directionWithFallback v e) * ‖v‖ = inner ℝ w v) ∧
  (∀ (E : Set (Euclidean 3)) (γ : Surface 1 3 E) (F : VectorField),
    ContinuousOn F (γ.map '' γ.domain.carrier) →
    (∀ u, ‖curveUnitTangent γ u‖ = 1 ∧
      curveVelocity γ u = ‖curveVelocity γ u‖ • curveUnitTangent γ u) ∧
    γ.domain.Integrable (surfaceIntegrand γ (vectorOneForm F)) ∧
    γ.domain.Integrable (fun u => ∑ i : Fin 3, F (γ.map u) i * curveVelocity γ u i) ∧
    γ.domain.Integrable (circulationIntegrand γ F) ∧
    γ.domain.Integrable (fun u => inner ℝ (F (γ.map u)) (curveUnitTangent γ u) * ‖curveVelocity γ u‖) ∧
    surfaceIntegral γ (vectorOneForm F) = circulation γ F ∧
    circulation γ F = γ.domain.integral (fun u => ∑ i : Fin 3, F (γ.map u) i * curveVelocity γ u i) ∧
    circulation γ F = γ.domain.integral
      (fun u => inner ℝ (F (γ.map u)) (curveUnitTangent γ u) * ‖curveVelocity γ u‖)) ∧
  (∀ (E : Set (Euclidean 3)) (γ : Surface 1 3 E) (C : Cell 1), γ.domain = .cell C →
    Chapter06.RectifiableCurveOn γ.toCurve.map (C.lower 0) (C.upper 0) ∧
    Chapter06.CurveLength γ.toCurve.map (C.lower 0) (C.upper 0) =
      ENNReal.ofReal (γ.domain.integral (fun u => ‖curveVelocity γ u‖)))

lemma directionWithFallback_norm (v e : Euclidean 3) (he : ‖e‖ = 1) :
    ‖directionWithFallback v e‖ = 1 := by
  by_cases hv : v = 0
  · simp [directionWithFallback, hv, he]
  · simp [directionWithFallback, hv, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v), norm_ne_zero_iff.mpr hv]

lemma directionWithFallback_reconstruct (v e : Euclidean 3) :
    v = ‖v‖ • directionWithFallback v e := by
  by_cases hv : v = 0
  · simp [directionWithFallback, hv]
  · simp [directionWithFallback, hv, smul_smul, norm_ne_zero_iff.mpr hv]

lemma directionWithFallback_weighted (v e w : Euclidean 3) :
    inner ℝ w (directionWithFallback v e) * ‖v‖ = inner ℝ w v := by
  calc
    _ = inner ℝ w (‖v‖ • directionWithFallback v e) := by
      rw [inner_smul_right]
      ring
    _ = inner ℝ w v := congrArg (inner ℝ w) (directionWithFallback_reconstruct v e).symm

lemma unitDirection_norm (v : Euclidean 3) : ‖unitDirection v‖ = 1 := by
  apply directionWithFallback_norm
  simp [coordinateVector, EuclideanSpace.basisFun_apply]

lemma unitDirection_reconstruct (v : Euclidean 3) : v = ‖v‖ • unitDirection v :=
  directionWithFallback_reconstruct v _

lemma unitDirection_weighted (v w : Euclidean 3) :
    inner ℝ w (unitDirection v) * ‖v‖ = inner ℝ w v :=
  directionWithFallback_weighted v _ w

lemma curveVelocity_continuousOn {E : Set (Euclidean 3)} (γ : Surface 1 3 E) :
    ContinuousOn (curveVelocity γ) γ.domain.carrier :=
  ((γ.regularity.continuousOn_fderiv_of_isOpen γ.open_neighborhood le_rfl).clm_apply
    continuousOn_const).mono γ.domain_subset

lemma surfaceIntegrand_vectorOneForm {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    (F : VectorField) (u : Coord 1) :
    surfaceIntegrand γ (vectorOneForm F) u = circulationIntegrand γ F u := by
  simp only [surfaceIntegrand, vectorOneForm, map_sum, map_smul, smul_eq_mul,
    evaluateForm_dx, circulationIntegrand, curveVelocity, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma circulationIntegrand_eq_sum {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    (F : VectorField) (u : Coord 1) :
    circulationIntegrand γ F u = ∑ i : Fin 3, F (γ.map u) i * curveVelocity γ u i := by
  simp only [circulationIntegrand, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma circulationIntegrand_continuousOn {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    {F : VectorField} (hF : ContinuousOn F (γ.map '' γ.domain.carrier)) :
    ContinuousOn (circulationIntegrand γ F) γ.domain.carrier :=
  (hF.comp (γ.regularity.continuousOn.mono γ.domain_subset) (mapsTo_image _ _)).inner
    (curveVelocity_continuousOn γ)

lemma surfaceIntegral_vectorOneForm {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    (F : VectorField) : surfaceIntegral γ (vectorOneForm F) = circulation γ F := by
  simp only [surfaceIntegral, circulation, funext (surfaceIntegrand_vectorOneForm γ F)]

set_option backward.isDefEq.respectTransparency false in
lemma curveVelocity_hasDerivAt {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    {t : ℝ} (ht : (fun _ : Fin 1 => t) ∈ γ.domain.carrier) :
    HasDerivAt γ.toCurve.map (curveVelocity γ (fun _ => t)) t := by
  have hd := γ.differentiableAt ht
  let L : ℝ →L[ℝ] Coord 1 := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)
  have h := hd.hasFDerivAt.comp t L.hasFDerivAt
  have hone : L 1 = Pi.single (0 : Fin 1) 1 := by ext j; fin_cases j; rfl
  change HasDerivAt (fun s => γ.map (L s))
    (fderiv ℝ γ.map (L t) (Pi.single 0 1)) t
  rw [← hone]
  exact h.hasDerivAt

lemma curve_length_native {E : Set (Euclidean 3)} (γ : Surface 1 3 E)
    (C : Cell 1) (hD : γ.domain = .cell C) :
    Chapter06.RectifiableCurveOn γ.toCurve.map (C.lower 0) (C.upper 0) ∧
    Chapter06.CurveLength γ.toCurve.map (C.lower 0) (C.upper 0) =
      ENNReal.ofReal (γ.domain.integral (fun u => ‖curveVelocity γ u‖)) := by
  have hm : MapsTo (fun t : ℝ => (fun _ : Fin 1 => t)) (Icc (C.lower 0) (C.upper 0)) γ.domain.carrier := by
    intro t ht
    rw [hD]
    exact (Cell.mem_carrier.mpr (fun i => by fin_cases i; exact ht))
  have hv := (curveVelocity_continuousOn γ).comp
    (continuous_pi (fun _ => continuous_id)).continuousOn hm
  have h := Chapter06.pma6_27 γ.toCurve.map (fun t => curveVelocity γ (fun _ => t))
    (C.lower 0) (C.upper 0) (C.lower_le_upper 0)
    (fun t ht => (curveVelocity_hasDerivAt γ (hm ht)).hasDerivWithinAt) hv
  refine ⟨h.1, ?_⟩
  rw [h.2.2, hD]
  change _ = ENNReal.ofReal (iteratedRIntegral C _)
  rw [iteratedRIntegral_one]

theorem pma10_48 : pma10_48_contract := by
  refine ⟨fun v e he => ⟨directionWithFallback_norm v e he,
    directionWithFallback_reconstruct v e, fun w => directionWithFallback_weighted v e w⟩, ?_,
    fun E γ C hD => curve_length_native γ C hD⟩
  intro E γ F hF
  have hi := ParameterDomain.integrable_of_continuousOn (circulationIntegrand_continuousOn γ hF)
  have hsum : (fun u => ∑ i : Fin 3, F (γ.map u) i * curveVelocity γ u i) =
      circulationIntegrand γ F := (funext (circulationIntegrand_eq_sum γ F)).symm
  have hweight : (fun u => inner ℝ (F (γ.map u)) (curveUnitTangent γ u) * ‖curveVelocity γ u‖) =
      circulationIntegrand γ F := funext fun u => unitDirection_weighted _ _
  have hform := funext (surfaceIntegrand_vectorOneForm γ F)
  refine ⟨fun u => ⟨unitDirection_norm _, unitDirection_reconstruct _⟩,
    hform.symm ▸ hi, hsum.symm ▸ hi, hi, hweight.symm ▸ hi,
    surfaceIntegral_vectorOneForm γ F, ?_, ?_⟩
  · rw [hsum]; rfl
  · rw [hweight]; rfl

end Rudin.PMA.Chapter10
