import Rudin.PMA.Chapter10.FormsAlgebra
import Rudin.PMA.Chapter10.SurfaceDomains

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma formCoefficient_fromCoefficients {n k : ℕ}
    (a : (Fin k → Fin n) → Euclidean n → ℝ) (S : Finset (Fin n)) (x : Euclidean n) :
    formCoefficient (formFromCoefficients a) S x =
      ∑ I, a I x * (exteriorBasis n).repr (coordinateWedge I) S := by
  simp [formCoefficient, formFromCoefficients, map_sum, map_smul]

lemma isFormOn_fromCoefficients {n k : ℕ} {E : Set (Euclidean n)}
    {a : (Fin k → Fin n) → Euclidean n → ℝ} (ha : ∀ I, ContinuousOn (a I) E) :
    IsFormOn E k (formFromCoefficients a) := by
  refine ⟨fun x _ => formFromCoefficients_grade a x, fun S => ?_⟩
  simp only [funext (formCoefficient_fromCoefficients a S)]
  exact continuousOn_finset_sum _ fun I _ => (ha I).mul continuousOn_const

lemma isCFormOn_fromCoefficients {n k r : ℕ} {E : Set (Euclidean n)}
    {a : (Fin k → Fin n) → Euclidean n → ℝ} (ha : ∀ I, ContDiffOn ℝ r (a I) E) :
    IsCFormOn r E k (formFromCoefficients a) := by
  refine ⟨fun x _ => formFromCoefficients_grade a x, fun S => ?_⟩
  simp only [funext (formCoefficient_fromCoefficients a S)]
  exact ContDiffOn.sum fun I _ => (ha I).mul contDiffOn_const

lemma IsCFormOn.isFormOn {n k r : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsCFormOn r E k ω) : IsFormOn E k ω :=
  ⟨hω.1, fun S => (hω.2 S).continuousOn⟩

lemma evaluateForm_wrong_degree {n k m : ℕ} (v : Fin k → Euclidean n)
    (I : Fin m → Fin n) (h : m ≠ k) : evaluateForm k v (coordinateWedge I) = 0 := by
  simp [evaluateForm, coordinateWedge, ExteriorAlgebra.liftAlternating_apply_ιMulti, h]

lemma continuousOn_evaluateForm_coordinateWedge {X : Type*} [TopologicalSpace X]
    {n k : ℕ} {s : Set X} {v : X → Fin k → Euclidean n}
    (hv : ∀ j, ContinuousOn (fun x => v x j) s) (I : Fin k → Fin n) :
    ContinuousOn (fun x => evaluateForm k (v x) (coordinateWedge I)) s := by
  simp only [evaluateForm_coordinateWedge]
  apply (continuous_id.matrix_det : Continuous (fun M : Matrix (Fin k) (Fin k) ℝ => M.det)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (EuclideanSpace.proj (I i) : Euclidean n →L[ℝ] ℝ).continuous.comp_continuousOn (hv j)

lemma continuousOn_evaluateForm_basis {X : Type*} [TopologicalSpace X]
    {n k : ℕ} {s : Set X} {v : X → Fin k → Euclidean n}
    (hv : ∀ j, ContinuousOn (fun x => v x j) s) (S : Finset (Fin n)) :
    ContinuousOn (fun x => evaluateForm k (v x) (exteriorBasis n S)) s := by
  let T : StandardIndex n S.card := ⟨S, rfl⟩
  change ContinuousOn (fun x => evaluateForm k (v x) (standardWedge T)) s
  rw [standardWedge_eq_coordinateWedge]
  by_cases h : S.card = k
  · subst k
    exact continuousOn_evaluateForm_coordinateWedge hv _
  · have hz : (fun x => evaluateForm k (v x)
        (coordinateWedge (Set.powersetCard.ofFinEmbEquiv.symm T))) = fun _ => 0 := by
      funext x
      exact evaluateForm_wrong_degree _ _ h
    rw [hz]
    exact continuousOn_const

lemma continuousOn_formEvaluation {X : Type*} [TopologicalSpace X]
    {n k : ℕ} {s : Set X} {v : X → Fin k → Euclidean n} {ω : X → CotangentExterior n}
    (hv : ∀ j, ContinuousOn (fun x => v x j) s)
    (hω : ∀ S, ContinuousOn (fun x => (exteriorBasis n).repr (ω x) S) s) :
    ContinuousOn (fun x => evaluateForm k (v x) (ω x)) s := by
  have he : (fun x => evaluateForm k (v x) (ω x)) =
      fun x => ∑ S, (exteriorBasis n).repr (ω x) S *
        evaluateForm k (v x) (exteriorBasis n S) := by
    funext x
    conv_lhs => rw [← (exteriorBasis n).sum_repr (ω x)]
    simp only [map_sum, map_smul, smul_eq_mul]
  rw [he]
  exact continuousOn_finset_sum _ fun S _ =>
    (hω S).mul (continuousOn_evaluateForm_basis hv S)

lemma Surface.continuousOn_integrand {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) {ω : FormField n} (hω : IsFormOn E k ω) :
    ContinuousOn (surfaceIntegrand Φ ω) Φ.domain.carrier := by
  apply continuousOn_formEvaluation
  · intro j
    exact ((Φ.regularity.continuousOn_fderiv_of_isOpen Φ.open_neighborhood le_rfl).clm_apply
      continuousOn_const).mono Φ.domain_subset
  · intro S
    exact (hω.2 S).comp (Φ.regularity.continuousOn.mono Φ.domain_subset) Φ.mapsTo

end Rudin.PMA.Chapter10
