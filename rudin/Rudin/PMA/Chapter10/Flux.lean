import Rudin.PMA.Chapter10.AreaElements
import Rudin.PMA.Chapter10.Circulation

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def surfaceUnitNormal {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (u : Coord 2) : Euclidean 3 :=
  unitDirection (surfaceNormal Φ u)

def fluxIntegrand {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (F : VectorField) (u : Coord 2) : ℝ :=
  inner ℝ (F (Φ.map u)) (surfaceNormal Φ u)

def flux {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (F : VectorField) : ℝ :=
  Φ.domain.integral (fluxIntegrand Φ F)

/-- Flux uses actual derivative minors and native area weights, including every
rank-deficient point. The normal belongs to the parameter, not a presumed inverse image map. -/
def pma10_49_contract : Prop :=
  ∀ (E : Set (Euclidean 3)) (Φ : Surface 2 3 E) (F : VectorField),
    ContinuousOn F (Φ.map '' Φ.domain.carrier) →
    (∀ u, ‖surfaceUnitNormal Φ u‖ = 1 ∧
      surfaceNormal Φ u = ‖surfaceNormal Φ u‖ • surfaceUnitNormal Φ u) ∧
    Φ.domain.Integrable (surfaceIntegrand Φ (vectorTwoForm F)) ∧
    Φ.domain.Integrable (fluxIntegrand Φ F) ∧
    Φ.domain.Integrable (fun u => inner ℝ (F (Φ.map u)) (surfaceUnitNormal Φ u) * ‖surfaceNormal Φ u‖) ∧
    surfaceIntegral Φ (vectorTwoForm F) = flux Φ F ∧
    flux Φ F = Φ.domain.integral
      (fun u => inner ℝ (F (Φ.map u)) (surfaceUnitNormal Φ u) * ‖surfaceNormal Φ u‖) ∧
    (∀ (u : Coord 2) (e : Euclidean 3), ‖e‖ = 1 →
      inner ℝ (F (Φ.map u)) (directionWithFallback (surfaceNormal Φ u) e) * ‖surfaceNormal Φ u‖ =
        fluxIntegrand Φ F u)

lemma fluxIntegrand_continuousOn {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    {F : VectorField} (hF : ContinuousOn F (Φ.map '' Φ.domain.carrier)) :
    ContinuousOn (fluxIntegrand Φ F) Φ.domain.carrier :=
  (hF.comp (Φ.regularity.continuousOn.mono Φ.domain_subset) (mapsTo_image _ _)).inner
    (surfaceNormal_continuousOn Φ)

lemma flux_integrable {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    {F : VectorField} (hF : ContinuousOn F (Φ.map '' Φ.domain.carrier)) :
    Φ.domain.Integrable (fluxIntegrand Φ F) :=
  ParameterDomain.integrable_of_continuousOn (fluxIntegrand_continuousOn Φ hF)

lemma surfaceIntegral_vectorTwoForm {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    (F : VectorField) : surfaceIntegral Φ (vectorTwoForm F) = flux Φ F := by
  unfold surfaceIntegral flux
  congr 1
  funext u
  exact surfaceIntegrand_vectorTwoForm Φ F u

lemma flux_eq_normal_component {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (F : VectorField) :
    flux Φ F = Φ.domain.integral
      (fun u => inner ℝ (F (Φ.map u)) (surfaceUnitNormal Φ u) * ‖surfaceNormal Φ u‖) := by
  unfold flux
  congr 1
  funext u
  exact (unitDirection_weighted _ _).symm

theorem pma10_49 : pma10_49_contract := by
  intro E Φ F hF
  have hi := flux_integrable Φ hF
  have hf : surfaceIntegrand Φ (vectorTwoForm F) = fluxIntegrand Φ F :=
    funext (surfaceIntegrand_vectorTwoForm Φ F)
  have hw : (fun u => inner ℝ (F (Φ.map u)) (surfaceUnitNormal Φ u) * ‖surfaceNormal Φ u‖) =
      fluxIntegrand Φ F := funext fun u => unitDirection_weighted _ _
  exact ⟨fun u => ⟨unitDirection_norm _, unitDirection_reconstruct _⟩,
    hf.symm ▸ hi, hi, hw.symm ▸ hi, surfaceIntegral_vectorTwoForm Φ F,
    flux_eq_normal_component Φ F, fun u e he => directionWithFallback_weighted _ _ _⟩

end Rudin.PMA.Chapter10
