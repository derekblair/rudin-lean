import Rudin.PMA.Chapter10.ClassicalStokes
import Rudin.PMA.Chapter10.PlanarGreen

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma exteriorDerivative_vectorTwoForm_density {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    EqOn (exteriorDerivative (vectorTwoForm F)) (densityForm (divergence F)) E :=
  exteriorDerivative_vectorTwoForm hE hF

lemma PositiveRegion.isCompact_carrier {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E) :
    IsCompact R.carrier := isCompact_iUnion fun i => (R.piece i).isCompact_carrier

lemma PositiveRegion.carrier_subset {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E) :
    R.carrier ⊆ E := iUnion_subset fun i => image_subset_iff.mpr (R.piece i).simplex.mapsTo

lemma divergence_theorem {E : Set (Euclidean 3)} (hE : IsOpen E) (R : PositiveRegion 3 E)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    regionIntegral R (divergence F) = chainFlux F R.boundary := by
  have hf := (contDiffOn_divergence (r := 0) hE hF).continuousOn
  rw [regionIntegral_eq_chain R hf, ← chainIntegral_vectorTwoForm, PositiveRegion.boundary,
    ← pma10_33 2 3 E (vectorTwoForm F) R.chain hE (isCFormOn_vectorTwoForm hF)]
  exact chainIntegral_congr_eqOn (isFormOn_densityForm hf)
    (pma10_18.1 3 2 E _ hE (isCFormOn_vectorTwoForm hF)).1
    (exteriorDerivative_vectorTwoForm_density hE hF).symm R.chain

lemma boundaryFlux_independent {E : Set (Euclidean 3)} (hE : IsOpen E)
    (R T : PositiveRegion 3 E) (hRT : R.carrier = T.carrier) {F : VectorField}
    (hF : ContinuousOn F E) : chainFlux F R.boundary = chainFlux F T.boundary := by
  rw [← chainIntegral_vectorTwoForm]
  exact R.boundary_independent T hE hRT _ (isFormOn_vectorTwoForm hF)

/-- The ordinary volume integral of divergence equals the actual outward
normal-component flux of an admissible positive region, including signed multiplicities. -/
def pma10_51_contract : Prop :=
  ∀ (E : Set (Euclidean 3)), IsOpen E → ∀ (R : PositiveRegion 3 E)
    (F : VectorField), ContDiffOn ℝ 1 F E →
    IntegrableOn (divergence F) R.carrier ∧
    regionIntegral R (divergence F) = chainIntegral (densityForm (divergence F)) R.chain ∧
    regionIntegral R (divergence F) = chainFlux F R.boundary ∧
    chainFlux F R.boundary = R.boundary.sum (fun σ z => (z : ℝ) *
      σ.toSurface.domain.integral
        (fun u => inner ℝ (F (σ.map u)) (surfaceUnitNormal σ.toSurface u) * ‖surfaceNormal σ.toSurface u‖)) ∧
    (∀ i : Fin R.size, (R.piece i).simplex.toSurface.domain.Integrable
      (surfaceIntegrand (R.piece i).simplex.toSurface (densityForm (divergence F)))) ∧
    (∀ σ : C2Simplex 2 3 E, σ ∈ R.boundary.support →
      σ.toSurface.domain.Integrable (fluxIntegrand σ.toSurface F) ∧
      σ.toSurface.domain.Integrable
        (fun u => inner ℝ (F (σ.map u)) (surfaceUnitNormal σ.toSurface u) * ‖surfaceNormal σ.toSurface u‖)) ∧
    (∀ (T : PositiveRegion 3 E), R.carrier = T.carrier → ∀ H : VectorField,
      ContinuousOn H E → chainFlux H R.boundary = chainFlux H T.boundary)

theorem pma10_51 : pma10_51_contract := by
  intro E hE R F hF
  have hf := (contDiffOn_divergence (r := 0) hE hF).continuousOn
  refine ⟨(hf.mono R.carrier_subset).integrableOn_compact R.isCompact_carrier,
    regionIntegral_eq_chain R hf, divergence_theorem hE R hF,
    chainFlux_eq_sum_normal_component _ _, ?_, ?_, ?_⟩
  · intro i
    exact ParameterDomain.integrable_of_continuousOn
      ((R.piece i).simplex.toSurface.continuousOn_integrand (isFormOn_densityForm hf))
  · intro σ hσ
    have h := pma10_49 E σ.toSurface F
      (hF.continuousOn.mono (image_subset_iff.mpr σ.toSurface.mapsTo))
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  · intro T hRT H hH
    exact boundaryFlux_independent hE R T hRT hH

end Rudin.PMA.Chapter10
