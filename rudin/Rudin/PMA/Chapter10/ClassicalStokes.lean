import Rudin.PMA.Chapter10.SurfaceChains
import Rudin.PMA.Chapter10.Flux
import Rudin.PMA.Chapter10.VectorFormDerivatives
import Rudin.PMA.Chapter10.ClosedExact

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def chainCirculation {E : Set (Euclidean 3)} (F : VectorField) : SimplexChain 1 3 E →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ (fun σ => circulation σ.toSurface F)

def chainFlux {E : Set (Euclidean 3)} (F : VectorField) : SimplexChain 2 3 E →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ (fun σ => flux σ.toSurface F)

lemma chainIntegral_vectorOneForm {E : Set (Euclidean 3)} (F : VectorField) :
    chainIntegral (E := E) (vectorOneForm F) = chainCirculation F := by
  simp only [chainIntegral, chainCirculation, surfaceIntegral_vectorOneForm]

lemma chainIntegral_vectorTwoForm {E : Set (Euclidean 3)} (F : VectorField) :
    chainIntegral (E := E) (vectorTwoForm F) = chainFlux F := by
  simp only [chainIntegral, chainFlux, surfaceIntegral_vectorTwoForm]

lemma chainFlux_eq_sum_normal_component {E : Set (Euclidean 3)}
    (Γ : SimplexChain 2 3 E) (F : VectorField) :
    chainFlux F Γ = Γ.sum (fun σ z => (z : ℝ) *
      σ.toSurface.domain.integral (fun u => inner ℝ (F (σ.map u)) (surfaceUnitNormal σ.toSurface u) *
        ‖surfaceNormal σ.toSurface u‖)) := by
  simp only [chainFlux, Finsupp.linearCombination_apply, zsmul_eq_mul, flux_eq_normal_component]
  rfl

lemma chainCirculation_eq_sum_tangent_component {E : Set (Euclidean 3)}
    (Γ : SimplexChain 1 3 E) (F : VectorField) :
    chainCirculation F Γ = Γ.sum (fun σ z => (z : ℝ) *
      σ.toSurface.domain.integral (fun u => inner ℝ (F (σ.map u)) (curveUnitTangent σ.toSurface u) *
        ‖curveVelocity σ.toSurface u‖)) := by
  have he (σ : C2Simplex 1 3 E) : circulation σ.toSurface F =
      σ.toSurface.domain.integral (fun u => inner ℝ (F (σ.map u)) (curveUnitTangent σ.toSurface u) *
        ‖curveVelocity σ.toSurface u‖) := by
    unfold circulation
    congr 1
    funext u
    exact (unitDirection_weighted _ _).symm
  simp only [chainCirculation, Finsupp.linearCombination_apply, zsmul_eq_mul, he]

lemma classical_stokes_surface {E : Set (Euclidean 3)} (hE : IsOpen E)
    (Φ : Surface 2 3 E) (h₂ : Φ.IsC2) {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    flux Φ (curl F) = chainCirculation F (Φ.boundaryChain h₂) := by
  rw [← surfaceIntegral_vectorTwoForm, ← chainIntegral_vectorOneForm,
    ← Φ.stokes hE h₂ (isCFormOn_vectorOneForm hF)]
  have he := exteriorDerivative_vectorOneForm hE hF
  exact (FormEqOn.of_eqOn (isFormOn_vectorTwoForm ((contDiffOn_curl (r := 0) hE hF).continuousOn))
    (pma10_18.1 3 1 E _ hE (isCFormOn_vectorOneForm hF)).1 he.symm) Φ

/-- Classical Stokes on every C2 cell or simplex surface, with actual oriented
chain boundary and native tangent/normal integrability. -/
def pma10_50_contract : Prop :=
  ∀ (E : Set (Euclidean 3)), IsOpen E → ∀ (Φ : Surface 2 3 E) (h₂ : Φ.IsC2)
    (F : VectorField), ContDiffOn ℝ 1 F E →
    flux Φ (curl F) = chainCirculation F (Φ.boundaryChain h₂) ∧
    flux Φ (curl F) = Φ.domain.integral
      (fun u => inner ℝ (curl F (Φ.map u)) (surfaceUnitNormal Φ u) * ‖surfaceNormal Φ u‖) ∧
    Φ.domain.Integrable (fluxIntegrand Φ (curl F)) ∧
    Φ.domain.Integrable
      (fun u => inner ℝ (curl F (Φ.map u)) (surfaceUnitNormal Φ u) * ‖surfaceNormal Φ u‖) ∧
    (∀ σ : C2Simplex 1 3 E, σ ∈ (Φ.boundaryChain h₂).support →
      σ.toSurface.domain.Integrable (circulationIntegrand σ.toSurface F) ∧
      σ.toSurface.domain.Integrable
        (fun u => inner ℝ (F (σ.map u)) (curveUnitTangent σ.toSurface u) * ‖curveVelocity σ.toSurface u‖)) ∧
    chainCirculation F (Φ.boundaryChain h₂) = (Φ.boundaryChain h₂).sum
      (fun σ z => (z : ℝ) * σ.toSurface.domain.integral
        (fun u => inner ℝ (F (σ.map u)) (curveUnitTangent σ.toSurface u) * ‖curveVelocity σ.toSurface u‖))

theorem pma10_50 : pma10_50_contract := by
  intro E hE Φ h₂ F hF
  have hcurl := (contDiffOn_curl (r := 0) hE hF).continuousOn
  have hflux := pma10_49 E Φ (curl F) (hcurl.mono (image_subset_iff.mpr Φ.mapsTo))
  refine ⟨classical_stokes_surface hE Φ h₂ hF, flux_eq_normal_component _ _,
    hflux.2.2.1, hflux.2.2.2.1, ?_, chainCirculation_eq_sum_tangent_component _ _⟩
  intro σ hσ
  have h := pma10_48.2.1 E σ.toSurface F
    (hF.continuousOn.mono (image_subset_iff.mpr σ.toSurface.mapsTo))
  exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩

end Rudin.PMA.Chapter10
