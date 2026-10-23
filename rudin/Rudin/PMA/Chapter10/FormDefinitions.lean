import Rudin.PMA.Chapter10.FormRegularity
import Rudin.PMA.Chapter10.ScalarForms
import Rudin.PMA.Chapter10.Simplex

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def ParameterDomain.Integrable {k : ℕ} (D : ParameterDomain k) (f : Coord k → ℝ) : Prop :=
  match D with
  | .cell C => IteratedRIntegrable C f
  | .simplex => IteratedRIntegrable (Cell.unit k) (simplexExtension f)

def pma10_11_contract : Prop :=
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Φ : Surface k n E) (ω : FormField n),
    IsFormOn E k ω → ContinuousOn (surfaceIntegrand Φ ω) Φ.domain.carrier ∧
      Φ.domain.Integrable (surfaceIntegrand Φ ω)) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n))
    (a : (Fin k → Fin n) → Euclidean n → ℝ),
    (∀ I, ContinuousOn (a I) E) → IsFormOn E k (formFromCoefficients a) ∧
      ∀ Φ : Surface k n E, surfaceIntegral Φ (formFromCoefficients a) =
        Φ.domain.integral (fun u => ∑ I, a I (Φ.map u) *
          Matrix.det (fun i j => (fderiv ℝ Φ.map u (Pi.single j 1)) (I i)))) ∧
  (∀ (r k n : ℕ) (E : Set (Euclidean n))
    (a : (Fin k → Fin n) → Euclidean n → ℝ),
    (∀ I, ContDiffOn ℝ r (a I) E) → IsCFormOn r E k (formFromCoefficients a)) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ),
    ContinuousOn f E → IsFormOn E 0 (scalarForm f)) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (ω : FormField n), IsFormOn E 0 ω →
    ∃ f : Euclidean n → ℝ, ContinuousOn f E ∧ EqOn (scalarForm f) ω E ∧
      ∀ g : Euclidean n → ℝ, EqOn (scalarForm g) ω E → EqOn g f E) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (Φ : Surface 0 n E) (f : Euclidean n → ℝ),
    surfaceIntegral Φ (scalarForm f) = f (Φ.map 0))

lemma ParameterDomain.integrable_of_continuousOn {k : ℕ} {D : ParameterDomain k}
    {f : Coord k → ℝ} (hf : ContinuousOn f D.carrier) : D.Integrable f := by
  cases D with
  | cell C => exact iteratedRIntegrable_of_continuousOn hf
  | simplex => exact simplex_iteratedRIntegrable hf

lemma ParameterDomain.integral_zero_dimension (D : ParameterDomain 0) (f : Coord 0 → ℝ) :
    D.integral f = f 0 := by
  cases D with
  | cell C => rfl
  | simplex => simp [ParameterDomain.integral, simplexRIntegral, iteratedRIntegral,
      simplexExtension, standardSimplex]

lemma surfaceIntegral_scalar_zero_dimension {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 0 n E) (f : Euclidean n → ℝ) :
    surfaceIntegral Φ (scalarForm f) = f (Φ.map 0) := by
  rw [surfaceIntegral, Φ.domain.integral_zero_dimension]
  exact evaluateForm_scalar _ _

theorem pma10_11 : pma10_11_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k n E Φ ω hω
    exact ⟨Φ.continuousOn_integrand hω,
      ParameterDomain.integrable_of_continuousOn (Φ.continuousOn_integrand hω)⟩
  · intro k n E a ha
    exact ⟨isFormOn_fromCoefficients ha, fun Φ => surfaceIntegral_fromCoefficients Φ a⟩
  · intro r k n E a ha
    exact isCFormOn_fromCoefficients ha
  · intro n E f hf
    exact isFormOn_scalarForm hf
  · intro n E ω hω
    obtain ⟨f, hf, he⟩ := zero_form_correspondence hω
    exact ⟨f, hf, he, fun _ hg => scalarForm_injective_on (hg.trans he.symm)⟩
  · intro n E Φ f
    exact surfaceIntegral_scalar_zero_dimension Φ f

end Rudin.PMA.Chapter10
