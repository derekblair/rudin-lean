import Rudin.PMA.Chapter10.ChainStokes
import Rudin.PMA.Chapter10.SimplexSeparation
import Rudin.PMA.Chapter10.SimplexBoundarySquared

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- A positive-degree exact form has a C¹ primitive of one lower degree.
No second derivatives of the primitive are assumed. -/
def IsExactOn {n : ℕ} (E : Set (Euclidean n)) : ℕ → FormField n → Prop
  | 0, _ => False
  | k + 1, ω => ∃ η : FormField n, IsCFormOn 1 E k η ∧ EqOn (exteriorDerivative η) ω E

/-- A closed form is C¹ and its exterior derivative vanishes on its domain. -/
def IsClosedOn {n : ℕ} (E : Set (Euclidean n)) (k : ℕ) (ω : FormField n) : Prop :=
  IsCFormOn 1 E k ω ∧ EqOn (exteriorDerivative ω) 0 E

/-- Source10.34: exactness and closedness, and exact C¹ forms are closed even
when their given primitives have only C¹ regularity. -/
def pma10_34_contract : Prop :=
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsExactOn E (k + 1) ω ↔
      ∃ η : FormField n, IsCFormOn 1 E k η ∧ EqOn (exteriorDerivative η) ω E) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsClosedOn E k ω ↔ IsCFormOn 1 E k ω ∧ EqOn (exteriorDerivative ω) 0 E) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsCFormOn 1 E (k + 1) ω → IsExactOn E (k + 1) ω → IsClosedOn E (k + 1) ω)


/-- Pointwise equality of genuine forms gives equality of their actual finite
chain integrals. -/
lemma chainIntegral_congr_eqOn {k n : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsFormOn E k ω) (hη : IsFormOn E k η) (he : EqOn ω η E)
    (Γ : SimplexChain k n E) : chainIntegral ω Γ = chainIntegral η Γ := by
  have hf : chainIntegral (k := k) (E := E) ω = chainIntegral η := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [chainIntegral_single, FormEqOn.of_eqOn hω hη he σ.toSurface]
  exact LinearMap.congr_fun hf Γ

/-- Exactness plus C¹ regularity of the resulting form implies closedness.
The primitive is only C¹: apply Stokes to it on the boundary, then use the
literal second-boundary cancellation and separation by affine simplices. -/
theorem IsExactOn.isClosedOn {k n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (he : IsExactOn E (k + 1) ω) (hE : IsOpen E) (hω : IsCFormOn 1 E (k + 1) ω) :
    IsClosedOn E (k + 1) ω := by
  obtain ⟨η, hη, hηω⟩ := he
  have hdω : IsFormOn E (k + 2) (exteriorDerivative ω) :=
    (isCFormOn_exteriorDerivative (r := 0) hE hω).isFormOn
  have hdη : IsFormOn E (k + 1) (exteriorDerivative η) :=
    (isCFormOn_exteriorDerivative (r := 0) hE hη).isFormOn
  refine ⟨hω, eqOn_zero_of_simplex_integrals_zero hE hdω ?_⟩
  intro σ
  have hs := pma10_33 (k + 1) n E ω (Finsupp.single σ 1) hE hω
  simp only [chainIntegral_single, Int.cast_one, one_mul, chainBoundary_single, one_smul] at hs
  calc
    surfaceIntegral σ.toSurface (exteriorDerivative ω) =
        chainIntegral ω (simplexBoundary σ) := hs
    _ = chainIntegral (exteriorDerivative η) (simplexBoundary σ) :=
      chainIntegral_congr_eqOn hω.isFormOn hdη hηω.symm _
    _ = chainIntegral η (chainBoundary (simplexBoundary σ)) :=
      pma10_33 k n E η (simplexBoundary σ) hE hη
    _ = 0 := by rw [chainBoundary_simplexBoundary, map_zero]

theorem pma10_34 : pma10_34_contract := by
  refine ⟨fun _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl, ?_⟩
  intro k n E ω hE hω he
  exact he.isClosedOn hE hω

end Rudin.PMA.Chapter10
