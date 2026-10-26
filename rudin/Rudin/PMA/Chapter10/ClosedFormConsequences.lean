import Rudin.PMA.Chapter10.ClosedExact
import Rudin.PMA.Chapter10.OneFormCoordinates

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Source10.35: the coordinate criteria for one-forms, dependence of exact-form
integrals only on the functional boundary, closed-form integrals on boundaries,
and the vanishing of the second boundary. -/
def pma10_35_contract : Prop :=
  (∀ (n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsCFormOn 1 E 1 ω →
      (IsClosedOn E 1 ω ↔ ∀ x ∈ E, ∀ i j : Fin n,
        coordinatePartial (formCoefficient ω {j}) x i =
          coordinatePartial (formCoefficient ω {i}) x j)) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsFormOn E 1 ω →
      (IsExactOn E 1 ω ↔ ∃ f : Euclidean n → ℝ, ContDiffOn ℝ 1 f E ∧
        ∀ x ∈ E, ∀ i : Fin n, coordinatePartial f x i = formCoefficient ω {i} x)) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsFormOn E (k + 1) ω → IsExactOn E (k + 1) ω →
      ∀ Γ Δ : SimplexChain (k + 1) n E,
        ChainEq (chainBoundary Γ) (chainBoundary Δ) → chainIntegral ω Γ = chainIntegral ω Δ) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsFormOn E (k + 1) ω → IsExactOn E (k + 1) ω →
      ∀ Γ : SimplexChain (k + 1) n E,
        ChainEq (chainBoundary Γ) 0 → chainIntegral ω Γ = 0) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsClosedOn E k ω → ∀ Γ : SimplexChain (k + 1) n E,
      chainIntegral ω (chainBoundary Γ) = 0) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Γ : SimplexChain (k + 2) n E),
    chainBoundary (chainBoundary Γ) = 0 ∧ ChainEq (chainBoundary (chainBoundary Γ)) 0)


lemma one_form_closed_iff_cross_partials {n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsCFormOn 1 E 1 ω) :
    IsClosedOn E 1 ω ↔ ∀ x ∈ E, ∀ i j : Fin n,
      coordinatePartial (formCoefficient ω {j}) x i =
        coordinatePartial (formCoefficient ω {i}) x j := by
  constructor
  · intro hc x hx
    exact (exteriorDerivative_one_form_eq_zero_iff hE hω hx).mp (hc.2 hx)
  · intro hp
    exact ⟨hω, fun x hx => (exteriorDerivative_one_form_eq_zero_iff hE hω hx).mpr (hp x hx)⟩

lemma one_form_exact_iff_potential {n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E 1 ω) :
    IsExactOn E 1 ω ↔ ∃ f : Euclidean n → ℝ, ContDiffOn ℝ 1 f E ∧
      ∀ x ∈ E, ∀ i : Fin n, coordinatePartial f x i = formCoefficient ω {i} x := by
  constructor
  · rintro ⟨η, hη, he⟩
    let f := formCoefficient η ∅
    have hs : EqOn (scalarForm f) η E :=
      fun x hx => scalarForm_eq_of_degree_zero (hη.1 x hx)
    have hd : EqOn (scalarDifferential f) ω E := by
      have hh : EqOn (exteriorDerivative (scalarForm f)) (exteriorDerivative η) E :=
        fun x hx => exteriorDerivative_congr_of_eqOn hE hs hx
      rw [exteriorDerivative_scalarForm] at hh
      exact hh.trans he
    refine ⟨f, hη.2 ∅, fun x hx i => ?_⟩
    have hh := congrArg (fun a => (exteriorBasis n).repr a {i}) (hd hx)
    change formCoefficient (scalarDifferential f) {i} x = formCoefficient ω {i} x at hh
    simpa only [formCoefficient_scalarDifferential_singleton] using hh
  · rintro ⟨f, hf, hp⟩
    refine ⟨scalarForm f, isCFormOn_scalarForm hf, ?_⟩
    rw [exteriorDerivative_scalarForm]
    intro x hx
    rw [scalarDifferential, one_form_expansion hω hx]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hp x hx i]

lemma chainIntegral_zero_form {k n : ℕ} {E : Set (Euclidean n)}
    (Γ : SimplexChain k n E) : chainIntegral (0 : FormField n) Γ = 0 := by
  have he : chainIntegral (k := k) (E := E) (0 : FormField n) = 0 := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [chainIntegral_single, surfaceIntegral_zero, mul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun he Γ

lemma exact_chainIntegral_eq_primitive_boundary {k n : ℕ} {E : Set (Euclidean n)}
    {ω η : FormField n} (hE : IsOpen E) (hω : IsFormOn E (k + 1) ω)
    (hη : IsCFormOn 1 E k η) (he : EqOn (exteriorDerivative η) ω E)
    (Γ : SimplexChain (k + 1) n E) :
    chainIntegral ω Γ = chainIntegral η (chainBoundary Γ) := by
  have hdη : IsFormOn E (k + 1) (exteriorDerivative η) :=
    (isCFormOn_exteriorDerivative (r := 0) hE hη).isFormOn
  rw [chainIntegral_congr_eqOn hω hdη he.symm Γ]
  exact pma10_33 k n E η Γ hE hη

lemma exact_chainIntegral_eq_of_boundary_eq {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E (k + 1) ω)
    (he : IsExactOn E (k + 1) ω) (Γ Δ : SimplexChain (k + 1) n E)
    (hboundary : ChainEq (chainBoundary Γ) (chainBoundary Δ)) :
    chainIntegral ω Γ = chainIntegral ω Δ := by
  obtain ⟨η, hη, heη⟩ := he
  rw [exact_chainIntegral_eq_primitive_boundary hE hω hη heη Γ,
    exact_chainIntegral_eq_primitive_boundary hE hω hη heη Δ]
  exact hboundary η hη.isFormOn

lemma exact_chainIntegral_eq_zero_of_cycle {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E (k + 1) ω)
    (he : IsExactOn E (k + 1) ω) (Γ : SimplexChain (k + 1) n E)
    (hcycle : ChainEq (chainBoundary Γ) 0) : chainIntegral ω Γ = 0 := by
  obtain ⟨η, hη, heη⟩ := he
  rw [exact_chainIntegral_eq_primitive_boundary hE hω hη heη Γ, hcycle η hη.isFormOn, map_zero]

lemma closed_chainIntegral_boundary_eq_zero {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsClosedOn E k ω)
    (Γ : SimplexChain (k + 1) n E) : chainIntegral ω (chainBoundary Γ) = 0 := by
  rw [← pma10_33 k n E ω Γ hE hω.1]
  have hdω : IsFormOn E (k + 1) (exteriorDerivative ω) :=
    (isCFormOn_exteriorDerivative (r := 0) hE hω.1).isFormOn
  rw [chainIntegral_congr_eqOn hdω (isFormOn_zero E) hω.2 Γ, chainIntegral_zero_form]

lemma not_exact_of_nonzero_cycle_integral {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E (k + 1) ω)
    (Γ : SimplexChain (k + 1) n E) (hcycle : ChainEq (chainBoundary Γ) 0)
    (hne : chainIntegral ω Γ ≠ 0) : ¬ IsExactOn E (k + 1) ω :=
  fun he => hne (exact_chainIntegral_eq_zero_of_cycle hE hω he Γ hcycle)

lemma not_boundary_of_closed_integral_ne_zero {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsClosedOn E k ω)
    (Γ : SimplexChain k n E) (hne : chainIntegral ω Γ ≠ 0) :
    ¬ ∃ Δ : SimplexChain (k + 1) n E, ChainEq (chainBoundary Δ) Γ := by
  rintro ⟨Δ, hΔ⟩
  exact hne ((hΔ ω hω.1.isFormOn).symm.trans (closed_chainIntegral_boundary_eq_zero hE hω Δ))

theorem pma10_35 : pma10_35_contract := by
  refine ⟨fun _ _ _ => one_form_closed_iff_cross_partials,
    fun _ _ _ => one_form_exact_iff_potential,
    fun _ _ _ _ => exact_chainIntegral_eq_of_boundary_eq,
    fun _ _ _ _ => exact_chainIntegral_eq_zero_of_cycle,
    fun _ _ _ _ => closed_chainIntegral_boundary_eq_zero, ?_⟩
  intro k n E Γ
  refine ⟨chainBoundary_twice Γ, ?_⟩
  rw [chainBoundary_twice]
  exact fun _ _ => rfl

end Rudin.PMA.Chapter10
