import Rudin.PMA.Chapter10.FormApproximation

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def Surface.coefficientWeight {n k : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (u : Coord k) : ℝ :=
  ∑ S : StandardIndex n k,
    |evaluateForm k (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (standardWedge S)|

lemma Surface.continuousOn_coefficientWeight {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) : ContinuousOn Φ.coefficientWeight Φ.domain.carrier := by
  apply continuousOn_finsetSum
  intro S hS
  apply ContinuousOn.abs
  apply continuousOn_evaluateForm_basis
  intro j
  exact ((Φ.regularity.continuousOn_fderiv_of_isOpen Φ.open_neighborhood le_rfl).clm_apply
    continuousOn_const).mono Φ.domain_subset

lemma Surface.coefficientWeight_nonneg {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (u : Coord k) : 0 ≤ Φ.coefficientWeight u :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

def Surface.coefficientBound {n k : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) : ℝ :=
  ∫ u in Φ.domain.carrier, Φ.coefficientWeight u

lemma Surface.coefficientBound_nonneg {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) : 0 ≤ Φ.coefficientBound :=
  integral_nonneg Φ.coefficientWeight_nonneg

lemma Surface.integrand_difference_bound {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) {ω η : FormField n} (hω : IsFormOn E k ω) (hη : IsFormOn E k η)
    {ε : ℝ} (hε : ∀ S : StandardIndex n k, ∀ x ∈ Φ.map '' Φ.domain.carrier,
      |formCoefficient η S.val x - formCoefficient ω S.val x| ≤ ε)
    {u : Coord k} (hu : u ∈ Φ.domain.carrier) :
    |surfaceIntegrand Φ η u - surfaceIntegrand Φ ω u| ≤ ε * Φ.coefficientWeight u := by
  classical
  unfold surfaceIntegrand
  rw [standard_expansion_field hη (Φ.mapsTo hu), standard_expansion_field hω (Φ.mapsTo hu)]
  simp only [map_sum, map_smul, smul_eq_mul, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ S : StandardIndex n k,
        |formCoefficient η S.val (Φ.map u) * evaluateForm k
          (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (standardWedge S) -
        formCoefficient ω S.val (Φ.map u) * evaluateForm k
          (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (standardWedge S)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S : StandardIndex n k, ε *
        |evaluateForm k (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (standardWedge S)| := by
      apply Finset.sum_le_sum
      intro S hS
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (hε S _ (mem_image_of_mem Φ.map hu)) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

lemma Surface.integral_difference_bound {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) {ω η : FormField n} (hω : IsFormOn E k ω) (hη : IsFormOn E k η)
    {ε : ℝ} (hε : ∀ S : StandardIndex n k, ∀ x ∈ Φ.map '' Φ.domain.carrier,
      |formCoefficient η S.val x - formCoefficient ω S.val x| ≤ ε) :
    |surfaceIntegral Φ η - surfaceIntegral Φ ω| ≤ ε * Φ.coefficientBound := by
  have hcω := Φ.continuousOn_integrand hω
  have hcη := Φ.continuousOn_integrand hη
  rw [surfaceIntegral, surfaceIntegral, ParameterDomain.integral_eq_setIntegral hcη,
    ParameterDomain.integral_eq_setIntegral hcω, ← integral_sub
      (hcη.integrableOn_compact Φ.domain.isCompact) (hcω.integrableOn_compact Φ.domain.isCompact)]
  have hb := (Φ.continuousOn_coefficientWeight.integrableOn_compact (μ := volume) Φ.domain.isCompact).const_mul ε
  have hh := norm_integral_le_of_norm_le (f := fun u => surfaceIntegrand Φ η u - surfaceIntegrand Φ ω u) hb
    (ae_restrict_of_forall_mem Φ.domain.isClosed.measurableSet
      (fun u hu => by simpa only [Real.norm_eq_abs] using Φ.integrand_difference_bound hω hη hε hu))
  simpa only [Real.norm_eq_abs, integral_const_mul, Surface.coefficientBound] using hh

def chainCarrier {n k : ℕ} {E : Set (Euclidean n)} (Γ : SimplexChain k n E) :
    Set (Euclidean n) := ⋃ σ ∈ Γ.support, σ.map '' standardSimplex k

lemma chainCarrier_isCompact {n k : ℕ} {E : Set (Euclidean n)} (Γ : SimplexChain k n E) :
    IsCompact (chainCarrier Γ) := by
  apply Γ.support.isCompact_biUnion
  intro σ hσ
  exact (isCompact_standardSimplex k).image_of_continuousOn
    (σ.toSurface.regularity.continuousOn.mono σ.toSurface.domain_subset)

lemma chainCarrier_subset {n k : ℕ} {E : Set (Euclidean n)} (Γ : SimplexChain k n E) :
    chainCarrier Γ ⊆ E := by
  rintro x hx
  obtain ⟨σ, _, u, hu, rfl⟩ := mem_iUnion₂.mp hx
  exact σ.mapsTo hu

def chainCoefficientBound {n k : ℕ} {E : Set (Euclidean n)} (Γ : SimplexChain k n E) : ℝ :=
  ∑ σ ∈ Γ.support, |(Γ σ : ℝ)| * σ.toSurface.coefficientBound

lemma chainCoefficientBound_nonneg {n k : ℕ} {E : Set (Euclidean n)} (Γ : SimplexChain k n E) :
    0 ≤ chainCoefficientBound Γ :=
  Finset.sum_nonneg fun σ _ => mul_nonneg (abs_nonneg _) σ.toSurface.coefficientBound_nonneg

lemma chainIntegral_difference_bound {n k : ℕ} {E : Set (Euclidean n)}
    (Γ : SimplexChain k n E) {ω η : FormField n} (hω : IsFormOn E k ω) (hη : IsFormOn E k η)
    {ε : ℝ} (hε : ∀ S : StandardIndex n k, ∀ x ∈ chainCarrier Γ,
      |formCoefficient η S.val x - formCoefficient ω S.val x| ≤ ε) :
    |chainIntegral η Γ - chainIntegral ω Γ| ≤ ε * chainCoefficientBound Γ := by
  classical
  simp only [chainIntegral, Finsupp.linearCombination_apply, Finsupp.sum, zsmul_eq_mul,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ σ ∈ Γ.support,
        |(Γ σ : ℝ) * surfaceIntegral σ.toSurface η - (Γ σ : ℝ) * surfaceIntegral σ.toSurface ω| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ ∈ Γ.support, ε * (|(Γ σ : ℝ)| * σ.toSurface.coefficientBound) := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [← mul_sub, abs_mul]
      calc
        _ ≤ |(Γ σ : ℝ)| * (ε * σ.toSurface.coefficientBound) :=
          mul_le_mul_of_nonneg_left (σ.toSurface.integral_difference_bound hω hη
            (fun S x hx => hε S x (mem_iUnion₂.mpr ⟨σ, hσ, hx⟩))) (abs_nonneg _)
        _ = _ := by ring
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- A finite native integration functional vanishing on C¹ forms vanishes on
all continuous forms. No regularity of the original coefficients is added. -/
lemma chainIntegral_zero_of_c1 {n k : ℕ} {E : Set (Euclidean n)} (Γ : SimplexChain k n E)
    (hΓ : ∀ η : FormField n, IsCFormOn 1 E k η → chainIntegral η Γ = 0)
    {ω : FormField n} (hω : IsFormOn E k ω) : chainIntegral ω Γ = 0 := by
  by_contra hne
  have hp : 0 < |chainIntegral ω Γ| := abs_pos.mpr hne
  let C := chainCoefficientBound Γ
  have hC : 0 ≤ C := chainCoefficientBound_nonneg Γ
  let ε := |chainIntegral ω Γ| / (C + 1)
  have hε : 0 < ε := div_pos hp (by positivity)
  obtain ⟨η, hη, ha⟩ := continuous_form_smooth_approximation
    (chainCarrier_isCompact Γ) (chainCarrier_subset Γ) hω hε
  have hb := chainIntegral_difference_bound Γ hω hη.isFormOn (fun S x hx => (ha S x hx).le)
  rw [hΓ η hη, zero_sub, abs_neg] at hb
  have hlt : ε * C < |chainIntegral ω Γ| := by
    have he : ε * (C + 1) = |chainIntegral ω Γ| :=
      div_mul_cancel₀ _ (by positivity : C + 1 ≠ 0)
    nlinarith
  exact (not_lt_of_ge hb) hlt

lemma chainEq_of_c1 {n k : ℕ} {E : Set (Euclidean n)} (Γ Δ : SimplexChain k n E)
    (h : ∀ η : FormField n, IsCFormOn 1 E k η → chainIntegral η Γ = chainIntegral η Δ) :
    ChainEq Γ Δ := by
  intro ω hω
  have hz := chainIntegral_zero_of_c1 (Γ - Δ)
    (fun η hη => by rw [map_sub, h η hη, sub_self]) hω
  simpa only [map_sub, sub_eq_zero] using hz

end Rudin.PMA.Chapter10
