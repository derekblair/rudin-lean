import Rudin.PMA.Chapter10.StandardForms
import Rudin.PMA.Chapter10.NativeSeparation

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Source10.15: vanishing of every actual surface integral forces all standard
coefficients to vanish; equivalently the genuine homogeneous form vanishes. -/
def pma10_15_contract : Prop :=
  ∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsFormOn E k ω →
      (FormEqOn E k ω 0 ↔ ∀ S : StandardIndex n k, ∀ x ∈ E, formCoefficient ω S.val x = 0) ∧
      (FormEqOn E k ω 0 ↔ EqOn ω 0 E)

/-- Linear part of the coordinate-plane parameterization. -/
def axisDifferential {k n : ℕ} (I : Fin k → Fin n) : Coord k →L[ℝ] Euclidean n :=
  ∑ j, (ContinuousLinearMap.proj j : Coord k →L[ℝ] ℝ).smulRight (coordinateVector n (I j))

@[simp] lemma axisDifferential_apply {k n : ℕ} (I : Fin k → Fin n) (t : Coord k) :
    axisDifferential I t = ∑ j, t j • coordinateVector n (I j) := by
  simp [axisDifferential]

@[simp] lemma axisDifferential_single {k n : ℕ} (I : Fin k → Fin n) (j : Fin k) :
    axisDifferential I (Pi.single j 1) = coordinateVector n (I j) := by
  classical
  simp [axisDifferential_apply, Pi.single_apply, ite_smul]

lemma axisParameterization_hasFDerivAt {k n : ℕ} (x : Euclidean n) (I : Fin k → Fin n)
    (u : Coord k) : HasFDerivAt (axisParameterization x I) (axisDifferential I) u := by
  simpa only [axisParameterization, axisDifferential_apply] using!
    (axisDifferential I).hasFDerivAt.const_add x

@[simp] lemma axisParameterization_fderiv {k n : ℕ} (x : Euclidean n) (I : Fin k → Fin n)
    (u : Coord k) : fderiv ℝ (axisParameterization x I) u = axisDifferential I :=
  (axisParameterization_hasFDerivAt x I u).fderiv

/-- Increasing coordinate planes extract exactly one standard coefficient.
The determinant computation is bridged to the dual exterior-power basis. -/
lemma evaluateForm_standard_axis {k n : ℕ} (S T : StandardIndex n k) :
    evaluateForm k (fun j => coordinateVector n (Set.powersetCard.ofFinEmbEquiv.symm S j))
      (standardWedge T) = if S = T then 1 else 0 := by
  classical
  have he : evaluateForm k
      (fun j => coordinateVector n (Set.powersetCard.ofFinEmbEquiv.symm S j)) (standardWedge T) =
      exteriorPower.ιMultiDual ℝ k (covectorBasis n) S
        (exteriorPower.ιMulti_family ℝ k (covectorBasis n) T) := by
    rw [standardWedge_eq_coordinateWedge, evaluateForm_coordinateWedge,
      exteriorPower.ιMulti_family, exteriorPower.ιMultiDual_apply_ιMulti]
    congr 1
    ext i j
    simp [coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply,
      Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [he]
  by_cases h : S = T
  · subst T
    simp only [ite_true, exteriorPower.ιMultiDual_apply_diag]
  · simp only [ite_eq_right h, exteriorPower.ιMultiDual_apply_nondiag ℝ k (covectorBasis n) S T h]

lemma evaluateForm_axis_coefficient {k n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) (S : StandardIndex n k) {x : Euclidean n} (hx : x ∈ E) :
    evaluateForm k (fun j => coordinateVector n (Set.powersetCard.ofFinEmbEquiv.symm S j)) (ω x) =
      formCoefficient ω S.val x := by
  classical
  rw [standard_expansion_field hω hx]
  simp only [map_sum, map_smul, smul_eq_mul, evaluateForm_standard_axis]
  simp

/-- An actual admissible coordinate box surface, without identifying functional
vanishing with pointwise alternating-tensor vanishing. -/
def axisSurface {k n : ℕ} {E : Set (Euclidean n)} (x : Euclidean n) (I : Fin k → Fin n)
    (C : Cell k) (hC : MapsTo (axisParameterization x I) C.carrier E) : Surface k n E where
  domain := .cell C
  map := axisParameterization x I
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (axisParameterization_contDiff x I 1).contDiffOn
  mapsTo := hC

lemma axisSurface_integral_coefficient {k n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) (S : StandardIndex n k) (x : Euclidean n) (C : Cell k)
    (hC : MapsTo (axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S)) C.carrier E) :
    surfaceIntegral (axisSurface x (Set.powersetCard.ofFinEmbEquiv.symm S) C hC) ω =
      iteratedRIntegral C
        (fun t => formCoefficient ω S.val (axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S) t)) := by
  let Φ := axisSurface x (Set.powersetCard.ofFinEmbEquiv.symm S) C hC
  have hc : ContinuousOn
      (fun t => formCoefficient ω S.val (axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S) t))
      C.carrier :=
    (hω.2 S.val).comp (axisParameterization_contDiff x _ 1).continuous.continuousOn hC
  change surfaceIntegral Φ ω = _
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand hω),
    iteratedRIntegral_eq_setIntegral hc]
  apply setIntegral_congr_fun C.isClosed_carrier.measurableSet
  intro t ht
  change evaluateForm k
    (fun j => fderiv ℝ (axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S)) t (Pi.single j 1))
    (ω (axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S) t)) = _
  simp only [axisParameterization_fderiv, axisDifferential_single]
  exact evaluateForm_axis_coefficient hω S (hC ht)

/-- The substantive separation argument: a nonzero coefficient produces an
admissible coordinate surface with a nonzero native integral. -/
theorem standard_coefficient_zero_of_functional_zero {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E k ω)
    (hzero : FormEqOn E k ω 0) (S : StandardIndex n k) {x : Euclidean n} (hx : x ∈ E) :
    formCoefficient ω S.val x = 0 := by
  by_contra hne
  let I := Set.powersetCard.ofFinEmbEquiv.symm S
  obtain ⟨C, _, hC, _, _, hI⟩ := exists_nonzero_axis_cell hE hx (hω.2 S.val) hne I
  let Φ := axisSurface x I C hC
  have hΦ : surfaceIntegral Φ ω = 0 := (hzero Φ).trans (surfaceIntegral_zero Φ)
  have he := axisSurface_integral_coefficient hω S x C hC
  exact hI (he.symm.trans hΦ)

lemma eqOn_zero_of_standard_coefficients_zero {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hω : IsFormOn E k ω)
    (hz : ∀ S : StandardIndex n k, ∀ x ∈ E, formCoefficient ω S.val x = 0) : EqOn ω 0 E := by
  intro x hx
  rw [standard_expansion_field hω hx]
  simp only [hz _ x hx, zero_smul, Finset.sum_const_zero, Pi.zero_apply]

theorem pma10_15 : pma10_15_contract := by
  intro k n E ω hE hω
  have hforward : FormEqOn E k ω 0 → ∀ S : StandardIndex n k, ∀ x ∈ E,
      formCoefficient ω S.val x = 0 :=
    fun hz S _ hx => standard_coefficient_zero_of_functional_zero hE hω hz S hx
  have hpoint : (∀ S : StandardIndex n k, ∀ x ∈ E, formCoefficient ω S.val x = 0) → EqOn ω 0 E :=
    eqOn_zero_of_standard_coefficients_zero hω
  have hback : EqOn ω 0 E → FormEqOn E k ω 0 := FormEqOn.of_eqOn hω (isFormOn_zero E)
  exact ⟨⟨hforward, fun hz => hback (hpoint hz)⟩,
    ⟨fun hz => hpoint (hforward hz), hback⟩⟩

/-- Uniqueness for two standard forms follows by applying the actual separation
argument to their difference and native integral linearity. -/
lemma FormEqOn.eqOn {k n : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hE : IsOpen E) (hω : IsFormOn E k ω) (hη : IsFormOn E k η)
    (he : FormEqOn E k ω η) : EqOn ω η E := by
  have hd : IsFormOn E k (ω + (-1 : ℝ) • η) := hω.add (hη.smul (-1))
  have hz : FormEqOn E k (ω + (-1 : ℝ) • η) 0 := by
    intro Φ
    rw [surfaceIntegral_add Φ hω (hη.smul (-1)), surfaceIntegral_smul Φ hη (-1),
      surfaceIntegral_zero, he Φ]
    ring
  have hp := (pma10_15 k n E _ hE hd).2.mp hz
  intro x hx
  apply sub_eq_zero.mp
  simpa only [Pi.add_apply, Pi.smul_apply, neg_one_smul, Pi.neg_apply, Pi.zero_apply, sub_eq_add_neg] using hp hx

lemma formEqOn_iff_eqOn {k n : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hE : IsOpen E) (hω : IsFormOn E k ω) (hη : IsFormOn E k η) :
    FormEqOn E k ω η ↔ EqOn ω η E :=
  ⟨FormEqOn.eqOn hE hω hη, FormEqOn.of_eqOn hω hη⟩

end Rudin.PMA.Chapter10
