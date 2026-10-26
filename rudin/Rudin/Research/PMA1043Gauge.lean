import Rudin.PMA.Chapter10.VectorPotentials

/-!
# The precise gauge-regularity obligation in PMA 10.43

This module classifies the C¹ vector potentials on the domains in the printed
contract, using the already-proved C² scalar converse. It does not prove the
missing C² vector converse: it identifies that converse with the existence of a
C² scalar gauge whose gradient corrects a given C¹ potential to C².
-/

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10
open Chapter09

lemma coordinatePartial_sub_gauge {n : ℕ} {f g : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinatePartial (fun y => f y - g y) x i =
      coordinatePartial f x i - coordinatePartial g x i := by
  change coordinatePartial (f - g) x i = _
  rw [coordinatePartial_eq_fderiv (hf.sub hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [sub_apply] using
    congrArg (fun A : Euclidean n →L[ℝ] ℝ => A (coordinateVector n i)) (fderiv_sub hf hg)

lemma curl_congr_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {A G : VectorField} (h : EqOn A G E) : EqOn (curl A) (curl G) E := by
  intro x hx
  have hp (i j : Fin 3) : coordinatePartial (fun y => A y j) x i =
      coordinatePartial (fun y => G y j) x i :=
    coordinatePartial_congr_of_eqOn hE (fun y hy => congrArg (fun v => v j) (h hy)) hx i
  ext i
  fin_cases i <;> simp [curl, hp]

lemma curl_add_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {A G : VectorField} (hA : ContDiffOn ℝ 1 A E) (hG : ContDiffOn ℝ 1 G E) :
    EqOn (curl (A + G)) (curl A + curl G) E := by
  intro x hx
  have hdA (i : Fin 3) : DifferentiableAt ℝ (fun y => A y i) x :=
    ((contDiffOn_map_coordinate hA i).differentiableOn (by norm_num)).differentiableAt
      (hE.mem_nhds hx)
  have hdG (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    ((contDiffOn_map_coordinate hG i).differentiableOn (by norm_num)).differentiableAt
      (hE.mem_nhds hx)
  have hp (i j : Fin 3) : coordinatePartial (fun y => A y j + G y j) x i =
      coordinatePartial (fun y => A y j) x i + coordinatePartial (fun y => G y j) x i :=
    coordinatePartial_add (hdA j) (hdG j) i
  ext i
  fin_cases i <;> simp [curl, hp] <;> ring

lemma curl_sub_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {A G : VectorField} (hA : ContDiffOn ℝ 1 A E) (hG : ContDiffOn ℝ 1 G E) :
    EqOn (curl (A - G)) (curl A - curl G) E := by
  intro x hx
  have hdA (i : Fin 3) : DifferentiableAt ℝ (fun y => A y i) x :=
    ((contDiffOn_map_coordinate hA i).differentiableOn (by norm_num)).differentiableAt
      (hE.mem_nhds hx)
  have hdG (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    ((contDiffOn_map_coordinate hG i).differentiableOn (by norm_num)).differentiableAt
      (hE.mem_nhds hx)
  have hp (i j : Fin 3) : coordinatePartial (fun y => A y j - G y j) x i =
      coordinatePartial (fun y => A y j) x i - coordinatePartial (fun y => G y j) x i :=
    coordinatePartial_sub_gauge (hdA j) (hdG j) i
  ext i
  fin_cases i <;> simp [curl, hp] <;> ring

/-- All C¹ potentials for the same field differ by the gradient of a C² scalar.
The equality is only on the original domain; ambient extensions are immaterial. -/
theorem same_curl_iff_gradient_gauge {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {A G : VectorField} (hA : ContDiffOn ℝ 1 A E) (hG : ContDiffOn ℝ 1 G E) :
    EqOn (curl G) (curl A) E ↔
      ∃ φ : Euclidean 3 → ℝ, ContDiffOn ℝ 2 φ E ∧ EqOn G (A + gradient φ) E := by
  constructor
  · intro he
    have hz : EqOn (curl (G - A)) 0 E := by
      intro x hx
      rw [curl_sub_eqOn hE hG hA hx]
      simp only [Pi.sub_apply, he hx, sub_self, Pi.zero_apply]
    obtain ⟨φ, hφ, hgrad⟩ := scalarPotential_c2_of_equivalent_convex e hU hE hc
      (hG.sub hA) hz
    refine ⟨φ, hφ, ?_⟩
    intro x hx
    change G x = A x + gradient φ x
    rw [hgrad hx]
    change G x = A x + (G x - A x)
    abel
  · rintro ⟨φ, hφ, he⟩
    have hg : ContDiffOn ℝ 1 (gradient φ) E := contDiffOn_gradient hE hφ
    intro x hx
    rw [curl_congr_eqOn hE he hx, curl_add_eqOn hE hA hg hx]
    simp only [Pi.add_apply, curl_gradient_eq_zero hE hφ hx, Pi.zero_apply, add_zero]

/-- The exact C² vector-potential endpoint is equivalent to regularizing any
fixed C¹ primitive by a C² scalar gauge. This is an equivalence, not an existence
assertion for such a gauge. -/
theorem c2_vectorPotential_iff_regularizing_gauge {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {A F : VectorField} (hA : ContDiffOn ℝ 1 A E) (hcurl : EqOn (curl A) F E) :
    (∃ G : VectorField, ContDiffOn ℝ 2 G E ∧ EqOn (curl G) F E) ↔
      ∃ φ : Euclidean 3 → ℝ, ContDiffOn ℝ 2 φ E ∧
        ContDiffOn ℝ 2 (A + gradient φ) E := by
  constructor
  · rintro ⟨G, hG, hGF⟩
    have hGA : EqOn (curl G) (curl A) E := hGF.trans hcurl.symm
    obtain ⟨φ, hφ, he⟩ := (same_curl_iff_gradient_gauge e hU hE hc hA
      (hG.of_le (by norm_num))).mp hGA
    exact ⟨φ, hφ, hG.congr (fun x hx => (he hx).symm)⟩
  · rintro ⟨φ, hφ, hregular⟩
    refine ⟨A + gradient φ, hregular, ?_⟩
    have hg : ContDiffOn ℝ 1 (gradient φ) E := contDiffOn_gradient hE hφ
    intro x hx
    rw [curl_add_eqOn hE hA hg hx]
    simpa only [Pi.add_apply, curl_gradient_eq_zero hE hφ hx, Pi.zero_apply, add_zero]
      using hcurl hx

/-- A counterexample must exclude every C² scalar gauge, not only a particular
radial or Coulomb representative. -/
theorem no_c2_vectorPotential_iff_no_regularizing_gauge {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {A F : VectorField} (hA : ContDiffOn ℝ 1 A E) (hcurl : EqOn (curl A) F E) :
    (¬ ∃ G : VectorField, ContDiffOn ℝ 2 G E ∧ EqOn (curl G) F E) ↔
      ∀ φ : Euclidean 3 → ℝ, ContDiffOn ℝ 2 φ E →
        ¬ ContDiffOn ℝ 2 (A + gradient φ) E := by
  rw [c2_vectorPotential_iff_regularizing_gauge e hU hE hc hA hcurl]
  simp only [not_exists, not_and]

/-- A C³ scalar gauge cannot repair a potential that is not C². The C² scalar
regularity in the preceding equivalence is therefore essential. -/
theorem c2_of_c3_regularizing_gauge {E : Set (Euclidean 3)} (hE : IsOpen E)
    {A : VectorField} {φ : Euclidean 3 → ℝ} (hφ : ContDiffOn ℝ 3 φ E)
    (hregular : ContDiffOn ℝ 2 (A + gradient φ) E) : ContDiffOn ℝ 2 A E := by
  have hg : ContDiffOn ℝ 2 (gradient φ) E := contDiffOn_gradient (r := 2) hE hφ
  have h := hregular.sub hg
  simpa only [Pi.add_apply, add_sub_cancel_right] using h

/-- The gauge-regularization obligation, stated with the same domains and fields
as source 10.43 and universally over every C¹ primitive. -/
def VectorPotentialGaugeRegularization : Prop :=
  ∀ (U E : Set (Euclidean 3)) (_e : C2DomainEquivalence U E) (F A : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E →
      EqOn (divergence F) 0 E → ContDiffOn ℝ 1 A E → EqOn (curl A) F E →
        ∃ φ : Euclidean 3 → ℝ, ContDiffOn ℝ 2 φ E ∧
          ContDiffOn ℝ 2 (A + gradient φ) E

/-- The complete printed contract holds exactly when the gauge-regularization
obligation holds. The other three clauses and existence of C¹ primitives are
already proved; this theorem supplies neither side unconditionally. -/
theorem pma10_43_contract_iff_gauge_regularization :
    pma10_43_contract ↔ VectorPotentialGaugeRegularization := by
  constructor
  · intro h U E e F A hU hE hc hF hz hA hcurl
    exact (c2_vectorPotential_iff_regularizing_gauge e hU hE hc hA hcurl).mp
      (h.2.2.2 U E e F hU hE hc hF hz)
  · intro h
    refine ⟨pma10_43_forward.1, pma10_43_forward.2, pma10_43_scalar_converse, ?_⟩
    intro U E e F hU hE hc hF hz
    obtain ⟨A, hA, hcurl⟩ := vectorPotential_c1_of_equivalent_convex e hU hE hc hF hz
    exact (c2_vectorPotential_iff_regularizing_gauge e hU hE hc hA hcurl).mpr
      (h U E e F A hU hE hc hF hz hA hcurl)

end Rudin.PMA.Chapter10
