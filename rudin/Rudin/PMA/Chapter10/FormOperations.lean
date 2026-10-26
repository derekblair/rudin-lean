import Rudin.PMA.Chapter10.FormDefinitions

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma ParameterDomain.isClosed {k : ℕ} (D : ParameterDomain k) : IsClosed D.carrier :=
  D.isCompact.isClosed

lemma ParameterDomain.integral_eq_setIntegral {k : ℕ} {D : ParameterDomain k}
    {f : Coord k → ℝ} (hf : ContinuousOn f D.carrier) :
    D.integral f = ∫ u in D.carrier, f u := by
  cases D with
  | cell C => exact iteratedRIntegral_eq_setIntegral hf
  | simplex => exact simplexRIntegral_eq_integral hf

lemma isFormOn_zero {n k : ℕ} (E : Set (Euclidean n)) : IsFormOn E k 0 := by
  refine ⟨fun _ _ => Submodule.zero_mem _, fun S => ?_⟩
  have he : formCoefficient (0 : FormField n) S = fun _ => 0 := by
    funext x
    simp [formCoefficient]
  rw [he]
  exact continuousOn_const

lemma IsFormOn.add {n k : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsFormOn E k ω) (hη : IsFormOn E k η) : IsFormOn E k (ω + η) := by
  refine ⟨fun x hx => Submodule.add_mem _ (hω.1 x hx) (hη.1 x hx), fun S => ?_⟩
  have he : formCoefficient (ω + η) S = fun x => formCoefficient ω S x + formCoefficient η S x := by
    funext x
    simp [formCoefficient]
  rw [he]
  exact (hω.2 S).add (hη.2 S)

lemma IsFormOn.smul {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) (c : ℝ) : IsFormOn E k (c • ω) := by
  refine ⟨fun x hx => Submodule.smul_mem _ c (hω.1 x hx), fun S => ?_⟩
  have he : formCoefficient (c • ω) S = fun x => c * formCoefficient ω S x := by
    funext x
    simp [formCoefficient]
  rw [he]
  exact continuousOn_const.mul (hω.2 S)

lemma surfaceIntegral_zero {n k : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E) :
    surfaceIntegral Φ 0 = 0 := by
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral
    (Φ.continuousOn_integrand (isFormOn_zero E))]
  simp [surfaceIntegrand]

lemma surfaceIntegral_add {n k : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    {ω η : FormField n} (hω : IsFormOn E k ω) (hη : IsFormOn E k η) :
    surfaceIntegral Φ (ω + η) = surfaceIntegral Φ ω + surfaceIntegral Φ η := by
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand (hω.add hη))]
  have he : surfaceIntegrand Φ (ω + η) = fun u => surfaceIntegrand Φ ω u + surfaceIntegrand Φ η u := by
    funext u
    simp [surfaceIntegrand]
  rw [he, integral_add
    ((Φ.continuousOn_integrand hω).integrableOn_compact Φ.domain.isCompact)
    ((Φ.continuousOn_integrand hη).integrableOn_compact Φ.domain.isCompact)]
  rw [surfaceIntegral, surfaceIntegral, ParameterDomain.integral_eq_setIntegral
    (Φ.continuousOn_integrand hω), ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand hη)]

lemma surfaceIntegral_smul {n k : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    {ω : FormField n} (hω : IsFormOn E k ω) (c : ℝ) :
    surfaceIntegral Φ (c • ω) = c * surfaceIntegral Φ ω := by
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand (hω.smul c))]
  have he : surfaceIntegrand Φ (c • ω) = fun u => c * surfaceIntegrand Φ ω u := by
    funext u
    simp [surfaceIntegrand]
  rw [he, integral_const_mul, surfaceIntegral,
    ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand hω)]

lemma FormEqOn.of_eqOn {n k : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsFormOn E k ω) (hη : IsFormOn E k η) (he : EqOn ω η E) : FormEqOn E k ω η := by
  intro Φ
  rw [surfaceIntegral, surfaceIntegral,
    ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand hω),
    ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand hη)]
  apply setIntegral_congr_fun Φ.domain.isClosed.measurableSet
  intro u hu
  simp only [surfaceIntegrand, he (Φ.mapsTo hu)]

lemma form_vanishes_above_dimension {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) (hnk : n < k) : EqOn ω 0 E := by
  letI : IsEmpty (StandardIndex n k) := ⟨fun S => by
    have h := Finset.card_le_univ S.val
    have hcard : S.val.card = k := S.prop
    simp only [Fintype.card_fin] at h
    omega⟩
  intro x hx
  let z : ⋀[ℝ]^k (Coord n) := ⟨ω x, hω.1 x hx⟩
  have hz := (covectorBasis n).exteriorPower k |>.sum_repr z
  have hz0 : z = 0 := by simpa only [Finset.univ_eq_empty, Finset.sum_empty] using hz.symm
  exact congrArg Subtype.val hz0

def coefficientWedge {n k : ℕ} (f : Euclidean n → ℝ) (I : Fin k → Fin n) :
    FormField n := fun x => f x • coordinateWedge I

def pma10_13_contract : Prop :=
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω η : FormField n),
    FormEqOn E k ω η ↔ ∀ Φ : Surface k n E, surfaceIntegral Φ ω = surfaceIntegral Φ η) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    FormEqOn E k ω 0 ↔ ∀ Φ : Surface k n E, surfaceIntegral Φ ω = 0) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω η : FormField n) (c : ℝ),
    IsFormOn E k ω → IsFormOn E k η → ∀ Φ : Surface k n E,
    surfaceIntegral Φ (c • ω + η) = c * surfaceIntegral Φ ω + surfaceIntegral Φ η) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ) (I : Fin k → Fin n)
    (i j : Fin k), i ≠ j →
    FormEqOn E k (coefficientWedge f (I ∘ Equiv.swap i j)) (-coefficientWedge f I)) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ) (I : Fin k → Fin n)
    (i j : Fin k), i ≠ j → I i = I j → FormEqOn E k (coefficientWedge f I) 0) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    n < k → IsFormOn E k ω → EqOn ω 0 E ∧ FormEqOn E k ω 0)

theorem pma10_13 : pma10_13_contract := by
  refine ⟨fun _ _ _ _ _ => Iff.rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro n k E ω
    simp only [FormEqOn, surfaceIntegral_zero]
  · intro n k E ω η c hω hη Φ
    rw [surfaceIntegral_add Φ (hω.smul c) hη, surfaceIntegral_smul Φ hω c]
  · intro n k E f I i j hij
    apply FormEqOn.of_eq
    funext x
    simp [coefficientWedge, coordinateWedge_swap I hij]
  · intro n k E f I i j hij hI
    apply FormEqOn.of_eq
    funext x
    simp [coefficientWedge, coordinateWedge_repeat I i j hij hI]
  · intro n k E ω hnk hω
    have he := form_vanishes_above_dimension hω hnk
    exact ⟨he, FormEqOn.of_eqOn hω (isFormOn_zero E) he⟩

end Rudin.PMA.Chapter10
