import Rudin.PMA.Chapter10.FormsAlgebra

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma exteriorBasis_empty (n : ℕ) : exteriorBasis n ∅ = 1 := by
  simpa only [standardWedge, coordinateWedge_zero] using
    (standardWedge_eq_coordinateWedge (⟨∅, rfl⟩ : StandardIndex n 0))

lemma algebraMap_eq_smul_empty (n : ℕ) (a : ℝ) :
    algebraMap ℝ (CotangentExterior n) a = a • exteriorBasis n ∅ := by
  rw [exteriorBasis_empty, Algebra.smul_def, mul_one]

lemma formCoefficient_scalarForm {n : ℕ} (f : Euclidean n → ℝ)
    (S : Finset (Fin n)) (x : Euclidean n) :
    formCoefficient (scalarForm f) S x = if S = ∅ then f x else 0 := by
  classical
  simp [formCoefficient, scalarForm, algebraMap_eq_smul_empty, Basis.repr_self,
    Finsupp.single_apply, eq_comm]

lemma isFormOn_scalarForm {n : ℕ} {E : Set (Euclidean n)} {f : Euclidean n → ℝ}
    (hf : ContinuousOn f E) : IsFormOn E 0 (scalarForm f) := by
  refine ⟨?_, fun S => ?_⟩
  · intro x _
    simp only [ExteriorAlgebra.exteriorPower, pow_zero, scalarForm, Submodule.mem_one]
    exact ⟨f x, rfl⟩
  · simp only [funext (formCoefficient_scalarForm f S)]
    by_cases h : S = ∅
    · simpa only [h, ite_true] using hf
    · simpa only [h, ite_false] using (continuousOn_const : ContinuousOn (fun _ => (0 : ℝ)) E)

lemma isCFormOn_scalarForm {n r : ℕ} {E : Set (Euclidean n)} {f : Euclidean n → ℝ}
    (hf : ContDiffOn ℝ r f E) : IsCFormOn r E 0 (scalarForm f) := by
  refine ⟨(isFormOn_scalarForm hf.continuousOn).1, fun S => ?_⟩
  simp only [funext (formCoefficient_scalarForm f S)]
  by_cases h : S = ∅
  · simpa only [h, ite_true] using hf
  · simpa only [h, ite_false] using (contDiffOn_const : ContDiffOn ℝ r (fun _ => (0 : ℝ)) E)

lemma scalarForm_eq_of_degree_zero {n : ℕ} {ω : FormField n} {x : Euclidean n}
    (h : ω x ∈ (⋀[ℝ]^0 (Coord n))) :
    scalarForm (formCoefficient ω ∅) x = ω x := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (by simpa only [ExteriorAlgebra.exteriorPower, pow_zero] using h)
  have he : formCoefficient ω ∅ x = a := by
    change (exteriorBasis n).repr (ω x) ∅ = a
    rw [← ha, algebraMap_eq_smul_empty]
    simp
  simpa only [scalarForm, he] using ha

lemma zero_form_correspondence {n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E 0 ω) :
    ∃ f : Euclidean n → ℝ, ContinuousOn f E ∧ EqOn (scalarForm f) ω E :=
  ⟨formCoefficient ω ∅, hω.2 ∅, fun _ hx => scalarForm_eq_of_degree_zero (hω.1 _ hx)⟩

lemma scalarForm_injective_on {n : ℕ} {E : Set (Euclidean n)} {f g : Euclidean n → ℝ}
    (h : EqOn (scalarForm f) (scalarForm g) E) : EqOn f g E := by
  intro x hx
  have he := congrArg (fun a => (exteriorBasis n).repr a ∅) (h hx)
  change formCoefficient (scalarForm f) ∅ x = formCoefficient (scalarForm g) ∅ x at he
  simpa only [formCoefficient_scalarForm, ite_true] using he

lemma evaluateForm_scalar {n : ℕ} (v : Fin 0 → Euclidean n) (a : ℝ) :
    evaluateForm 0 v (algebraMap ℝ (CotangentExterior n) a) = a := by
  rw [algebraMap_eq_smul_empty, exteriorBasis_empty]
  have h : evaluateForm 0 v 1 = 1 := by
    simpa only [coordinateWedge_zero] using
      ((evaluateForm_coordinateWedge (Fin.elim0 : Fin 0 → Fin n) v).trans Matrix.det_fin_zero)
  simp [h]

end Rudin.PMA.Chapter10
