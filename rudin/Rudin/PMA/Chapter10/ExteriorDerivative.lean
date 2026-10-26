import Rudin.PMA.Chapter10.FormSeparation
import Rudin.PMA.Chapter10.FormExamples
import Rudin.PMA.Chapter10.CoordinateDifferentiation
import Rudin.PMA.Chapter10.WedgeProducts

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Exterior differentiation in the fixed coordinate basis. Coefficient
differentials are multiplied on the left, as in the source convention. -/
def exteriorDerivative {n : ℕ} (ω : FormField n) : FormField n := fun x =>
  ∑ i : Fin n, ∑ S : Finset (Fin n),
    coordinatePartial (formCoefficient ω S) x i • (dx i * exteriorBasis n S)

/-- Differential of a scalar function, viewed as a one-form. -/
def scalarDifferential {n : ℕ} (f : Euclidean n → ℝ) : FormField n := fun x =>
  ∑ i : Fin n, coordinatePartial f x i • dx i

/-- The coefficientwise directional derivative, before wedging with a coordinate differential. -/
def coefficientDerivative {n : ℕ} (ω : FormField n) (i : Fin n) : FormField n := fun x =>
  ∑ S : Finset (Fin n), coordinatePartial (formCoefficient ω S) x i • exteriorBasis n S

def pma10_18_contract : Prop :=
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsCFormOn 1 E k ω → IsFormOn E (k + 1) (exteriorDerivative ω) ∧
      ∀ x ∈ E, exteriorDerivative ω x =
        ∑ S : StandardIndex n k, scalarDifferential (formCoefficient ω S.val) x * standardWedge S) ∧
  (∀ (n : ℕ) (f : Euclidean n → ℝ), exteriorDerivative (scalarForm f) = scalarDifferential f) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ),
    IsOpen E → ContDiffOn ℝ 1 f E → ∀ x ∈ E, ∀ v : Fin 1 → Euclidean n,
      evaluateForm 1 v (scalarDifferential f x) = fderiv ℝ f x (v 0))

def pma10_19_contract : Prop :=
  (∀ (n : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ),
    IsOpen E → ContDiffOn ℝ 1 f E → ∀ Φ : Surface 1 n E,
      Φ.domain.Integrable (surfaceIntegrand Φ (scalarDifferential f)) ∧
      surfaceIntegral Φ (scalarDifferential f) =
        f (Φ.map (fun _ => Φ.domain.interval.2)) - f (Φ.map (fun _ => Φ.domain.interval.1))) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ),
    IsOpen E → ContDiffOn ℝ 1 f E → ∀ Φ Ψ : Surface 1 n E,
      Φ.map (fun _ => Φ.domain.interval.1) = Ψ.map (fun _ => Ψ.domain.interval.1) →
      Φ.map (fun _ => Φ.domain.interval.2) = Ψ.map (fun _ => Ψ.domain.interval.2) →
      surfaceIntegral Φ (scalarDifferential f) = surfaceIntegral Ψ (scalarDifferential f)) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (f : Euclidean n → ℝ),
    IsOpen E → ContDiffOn ℝ 1 f E → ∀ Φ : Surface 1 n E,
      Φ.map (fun _ => Φ.domain.interval.1) = Φ.map (fun _ => Φ.domain.interval.2) →
      surfaceIntegral Φ (scalarDifferential f) = 0) ∧
  (¬ ∃ f : Euclidean 2 → ℝ, ContDiff ℝ 1 f ∧
    EqOn (scalarDifferential f) (coordinateOneForm 0 1) univ)

def pma10_20_contract : Prop :=
  (∀ (n k m : ℕ) (E : Set (Euclidean n)) (ω η : FormField n),
    IsOpen E → IsCFormOn 1 E k ω → IsCFormOn 1 E m η →
      EqOn (exteriorDerivative (wedge ω η))
        (wedge (exteriorDerivative ω) η + ((-1 : ℝ) ^ k) • wedge ω (exteriorDerivative η)) E) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsCFormOn 2 E k ω → IsCFormOn 1 E (k + 1) (exteriorDerivative ω) ∧
      EqOn (exteriorDerivative (exteriorDerivative ω)) 0 E)

@[simp] theorem formCoefficient_coefficientDerivative {n : ℕ} (ω : FormField n) (i : Fin n)
    (S : Finset (Fin n)) (x : Euclidean n) :
    formCoefficient (coefficientDerivative ω i) S x = coordinatePartial (formCoefficient ω S) x i := by
  classical
  simp [formCoefficient, coefficientDerivative, map_sum, map_smul, Basis.repr_self,
    Finsupp.single_apply, eq_comm]

theorem exteriorDerivative_eq_sum {n : ℕ} (ω : FormField n) (x : Euclidean n) :
    exteriorDerivative ω x = ∑ i, dx i * coefficientDerivative ω i x := by
  simp only [exteriorDerivative, coefficientDerivative, Finset.mul_sum, mul_smul_comm]

theorem coefficientDerivative_congr_of_eqOn {n : ℕ} {E : Set (Euclidean n)}
    {ω η : FormField n} (hE : IsOpen E) (he : EqOn ω η E)
    {x : Euclidean n} (hx : x ∈ E) (i : Fin n) :
    coefficientDerivative ω i x = coefficientDerivative η i x := by
  apply Finset.sum_congr rfl
  intro S hS
  have hc : EqOn (formCoefficient ω S) (formCoefficient η S) E := fun y hy =>
    congrArg (fun a => (exteriorBasis n).repr a S) (he hy)
  rw [coordinatePartial_congr_of_eqOn hE hc hx i]

/-- Differentiation of a finite linear combination in the fixed exterior basis. -/
theorem coefficientDerivative_sum_smul {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Euclidean n → ℝ) (v : ι → CotangentExterior n) {x : Euclidean n}
    (ha : ∀ j, DifferentiableAt ℝ (a j) x) (i : Fin n) :
    coefficientDerivative (fun y => ∑ j, a j y • v j) i x =
      ∑ j, coordinatePartial (a j) x i • v j := by
  classical
  have he (S : Finset (Fin n)) : formCoefficient (fun y => ∑ j, a j y • v j) S =
      fun y => ∑ j, a j y * (exteriorBasis n).repr (v j) S := by
    funext y
    simp only [formCoefficient, map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  simp only [coefficientDerivative, he]
  simp_rw [coordinatePartial_sum (fun j => (ha j).mul_const _),
    coordinatePartial_mul_const (ha _) _, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.smul_sum, (exteriorBasis n).sum_repr]

theorem coefficientDerivative_mem {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsFormOn E k ω) {x : Euclidean n} (hx : x ∈ E) (i : Fin n) :
    coefficientDerivative ω i x ∈ (⋀[ℝ]^k (Coord n)) := by
  classical
  apply Submodule.sum_mem
  intro S hS
  by_cases hcard : S.card = k
  · have hs : exteriorBasis n S ∈ (⋀[ℝ]^k (Coord n)) :=
      standardWedge_mem (⟨S, hcard⟩ : StandardIndex n k)
    exact Submodule.smul_mem _ _ hs
  · have hz : EqOn (formCoefficient ω S) (fun _ => 0) E := fun y hy =>
      exteriorBasis_repr_eq_zero_of_degree (hω.1 y hy) S hcard
    rw [coordinatePartial_congr_of_eqOn hE hz hx i, coordinatePartial_const, zero_smul]
    exact Submodule.zero_mem _

theorem exteriorDerivative_mem {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsFormOn E k ω) {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative ω x ∈ (⋀[ℝ]^(k + 1) (Coord n)) := by
  rw [exteriorDerivative_eq_sum]
  apply Submodule.sum_mem
  intro i hi
  have hdx : dx i ∈ (⋀[ℝ]^1 (Coord n)) := by
    rw [dx_eq_coordinateWedge]
    exact coordinateWedge_mem _
  simpa only [Nat.add_comm 1 k] using homogeneous_mul_mem hdx (coefficientDerivative_mem hE hω hx i)

theorem formCoefficient_exteriorDerivative {n : ℕ} (ω : FormField n)
    (T : Finset (Fin n)) (x : Euclidean n) :
    formCoefficient (exteriorDerivative ω) T x =
      ∑ i : Fin n, ∑ S : Finset (Fin n), coordinatePartial (formCoefficient ω S) x i *
        (exteriorBasis n).repr (dx i * exteriorBasis n S) T := by
  simp only [formCoefficient, exteriorDerivative, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem isCFormOn_exteriorDerivative {n k r : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsCFormOn (r + 1) E k ω) :
    IsCFormOn r E (k + 1) (exteriorDerivative ω) := by
  refine ⟨fun x hx => exteriorDerivative_mem hE hω.isFormOn hx, fun T => ?_⟩
  simp only [funext (formCoefficient_exteriorDerivative ω T)]
  apply ContDiffOn.sum
  intro i hi
  apply ContDiffOn.sum
  intro S hS
  exact (contDiffOn_coordinatePartial hE (hω.2 S) i).mul contDiffOn_const

theorem exteriorDerivative_standard_expansion {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsFormOn E k ω) {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative ω x =
      ∑ S : StandardIndex n k, scalarDifferential (formCoefficient ω S.val) x * standardWedge S := by
  classical
  rw [exteriorDerivative_eq_sum]
  have hi (i : Fin n) : coefficientDerivative ω i x =
      ∑ S : StandardIndex n k, coordinatePartial (formCoefficient ω S.val) x i • standardWedge S := by
    have h := standard_expansion (coefficientDerivative ω i x) (coefficientDerivative_mem hE hω hx i)
    change coefficientDerivative ω i x = ∑ S : StandardIndex n k,
      formCoefficient (coefficientDerivative ω i) S.val x • standardWedge S at h
    simpa only [formCoefficient_coefficientDerivative] using h
  simp only [hi, Finset.mul_sum, mul_smul_comm, scalarDifferential, Finset.sum_mul, smul_mul_assoc]
  exact Finset.sum_comm

theorem exteriorDerivative_scalarForm {n : ℕ} (f : Euclidean n → ℝ) :
    exteriorDerivative (scalarForm f) = scalarDifferential f := by
  classical
  funext x
  unfold exteriorDerivative scalarDifferential
  apply Finset.sum_congr rfl
  intro i hi
  have he (S : Finset (Fin n)) : formCoefficient (scalarForm f) S =
      if S = ∅ then f else fun _ => 0 := by
    funext y
    simp only [formCoefficient_scalarForm]
    split_ifs <;> rfl
  simp only [he]
  have hd (S : Finset (Fin n)) : coordinatePartial (if S = ∅ then f else fun _ => 0) x i =
      if S = ∅ then coordinatePartial f x i else 0 := by
    split_ifs <;> simp only [coordinatePartial_const]
  simp [hd, exteriorBasis_empty]

theorem evaluateForm_scalarDifferential {n : ℕ} {f : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (v : Fin 1 → Euclidean n) :
    evaluateForm 1 v (scalarDifferential f x) = fderiv ℝ f x (v 0) := by
  simp only [scalarDifferential, map_sum, map_smul, smul_eq_mul, evaluateForm_dx]
  rw [linear_apply_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coordinatePartial_eq_fderiv hf]

theorem pma10_18 : pma10_18_contract := by
  refine ⟨?_, fun _ _ => exteriorDerivative_scalarForm _, ?_⟩
  · intro n k E ω hE hω
    exact ⟨(isCFormOn_exteriorDerivative (r := 0) hE hω).isFormOn,
      fun x hx => exteriorDerivative_standard_expansion hE hω.isFormOn hx⟩
  · intro n E f hE hf x hx v
    exact evaluateForm_scalarDifferential
      (hf.differentiableOn_one.differentiableAt (hE.mem_nhds hx)) v

end Rudin.PMA.Chapter10
