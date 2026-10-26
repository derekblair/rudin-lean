import Rudin.PMA.Chapter10.FormOperations

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Pull a covector back by a linear map, in the fixed coordinate bases. -/
def covectorPullback {n m : ℕ} (A : Operator n m) : Coord m →ₗ[ℝ] Coord n where
  toFun a j := ∑ i, a i * A (coordinateVector n j) i
  map_add' a b := by ext j; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c a := by ext j; simp [Finset.mul_sum, mul_assoc]

/-- Pullback acts by the exterior-algebra map induced by the actual derivative. -/
def pullbackForm {n m : ℕ} (T : Euclidean n → Euclidean m) (ω : FormField m) :
    FormField n := fun x => ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (ω (T x))

lemma covectorPullback_basis {n m : ℕ} (A : Operator n m) (i : Fin m) (j : Fin n) :
    covectorPullback A (covectorBasis m i) j = A (coordinateVector n j) i := by
  simp [covectorPullback, covectorBasis, Pi.basisFun_apply, Pi.single_apply]

lemma covectorPullback_pairing {n m : ℕ} (A : Operator n m) (a : Coord m) (v : Euclidean n) :
    ∑ j, covectorPullback A a j * v j = ∑ i, a i * A v i := by
  simp only [covectorPullback, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  have h := linear_apply_eq_sum_coordinates ((EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).comp A) v
  change A v i = ∑ j, A (coordinateVector n j) i * v j at h
  rw [h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma covectorPullback_comp {n m p : ℕ} (A : Operator n m) (B : Operator m p) :
    covectorPullback (B.comp A) = (covectorPullback A).comp (covectorPullback B) := by
  apply LinearMap.ext
  intro a
  funext j
  symm
  exact covectorPullback_pairing B a (A (coordinateVector n j))

lemma covectorPullback_id (n : ℕ) :
    covectorPullback (ContinuousLinearMap.id ℝ (Euclidean n)) = LinearMap.id := by
  ext a j
  simp [covectorPullback, coordinateVector, EuclideanSpace.basisFun_apply,
    EuclideanSpace.single_apply]

lemma pullbackForm_add {n m : ℕ} (T : Euclidean n → Euclidean m) (ω η : FormField m) :
    pullbackForm T (ω + η) = pullbackForm T ω + pullbackForm T η := by
  funext x
  exact map_add _ _ _

lemma pullbackForm_wedge {n m : ℕ} (T : Euclidean n → Euclidean m) (ω η : FormField m) :
    pullbackForm T (wedge ω η) = wedge (pullbackForm T ω) (pullbackForm T η) := by
  funext x
  exact map_mul _ _ _

lemma pullbackForm_smul {n m : ℕ} (T : Euclidean n → Euclidean m) (ω : FormField m) (c : ℝ) :
    pullbackForm T (c • ω) = c • pullbackForm T ω := by
  funext x
  change ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (c • ω (T x)) =
    c • ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (ω (T x))
  exact map_smul _ _ _

lemma pullbackForm_scalar {n m : ℕ} (T : Euclidean n → Euclidean m) (f : Euclidean m → ℝ) :
    pullbackForm T (scalarForm f) = scalarForm (f ∘ T) := by
  funext x
  exact AlgHom.commutes _ _

lemma pullbackForm_comp_at {n m p : ℕ} {T : Euclidean n → Euclidean m}
    {S : Euclidean m → Euclidean p} {x : Euclidean n}
    (hT : DifferentiableAt ℝ T x) (hS : DifferentiableAt ℝ S (T x)) (ω : FormField p) :
    pullbackForm (S ∘ T) ω x = pullbackForm T (pullbackForm S ω) x := by
  unfold pullbackForm
  rw [fderiv_comp x hS hT, covectorPullback_comp]
  exact congrArg (fun F : CotangentExterior p →ₐ[ℝ] CotangentExterior n => F (ω (S (T x))))
    (ExteriorAlgebra.map_comp_map (covectorPullback (fderiv ℝ S (T x)))
      (covectorPullback (fderiv ℝ T x))).symm

lemma pullbackForm_coordinateWedge {n m k : ℕ} (T : Euclidean n → Euclidean m)
    (I : Fin k → Fin m) (x : Euclidean n) :
    ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (coordinateWedge I) =
      (List.ofFn fun j => ExteriorAlgebra.ι ℝ
        (covectorPullback (fderiv ℝ T x) (covectorBasis m (I j)))).prod := by
  rw [coordinateWedge, ExteriorAlgebra.map_apply_ιMulti]
  rfl

end Rudin.PMA.Chapter10
