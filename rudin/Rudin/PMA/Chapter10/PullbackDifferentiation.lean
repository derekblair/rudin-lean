import Rudin.PMA.Chapter10.PullbackRegularity
import Rudin.PMA.Chapter10.ExteriorDerivativeRules

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

lemma exteriorDerivative_congr_of_eqOn {n : ℕ} {E : Set (Euclidean n)}
    {ω η : FormField n} (hE : IsOpen E) (he : EqOn ω η E)
    {x : Euclidean n} (hx : x ∈ E) : exteriorDerivative ω x = exteriorDerivative η x := by
  simp only [exteriorDerivative_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficientDerivative_congr_of_eqOn hE he hx i]

lemma coefficientDerivative_sum {n : ℕ} {ι : Type*} [Fintype ι]
    {ω : ι → FormField n} {x : Euclidean n}
    (hω : ∀ a, CoefficientsDifferentiableAt (ω a) x) (i : Fin n) :
    coefficientDerivative (fun y => ∑ a, ω a y) i x =
      ∑ a, coefficientDerivative (ω a) i x := by
  classical
  have he (S : Finset (Fin n)) : formCoefficient (fun y => ∑ a, ω a y) S =
      fun y => ∑ a, formCoefficient (ω a) S y := by
    funext y
    simp only [formCoefficient, map_sum, Finsupp.finsetSum_apply]
  simp only [coefficientDerivative, he, coordinatePartial_sum (fun a => hω a _), Finset.sum_smul]
  exact Finset.sum_comm

lemma exteriorDerivative_sum {n : ℕ} {ι : Type*} [Fintype ι]
    {ω : ι → FormField n} {x : Euclidean n}
    (hω : ∀ a, CoefficientsDifferentiableAt (ω a) x) :
    exteriorDerivative (fun y => ∑ a, ω a y) x = ∑ a, exteriorDerivative (ω a) x := by
  simp only [exteriorDerivative_eq_sum, coefficientDerivative_sum hω, Finset.mul_sum]
  exact Finset.sum_comm

lemma exteriorDerivative_function_smul {n k : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → ℝ} {ω : FormField n} (hE : IsOpen E)
    (hf : ContDiffOn ℝ 1 f E) (hω : IsCFormOn 1 E k ω)
    {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative (fun y => f y • ω y) x =
      scalarDifferential f x * ω x + f x • exteriorDerivative ω x := by
  rw [← wedge_scalar_left f ω]
  simpa only [exteriorDerivative_scalarForm, pow_zero, one_smul, wedge,
    scalarForm, ← Algebra.smul_def] using
    exteriorDerivative_wedge hE (isCFormOn_scalarForm hf) hω hx

/-- The scalar chain rule, expressed in the native exterior-algebra model. -/
lemma pullback_scalarDifferential {n m : ℕ} {T : Euclidean n → Euclidean m}
    {f : Euclidean m → ℝ} {x : Euclidean n}
    (hT : DifferentiableAt ℝ T x) (hf : DifferentiableAt ℝ f (T x)) :
    pullbackForm T (scalarDifferential f) x = scalarDifferential (f ∘ T) x := by
  classical
  have hchain (j : Fin n) : coordinatePartial (f ∘ T) x j =
      ∑ i : Fin m, coordinatePartial f (T x) i *
        coordinatePartial (fun y => T y i) x j := by
    rw [coordinatePartial_eq_fderiv (hf.comp x hT), fderiv_comp x hf hT]
    change fderiv ℝ f (T x) (fderiv ℝ T x (coordinateVector n j)) = _
    rw [linear_apply_eq_sum_coordinates]
    apply Finset.sum_congr rfl
    intro i hi
    rw [coordinatePartial_eq_fderiv hf]
    have hd : HasFDerivAt (fun y => T y i)
        ((EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).comp (fderiv ℝ T x)) x :=
      (EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).hasFDerivAt.comp x hT.hasFDerivAt
    rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv]
    rfl
  calc
    pullbackForm T (scalarDifferential f) x =
        ∑ i : Fin m, coordinatePartial f (T x) i • scalarDifferential (fun y => T y i) x := by
      simp only [pullbackForm, scalarDifferential, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [pullback_dx_eq_scalarDifferential hT]
      rfl
    _ = ∑ j : Fin n, (∑ i : Fin m, coordinatePartial f (T x) i *
        coordinatePartial (fun y => T y i) x j) • dx j := by
      simp only [scalarDifferential, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    _ = scalarDifferential (f ∘ T) x := by
      simp only [scalarDifferential, hchain]

/-- Every ordered product of exact coordinate differentials is closed. -/
lemma exteriorDerivative_differentialProduct {n m : ℕ} {E : Set (Euclidean n)}
    {T : Euclidean n → Euclidean m} (hE : IsOpen E) (hT : ContDiffOn ℝ 2 T E)
    (L : List (Fin m)) : EqOn (exteriorDerivative (differentialProduct T L)) 0 E := by
  induction L with
  | nil =>
      intro x hx
      simp only [differentialProduct_nil, exteriorDerivative_scalarForm, scalarDifferential,
        coordinatePartial_const, zero_smul, Finset.sum_const_zero, Pi.zero_apply]
  | cons i L ih =>
      intro x hx
      have hi : ContDiffOn ℝ 2 (fun y => T y i) E := contDiffOn_map_coordinate hT i
      have hd : exteriorDerivative (scalarDifferential (fun y => T y i)) x = 0 := by
        rw [← exteriorDerivative_scalarForm]
        exact exteriorDerivative_twice_eq_zero hE (isCFormOn_scalarForm hi) hx
      rw [differentialProduct_cons,
        exteriorDerivative_wedge hE (isCFormOn_scalarDifferential (r := 1) hE hi)
          (isCFormOn_differentialProduct (r := 1) hE hT L) hx]
      simp only [wedge, hd, ih hx, Pi.zero_apply, zero_mul, mul_zero, smul_zero, add_zero]

/-- Exterior differentiation commutes with pullback under exactly C² regularity
of the map and C¹ regularity of the form. -/
lemma exteriorDerivative_pullback {n m k : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    {T : Euclidean n → Euclidean m} {ω : FormField m} (hE : IsOpen E) (hV : IsOpen V)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) (hω : IsCFormOn 1 V k ω) :
    EqOn (exteriorDerivative (pullbackForm T ω)) (pullbackForm T (exteriorDerivative ω)) E := by
  classical
  let L (S : StandardIndex m k) := List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm S)
  let a (S : StandardIndex m k) := formCoefficient ω S.val ∘ T
  let β (S : StandardIndex m k) := differentialProduct T (L S)
  have ha (S : StandardIndex m k) : ContDiffOn ℝ 1 (a S) E :=
    (hω.2 S.val).comp (hT.of_le (by norm_num)) hTV
  have hβ (S : StandardIndex m k) : IsCFormOn 1 E k (β S) := by
    simpa only [β, L, List.length_ofFn] using
      isCFormOn_differentialProduct (r := 1) hE hT (L S)
  have he : EqOn (pullbackForm T ω) (fun y => ∑ S, a S y • β S y) E := by
    intro y hy
    rw [pullbackForm_standard_expansion T hω.isFormOn (hTV hy)]
    apply Finset.sum_congr rfl
    intro S hS
    rw [pullback_standardWedge_eq_product
      ((hT.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds hy))]
    rfl
  intro x hx
  have hTx : DifferentiableAt ℝ T x :=
    (hT.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds hx)
  have hleft : exteriorDerivative (pullbackForm T ω) x =
      ∑ S : StandardIndex m k, scalarDifferential (a S) x * β S x := by
    rw [exteriorDerivative_congr_of_eqOn hE he hx,
      exteriorDerivative_sum (fun S => ((hβ S).smul_function (ha S)).coefficientsDifferentiableAt hE hx)]
    apply Finset.sum_congr rfl
    intro S hS
    rw [exteriorDerivative_function_smul hE (ha S) (hβ S) hx]
    have hd : exteriorDerivative (β S) x = 0 :=
      exteriorDerivative_differentialProduct hE hT (L S) hx
    rw [hd, smul_zero, add_zero]
  have hright : pullbackForm T (exteriorDerivative ω) x =
      ∑ S : StandardIndex m k, scalarDifferential (a S) x * β S x := by
    unfold pullbackForm
    rw [exteriorDerivative_standard_expansion hV hω.isFormOn (hTV hx)]
    simp only [map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro S hS
    have hc := pullback_scalarDifferential hTx
      ((hω.2 S.val).differentiableOn_one.differentiableAt (hV.mem_nhds (hTV hx)))
    change ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x))
      (scalarDifferential (formCoefficient ω S.val) (T x)) = scalarDifferential (a S) x at hc
    rw [hc, pullback_standardWedge_eq_product hTx]
  exact hleft.trans hright.symm

theorem pma10_22 : pma10_22_contract := by
  constructor
  · intro n m T ω η
    exact ⟨pullbackForm_add T ω η, pullbackForm_wedge T ω η⟩
  · intro n m k E V T ω hE hV hT hTV hω
    exact ⟨pullbackForm_isCFormOn (r := 1) hE hT hTV hω,
      exteriorDerivative_pullback hE hV hT hTV hω⟩

end Rudin.PMA.Chapter10
