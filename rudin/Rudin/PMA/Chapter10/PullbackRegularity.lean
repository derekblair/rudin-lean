import Rudin.PMA.Chapter10.Pullbacks

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

lemma IsCFormOn.congr {n k r : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsCFormOn r E k ω) (he : EqOn η ω E) : IsCFormOn r E k η := by
  refine ⟨fun x hx => by rw [he hx]; exact hω.1 x hx, fun S => ?_⟩
  exact (hω.2 S).congr (fun x hx => congrArg (fun a => (exteriorBasis n).repr a S) (he hx))

lemma IsFormOn.isCFormOn_zero {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) : IsCFormOn 0 E k ω :=
  ⟨hω.1, fun S => contDiffOn_zero.mpr (hω.2 S)⟩

lemma IsCFormOn.wedge {n k l r : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsCFormOn r E k ω) (hη : IsCFormOn r E l η) :
    IsCFormOn r E (k + l) (wedge ω η) := by
  refine ⟨fun x hx => homogeneous_mul_mem (hω.1 x hx) (hη.1 x hx), fun R => ?_⟩
  rw [funext (formCoefficient_wedge ω η R)]
  apply ContDiffOn.sum
  intro S hS
  apply ContDiffOn.sum
  intro T hT
  exact ((hω.2 S).mul (hη.2 T)).mul contDiffOn_const

lemma IsCFormOn.smul_function {n k r : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} {f : Euclidean n → ℝ} (hω : IsCFormOn r E k ω)
    (hf : ContDiffOn ℝ r f E) : IsCFormOn r E k (fun x => f x • ω x) := by
  refine ⟨fun x hx => Submodule.smul_mem _ _ (hω.1 x hx), fun S => ?_⟩
  have he : formCoefficient (fun x => f x • ω x) S = fun x => f x * formCoefficient ω S x := by
    funext x
    simp only [formCoefficient, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact hf.mul (hω.2 S)

lemma isCFormOn_sum {n k r : ℕ} {ι : Type*} [Fintype ι] {E : Set (Euclidean n)}
    {ω : ι → FormField n} (hω : ∀ i, IsCFormOn r E k (ω i)) :
    IsCFormOn r E k (fun x => ∑ i, ω i x) := by
  refine ⟨fun x hx => Submodule.sum_mem _ (fun i _ => (hω i).1 x hx), fun S => ?_⟩
  have he : formCoefficient (fun x => ∑ i, ω i x) S = fun x => ∑ i, formCoefficient (ω i) S x := by
    funext x
    simp only [formCoefficient, map_sum, Finsupp.finsetSum_apply]
  rw [he]
  exact ContDiffOn.sum (fun i _ => (hω i).2 S)

lemma isCFormOn_scalarDifferential {n r : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → ℝ} (hE : IsOpen E) (hf : ContDiffOn ℝ (r + 1) f E) :
    IsCFormOn r E 1 (scalarDifferential f) := by
  simpa only [exteriorDerivative_scalarForm, Nat.zero_add] using
    isCFormOn_exteriorDerivative (r := r) hE (isCFormOn_scalarForm hf)

lemma contDiffOn_map_coordinate {n m r : ℕ} {E : Set (Euclidean n)}
    {T : Euclidean n → Euclidean m} (hT : ContDiffOn ℝ r T E) (i : Fin m) :
    ContDiffOn ℝ r (fun x => T x i) E :=
  (EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).contDiff.comp_contDiffOn hT

lemma covector_ι_eq_sum {n : ℕ} (a : Coord n) :
    ExteriorAlgebra.ι ℝ a = ∑ j, a j • dx j := by
  have he : a = ∑ j, a j • covectorBasis n j := by
    simpa only [covectorBasis, Pi.basisFun_repr] using ((covectorBasis n).sum_repr a).symm
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, dx]

lemma pullback_dx_eq_scalarDifferential {n m : ℕ} {T : Euclidean n → Euclidean m}
    {x : Euclidean n} (hT : DifferentiableAt ℝ T x) (i : Fin m) :
    ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (dx i) =
      scalarDifferential (fun y => T y i) x := by
  rw [dx, ExteriorAlgebra.map_apply_ι, covector_ι_eq_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [covectorPullback_basis]
  have hd : HasFDerivAt (fun y => T y i)
      ((EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).comp (fderiv ℝ T x)) x :=
    (EuclideanSpace.proj i : Euclidean m →L[ℝ] ℝ).hasFDerivAt.comp x hT.hasFDerivAt
  rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv]
  rfl

/-- An ordered product of differentials of coordinate functions of a map. -/
def differentialProduct {n m : ℕ} (T : Euclidean n → Euclidean m)
    (L : List (Fin m)) : FormField n := fun x =>
  (L.map (fun i => scalarDifferential (fun y => T y i) x)).prod

@[simp] lemma differentialProduct_nil {n m : ℕ} (T : Euclidean n → Euclidean m) :
    differentialProduct T [] = scalarForm (fun _ => 1) := by
  funext x
  simp [differentialProduct, scalarForm]

@[simp] lemma differentialProduct_cons {n m : ℕ} (T : Euclidean n → Euclidean m)
    (i : Fin m) (L : List (Fin m)) :
    differentialProduct T (i :: L) =
      wedge (scalarDifferential (fun y => T y i)) (differentialProduct T L) := rfl

lemma isCFormOn_differentialProduct {n m r : ℕ} {E : Set (Euclidean n)}
    {T : Euclidean n → Euclidean m} (hE : IsOpen E) (hT : ContDiffOn ℝ (r + 1) T E)
    (L : List (Fin m)) : IsCFormOn r E L.length (differentialProduct T L) := by
  induction L with
  | nil => simpa only [differentialProduct_nil, List.length_nil] using
      (isCFormOn_scalarForm (contDiffOn_const : ContDiffOn ℝ r (fun _ : Euclidean n => (1 : ℝ)) E))
  | cons i L ih =>
      simpa only [differentialProduct_cons, List.length_cons, Nat.add_comm 1] using
        (isCFormOn_scalarDifferential hE (contDiffOn_map_coordinate hT i)).wedge ih

lemma pullback_standardWedge_eq_product {n m k : ℕ} {T : Euclidean n → Euclidean m}
    {x : Euclidean n} (hT : DifferentiableAt ℝ T x) (S : StandardIndex m k) :
    ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (standardWedge S) =
      differentialProduct T (List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm S)) x := by
  rw [standardWedge_eq_coordinateWedge, pullbackForm_coordinateWedge]
  simp only [differentialProduct, List.map_ofFn]
  congr 1
  apply List.ofFn_inj.mpr
  funext j
  simpa only [dx, ExteriorAlgebra.map_apply_ι, Function.comp_def] using
    pullback_dx_eq_scalarDifferential hT (Set.powersetCard.ofFinEmbEquiv.symm S j)

lemma pullbackForm_standard_expansion {n m k : ℕ} {V : Set (Euclidean m)}
    (T : Euclidean n → Euclidean m) {ω : FormField m} (hω : IsFormOn V k ω)
    {x : Euclidean n} (hx : T x ∈ V) :
    pullbackForm T ω x = ∑ S : StandardIndex m k,
      formCoefficient ω S.val (T x) •
        ExteriorAlgebra.map (covectorPullback (fderiv ℝ T x)) (standardWedge S) := by
  unfold pullbackForm
  rw [standard_expansion_field hω hx]
  simp only [map_sum, map_smul]

lemma pullbackForm_isCFormOn {n m k r : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    {T : Euclidean n → Euclidean m} {ω : FormField m} (hE : IsOpen E)
    (hT : ContDiffOn ℝ (r + 1) T E) (hTV : MapsTo T E V) (hω : IsCFormOn r V k ω) :
    IsCFormOn r E k (pullbackForm T ω) := by
  classical
  have hTr : ContDiffOn ℝ r T E := hT.of_le (by exact_mod_cast Nat.le_succ r)
  have hprod (S : StandardIndex m k) : IsCFormOn r E k
      (differentialProduct T (List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm S))) := by
    simpa only [List.length_ofFn] using
      isCFormOn_differentialProduct hE hT (List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm S))
  have hs := isCFormOn_sum (fun S : StandardIndex m k =>
    (hprod S).smul_function ((hω.2 S.val).comp hTr hTV))
  apply hs.congr
  intro x hx
  rw [pullbackForm_standard_expansion T hω.isFormOn (hTV hx)]
  apply Finset.sum_congr rfl
  intro S hS
  rw [pullback_standardWedge_eq_product
    ((hT.differentiableOn (by exact_mod_cast Nat.succ_ne_zero r)).differentiableAt (hE.mem_nhds hx))]
  rfl

lemma pullbackForm_isFormOn {n m k : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    {T : Euclidean n → Euclidean m} {ω : FormField m} (hE : IsOpen E)
    (hT : ContDiffOn ℝ 1 T E) (hTV : MapsTo T E V) (hω : IsFormOn V k ω) :
    IsFormOn E k (pullbackForm T ω) :=
  (pullbackForm_isCFormOn (r := 0) hE hT hTV hω.isCFormOn_zero).isFormOn

end Rudin.PMA.Chapter10
