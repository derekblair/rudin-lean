import Rudin.PMA.Chapter10.ExteriorDerivative

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma exteriorBasis_singleton {n : ℕ} (i : Fin n) : exteriorBasis n {i} = dx i := by
  let S : StandardIndex n 1 := ⟨{i}, Finset.card_singleton i⟩
  have hI : (Set.powersetCard.ofFinEmbEquiv.symm S : Fin 1 → Fin n) = fun _ => i := by
    funext j
    have hm := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S
      (Set.powersetCard.ofFinEmbEquiv.symm S j)).mp ⟨j, rfl⟩
    exact Finset.mem_singleton.mp hm
  change standardWedge S = dx i
  rw [standardWedge_eq_coordinateWedge, hI, ← dx_eq_coordinateWedge]

lemma one_form_expansion {n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E 1 ω) {x : Euclidean n} (hx : x ∈ E) :
    ω x = ∑ i : Fin n, formCoefficient ω {i} x • dx i := by
  classical
  apply (exteriorBasis n).repr.injective
  ext S
  by_cases hS : S.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hS
    simp [← exteriorBasis_singleton, map_sum, map_smul, Basis.repr_self,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, formCoefficient, eq_comm]
  · have hn (i : Fin n) : ({i} : Finset (Fin n)) ≠ S := by
      intro he
      exact hS (he ▸ Finset.card_singleton i)
    rw [exteriorBasis_repr_eq_zero_of_degree (hω.1 x hx) S hS]
    simp [← exteriorBasis_singleton, map_sum, map_smul, Basis.repr_self,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, hn]

lemma formCoefficient_scalarDifferential_singleton {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i : Fin n) :
    formCoefficient (scalarDifferential f) {i} x = coordinatePartial f x i := by
  classical
  simp [formCoefficient, scalarDifferential, ← exteriorBasis_singleton,
    map_sum, map_smul, Basis.repr_self, Finsupp.single_apply, eq_comm]

lemma exteriorDerivative_one_form {n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsCFormOn 1 E 1 ω) {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative ω x = ∑ i : Fin n, ∑ j : Fin n,
      coordinatePartial (formCoefficient ω {j}) x i • (dx i * dx j) := by
  have he : EqOn ω (fun y => ∑ j : Fin n, formCoefficient ω {j} y • dx j) E :=
    fun y hy => one_form_expansion hω.isFormOn hy
  rw [exteriorDerivative_eq_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coefficientDerivative_congr_of_eqOn hE he hx i,
    coefficientDerivative_sum_smul (fun j => formCoefficient ω {j}) (fun j => dx j)
      (fun j => (hω.2 {j}).differentiableOn_one.differentiableAt (hE.mem_nhds hx)) i]
  simp only [Finset.mul_sum, mul_smul_comm]

lemma evaluateForm_two_dx_mul_dx {n : ℕ} (v : Fin 2 → Euclidean n) (i j : Fin n) :
    evaluateForm 2 v (dx i * dx j) = v 0 i * v 1 j - v 1 i * v 0 j := by
  rw [dx_eq_coordinateWedge, dx_eq_coordinateWedge, coordinateWedge_mul,
    evaluateForm_coordinateWedge]
  let M : Matrix (Fin 2) (Fin 2) ℝ :=
    fun a b => v b (Fin.append (fun _ : Fin 1 => i) (fun _ : Fin 1 => j) a)
  change Matrix.det M = _
  rw [Matrix.det_fin_two]
  rfl

lemma evaluateForm_two_exteriorDerivative {n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hE : IsOpen E) (hω : IsCFormOn 1 E 1 ω) {x : Euclidean n} (hx : x ∈ E)
    (i j : Fin n) :
    evaluateForm 2 ![coordinateVector n i, coordinateVector n j] (exteriorDerivative ω x) =
      coordinatePartial (formCoefficient ω {j}) x i -
        coordinatePartial (formCoefficient ω {i}) x j := by
  classical
  rw [exteriorDerivative_one_form hE hω hx]
  simp only [map_sum, map_smul, smul_eq_mul, evaluateForm_two_dx_mul_dx]
  simp [coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply,
    Finset.sum_sub_distrib, mul_sub, eq_comm]

lemma exteriorDerivative_one_form_eq_zero_iff {n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsCFormOn 1 E 1 ω) {x : Euclidean n} (hx : x ∈ E) :
    exteriorDerivative ω x = 0 ↔ ∀ i j : Fin n,
      coordinatePartial (formCoefficient ω {j}) x i =
        coordinatePartial (formCoefficient ω {i}) x j := by
  classical
  constructor
  · intro hz i j
    have he := evaluateForm_two_exteriorDerivative hE hω hx i j
    rw [hz, map_zero] at he
    exact sub_eq_zero.mp he.symm
  · intro hs
    rw [exteriorDerivative_one_form hE hω hx, ← Finset.sum_product', Finset.univ_product_univ]
    apply Finset.sum_ninvolution (Prod.swap : Fin n × Fin n → Fin n × Fin n)
    · rintro ⟨i, j⟩
      dsimp only [Prod.swap]
      rw [hs j i, dx_mul_swap j i, smul_neg]
      exact add_neg_cancel _
    · rintro ⟨i, j⟩ hn he
      have hij : j = i := congrArg Prod.fst he
      subst j
      exact hn (by simp only [dx_mul_dx, smul_zero])
    · intro p
      exact Finset.mem_univ _
    · intro p
      exact Prod.swap_swap p

end Rudin.PMA.Chapter10
