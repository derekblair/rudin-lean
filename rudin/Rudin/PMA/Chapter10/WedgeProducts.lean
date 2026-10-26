import Rudin.PMA.Chapter10.StandardForms
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Count the negative differences `J j - I i` in the source sign formula. -/
def crossInversionCount {n p q : ℕ} (I : Fin p → Fin n) (J : Fin q → Fin n) : ℕ :=
  ∑ i, (Finset.univ.filter (fun j => J j < I i)).card

def pma10_16_contract : Prop :=
  (∀ (n p q : ℕ) (I : Fin p → Fin n) (J : Fin q → Fin n),
    coordinateWedge I * coordinateWedge J = coordinateWedge (Fin.append I J)) ∧
  (∀ (n p q : ℕ) (S : StandardIndex n p) (T : StandardIndex n q),
    ¬Disjoint S.val T.val → standardWedge S * standardWedge T = 0) ∧
  (∀ (n p q : ℕ) (S : StandardIndex n p) (T : StandardIndex n q)
      (h : Disjoint S.val T.val),
    standardWedge S * standardWedge T =
      (-1 : ℝ) ^ crossInversionCount (Set.powersetCard.ofFinEmbEquiv.symm S)
        (Set.powersetCard.ofFinEmbEquiv.symm T) • standardWedge (Set.powersetCard.disjUnion h)) ∧
  (∀ (n p q r : ℕ) (S : StandardIndex n p) (T : StandardIndex n q) (U : StandardIndex n r),
    (standardWedge S * standardWedge T) * standardWedge U =
      standardWedge S * (standardWedge T * standardWedge U))

def pma10_17_contract : Prop :=
  (∀ (n p q : ℕ) (E : Set (Euclidean n)) (ω η : FormField n),
    IsFormOn E p ω → IsFormOn E q η → IsFormOn E (p + q) (wedge ω η) ∧
    ∀ x ∈ E, wedge ω η x =
      ∑ S : StandardIndex n p, ∑ T : StandardIndex n q,
        (formCoefficient ω S.val x * formCoefficient η T.val x) • (standardWedge S * standardWedge T)) ∧
  (∀ (n : ℕ) (ω η θ : FormField n), wedge (ω + η) θ = wedge ω θ + wedge η θ ∧
    wedge ω (η + θ) = wedge ω η + wedge ω θ ∧
    wedge (wedge ω η) θ = wedge ω (wedge η θ)) ∧
  (∀ (n : ℕ) (f : Euclidean n → ℝ) (ω : FormField n),
    wedge (scalarForm f) ω = (fun x => f x • ω x) ∧
    wedge ω (scalarForm f) = (fun x => f x • ω x)) ∧
  (∀ (n p q : ℕ) (E : Set (Euclidean n)) (ω η : FormField n),
    IsFormOn E p ω → IsFormOn E q η →
    EqOn (wedge ω η) ((-1 : ℝ)^(p*q) • wedge η ω) E)

lemma homogeneous_mul_mem {k m n : ℕ} {a b : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) (hb : b ∈ (⋀[ℝ]^m (Coord n))) :
    a * b ∈ (⋀[ℝ]^(k + m) (Coord n)) := SetLike.mul_mem_graded ha hb

lemma tupleSign_all_pairs {k : ℕ} (t : Fin k → ℤ) :
    tupleSign t = ∏ i, ∏ j, if i < j then Int.sign (t j - t i) else 1 := by
  simp only [tupleSign, ← Finset.filter_lt_eq_Ioi, Finset.prod_filter]

lemma tupleSign_append {n p q : ℕ} {I : Fin p → Fin n} {J : Fin q → Fin n}
    (hI : StrictMono I) (hJ : StrictMono J) (hne : ∀ i j, I i ≠ J j) :
    tupleSign (fun l => ((Fin.append I J l).val : ℤ)) =
      (-1 : ℤ)^crossInversionCount I J := by
  let t : Fin (p+q) → ℤ := fun l => ((Fin.append I J l).val : ℤ)
  have hleft (i : Fin p) :
      (∏ j, if Fin.castAdd q i < j then Int.sign (t j - t (Fin.castAdd q i)) else 1) =
        ∏ j : Fin q, Int.sign (((J j).val : ℤ) - ((I i).val : ℤ)) := by
    rw [Fin.prod_univ_add]
    have hfirst : (∏ j : Fin p, if Fin.castAdd q i < Fin.castAdd q j then
        Int.sign (t (Fin.castAdd q j) - t (Fin.castAdd q i)) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      by_cases hij : i < j
      · rw [if_pos (by exact hij)]
        simp only [t, Fin.append_left]
        apply Int.sign_eq_one_of_pos
        exact sub_pos.mpr (by exact_mod_cast (show (I i).val < (I j).val from hI hij))
      · rw [if_neg (by exact hij)]
    rw [hfirst, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_pos (by change i.val < p + j.val; omega)]
    simp only [t, Fin.append_left, Fin.append_right]
  have hright (i : Fin q) :
      (∏ j, if Fin.natAdd p i < j then Int.sign (t j - t (Fin.natAdd p i)) else 1) = 1 := by
    rw [Fin.prod_univ_add]
    have hfirst : (∏ j : Fin p, if Fin.natAdd p i < Fin.castAdd q j then
        Int.sign (t (Fin.castAdd q j) - t (Fin.natAdd p i)) else 1) = 1 := by
      apply Finset.prod_eq_one
      intro j hj
      rw [if_neg (by change ¬ (p + i.val < j.val); omega)]
    rw [hfirst, one_mul]
    apply Finset.prod_eq_one
    intro j hj
    by_cases hij : i < j
    · rw [if_pos (by simpa only [Fin.natAdd_lt_natAdd_iff] using hij)]
      simp only [t, Fin.append_right]
      apply Int.sign_eq_one_of_pos
      exact sub_pos.mpr (by exact_mod_cast (show (J i).val < (J j).val from hJ hij))
    · rw [if_neg (by simpa only [Fin.natAdd_lt_natAdd_iff] using hij)]
  rw [tupleSign_all_pairs, Fin.prod_univ_add]
  change (∏ i : Fin p, ∏ j, if Fin.castAdd q i < j then Int.sign (t j - t (Fin.castAdd q i)) else 1) *
    (∏ i : Fin q, ∏ j, if Fin.natAdd p i < j then Int.sign (t j - t (Fin.natAdd p i)) else 1) = _
  simp only [hleft, hright, Finset.prod_const_one, mul_one]
  have hsign (i : Fin p) (j : Fin q) :
      Int.sign (((J j).val : ℤ) - ((I i).val : ℤ)) = if J j < I i then -1 else 1 := by
    by_cases h : J j < I i
    · rw [if_pos h]
      apply Int.sign_eq_neg_one_of_neg
      exact sub_neg.mpr (by exact_mod_cast (show (J j).val < (I i).val from h))
    · rw [if_neg h]
      apply Int.sign_eq_one_of_pos
      have hl : I i < J j := lt_of_le_of_ne (le_of_not_gt h) (hne i j)
      exact sub_pos.mpr (by exact_mod_cast (show (I i).val < (J j).val from hl))
  simp_rw [hsign]
  have hcount (i : Fin p) : (∏ j : Fin q, if J j < I i then (-1 : ℤ) else 1) =
      (-1 : ℤ)^((Finset.univ.filter (fun j => J j < I i)).card) := by
    rw [← Finset.prod_filter]
    simp
  simp_rw [hcount]
  exact Finset.prod_pow_eq_pow_sum _ _ _

lemma standardWedge_mul_of_not_disjoint {n p q : ℕ} (S : StandardIndex n p)
    (T : StandardIndex n q) (h : ¬Disjoint S.val T.val) :
    standardWedge S * standardWedge T = 0 :=
  ExteriorAlgebra.basis_mul_of_not_disjoint (covectorBasis n) S T h

lemma standardWedge_mul_of_disjoint {n p q : ℕ} (S : StandardIndex n p)
    (T : StandardIndex n q) (h : Disjoint S.val T.val) :
    standardWedge S * standardWedge T =
      (-1 : ℝ)^crossInversionCount (Set.powersetCard.ofFinEmbEquiv.symm S)
        (Set.powersetCard.ofFinEmbEquiv.symm T) • standardWedge (Set.powersetCard.disjUnion h) := by
  let I := Set.powersetCard.ofFinEmbEquiv.symm S
  let J := Set.powersetCard.ofFinEmbEquiv.symm T
  have hne : ∀ i j, I i ≠ J j := by
    intro i j heq
    apply Finset.disjoint_left.mp h
    · exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S (I i)).mp ⟨i, rfl⟩
    · rw [heq]
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T (J j)).mp ⟨j, rfl⟩
  have hinj : Injective (Fin.append I J) :=
    Fin.append_injective_iff.mpr ⟨I.injective, J.injective, hne⟩
  obtain ⟨U, hU, hprod⟩ := coordinateWedge_sorted hinj
  have hUeq : U = Set.powersetCard.disjUnion h := by
    apply Subtype.ext
    ext x
    change x ∈ U ↔ x ∈ Set.powersetCard.disjUnion h
    rw [← Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem U, hU]
    change (∃ l, Fin.append I J l = x) ↔ x ∈ Set.powersetCard.disjUnion h
    rw [Set.powersetCard.mem_disjUnion]
    constructor
    · rintro ⟨l, hl⟩
      refine Fin.addCases (fun i hi => ?_) (fun j hj => ?_) l hl
      · left
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S x).mp
          ⟨i, by simpa only [Fin.append_left] using hi⟩
      · right
        exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T x).mp
          ⟨j, by simpa only [Fin.append_right] using hj⟩
    · intro hx
      rcases hx with hx | hx
      · obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S x).mpr hx
        exact ⟨Fin.castAdd q i, by simpa only [Fin.append_left] using hi⟩
      · obtain ⟨j, hj⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem T x).mpr hx
        exact ⟨Fin.natAdd p j, by simpa only [Fin.append_right] using hj⟩
  rw [standardWedge_eq_coordinateWedge, standardWedge_eq_coordinateWedge,
    coordinateWedge_mul, hprod, hUeq, tupleSign_append I.strictMono J.strictMono hne]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one, I, J]

theorem pma10_16 : pma10_16_contract := by
  exact ⟨fun _ _ _ => coordinateWedge_mul, fun _ _ _ => standardWedge_mul_of_not_disjoint,
    fun _ _ _ => standardWedge_mul_of_disjoint, fun _ _ _ _ S T U => mul_assoc _ _ _⟩

lemma coordinateWedge_mul_anticomm {n k m : ℕ} (I : Fin k → Fin n) (J : Fin m → Fin n) :
    coordinateWedge I * coordinateWedge J =
      (-1 : ℝ)^(k*m) • (coordinateWedge J * coordinateWedge I) := by
  have h := ExteriorAlgebra.ιMulti_mul_ιMulti_anticomm ℝ
    (fun i => covectorBasis n (I i)) (fun j => covectorBasis n (J j))
  simpa only [coordinateWedge, Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg,
    Units.val_one, ← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Nat.mul_comm] using h

lemma homogeneous_mul_anticomm {n k m : ℕ} {a b : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) (hb : b ∈ (⋀[ℝ]^m (Coord n))) :
    a * b = (-1 : ℝ)^(k*m) • (b * a) := by
  rw [standard_expansion a ha, standard_expansion b hb]
  simp only [Finset.sum_mul, Finset.mul_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  rw [standardWedge_eq_coordinateWedge, standardWedge_eq_coordinateWedge,
    smul_mul_smul_comm, coordinateWedge_mul_anticomm, smul_mul_smul_comm]
  simp only [smul_smul]
  congr 1
  ring

lemma homogeneous_mul_dx_comm {k n : ℕ} {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) (i : Fin n) :
    a * dx i = (-1 : ℝ)^k • (dx i * a) := by
  have hdx : dx i ∈ (⋀[ℝ]^1 (Coord n)) := by
    change ExteriorAlgebra.ι ℝ (covectorBasis n i) ∈ _
    simpa only [ExteriorAlgebra.exteriorPower, pow_one] using LinearMap.mem_range_self (ExteriorAlgebra.ι ℝ) (covectorBasis n i)
  simpa only [Nat.mul_one] using homogeneous_mul_anticomm ha hdx

lemma formCoefficient_wedge {n : ℕ} (ω η : FormField n) (R : Finset (Fin n))
    (x : Euclidean n) : formCoefficient (wedge ω η) R x =
      ∑ S : Finset (Fin n), ∑ T : Finset (Fin n),
        (formCoefficient ω S x * formCoefficient η T x) *
          (exteriorBasis n).repr (exteriorBasis n S * exteriorBasis n T) R := by
  change (exteriorBasis n).repr (ω x * η x) R = _
  rw [formField_expansion ω x, formField_expansion η x]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, smul_mul_smul_comm,
    map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

lemma IsFormOn.wedge {n p q : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsFormOn E p ω) (hη : IsFormOn E q η) : IsFormOn E (p+q) (wedge ω η) := by
  refine ⟨fun x hx => homogeneous_mul_mem (hω.1 x hx) (hη.1 x hx), ?_⟩
  intro R
  have he := funext (formCoefficient_wedge ω η R)
  rw [he]
  apply continuousOn_finset_sum
  intro S hS
  apply continuousOn_finset_sum
  intro T hT
  exact ((hω.2 S).mul (hη.2 T)).mul continuousOn_const

lemma wedge_standard_expansion {n p q : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (hω : IsFormOn E p ω) (hη : IsFormOn E q η) {x : Euclidean n} (hx : x ∈ E) :
    wedge ω η x = ∑ S : StandardIndex n p, ∑ T : StandardIndex n q,
      (formCoefficient ω S.val x * formCoefficient η T.val x) • (standardWedge S * standardWedge T) := by
  change ω x * η x = _
  rw [standard_expansion_field hω hx, standard_expansion_field hη hx]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
  rw [Finset.sum_comm]

lemma wedge_scalar_left {n : ℕ} (f : Euclidean n → ℝ) (ω : FormField n) :
    wedge (scalarForm f) ω = fun x => f x • ω x := by
  funext x
  exact (Algebra.smul_def (f x) (ω x)).symm

lemma wedge_scalar_right {n : ℕ} (f : Euclidean n → ℝ) (ω : FormField n) :
    wedge ω (scalarForm f) = fun x => f x • ω x := by
  funext x
  change ω x * algebraMap ℝ (CotangentExterior n) (f x) = f x • ω x
  rw [Algebra.smul_def, Algebra.commutes]

theorem pma10_17 : pma10_17_contract := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n p q E ω η hω hη
    exact ⟨hω.wedge hη, fun x hx => wedge_standard_expansion hω hη hx⟩
  · intro n ω η θ
    exact ⟨wedge_add_left ω η θ, wedge_add_right ω η θ, wedge_assoc ω η θ⟩
  · intro n f ω
    exact ⟨wedge_scalar_left f ω, wedge_scalar_right f ω⟩
  · intro n p q E ω η hω hη x hx
    exact homogeneous_mul_anticomm (hω.1 x hx) (hη.1 x hx)

end Rudin.PMA.Chapter10
