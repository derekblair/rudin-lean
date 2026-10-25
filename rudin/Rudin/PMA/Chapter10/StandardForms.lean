import Rudin.PMA.Chapter10.FormOperations
import Rudin.PMA.Chapter09.Determinants

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The unreduced two-form displayed in 10.14, with zero-based indices. -/
def rawTwoForm : FormField 3 := fun x =>
  x 0 • coordinateWedge ![1, 0] - x 1 • coordinateWedge ![2, 1] +
    x 2 • coordinateWedge ![1, 2] + coordinateWedge ![0, 1]

def standardTwoForm : FormField 3 := fun x =>
  (1 - x 0) • coordinateWedge ![0, 1] + (x 1 + x 2) • coordinateWedge ![1, 2]

def pma10_14_contract : Prop :=
  (∀ n k : ℕ, Nat.card (StandardIndex n k) = n.choose k) ∧
  (∀ (n k : ℕ) (I : Fin k → Fin n), StrictMono I → ∀ σ : Equiv.Perm (Fin k),
    tupleSign (fun j => ((I (σ j)).val : ℤ)) = (σ.sign : ℤ)) ∧
  (∀ (n k : ℕ) (I : Fin k → Fin n), Injective I → ∃ S : StandardIndex n k,
    range (Set.powersetCard.ofFinEmbEquiv.symm S) = range I ∧
    coordinateWedge I = (tupleSign (fun j => ((I j).val : ℤ)) : ℝ) • standardWedge S) ∧
  (∀ (n k : ℕ) (I : Fin k → Fin n) (i j : Fin k), i ≠ j → I i = I j →
    coordinateWedge I = 0) ∧
  (∀ (n k : ℕ) (E : Set (Euclidean n)) (ω : FormField n), IsFormOn E k ω →
    (∀ S : StandardIndex n k, ContinuousOn (formCoefficient ω S.val) E) ∧
    ∀ x ∈ E, ω x = ∑ S : StandardIndex n k, formCoefficient ω S.val x • standardWedge S) ∧
  (∀ (n k r : ℕ) (E : Set (Euclidean n)) (ω : FormField n), IsCFormOn r E k ω →
    (∀ S : StandardIndex n k, ContDiffOn ℝ r (formCoefficient ω S.val) E) ∧
    ∀ x ∈ E, ω x = ∑ S : StandardIndex n k, formCoefficient ω S.val x • standardWedge S) ∧
  coordinateWedge (![0, 4, 2, 1] : Fin 4 → Fin 5) =
    -coordinateWedge (![0, 1, 2, 4] : Fin 4 → Fin 5) ∧
  coordinateWedge (![3, 1, 2] : Fin 3 → Fin 4) =
    coordinateWedge (![1, 2, 3] : Fin 3 → Fin 4) ∧
  rawTwoForm = standardTwoForm

/-- The standard expansion uses the actual coefficients of the ambient exterior basis. -/
lemma standard_expansion {n k : ℕ} (a : CotangentExterior n)
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) :
    a = ∑ S : StandardIndex n k, (exteriorBasis n).repr a S.val • standardWedge S := by
  let b := (covectorBasis n).exteriorPower k
  let z : ⋀[ℝ]^k (Coord n) := ⟨a, ha⟩
  have hz : a = ∑ S : StandardIndex n k, b.repr z S • standardWedge S := by
    have h := congrArg Subtype.val (b.sum_repr z)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, standardWedge, exteriorBasis, b, z,
      ← ExteriorAlgebra.basis_eq_coe_basis] using h.symm
  have hc (S : StandardIndex n k) : (exteriorBasis n).repr a S.val = b.repr z S := by
    rw [hz]
    simp [standardWedge, map_sum, map_smul, Basis.repr_self, Finsupp.single_apply,
      ← Subtype.ext_iff]
  simpa only [hc] using hz

lemma standard_index_count (n k : ℕ) : Nat.card (StandardIndex n k) = n.choose k := by
  simpa only [Nat.card_fin] using Set.powersetCard.card (α := Fin n) (n := k)

lemma standard_expansion_field {n k : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) {x : Euclidean n} (hx : x ∈ E) :
    ω x = ∑ S : StandardIndex n k, formCoefficient ω S.val x • standardWedge S :=
  standard_expansion (ω x) (hω.1 x hx)

lemma exteriorBasis_repr_eq_zero_of_degree {n k : ℕ} {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) (S : Finset (Fin n)) (hS : S.card ≠ k) :
    (exteriorBasis n).repr a S = 0 := by
  rw [standard_expansion a ha]
  have hne (T : StandardIndex n k) : T.val ≠ S := by
    intro h
    apply hS
    rw [← h]
    exact T.prop
  simp [standardWedge, map_sum, map_smul, Basis.repr_self, Finsupp.single_apply, hne]

lemma tupleSign_comp {k : ℕ} (t : Fin k → ℤ) (σ : Equiv.Perm (Fin k)) :
    tupleSign (t ∘ σ) = (σ.sign : ℤ) * tupleSign t := by
  have ha : ∀ i j : Fin k, Int.sign (t j - t i) = -Int.sign (t i - t j) := by
    intro i j
    rw [← Int.sign_neg, neg_sub]
  simpa [tupleSign, Function.comp_def] using σ.prod_Ioi_comp_eq_sign_mul_prod ha

lemma tupleSign_increasing {n k : ℕ} {I : Fin k → Fin n} (hI : StrictMono I) :
    tupleSign (fun j => ((I j).val : ℤ)) = 1 := by
  unfold tupleSign
  apply Finset.prod_eq_one
  intro i hi
  apply Finset.prod_eq_one
  intro j hj
  apply Int.sign_eq_one_of_pos
  apply sub_pos.mpr
  change ((I i).val : ℤ) < ((I j).val : ℤ)
  exact_mod_cast (show (I i).val < (I j).val from hI (Finset.mem_Ioi.mp hj))

lemma tupleSign_increasing_perm {n k : ℕ} {I : Fin k → Fin n} (hI : StrictMono I)
    (σ : Equiv.Perm (Fin k)) :
    tupleSign (fun j => ((I (σ j)).val : ℤ)) = (σ.sign : ℤ) := by
  change tupleSign ((fun j => ((I j).val : ℤ)) ∘ σ) = _
  rw [tupleSign_comp, tupleSign_increasing hI, mul_one]

lemma coordinateWedge_sorted {n k : ℕ} {I : Fin k → Fin n} (hI : Injective I) :
    ∃ S : StandardIndex n k,
      range (Set.powersetCard.ofFinEmbEquiv.symm S) = range I ∧
      coordinateWedge I = (tupleSign (fun j => ((I j).val : ℤ)) : ℝ) • standardWedge S := by
  let σ := Tuple.sort I
  have hmono : StrictMono (I ∘ σ) :=
    (Tuple.monotone_sort I).strictMono_of_injective (hI.comp σ.injective)
  let e : Fin k ↪o Fin n := OrderEmbedding.ofStrictMono (I ∘ σ) hmono
  let S : StandardIndex n k := Set.powersetCard.ofFinEmbEquiv e
  have hS : (Set.powersetCard.ofFinEmbEquiv.symm S : Fin k → Fin n) = I ∘ σ := by
    simp [S, e]
  have hsign : tupleSign (fun j => ((I j).val : ℤ)) = (Equiv.Perm.sign σ.symm : ℤ) := by
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using
      tupleSign_increasing_perm hmono σ.symm
  refine ⟨S, ?_, ?_⟩
  · rw [hS]
    exact σ.surjective.range_comp I
  · rw [standardWedge_eq_coordinateWedge, hS, hsign]
    have h := coordinateWedge_perm (I ∘ σ) σ.symm
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id,
      Units.smul_def, Int.cast_smul_eq_zsmul] using h

lemma coordinateWedge_four_reordering :
    coordinateWedge (![0, 4, 2, 1] : Fin 4 → Fin 5) =
      -coordinateWedge (![0, 1, 2, 4] : Fin 4 → Fin 5) := by
  have h := coordinateWedge_swap (![0, 1, 2, 4] : Fin 4 → Fin 5) (i := 1) (j := 3) (by decide)
  convert h using 1
  congr 1
  ext i
  fin_cases i <;> rfl

lemma coordinateWedge_three_reordering :
    coordinateWedge (![3, 1, 2] : Fin 3 → Fin 4) =
      coordinateWedge (![1, 2, 3] : Fin 3 → Fin 4) := by
  have h₁ : coordinateWedge (![3, 1, 2] : Fin 3 → Fin 4) =
      -coordinateWedge (![1, 3, 2] : Fin 3 → Fin 4) := by
    convert coordinateWedge_swap (![1, 3, 2] : Fin 3 → Fin 4) (i := 0) (j := 1) (by decide) using 1
    congr 1
    ext i
    fin_cases i <;> rfl
  have h₂ : coordinateWedge (![1, 3, 2] : Fin 3 → Fin 4) =
      -coordinateWedge (![1, 2, 3] : Fin 3 → Fin 4) := by
    convert coordinateWedge_swap (![1, 2, 3] : Fin 3 → Fin 4) (i := 1) (j := 2) (by decide) using 1
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [h₁, h₂, neg_neg]

lemma coordinateWedge_pair_swap {n : ℕ} (i j : Fin n) :
    coordinateWedge ![i, j] = -coordinateWedge ![j, i] := by
  simpa [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply,
    Matrix.vecTail, Function.comp_def]
    using dx_mul_swap i j

lemma rawTwoForm_standard : rawTwoForm = standardTwoForm := by
  funext x
  simp only [rawTwoForm, standardTwoForm, coordinateWedge_pair_swap (1 : Fin 3) 0,
    coordinateWedge_pair_swap (2 : Fin 3) 1, smul_neg]
  module

theorem pma10_14 : pma10_14_contract := by
  refine ⟨standard_index_count, fun _ _ _ hI => tupleSign_increasing_perm hI,
    fun _ _ _ hI => coordinateWedge_sorted hI, fun _ _ => coordinateWedge_repeat,
    ?_, ?_, coordinateWedge_four_reordering, coordinateWedge_three_reordering,
    rawTwoForm_standard⟩
  · intro n k E ω hω
    exact ⟨fun S => hω.2 S.val, fun x hx => standard_expansion_field hω hx⟩
  · intro n k r E ω hω
    exact ⟨fun S => hω.2 S.val, fun x hx => standard_expansion (ω x) (hω.1 x hx)⟩

end Rudin.PMA.Chapter10
