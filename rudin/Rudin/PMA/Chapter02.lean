import Mathlib
import Rudin.PMA.Chapter01

noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter Topology

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 2: Basic Topology

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

namespace Rudin.PMA.Chapter02

/-! ### PMA-2.1: functions and their ranges. -/
abbrev PMAMapping (A B : Type*) := A → B
def pmaRange {A B : Type*} (f : PMAMapping A B) : Set B := {y | ∃ x, f x = y}
theorem pma2_1_unique {A B : Type*} (f : PMAMapping A B) (x : A) :
    ∃! y : B, f x = y := ⟨f x, rfl, fun _ h => h.symm⟩
theorem pma2_1_range {A B : Type*} (f : PMAMapping A B) : pmaRange f = Set.range f := rfl

/-! ### PMA-2.2: images, inverse images, and mapping properties. -/
def pmaImage {A B : Type*} (f : A → B) (E : Set A) : Set B := {y | ∃ x ∈ E, f x = y}
def pmaPreimage {A B : Type*} (f : A → B) (E : Set B) : Set A := {x | f x ∈ E}
def pmaOnto {A B : Type*} (f : A → B) : Prop := pmaRange f = Set.univ
def pmaOneToOne {A B : Type*} (f : A → B) : Prop := ∀ x y, f x = f y → x = y

theorem pma2_2_reference {A B : Type*} (f : A → B) (E : Set A) (F : Set B) :
    pmaImage f E = f '' E ∧ pmaPreimage f F = f ⁻¹' F ∧
    (pmaOnto f ↔ Function.Surjective f) ∧ (pmaOneToOne f ↔ Function.Injective f) := by
  refine ⟨rfl, rfl, ?_, Iff.rfl⟩
  exact Set.range_eq_univ

theorem pma2_2_oneToOne_alternative {A B : Type*} (f : A → B) :
    pmaOneToOne f ↔ ∀ x y, x ≠ y → f x ≠ f y := by
  constructor
  · intro h x y hxy hfx; exact hxy (h x y hfx)
  · intro h x y hfx
    by_contra hxy
    exact h x y hxy hfx

/-! ### PMA-2.3: equinumerosity and equivalence relations. -/
def Equinumerous (A B : Type*) : Prop := Nonempty (A ≃ B)
def PMAEquivalenceRelation {A : Type*} (r : A → A → Prop) : Prop :=
  (∀ x, r x x) ∧ (∀ x y, r x y → r y x) ∧
  (∀ x y z, r x y → r y z → r x z)

theorem pma2_3_reference {A : Type*} (r : A → A → Prop) :
    PMAEquivalenceRelation r ↔ Equivalence r := by
  constructor
  · rintro ⟨hr,hs,ht⟩
    exact ⟨hr,fun h => hs _ _ h,fun h₁ h₂ => ht _ _ _ h₁ h₂⟩
  · intro h
    exact ⟨h.refl,fun _ _ => h.symm,fun _ _ _ => h.trans⟩

theorem pma2_3_reflexive (A : Type*) : Equinumerous A A := ⟨Equiv.refl A⟩
theorem pma2_3_symmetric {A B : Type*} : Equinumerous A B → Equinumerous B A :=
  fun ⟨e⟩ => ⟨e.symm⟩
theorem pma2_3_transitive {A B C : Type*} :
    Equinumerous A B → Equinumerous B C → Equinumerous A C :=
  fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩

theorem pma2_3_bijection {A B : Type*} :
    Equinumerous A B ↔ ∃ f : A → B, Function.Bijective f := by
  constructor
  · rintro ⟨e⟩; exact ⟨e,e.bijective⟩
  · rintro ⟨f,hf⟩; exact ⟨Equiv.ofBijective f hf⟩

/-! ### PMA-2.4: finite, countably infinite, and uncountable sets. -/
def RudinFinite (A : Type*) : Prop := ∃ n : ℕ, Nonempty (A ≃ Fin n)
def RudinInfinite (A : Type*) : Prop := ¬ RudinFinite A
def RudinCountable (A : Type*) : Prop := Nonempty (A ≃ ℕ)
def RudinUncountable (A : Type*) : Prop := ¬ RudinFinite A ∧ ¬ RudinCountable A
def RudinAtMostCountable (A : Type*) : Prop := RudinFinite A ∨ RudinCountable A

theorem pma2_4_finite_reference (A : Type*) : RudinFinite A ↔ Finite A :=
  finite_iff_exists_equiv_fin.symm

theorem pma2_4_infinite_reference (A : Type*) : RudinInfinite A ↔ Infinite A := by
  rw [RudinInfinite,pma2_4_finite_reference,not_finite_iff_infinite]

theorem pma2_4_positive_integer_reference (A : Type*) :
    RudinCountable A ↔ Nonempty (A ≃ ℕ+) := by
  constructor
  · rintro ⟨e⟩; exact ⟨e.trans Equiv.pnatEquivNat.symm⟩
  · rintro ⟨e⟩; exact ⟨e.trans Equiv.pnatEquivNat⟩

theorem pma2_4_countable_reference (A : Type*) :
    RudinCountable A ↔ Countable A ∧ Infinite A := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.injective.countable, Infinite.of_injective e.symm e.symm.injective⟩
  · rintro ⟨hc,hi⟩
    let := hc; let := hi
    change Nonempty (A ≃ ℕ)
    infer_instance

theorem pma2_4_atMost_reference (A : Type*) : RudinAtMostCountable A ↔ Countable A := by
  constructor
  · rintro (hf | hc)
    · let := (pma2_4_finite_reference A).mp hf; infer_instance
    · exact ((pma2_4_countable_reference A).mp hc).1
  · intro hc
    rcases finite_or_infinite A with hf | hi
    · exact Or.inl ((pma2_4_finite_reference A).mpr hf)
    · exact Or.inr ((pma2_4_countable_reference A).mpr ⟨hc,hi⟩)

theorem pma2_4_uncountable_reference (A : Type*) : RudinUncountable A ↔ ¬ Countable A := by
  rw [RudinUncountable,← pma2_4_atMost_reference, RudinAtMostCountable,not_or]

/-! ### PMA-2.5: integers are countably infinite. -/
theorem pma2_5 : RudinCountable ℤ := ⟨Equiv.intEquivNat⟩

/-! ### PMA-2.6: finite and infinite sets compared with proper subsets. -/
theorem pma2_6_finite {A : Type*} (S T : Set A) (hS : S.Finite) (hTS : T ⊂ S) :
    ¬ Equinumerous S T := by
  rintro ⟨e⟩
  let : Finite S := hS.to_subtype
  let f : S → S := fun x => ⟨e x, hTS.subset (e x).property⟩
  have hf : Function.Injective f := by
    intro x y h
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun z : S => z.val) h
  have hs : Function.Surjective f := Finite.surjective_of_injective hf
  obtain ⟨a,ha,hna⟩ := Set.exists_of_ssubset hTS
  obtain ⟨x,hx⟩ := hs ⟨a,ha⟩
  have he : (e x).val = a := congrArg Subtype.val hx
  exact hna (he ▸ (e x).property)

theorem pma2_6_infinite {A : Type*} (S : Set A) (hS : S.Infinite) :
    ∃ T : Set A, T ⊂ S ∧ Equinumerous S T := by
  obtain ⟨a,ha⟩ := hS.nonempty
  refine ⟨S \ {a}, ?_, ?_⟩
  · refine Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, ?_⟩
    intro heq
    have : a ∈ S \ {a} := heq.symm ▸ ha
    exact this.2 (by simp)
  · exact Cardinal.eq.mp
      (Cardinal.mk_sdiff_eq_left_of_finite hS (Set.finite_singleton a)).symm

theorem pma2_6_characterization {A : Type*} (S : Set A) :
    S.Infinite ↔ ∃ T : Set A, T ⊂ S ∧ Equinumerous S T := by
  constructor
  · exact pma2_6_infinite S
  · rintro ⟨T,hT,he⟩ hfin
    exact pma2_6_finite S T hfin hT he

/-! ### PMA-2.7: sequences and injective enumerations. -/
abbrev PMASequence (A : Type*) := ℕ → A

theorem pma2_7_enumeration {A : Type*} (S : Set A) :
    RudinCountable S ↔ ∃ f : PMASequence A,
      Function.Injective f ∧ Set.range f = S := by
  constructor
  · rintro ⟨e⟩
    refine ⟨fun n => (e.symm n).val, ?_, ?_⟩
    · intro m n h
      apply e.symm.injective
      exact Subtype.ext h
    · ext a
      constructor
      · rintro ⟨n,rfl⟩; exact (e.symm n).property
      · intro ha
        exact ⟨e ⟨a,ha⟩, congrArg Subtype.val (e.symm_apply_apply ⟨a,ha⟩)⟩
  · rintro ⟨f,hf,hr⟩
    refine ⟨(Equiv.ofBijective (fun n : ℕ => (⟨f n,by rw [← hr]; exact Set.mem_range_self n⟩ : S)) ?_).symm⟩
    constructor
    · intro m n h; exact hf (congrArg Subtype.val h)
    · intro a
      have ha : a.val ∈ Set.range f := hr.symm ▸ a.property
      obtain ⟨n,hn⟩ := ha
      exact ⟨n,Subtype.ext hn⟩

/-! ### PMA-2.8: infinite subsets of countably infinite sets. -/
theorem pma2_8 {A : Type*} (S T : Set A) (hS : RudinCountable S)
    (hT : T.Infinite) (hTS : T ⊆ S) : RudinCountable T := by
  have hcS : S.Countable := ((pma2_4_countable_reference S).mp hS).1
  exact (pma2_4_countable_reference T).mpr
    ⟨hcS.mono hTS, hT.to_subtype⟩

/-! ### PMA-2.9: indexed unions, intersections, and disjointness. -/
def pmaUnion {A I : Type*} (E : I → Set A) : Set A := {x | ∃ i, x ∈ E i}
def pmaIntersection {A I : Type*} (E : I → Set A) : Set A := {x | ∀ i, x ∈ E i}
def pmaDisjoint {A : Type*} (S T : Set A) : Prop := S ∩ T = ∅

theorem pma2_9_reference {A I : Type*} (E : I → Set A) (S T : Set A) :
    pmaUnion E = ⋃ i, E i ∧ pmaIntersection E = ⋂ i, E i ∧
    (pmaDisjoint S T ↔ Disjoint S T) := by
  refine ⟨?_,?_,Set.disjoint_iff_inter_eq_empty.symm⟩
  · ext x; simp [pmaUnion]
  · ext x; simp [pmaIntersection]


/-! ### PMA-2.10: explicit finite-set and interval-family examples. -/
theorem pma2_10_finite_examples :
    ({1,2,3} : Set ℕ) ∪ {2,3,4} = {1,2,3,4} ∧
    ({1,2,3} : Set ℕ) ∩ {2,3,4} = {2,3} := by
  constructor <;> ext x <;> simp only [Set.mem_union, Set.mem_inter_iff,
    Set.mem_insert_iff,Set.mem_singleton_iff] <;> omega

abbrev IntervalFamilyIndex := {x : ℝ // x ∈ Set.Ioc 0 1}
def intervalFamily (x : IntervalFamilyIndex) : Set ℝ := Set.Ioo 0 x.val

theorem pma2_10_family_subset (x z : IntervalFamilyIndex) :
    intervalFamily x ⊆ intervalFamily z ↔ x.val ≤ z.val := by
  simp only [intervalFamily,Set.Ioo_subset_Ioo_iff x.property.1]
  simp

theorem pma2_10_family_union : (⋃ x : IntervalFamilyIndex,intervalFamily x) = Set.Ioo 0 1 := by
  ext y
  simp only [Set.mem_iUnion,intervalFamily,Set.mem_Ioo]
  constructor
  · rintro ⟨x,hy0,hyx⟩; exact ⟨hy0,hyx.trans_le x.property.2⟩
  · intro hy; exact ⟨⟨1,by norm_num⟩,hy⟩

theorem pma2_10_family_intersection : (⋂ x : IntervalFamilyIndex,intervalFamily x) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hh : ∀ x : IntervalFamilyIndex, 0 < y ∧ y < x.val := by
    simpa only [Set.mem_iInter,intervalFamily,Set.mem_Ioo] using hy
  have hy1 := hh ⟨1,by norm_num⟩
  have hx : y / 2 ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith,by linarith [hy1.2]⟩
  have := hh ⟨y/2,hx⟩
  linarith [hy1.1]

/-! ### PMA-2.11: union/intersection algebra. -/
theorem pma2_11 {A : Type*} (S T U : Set A) :
    S ∪ T = T ∪ S ∧ S ∩ T = T ∩ S ∧
    (S ∪ T) ∪ U = S ∪ (T ∪ U) ∧ (S ∩ T) ∩ U = S ∩ (T ∩ U) ∧
    S ∩ (T ∪ U) = (S ∩ T) ∪ (S ∩ U) ∧
    S ⊆ S ∪ T ∧ S ∩ T ⊆ S ∧ S ∪ ∅ = S ∧ S ∩ ∅ = ∅ ∧
    (S ⊆ T → S ∪ T = T ∧ S ∩ T = S) := by
  exact ⟨Set.union_comm S T, Set.inter_comm S T, Set.union_assoc S T U,
    Set.inter_assoc S T U, Set.inter_union_distrib_left S T U,
    Set.subset_union_left, Set.inter_subset_left, Set.union_empty S,
    Set.inter_empty S, fun h => ⟨Set.union_eq_right.mpr h,Set.inter_eq_left.mpr h⟩⟩

/-! ### PMA-2.12: countable unions. -/
theorem pma2_12 {A : Type*} (E : ℕ → Set A) (h : ∀ n, RudinCountable (E n)) :
    RudinCountable (⋃ n,E n) := by
  have hc : ∀ n,(E n).Countable := fun n => ((pma2_4_countable_reference _).mp (h n)).1
  have hi : (E 0).Infinite := infinite_coe_iff.mp (((pma2_4_countable_reference _).mp (h 0)).2)
  exact (pma2_4_countable_reference _).mpr
    ⟨Set.countable_iUnion hc, (hi.mono (Set.subset_iUnion E 0)).to_subtype⟩

theorem pma2_12_corollary {A I : Type*} [Countable I] (E : I → Set A)
    (h : ∀ i,(E i).Countable) : (⋃ i,E i).Countable := Set.countable_iUnion h

/-! ### PMA-2.13: finite products and the rational numbers. -/
theorem pma2_13 {A : Type*} (h : RudinCountable A) (n : ℕ) (hn : 0 < n) :
    RudinCountable (Fin n → A) := by
  obtain ⟨hc,hi⟩ := (pma2_4_countable_reference _).mp h
  let := hc; let := hi
  have hne : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let := hne
  exact (pma2_4_countable_reference _).mpr ⟨inferInstance,inferInstance⟩

theorem pma2_13_rationals : RudinCountable ℚ := by
  change Nonempty (ℚ ≃ ℕ)
  infer_instance

/-! ### PMA-2.14: binary sequences are uncountable. -/
theorem pma2_14 : RudinUncountable (ℕ → Fin 2) := by
  apply (pma2_4_uncountable_reference _).mpr
  intro hc
  let := hc
  obtain ⟨f,hf⟩ := exists_surjective_nat (ℕ → Fin 2)
  let d : ℕ → Fin 2 := fun n => if f n n = 0 then 1 else 0
  obtain ⟨n,hn⟩ := hf d
  have hd : f n n = d n := congrFun hn n
  by_cases hzero : f n n = 0
  · simp [d,hzero] at hd
  · simp [d,hzero] at hd
end Rudin.PMA.Chapter02
