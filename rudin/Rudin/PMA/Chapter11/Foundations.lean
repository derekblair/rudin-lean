import Mathlib

noncomputable section
open Set Filter Topology MeasureTheory
open scoped BigOperators ENNReal

namespace Rudin.PMA.Chapter11

variable {X I : Type*} {R : Set (Set X)} {A B : Set X} {φ : Set X → EReal}

/-! PMA 11.1–11.3 and 11.12. Set functions take values in `EReal`, so negative
values and either sign of infinity are retained. Natural-number indexing starts
at zero, an inessential reindexing of the book's sequences. -/

/-- 11.1: the literal closure conditions; the empty family is permitted. -/
structure SetRing (R : Set (Set X)) : Prop where
  union_mem : ∀ ⦃A B⦄, A ∈ R → B ∈ R → A ∪ B ∈ R
  sdiff_mem : ∀ ⦃A B⦄, A ∈ R → B ∈ R → A \ B ∈ R

/-- 11.1: a ring closed under countable unions. -/
structure SigmaRing (R : Set (Set X)) : Prop extends SetRing R where
  iUnion_mem : ∀ (A : ℕ → Set X), (∀ n, A n ∈ R) → (⋃ n, A n) ∈ R

theorem pma11_1_inter (hR : SetRing R) (hA : A ∈ R) (hB : B ∈ R) : A ∩ B ∈ R := by
  rw [← sdiff_sdiff_right_self]
  exact hR.sdiff_mem hA (hR.sdiff_mem hA hB)

theorem SetRing.empty_mem (hR : SetRing R) (hne : R.Nonempty) : ∅ ∈ R := by
  obtain ⟨A, hA⟩ := hne
  simpa using hR.sdiff_mem hA hA

theorem SetRing.toIsSetRing (hR : SetRing R) (hne : R.Nonempty) : IsSetRing R where
  empty_mem := hR.empty_mem hne
  union_mem := hR.union_mem
  sdiff_mem := fun _ _ hA hB => hR.sdiff_mem hA hB

theorem pma11_1_iInter (hR : SigmaRing R) (A : ℕ → Set X) (hA : ∀ n, A n ∈ R) :
    (⋂ n, A n) ∈ R := by
  have h := hR.sdiff_mem (hA 0)
    (hR.iUnion_mem (fun n => A 0 \ A n) (fun n => hR.sdiff_mem (hA 0) (hA n)))
  convert h using 1
  ext x
  simp only [mem_iInter, Set.mem_sdiff, mem_iUnion, not_exists, not_and, not_not]
  aesop

/-- 11.2: the range contains neither both infinities nor only an infinity.
The finite-value witness also records the nonemptiness implicit in this exclusion. -/
structure AdmissibleSetFunction (R : Set (Set X)) (φ : Set X → EReal) : Prop where
  no_opposite_infinities : ∀ A ∈ R, ∀ B ∈ R, ¬ (φ A = ⊤ ∧ φ B = ⊥)
  finite_value : ∃ A ∈ R, φ A ≠ ⊤ ∧ φ A ≠ ⊥

/-- 11.2, equation (3). -/
def AdditiveSetFunction (R : Set (Set X)) (φ : Set X → EReal) : Prop :=
  ∀ A ∈ R, ∀ B ∈ R, Disjoint A B → φ (A ∪ B) = φ A + φ B

/-- 11.2, equation (4), with the series expressed as convergence of its partial sums.
Membership of the union is required because the function is defined on a ring,
not necessarily on a sigma-ring. -/
def CountablyAdditiveSetFunction (R : Set (Set X)) (φ : Set X → EReal) : Prop :=
  ∀ A : ℕ → Set X, (∀ n, A n ∈ R) → Pairwise (fun i j => Disjoint (A i) (A j)) →
    (⋃ n, A n) ∈ R →
    Tendsto (fun n => ∑ i ∈ Finset.range n, φ (A i)) atTop (𝓝 (φ (⋃ n, A n)))

theorem pma11_2_empty (hR : SetRing R) (hφ : AdmissibleSetFunction R φ)
    (hadd : AdditiveSetFunction R φ) : φ ∅ = 0 := by
  obtain ⟨A, hA, ht, hb⟩ := hφ.finite_value
  have h := hadd A hA ∅ (hR.empty_mem ⟨A, hA⟩) disjoint_bot_right
  simp only [union_empty] at h
  lift φ A to ℝ using ⟨ht, hb⟩ with a ha
  have h' := congrArg (fun z : EReal => z - (a : EReal)) h
  simpa [EReal.add_sub_cancel_left] using h'.symm

theorem pma11_2_finite_union (hR : SetRing R) (hφ : AdmissibleSetFunction R φ)
    (hadd : AdditiveSetFunction R φ) (s : Finset I) (A : I → Set X)
    (hA : ∀ i ∈ s, A i ∈ R) (hd : (s : Set I).PairwiseDisjoint A) :
    φ (⋃ i ∈ s, A i) = ∑ i ∈ s, φ (A i) := by
  classical
  have hnonempty : R.Nonempty := by obtain ⟨A, hA, _⟩ := hφ.finite_value; exact ⟨A, hA⟩
  induction s using Finset.induction with
  | empty => simp [pma11_2_empty hR hφ hadd]
  | @insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    rw [hadd _ (hA i (Finset.mem_insert_self i s)) _
      ((hR.toIsSetRing hnonempty).biUnion_mem s (fun j hj => hA j (Finset.mem_insert_of_mem hj)))]
    · rw [ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)) (fun j hj k hk hjk => hd (by simp [hj]) (by simp [hk]) hjk)]
    · apply disjoint_iUnion_right.mpr
      intro j
      apply disjoint_iUnion_right.mpr
      intro hj
      exact hd (by simp) (by simp [hj]) (by aesop)

theorem pma11_2_inclusion_exclusion (hR : SetRing R)
    (hadd : AdditiveSetFunction R φ) (hA : A ∈ R) (hB : B ∈ R) :
    φ (A ∪ B) + φ (A ∩ B) = φ A + φ B := by
  have hB' : B = (B \ A) ∪ (A ∩ B) := by ext x; simp only [mem_union, Set.mem_sdiff, mem_inter_iff]; tauto
  have hAB : A ∪ B = A ∪ (B \ A) := by ext x; simp only [mem_union, Set.mem_sdiff]; tauto
  have hd : Disjoint (B \ A) (A ∩ B) := by exact disjoint_left.mpr (fun x hx hy => hx.2 hy.1)
  rw [hAB, hadd _ hA _ (hR.sdiff_mem hB hA) disjoint_sdiff_right]
  rw [add_assoc, ← hadd _ (hR.sdiff_mem hB hA) _ (pma11_1_inter hR hA hB) hd, ← hB']

theorem pma11_2_mono (hR : SetRing R) (hadd : AdditiveSetFunction R φ)
    (hnonneg : ∀ A ∈ R, 0 ≤ φ A) (hA : A ∈ R) (hB : B ∈ R) (hAB : A ⊆ B) :
    φ A ≤ φ B := by
  have h : B = A ∪ (B \ A) := by ext x; simp only [mem_union, Set.mem_sdiff]; exact ⟨fun hx => by by_cases ha : x ∈ A <;> aesop, fun hx => by aesop⟩
  rw [h, hadd _ hA _ (hR.sdiff_mem hB hA) disjoint_sdiff_right]
  exact le_add_of_nonneg_right (hnonneg _ (hR.sdiff_mem hB hA))

theorem pma11_2_sdiff (hR : SetRing R) (hadd : AdditiveSetFunction R φ)
    (hA : A ∈ R) (hB : B ∈ R) (hBA : B ⊆ A) (ht : φ B ≠ ⊤) (hb : φ B ≠ ⊥) :
    φ (A \ B) = φ A - φ B := by
  have h : A = (A \ B) ∪ B := (sdiff_union_of_subset hBA).symm
  have heq := hadd _ (hR.sdiff_mem hA hB) _ hB disjoint_sdiff_left
  rw [← h] at heq
  lift φ B to ℝ using ⟨ht, hb⟩ with b hb'
  rw [heq, EReal.add_sub_cancel_right]

private theorem affine_limit (b : ℝ) (a : EReal)
    (h : Tendsto (fun n : ℕ => (b : EReal) + n • a) atTop (𝓝 (b : EReal))) : a = 0 := by
  induction a using EReal.rec with
  | bot =>
    have hs := h.comp (tendsto_add_atTop_nat 1)
    have hh : Tendsto (fun _ : ℕ => (⊥ : EReal)) atTop (𝓝 (b : EReal)) := by
      simpa only [Function.comp_def, add_nsmul, one_nsmul, EReal.add_bot] using hs
    exact False.elim ((EReal.bot_ne_coe b) (tendsto_nhds_unique tendsto_const_nhds hh))
  | top =>
    have hs := h.comp (tendsto_add_atTop_nat 1)
    have he (n : ℕ) : (b : EReal) + (n + 1) • (⊤ : EReal) = ⊤ := by
      induction n with
      | zero => simp
      | succ n ih => rw [succ_nsmul, ← add_assoc, ih]; simp
    have hh : Tendsto (fun _ : ℕ => (⊤ : EReal)) atTop (𝓝 (b : EReal)) := by
      simpa only [Function.comp_def, he] using hs
    exact False.elim ((EReal.top_ne_coe b) (tendsto_nhds_unique tendsto_const_nhds hh))
  | coe a =>
    have hr : Tendsto (fun n : ℕ => b + n • a) atTop (𝓝 b) := by
      apply EReal.tendsto_coe.mp
      simpa only [EReal.coe_add, EReal.coe_nsmul] using h
    have hs := (hr.comp (tendsto_add_atTop_nat 1)).sub hr
    have he (n : ℕ) : (b + (n + 1) • a) - (b + n • a) = a := by
      simp; ring
    simp only [Function.comp_def, he, sub_self] at hs
    have ha : a = 0 := tendsto_nhds_unique tendsto_const_nhds hs
    simp [ha]

theorem countablyAdditive_empty {X : Type*} {R : Set (Set X)}
    {φ : Set X → EReal} (hR : SetRing R) (hφ : AdmissibleSetFunction R φ)
    (hc : CountablyAdditiveSetFunction R φ) : φ ∅ = 0 := by
  classical
  obtain ⟨B, hB, ht, hb⟩ := hφ.finite_value
  let A : ℕ → Set X := fun n => if n = 0 then B else ∅
  have he : ∅ ∈ R := hR.empty_mem ⟨B, hB⟩
  have hA : ∀ n, A n ∈ R := by intro n; dsimp [A]; split <;> assumption
  have hd : Pairwise (fun i j => Disjoint (A i) (A j)) := by
    intro i j hij
    dsimp [A]
    split_ifs with hi hj hj <;> simp_all
  have hu : (⋃ n, A n) = B := by
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      dsimp [A] at hn
      split_ifs at hn <;> aesop
    · intro hx
      exact ⟨0, by simpa [A] using hx⟩
  have hlim := hc A hA hd (by rw [hu]; exact hB)
  rw [hu] at hlim
  have hs (n : ℕ) : (∑ i ∈ Finset.range (n + 1), φ (A i)) = φ B + n • φ ∅ := by
    induction n with
    | zero => simp [A]
    | succ n ih => rw [Finset.sum_range_succ, ih]; simp [A, succ_nsmul, add_assoc]
  have hlim' := hlim.comp (tendsto_add_atTop_nat 1)
  simp only [Function.comp_def, hs] at hlim'
  lift φ B to ℝ using ⟨ht, hb⟩ with b hb'
  exact affine_limit b (φ ∅) hlim'

theorem countablyAdditive_additive {X : Type*} {R : Set (Set X)}
    {φ : Set X → EReal} (hR : SetRing R) (hφ : AdmissibleSetFunction R φ)
    (hc : CountablyAdditiveSetFunction R φ) : AdditiveSetFunction R φ := by
  classical
  intro A hA B hB hAB
  have hzero := countablyAdditive_empty hR hφ hc
  let C : ℕ → Set X := fun n => if n = 0 then A else if n = 1 then B else ∅
  have he : ∅ ∈ R := hR.empty_mem ⟨A, hA⟩
  have hC : ∀ n, C n ∈ R := by intro n; dsimp [C]; split_ifs <;> assumption
  have hd : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    dsimp [C]
    split_ifs <;> simp_all [Disjoint.symm hAB]
  have hu : (⋃ n, C n) = A ∪ B := by
    ext x
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨n, hn⟩
      dsimp [C] at hn
      split_ifs at hn <;> aesop
    · intro hx
      rcases hx with hx | hx
      · exact ⟨0, by simpa [C] using hx⟩
      · exact ⟨1, by simpa [C] using hx⟩
  have hlim := hc C hC hd (by rw [hu]; exact hR.union_mem hA hB)
  rw [hu] at hlim
  have hs (n : ℕ) : (∑ i ∈ Finset.range (n + 2), φ (C i)) = φ A + φ B := by
    induction n with
    | zero => simp [Finset.sum_range_succ, C]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hn1 : n + 2 ≠ 1 := by omega
      simp [C, hn1, hzero]
  have hlim' := hlim.comp (tendsto_add_atTop_nat 2)
  simp only [Function.comp_def, hs] at hlim'
  exact (tendsto_nhds_unique tendsto_const_nhds hlim').symm

/-- 11.3, continuity from below. The additive premise is supplied separately;
its redundancy under the printed hypotheses is `countablyAdditive_additive`. -/
theorem pma11_3_of_additive (hR : SetRing R) (hφ : AdmissibleSetFunction R φ)
    (hadd : AdditiveSetFunction R φ) (hcount : CountablyAdditiveSetFunction R φ)
    (A : ℕ → Set X) (hA : ∀ n, A n ∈ R) (hmono : Monotone A)
    (hunion : (⋃ n, A n) ∈ R) :
    Tendsto (fun n => φ (A n)) atTop (𝓝 (φ (⋃ n, A n))) := by
  have hR' := hR.toIsSetRing ⟨A 0, hA 0⟩
  have hd := hcount (disjointed A) (hR'.disjointed_mem hA)
    (disjoint_disjointed A) (by simpa only [iUnion_disjointed] using hunion)
  rw [iUnion_disjointed] at hd
  have hs (n : ℕ) : (∑ i ∈ Finset.range (n + 1), φ (disjointed A i)) = φ (A n) := by
    rw [← pma11_2_finite_union hR hφ hadd _ _
      (fun i _ => hR'.disjointed_mem hA i) ((disjoint_disjointed A).set_pairwise _)]
    rw [biUnion_range_succ_disjointed, hmono.partialSups_eq]
  simpa only [Function.comp_def, hs] using hd.comp (tendsto_add_atTop_nat 1)

/-- 11.3 with exactly the printed countable-additivity hypotheses. -/
theorem pma11_3 (hR : SetRing R) (hφ : AdmissibleSetFunction R φ)
    (hc : CountablyAdditiveSetFunction R φ) (A : ℕ → Set X)
    (hA : ∀ n, A n ∈ R) (hmono : Monotone A) (hunion : (⋃ n, A n) ∈ R) :
    Tendsto (fun n => φ (A n)) atTop (𝓝 (φ (⋃ n, A n))) :=
  pma11_3_of_additive hR hφ (countablyAdditive_additive hR hφ hc) hc A hA hmono hunion

/-- 11.12: a measure on a sigma-ring, without forcing the whole space measurable. -/
structure RingMeasureSpace (X : Type*) where
  sets : Set (Set X)
  sigmaRing : SigmaRing sets
  empty_mem : ∅ ∈ sets
  measure : Set X → ℝ≥0∞
  measure_empty : measure ∅ = 0
  measure_iUnion : ∀ A : ℕ → Set X, (∀ n, A n ∈ sets) →
    Pairwise (fun i j => Disjoint (A i) (A j)) → measure (⋃ n, A n) = ∑' n, measure (A n)

/-- 11.12: Rudin calls the space measurable when its universe belongs to the ring. -/
def RingMeasureSpace.IsMeasurable (m : RingMeasureSpace X) : Prop := Set.univ ∈ m.sets

/-- Bridge from the book's sigma-ring-with-universe convention to Mathlib. -/
@[instance_reducible] def RingMeasureSpace.toMeasurableSpace (m : RingMeasureSpace X) (hX : m.IsMeasurable) :
    MeasurableSpace X where
  MeasurableSet' := fun A => A ∈ m.sets
  measurableSet_empty := m.empty_mem
  measurableSet_compl A hA := by
    convert m.sigmaRing.sdiff_mem hX hA using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_sdiff, Set.mem_univ, true_and]
  measurableSet_iUnion A hA := m.sigmaRing.iUnion_mem A hA

/-- No measure is lost when a book-style measurable space is encoded by Mathlib. -/
def RingMeasureSpace.toMeasure (m : RingMeasureSpace X) (hX : m.IsMeasurable) :
    @Measure X (m.toMeasurableSpace hX) :=
  @Measure.ofMeasurable X (m.toMeasurableSpace hX) (fun A _ => m.measure A)
    m.measure_empty (fun A hA hd => m.measure_iUnion A hA hd)

theorem RingMeasureSpace.toMeasure_apply (m : RingMeasureSpace X) (hX : m.IsMeasurable)
    {A : Set X} (hA : A ∈ m.sets) : m.toMeasure hX A = m.measure A :=
  @Measure.ofMeasurable_apply X (m.toMeasurableSpace hX) _ _ _ A hA

/-- Every native measure space is a book-style measure space. -/
def ringMeasureSpaceOfMeasure [MeasurableSpace X] (μ : Measure X) : RingMeasureSpace X where
  sets := {A | MeasurableSet A}
  sigmaRing := {
    union_mem := fun _ _ hA hB => hA.union hB
    sdiff_mem := fun _ _ hA hB => hA.diff hB
    iUnion_mem := fun _A hA => MeasurableSet.iUnion hA }
  empty_mem := MeasurableSet.empty
  measure := μ
  measure_empty := measure_empty
  measure_iUnion := fun _A hA hd => measure_iUnion hd hA

theorem pma11_12_measurable [MeasurableSpace X] (μ : Measure X) :
    (ringMeasureSpaceOfMeasure μ).IsMeasurable := MeasurableSet.univ

/-- 11.12's Lebesgue example uses the completion of Euclidean volume, so all
Lebesgue measurable sets, including subsets of null sets, are included. -/
def pma11_12_lebesgue (p : ℕ) :
    RingMeasureSpace (NullMeasurableSpace (Fin p → ℝ) volume) :=
  ringMeasureSpaceOfMeasure (volume : Measure (Fin p → ℝ)).completion

/-- 11.12's counting example; positive integers are reindexed by `ℕ`. -/
theorem pma11_12_counting (A : Set ℕ) : Measure.count A = A.encard :=
  Measure.count_apply (Set.to_countable A).measurableSet

/-- 11.12's probability example: disjoint events add and the whole space has mass one. -/
theorem pma11_12_probability [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (A B : Set X) (hB : MeasurableSet B) (hd : Disjoint A B) :
    μ univ = 1 ∧ μ (A ∪ B) = μ A + μ B :=
  ⟨measure_univ, measure_union hd hB⟩

end Rudin.PMA.Chapter11
