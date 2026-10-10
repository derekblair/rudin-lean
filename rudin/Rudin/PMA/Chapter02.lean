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
/-! ### PMA-2.15: Distance functions and metric spaces. -/
def IsDistanceFunction {X : Type*} (d : X → X → ℝ) : Prop :=
  (∀ p q, p ≠ q → 0 < d p q) ∧ (∀ p, d p p = 0) ∧
    (∀ p q, d p q = d q p) ∧ (∀ p q r, d p q ≤ d p r + d r q)

@[instance_reducible] def metricSpaceOfDistance {X : Type*} (d : X → X → ℝ)
    (h : IsDistanceFunction d) : MetricSpace X where
  dist := d
  dist_self := h.2.1
  dist_comm := h.2.2.1
  dist_triangle := fun p q r => h.2.2.2 p r q
  eq_of_dist_eq_zero := by
    intro p q hpq
    by_contra hp
    exact (ne_of_gt (h.1 p q hp)) hpq

theorem distanceFunction_of_metric {X : Type*} [MetricSpace X] :
    IsDistanceFunction (dist : X → X → ℝ) :=
  ⟨fun _ _ h => dist_pos.mpr h, dist_self, dist_comm, fun p q r => dist_triangle p r q⟩

theorem metricSpaceOfDistance_dist {X : Type*} (d : X → X → ℝ)
    (h : IsDistanceFunction d) : (metricSpaceOfDistance d h).dist = d := rfl

/-! ### PMA-2.16: Euclidean metrics and the metric induced on a subset. -/
theorem euclidean_distance (k : ℕ) (x y : EuclideanSpace ℝ (Fin k)) :
    dist x y = ‖x - y‖ := dist_eq_norm x y

theorem euclidean_isDistanceFunction (k : ℕ) :
    IsDistanceFunction (fun x y : EuclideanSpace ℝ (Fin k) => ‖x - y‖) := by
  simpa only [← dist_eq_norm] using
    (distanceFunction_of_metric (X := EuclideanSpace ℝ (Fin k)))

theorem real_distance (x y : ℝ) : dist x y = |x-y| := Real.dist_eq x y

theorem complex_distance (x y : ℂ) : dist x y = ‖x-y‖ := dist_eq_norm x y

theorem real_isDistanceFunction :
    IsDistanceFunction (fun x y : ℝ => |x-y|) := by
  simpa only [← Real.dist_eq] using (distanceFunction_of_metric (X := ℝ))

theorem complex_isDistanceFunction :
    IsDistanceFunction (fun x y : ℂ => ‖x-y‖) := by
  simpa only [← dist_eq_norm] using (distanceFunction_of_metric (X := ℂ))

theorem subset_distance {X : Type*} [MetricSpace X] (Y : Set X) (p q : Y) :
    dist p q = dist (p : X) (q : X) := rfl

theorem subset_isDistanceFunction {X : Type*} [MetricSpace X] (Y : Set X) :
    IsDistanceFunction (fun p q : Y => dist (p : X) (q : X)) :=
  distanceFunction_of_metric

/-! ### PMA-2.17: Intervals, cells, balls, and convex sets.

The definitions extend to arbitrary radii and endpoints; in particular they cover
Rudin's positive radii and strictly ordered cell endpoints. -/
def segment (a b : ℝ) : Set ℝ := {x | a < x ∧ x < b}
def interval (a b : ℝ) : Set ℝ := {x | a ≤ x ∧ x ≤ b}
def leftClosedInterval (a b : ℝ) : Set ℝ := {x | a ≤ x ∧ x < b}
def rightClosedInterval (a b : ℝ) : Set ℝ := {x | a < x ∧ x ≤ b}
def kCell {k : ℕ} (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ i, a i ≤ x i ∧ x i ≤ b i}
def openEuclideanBall {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :=
  {y | ‖y - x‖ < r}
def closedEuclideanBall {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :=
  {y | ‖y - x‖ ≤ r}
def IsConvexSet {V : Type*} [AddCommGroup V] [Module ℝ V] (E : Set V) : Prop :=
  ∀ x ∈ E, ∀ y ∈ E, ∀ t : ℝ, 0 < t → t < 1 → t • x + (1-t) • y ∈ E

theorem segment_eq_Ioo (a b : ℝ) : segment a b = Ioo a b := rfl
theorem interval_eq_Icc (a b : ℝ) : interval a b = Icc a b := rfl
theorem leftClosedInterval_eq_Ico (a b : ℝ) : leftClosedInterval a b = Ico a b := rfl
theorem rightClosedInterval_eq_Ioc (a b : ℝ) : rightClosedInterval a b = Ioc a b := rfl

theorem openEuclideanBall_eq_ball {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    openEuclideanBall x r = Metric.ball x r := by
  ext y
  simp [openEuclideanBall, Metric.mem_ball, dist_eq_norm]

theorem closedEuclideanBall_eq_closedBall {k : ℕ} (x : EuclideanSpace ℝ (Fin k))
    (r : ℝ) : closedEuclideanBall x r = Metric.closedBall x r := by
  ext y
  simp [closedEuclideanBall, Metric.mem_closedBall, dist_eq_norm]

theorem isConvexSet_iff_convex {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : Set V) : IsConvexSet E ↔ Convex ℝ E := by
  constructor
  · intro h x hx y hy a b ha hb hab
    by_cases ha0 : a = 0
    · simpa [ha0, (by linarith : b = 1)] using hy
    by_cases hb0 : b = 0
    · simpa [hb0, (by linarith : a = 1)] using hx
    have ha1 : a < 1 := by
      have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      linarith
    have hb' : b = 1-a := by linarith
    subst b
    exact h x hx y hy a (lt_of_le_of_ne ha (Ne.symm ha0)) ha1
  · intro h x hx y hy t ht ht1
    exact h hx hy (le_of_lt ht) (by linarith) (by ring)

theorem openEuclideanBall_convex {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    IsConvexSet (openEuclideanBall x r) := by
  rw [isConvexSet_iff_convex, openEuclideanBall_eq_ball]
  exact convex_ball x r

theorem closedEuclideanBall_convex {k : ℕ} (x : EuclideanSpace ℝ (Fin k)) (r : ℝ) :
    IsConvexSet (closedEuclideanBall x r) := by
  rw [isConvexSet_iff_convex, closedEuclideanBall_eq_closedBall]
  exact convex_closedBall x r

theorem kCell_convex {k : ℕ} (a b : Fin k → ℝ) : IsConvexSet (kCell a b) := by
  intro x hx y hy t ht ht1 i
  have hx' := hx i
  have hy' := hy i
  change a i ≤ t * x i + (1-t) * y i ∧ t * x i + (1-t) * y i ≤ b i
  constructor <;> nlinarith

/-! ### PMA-2.18: Metric topology terminology. -/
def neighborhood {X : Type*} [MetricSpace X] (p : X) (r : ℝ) : Set X :=
  {q | dist p q < r}
def IsLimitPoint {X : Type*} [MetricSpace X] (p : X) (E : Set X) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ q ∈ E, q ≠ p ∧ dist p q < r
def IsIsolatedPoint {X : Type*} [MetricSpace X] (p : X) (E : Set X) : Prop :=
  p ∈ E ∧ ¬ IsLimitPoint p E
def IsClosedSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  ∀ p, IsLimitPoint p E → p ∈ E
def IsInteriorPoint {X : Type*} [MetricSpace X] (p : X) (E : Set X) : Prop :=
  ∃ r : ℝ, 0 < r ∧ neighborhood p r ⊆ E
def IsOpenSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  ∀ p ∈ E, IsInteriorPoint p E
def complement {X : Type*} (E : Set X) : Set X := {p | p ∉ E}
def IsPerfectSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  IsClosedSet E ∧ ∀ p ∈ E, IsLimitPoint p E
def IsBoundedSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  ∃ M : ℝ, ∃ q : X, ∀ p ∈ E, dist p q < M
def IsDenseSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  ∀ p : X, p ∈ E ∨ IsLimitPoint p E

theorem neighborhood_eq_ball {X : Type*} [MetricSpace X] (p : X) (r : ℝ) :
    neighborhood p r = Metric.ball p r := by
  ext q
  simp [neighborhood, Metric.mem_ball, dist_comm]

theorem isLimitPoint_iff_accPt {X : Type*} [MetricSpace X] (p : X) (E : Set X) :
    IsLimitPoint p E ↔ AccPt p (𝓟 E) := by
  rw [accPt_iff_nhds]
  constructor
  · intro h U hU
    obtain ⟨r, hr, hUr⟩ := Metric.mem_nhds_iff.mp hU
    obtain ⟨q, hqE, hqp, hqr⟩ := h r hr
    exact ⟨q, ⟨hUr (by simpa [Metric.mem_ball, dist_comm] using hqr), hqE⟩, hqp⟩
  · intro h r hr
    obtain ⟨q, ⟨hqB, hqE⟩, hqp⟩ := h (Metric.ball p r) (Metric.ball_mem_nhds p hr)
    exact ⟨q, hqE, hqp, by simpa [Metric.mem_ball, dist_comm] using hqB⟩

theorem isIsolatedPoint_iff_mem_not_accPt {X : Type*} [MetricSpace X]
    (p : X) (E : Set X) :
    IsIsolatedPoint p E ↔ p ∈ E ∧ ¬ AccPt p (𝓟 E) := by
  simp only [IsIsolatedPoint, isLimitPoint_iff_accPt]

theorem isClosedSet_iff_isClosed {X : Type*} [MetricSpace X] (E : Set X) :
    IsClosedSet E ↔ IsClosed E := by
  rw [isClosed_iff_derivedSet_subset]
  simp only [IsClosedSet, isLimitPoint_iff_accPt, Set.subset_def, mem_derivedSet]

theorem isInteriorPoint_iff_mem_interior {X : Type*} [MetricSpace X] (p : X)
    (E : Set X) : IsInteriorPoint p E ↔ p ∈ interior E := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
  simp [IsInteriorPoint, neighborhood_eq_ball]

theorem isOpenSet_iff_isOpen {X : Type*} [MetricSpace X] (E : Set X) :
    IsOpenSet E ↔ IsOpen E := by
  rw [Metric.isOpen_iff]
  simp [IsOpenSet, IsInteriorPoint, neighborhood_eq_ball]

theorem complement_eq_compl {X : Type*} (E : Set X) : complement E = Eᶜ := rfl

theorem isPerfectSet_iff_perfect {X : Type*} [MetricSpace X] (E : Set X) :
    IsPerfectSet E ↔ Perfect E := by
  simp only [IsPerfectSet, isClosedSet_iff_isClosed, isLimitPoint_iff_accPt,
    perfect_def, Preperfect]

theorem isBoundedSet_iff_isBounded {X : Type*} [MetricSpace X] [Nonempty X]
    (E : Set X) : IsBoundedSet E ↔ Bornology.IsBounded E := by
  obtain ⟨q⟩ := ‹Nonempty X›
  constructor
  · rintro ⟨M, q, h⟩
    exact (Metric.isBounded_iff_subset_ball q).mpr ⟨M, h⟩
  · intro h
    obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_ball q).mp h
    exact ⟨M, q, hM⟩

theorem isDenseSet_iff_dense {X : Type*} [MetricSpace X] (E : Set X) :
    IsDenseSet E ↔ Dense E := by
  simp only [IsDenseSet, isLimitPoint_iff_accPt, Dense,
    closure_eq_self_union_derivedSet, Set.mem_union, mem_derivedSet]

/-! ### PMA-2.19: Every metric neighborhood is open. -/
theorem neighborhood_isOpen {X : Type*} [MetricSpace X] (p : X) (r : ℝ) :
    IsOpenSet (neighborhood p r) := by
  rw [isOpenSet_iff_isOpen, neighborhood_eq_ball]
  exact Metric.isOpen_ball

/-! ### PMA-2.20: A limit point has infinitely many set members in every neighborhood. -/
theorem limitPoint_infinite_neighborhood {X : Type*} [MetricSpace X] {p : X}
    {E : Set X} (hp : IsLimitPoint p E) {r : ℝ} (hr : 0 < r) :
    (E ∩ neighborhood p r).Infinite := by
  intro hfin
  have hclosed := (hfin.sdiff (t := {p})).isClosed
  have hpclosure : p ∈ closure ((E ∩ neighborhood p r) \ {p}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨q, hqE, hqp, hqr⟩ := hp (min ε r) (lt_min hε hr)
    exact ⟨q, ⟨⟨hqE, lt_of_lt_of_le hqr (min_le_right _ _)⟩,
      by simpa using hqp⟩, lt_of_lt_of_le hqr (min_le_left _ _)⟩
  have hp' := hclosed.closure_subset hpclosure
  exact hp'.2 (by simp)

theorem finite_no_limitPoint {X : Type*} [MetricSpace X] {E : Set X}
    (hE : E.Finite) (p : X) : ¬ IsLimitPoint p E := by
  intro hp
  exact limitPoint_infinite_neighborhood hp zero_lt_one (hE.inter_of_left _)

/-! ### PMA-2.21: Classification of the seven example sets. -/

def complexIntegers : Set ℂ := Set.range (fun n : ℤ => (n : ℂ))
def reciprocalIntegers : Set ℂ := Set.range (fun n : ℕ => Complex.ofReal (1 / (n+1 : ℝ)))
def complexSegment (a b : ℝ) : Set ℂ := Complex.ofReal '' Ioo a b

private theorem real_subset_not_open {E : Set ℂ} (hne : E.Nonempty)
    (hreal : ∀ z ∈ E, z.im = 0) : ¬ IsOpenSet E := by
  intro h
  obtain ⟨p,hp⟩ := hne
  obtain ⟨r,hr,hpr⟩ := h p hp
  have him : (p + ((r/2 : ℝ) : ℂ) * Complex.I).im = r/2 := by
    simp [hreal p hp]
  have hnorm : ‖((r/2 : ℝ) : ℂ) * Complex.I‖ < r := by
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r/2)]
    linarith
  have hdist : dist p (p+((r/2 : ℝ) : ℂ)*Complex.I) < r := by
    simpa [dist_eq_norm', add_sub_cancel_left] using hnorm
  have hp' := hpr hdist
  have hzero := hreal _ hp'
  rw [him] at hzero
  linarith

private theorem nonempty_finite_not_perfect {E : Set ℂ} (hne : E.Nonempty)
    (hfin : E.Finite) : ¬ IsPerfectSet E := by
  intro hp
  obtain ⟨p,hpE⟩ := hne
  exact finite_no_limitPoint hfin p (hp.2 p hpE)

private theorem nonempty_finite_not_open {E : Set ℂ} (hne : E.Nonempty)
    (hfin : E.Finite) : ¬ IsOpenSet E := by
  intro ho
  obtain ⟨p,hpE⟩ := hne
  have hacc := ((isOpenSet_iff_isOpen E).mp ho).preperfect p hpE
  exact finite_no_limitPoint hfin p ((isLimitPoint_iff_accPt p E).mpr hacc)

theorem openUnitBall_classification :
    ¬ IsClosedSet (Metric.ball (0 : ℂ) 1) ∧
      IsOpenSet (Metric.ball (0 : ℂ) 1) ∧
      ¬ IsPerfectSet (Metric.ball (0 : ℂ) 1) ∧
      IsBoundedSet (Metric.ball (0 : ℂ) 1) := by
  have hnclosed : ¬ IsClosedSet (Metric.ball (0 : ℂ) 1) := by
    rw [isClosedSet_iff_isClosed]
    intro hc
    have hEq := hc.closure_eq
    rw [closure_ball 0 one_ne_zero] at hEq
    have hmem : (1 : ℂ) ∈ Metric.closedBall 0 1 := by simp
    rw [hEq] at hmem
    simp at hmem
  refine ⟨hnclosed, (isOpenSet_iff_isOpen _).mpr Metric.isOpen_ball,
    fun h => hnclosed h.1, ?_⟩
  exact (isBoundedSet_iff_isBounded _).mpr Metric.isBounded_ball

theorem closedUnitBall_classification :
    IsClosedSet (Metric.closedBall (0 : ℂ) 1) ∧
      ¬ IsOpenSet (Metric.closedBall (0 : ℂ) 1) ∧
      IsPerfectSet (Metric.closedBall (0 : ℂ) 1) ∧
      IsBoundedSet (Metric.closedBall (0 : ℂ) 1) := by
  refine ⟨(isClosedSet_iff_isClosed _).mpr Metric.isClosed_closedBall, ?_, ?_,
    (isBoundedSet_iff_isBounded _).mpr Metric.isBounded_closedBall⟩
  · rw [isOpenSet_iff_isOpen]
    intro ho
    have hEq := ho.interior_eq
    rw [interior_closedBall 0 one_ne_zero] at hEq
    have hmem : (1 : ℂ) ∈ Metric.closedBall 0 1 := by simp
    rw [← hEq] at hmem
    simp at hmem
  · rw [isPerfectSet_iff_perfect, ← closure_ball 0 one_ne_zero]
    exact Metric.isOpen_ball.perfect_closure

theorem finite_complex_set_classification {E : Set ℂ} (hne : E.Nonempty)
    (hfin : E.Finite) :
    IsClosedSet E ∧ ¬ IsOpenSet E ∧ ¬ IsPerfectSet E ∧ IsBoundedSet E := by
  exact ⟨(isClosedSet_iff_isClosed _).mpr hfin.isClosed,
    nonempty_finite_not_open hne hfin, nonempty_finite_not_perfect hne hfin,
    (isBoundedSet_iff_isBounded _).mpr hfin.isBounded⟩

private theorem complexIntegers_no_limitPoint (p : ℂ) : ¬ IsLimitPoint p complexIntegers := by
  intro hp
  have hclosed : IsClosed complexIntegers := Complex.isClosed_range_intCast
  have hdiscrete : IsDiscrete complexIntegers :=
    Complex.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range
  have hdisjoint := (isClosed_and_discrete_iff.mp ⟨hclosed,hdiscrete⟩) p
  have hbot : 𝓝[≠] p ⊓ 𝓟 complexIntegers = ⊥ := hdisjoint.eq_bot
  have hacc := (isLimitPoint_iff_accPt p complexIntegers).mp hp
  exact hacc.ne hbot

theorem complexIntegers_classification :
    IsClosedSet complexIntegers ∧ ¬ IsOpenSet complexIntegers ∧
      ¬ IsPerfectSet complexIntegers ∧ ¬ IsBoundedSet complexIntegers := by
  refine ⟨(isClosedSet_iff_isClosed _).mpr Complex.isClosed_range_intCast, ?_, ?_, ?_⟩
  · apply real_subset_not_open (E := complexIntegers) ⟨0,⟨0,by simp⟩⟩
    rintro z ⟨n,rfl⟩
    simp
  · intro hp
    exact complexIntegers_no_limitPoint 0 (hp.2 0 ⟨0,by simp⟩)
  · rintro ⟨M,q,h⟩
    obtain ⟨n,hn⟩ := exists_nat_gt (M + ‖q‖)
    have hmem : (n : ℂ) ∈ complexIntegers := ⟨(n : ℤ),by simp⟩
    have hd := h (n : ℂ) hmem
    have hnorm : ‖(n : ℂ)‖ ≤ dist (n : ℂ) q + ‖q‖ := by
      simpa [dist_eq_norm] using norm_sub_norm_le (n : ℂ) q
    have hn' : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    rw [hn'] at hnorm
    linarith

private theorem reciprocal_positive (n : ℕ) : 0 < 1 / (n+1 : ℝ) := by positivity

private theorem reciprocal_le_one (n : ℕ) : 1 / (n+1 : ℝ) ≤ 1 := by
  apply (div_le_one (by positivity)).mpr
  exact_mod_cast (Nat.le_add_left 1 n)

theorem reciprocalIntegers_zero_limitPoint : IsLimitPoint (0 : ℂ) reciprocalIntegers := by
  intro r hr
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hr
  refine ⟨Complex.ofReal (1 / (n+1 : ℝ)), ⟨n,rfl⟩, ?_, ?_⟩
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (reciprocal_positive n))
  · rw [← Complex.ofReal_zero, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    simpa only [zero_sub, abs_neg, abs_of_pos (reciprocal_positive n)] using hn

private theorem reciprocalIntegers_member_not_limitPoint (n : ℕ) :
    ¬ IsLimitPoint (Complex.ofReal (1 / (n+1 : ℝ))) reciprocalIntegers := by
  let δ : ℝ := 1 / (n+1 : ℝ) - 1 / (n+2 : ℝ)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt (by positivity) (by linarith))
  intro hp
  obtain ⟨q,⟨m,rfl⟩,hqp,hd⟩ := hp δ hδ
  have hmn : m ≠ n := by
    intro h
    subst m
    exact hqp rfl
  have hd' : |1 / (n+1 : ℝ) - 1 / (m+1 : ℝ)| < δ := by
    rw [Complex.isometry_ofReal.dist_eq, Real.dist_eq] at hd
    exact hd
  rcases lt_or_gt_of_ne hmn with hmn | hnm
  · have hbound : 1 / (n+2 : ℝ) ≤ 1 / (n+1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have hmn' : (m+1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le m) hmn)
    have hnm' : 1 / (n : ℝ) ≤ 1 / (m+1 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hmn'
    have hgap : 1 / (n+1 : ℝ) - 1 / (n+2 : ℝ) ≤
        1 / (n : ℝ) - 1 / (n+1 : ℝ) := by
      field_simp
      nlinarith
    have hh := (abs_lt.mp hd').1
    dsimp [δ] at hh
    linarith
  · have hnm' : (n+2 : ℝ) ≤ (m+1 : ℝ) := by exact_mod_cast (show n+2 ≤ m+1 by omega)
    have hbound : 1 / (m+1 : ℝ) ≤ 1 / (n+2 : ℝ) :=
      one_div_le_one_div_of_le (by positivity) hnm'
    have hh := (abs_lt.mp hd').2
    dsimp [δ] at hh
    linarith

theorem reciprocalIntegers_no_member_limitPoint :
    ∀ p ∈ reciprocalIntegers, ¬ IsLimitPoint p reciprocalIntegers := by
  rintro p ⟨n,rfl⟩
  exact reciprocalIntegers_member_not_limitPoint n

theorem reciprocalIntegers_classification :
    ¬ IsClosedSet reciprocalIntegers ∧ ¬ IsOpenSet reciprocalIntegers ∧
      ¬ IsPerfectSet reciprocalIntegers ∧ IsBoundedSet reciprocalIntegers := by
  have hnotclosed : ¬ IsClosedSet reciprocalIntegers := by
    intro hc
    have hm := hc 0 reciprocalIntegers_zero_limitPoint
    obtain ⟨n,hn⟩ := hm
    change Complex.ofReal (1 / (n+1 : ℝ)) = 0 at hn
    have hn' : (1 / (n+1 : ℝ)) = 0 := Complex.ofReal_injective hn
    exact ne_of_gt (reciprocal_positive n) hn'
  refine ⟨hnotclosed, ?_, fun h => hnotclosed h.1, ?_⟩
  · apply real_subset_not_open (E := reciprocalIntegers) ⟨1,⟨0,by norm_num⟩⟩
    rintro z ⟨n,rfl⟩
    simp
  · refine ⟨2,0,?_⟩
    rintro p ⟨n,rfl⟩
    rw [← Complex.ofReal_zero, Complex.isometry_ofReal.dist_eq, Real.dist_eq]
    rw [sub_zero,abs_of_pos (reciprocal_positive n)]
    exact lt_of_le_of_lt (reciprocal_le_one n) (by norm_num)

theorem complex_universe_classification :
    IsClosedSet (univ : Set ℂ) ∧ IsOpenSet (univ : Set ℂ) ∧
      IsPerfectSet (univ : Set ℂ) ∧ ¬ IsBoundedSet (univ : Set ℂ) := by
  refine ⟨(isClosedSet_iff_isClosed _).mpr isClosed_univ,
    (isOpenSet_iff_isOpen _).mpr isOpen_univ, ?_, ?_⟩
  · rw [isPerfectSet_iff_perfect]
    exact ⟨isClosed_univ,isOpen_univ.preperfect⟩
  · rw [isBoundedSet_iff_isBounded]
    exact NormedSpace.unbounded_univ ℂ ℂ

theorem complexSegment_classification {a b : ℝ} (hab : a < b) :
    ¬ IsClosedSet (complexSegment a b) ∧ ¬ IsOpenSet (complexSegment a b) ∧
      ¬ IsPerfectSet (complexSegment a b) ∧ IsBoundedSet (complexSegment a b) ∧
      IsOpenSet (segment a b) := by
  have hnotclosed : ¬ IsClosedSet (complexSegment a b) := by
    intro hc
    have hpre := ((isClosedSet_iff_isClosed _).mp hc).preimage Complex.continuous_ofReal
    have heq : Complex.ofReal ⁻¹' complexSegment a b = Ioo a b := by
      exact Set.preimage_image_eq _ Complex.ofReal_injective
    rw [heq] at hpre
    have hcl : a ∈ closure (Ioo a b) := by
      rw [closure_Ioo hab.ne]
      exact ⟨le_rfl,hab.le⟩
    exact (hpre.closure_subset hcl).1.false
  refine ⟨hnotclosed, ?_, fun h => hnotclosed h.1, ?_,
    (isOpenSet_iff_isOpen _).mpr isOpen_Ioo⟩
  · apply real_subset_not_open ((Set.nonempty_Ioo.mpr hab).image Complex.ofReal)
    rintro z ⟨x,hx,rfl⟩
    simp
  · rw [isBoundedSet_iff_isBounded]
    exact ((isCompact_Icc : IsCompact (Icc a b)).image Complex.continuous_ofReal).isBounded.subset
      (Set.image_mono Ioo_subset_Icc_self)

/-! ### PMA-2.22: De Morgan's law for arbitrary unions. -/
theorem complement_iUnion {X I : Type*} (E : I → Set X) :
    complement (⋃ i, E i) = ⋂ i, complement (E i) := by
  ext x
  simp [complement]

/-! ### PMA-2.23: Open and closed complements. -/
theorem open_iff_complement_closed {X : Type*} [MetricSpace X] (E : Set X) :
    IsOpenSet E ↔ IsClosedSet (complement E) := by
  rw [isOpenSet_iff_isOpen, isClosedSet_iff_isClosed, complement_eq_compl,
    isClosed_compl_iff]

theorem closed_iff_complement_open {X : Type*} [MetricSpace X] (E : Set X) :
    IsClosedSet E ↔ IsOpenSet (complement E) := by
  rw [isOpenSet_iff_isOpen, isClosedSet_iff_isClosed, complement_eq_compl,
    isOpen_compl_iff]

/-! ### PMA-2.24: Unions and intersections of open and closed sets. -/
theorem arbitrary_union_open {X I : Type*} [MetricSpace X] (G : I → Set X)
    (hG : ∀ i, IsOpenSet (G i)) : IsOpenSet (⋃ i, G i) := by
  rw [isOpenSet_iff_isOpen]
  exact isOpen_iUnion fun i => (isOpenSet_iff_isOpen _).mp (hG i)

theorem arbitrary_intersection_closed {X I : Type*} [MetricSpace X] (F : I → Set X)
    (hF : ∀ i, IsClosedSet (F i)) : IsClosedSet (⋂ i, F i) := by
  rw [isClosedSet_iff_isClosed]
  exact isClosed_iInter fun i => (isClosedSet_iff_isClosed _).mp (hF i)

theorem finite_intersection_open {X I : Type*} [MetricSpace X] [Finite I]
    (G : I → Set X) (hG : ∀ i, IsOpenSet (G i)) : IsOpenSet (⋂ i, G i) := by
  rw [isOpenSet_iff_isOpen]
  exact isOpen_iInter_of_finite fun i => (isOpenSet_iff_isOpen _).mp (hG i)

theorem finite_union_closed {X I : Type*} [MetricSpace X] [Finite I]
    (F : I → Set X) (hF : ∀ i, IsClosedSet (F i)) : IsClosedSet (⋃ i, F i) := by
  rw [isClosedSet_iff_isClosed]
  exact isClosed_iUnion_of_finite fun i => (isClosedSet_iff_isClosed _).mp (hF i)

/-! ### PMA-2.25: Infinite intersections of open sets and unions of closed sets. -/
def shrinkingSegment (n : ℕ) : Set ℝ := Ioo (-(1 / (n+1 : ℝ))) (1 / (n+1 : ℝ))

theorem shrinkingSegment_isOpen (n : ℕ) : IsOpenSet (shrinkingSegment n) :=
  (isOpenSet_iff_isOpen _).mpr isOpen_Ioo

theorem iInter_shrinkingSegment : (⋂ n, shrinkingSegment n) = ({0} : Set ℝ) := by
  ext x
  simp only [mem_iInter, shrinkingSegment, mem_Ioo, mem_singleton_iff]
  constructor
  · intro hx
    have habs : ∀ n : ℕ, |x| < 1 / (n+1 : ℝ) := fun n => abs_lt.mpr (hx n)
    by_contra h
    have hpos : 0 < |x| := abs_pos.mpr h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
    exact (not_lt_of_ge (le_of_lt (habs n))) hn
  · intro hx
    subst x
    intro n
    have hpos : 0 < 1 / (n+1 : ℝ) := by positivity
    constructor <;> linarith

theorem iInter_shrinkingSegment_not_open : ¬ IsOpenSet (⋂ n, shrinkingSegment n) := by
  rw [iInter_shrinkingSegment, isOpenSet_iff_isOpen]
  exact not_isOpen_singleton 0

theorem closed_complements_shrinkingSegment (n : ℕ) :
    IsClosedSet ((shrinkingSegment n)ᶜ) := by
  exact (isClosedSet_iff_isClosed _).mpr isOpen_Ioo.isClosed_compl

theorem iUnion_complements_shrinkingSegment_not_closed :
    ¬ IsClosedSet (⋃ n, (shrinkingSegment n)ᶜ) := by
  rw [isClosedSet_iff_isClosed]
  intro h
  apply iInter_shrinkingSegment_not_open
  rw [isOpenSet_iff_isOpen]
  simpa only [compl_iUnion, compl_compl] using h.isOpen_compl

/-! ### PMA-2.26: Closure as a set together with its limit points. -/
def limitPoints {X : Type*} [MetricSpace X] (E : Set X) : Set X :=
  {p | IsLimitPoint p E}
def setClosure {X : Type*} [MetricSpace X] (E : Set X) : Set X := E ∪ limitPoints E

theorem limitPoints_eq_derivedSet {X : Type*} [MetricSpace X] (E : Set X) :
    limitPoints E = derivedSet E := by
  ext p
  exact isLimitPoint_iff_accPt p E

theorem setClosure_eq_closure {X : Type*} [MetricSpace X] (E : Set X) :
    setClosure E = closure E := by
  rw [setClosure, limitPoints_eq_derivedSet, closure_eq_self_union_derivedSet]

/-! ### PMA-2.27: Closure is the smallest closed superset. -/
theorem closure_closed {X : Type*} [MetricSpace X] (E : Set X) :
    IsClosedSet (setClosure E) := by
  rw [isClosedSet_iff_isClosed, setClosure_eq_closure]
  exact isClosed_closure

theorem closure_eq_self_iff_closed {X : Type*} [MetricSpace X] (E : Set X) :
    setClosure E = E ↔ IsClosedSet E := by
  rw [setClosure_eq_closure, isClosedSet_iff_isClosed, closure_eq_iff_isClosed]

theorem closure_minimal {X : Type*} [MetricSpace X] {E F : Set X}
    (hF : IsClosedSet F) (hEF : E ⊆ F) : setClosure E ⊆ F := by
  rw [setClosure_eq_closure]
  exact _root_.closure_minimal hEF ((isClosedSet_iff_isClosed F).mp hF)

/-! ### PMA-2.28: A supremum belongs to the closure. -/
theorem supremum_mem_closure {E : Set ℝ} (hE : E.Nonempty) (hb : BddAbove E) :
    sSup E ∈ setClosure E := by
  rw [setClosure_eq_closure]
  exact csSup_mem_closure hE hb

theorem supremum_mem_closed {E : Set ℝ} (hE : E.Nonempty) (hb : BddAbove E)
    (hc : IsClosedSet E) : sSup E ∈ E :=
  ((isClosedSet_iff_isClosed E).mp hc).csSup_mem hE hb

/-! ### PMA-2.29: Relative openness in a metric subspace. -/
def IsRelativelyOpen {X : Type*} [MetricSpace X] (Y E : Set X) : Prop :=
  ∀ p ∈ E, ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Y, dist p q < r → q ∈ E

theorem isRelativelyOpen_iff_subtype_open {X : Type*} [MetricSpace X]
    {Y E : Set X} (hEY : E ⊆ Y) :
    IsRelativelyOpen Y E ↔ IsOpen (Subtype.val ⁻¹' E : Set Y) := by
  rw [Metric.isOpen_iff]
  constructor
  · intro h p hp
    obtain ⟨r, hr, hpr⟩ := h p hp
    refine ⟨r, hr, ?_⟩
    intro q hq
    apply hpr q q.property
    change dist (q : X) (p : X) < r at hq
    simpa only [dist_comm] using hq
  · intro h p hp
    obtain ⟨r, hr, hpr⟩ := h ⟨p, hEY hp⟩ hp
    refine ⟨r, hr, ?_⟩
    intro q hq hdist
    exact hpr (show (⟨q,hq⟩ : Y) ∈ Metric.ball ⟨p,hEY hp⟩ r by
      change dist q p < r
      simpa only [dist_comm] using hdist)

/-! ### PMA-2.30: Relatively open sets are ambient open intersections. -/
theorem relativelyOpen_iff_ambient_intersection {X : Type*} [MetricSpace X]
    {Y E : Set X} (hEY : E ⊆ Y) :
    IsRelativelyOpen Y E ↔ ∃ G : Set X, IsOpenSet G ∧ E = Y ∩ G := by
  rw [isRelativelyOpen_iff_subtype_open hEY, isOpen_induced_iff]
  constructor
  · rintro ⟨G,hG,hEq⟩
    refine ⟨G, (isOpenSet_iff_isOpen G).mpr hG, ?_⟩
    ext p
    constructor
    · intro hp
      have hx : (⟨p,hEY hp⟩ : Y) ∈ Subtype.val ⁻¹' E := hp
      rw [← hEq] at hx
      exact ⟨hEY hp,hx⟩
    · rintro ⟨hpY,hpG⟩
      have hx : (⟨p,hpY⟩ : Y) ∈ Subtype.val ⁻¹' G := hpG
      rw [hEq] at hx
      exact hx
  · rintro ⟨G,hG,rfl⟩
    refine ⟨G,(isOpenSet_iff_isOpen G).mp hG, ?_⟩
    ext p
    simp
/-! ### PMA-2.31: an open cover consists of open sets whose union contains the set. -/

def OpenCover {X : Type*} [TopologicalSpace X] (E : Set X) {ι : Type*}
    (G : ι → Set X) : Prop := (∀ i, IsOpen (G i)) ∧ E ⊆ ⋃ i, G i

theorem pma2_31_reference {X : Type*} [TopologicalSpace X] (E : Set X)
    {ι : Type*} (G : ι → Set X) :
    OpenCover E G ↔ (∀ i, IsOpen (G i)) ∧ ∀ x ∈ E, ∃ i, x ∈ G i := by
  simp [OpenCover, Set.subset_def]

/-! ### PMA-2.32: compactness is the finite subcover property; finite sets are compact. -/

universe u

def RudinCompact {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  ∀ {ι : Type u} (G : ι → Set X), OpenCover K G →
    ∃ t : Finset ι, K ⊆ ⋃ i ∈ t, G i

theorem pma2_32_reference {X : Type u} [TopologicalSpace X] (K : Set X) :
    RudinCompact K ↔ IsCompact K := by
  constructor
  · intro h
    apply isCompact_iff_finite_subcover.mpr
    intro ι G ho hc
    exact h G ⟨ho, hc⟩
  · intro h ι G hG
    exact h.elim_finite_subcover G hG.1 hG.2

theorem pma2_32_finite {X : Type u} [TopologicalSpace X] {K : Set X}
    (hK : K.Finite) : RudinCompact K :=
  (pma2_32_reference K).mpr hK.isCompact

/-! ### PMA-2.33: compactness agrees in an ambient space and a metric subspace. -/

theorem pma2_33 {X : Type u} [MetricSpace X] (Y K : Set X) (hKY : K ⊆ Y) :
    RudinCompact K ↔ RudinCompact ((↑) ⁻¹' K : Set Y) := by
  rw [pma2_32_reference, pma2_32_reference,
    Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have he : ((↑) '' ((↑) ⁻¹' K : Set Y) : Set X) = K := by
    rw [Set.image_preimage_eq_inter_range]
    simpa using (Set.inter_eq_left.mpr hKY)
  rw [he]

/-! ### PMA-2.34: compact subsets of metric spaces are closed. -/

theorem pma2_34 {X : Type u} [MetricSpace X] {K : Set X}
    (hK : RudinCompact K) : IsClosed K :=
  ((pma2_32_reference K).mp hK).isClosed

/-! ### PMA-2.35: closed subsets of compact sets, and closed intersections, are compact. -/

theorem pma2_35 {X : Type u} [MetricSpace X] {F K : Set X}
    (hF : IsClosed F) (hK : RudinCompact K) (hFK : F ⊆ K) : RudinCompact F :=
  (pma2_32_reference F).mpr <|
    ((pma2_32_reference K).mp hK).of_isClosed_subset hF hFK

theorem pma2_35_corollary {X : Type u} [MetricSpace X] {F K : Set X}
    (hF : IsClosed F) (hK : RudinCompact K) : RudinCompact (F ∩ K) := by
  apply pma2_35 (hF.inter (pma2_34 hK)) hK
  exact Set.inter_subset_right

/-! ### PMA-2.36: compact sets with the finite intersection property have a common point. -/

theorem pma2_36 {X : Type u} [MetricSpace X] {ι : Type*}
    (K : ι → Set X) (hK : ∀ i, RudinCompact (K i))
    (hfinite : ∀ t : Finset ι, (⋂ i ∈ t, K i).Nonempty) :
    (⋂ i, K i).Nonempty := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · let := hι
    simpa using hfinite (∅ : Finset ι)
  · let := hι
    let i₀ : ι := Classical.choice inferInstance
    have h : (K i₀ ∩ ⋂ i, K i).Nonempty := by
      apply ((pma2_32_reference (K i₀)).mp (hK i₀)).inter_iInter_nonempty K
        (fun i => pma2_34 (hK i))
      intro t
      obtain ⟨x, hx⟩ := hfinite (insert i₀ t)
      refine ⟨x, ?_, ?_⟩
      · exact Set.mem_iInter.mp (Set.mem_iInter.mp hx i₀) (Finset.mem_insert_self _ _)
      · simp only [Set.mem_iInter] at hx ⊢
        exact fun i hi => hx i (Finset.mem_insert_of_mem hi)
    exact h.mono Set.inter_subset_right

theorem pma2_36_corollary {X : Type u} [MetricSpace X] (K : ℕ → Set X)
    (hK : ∀ n, RudinCompact (K n)) (hne : ∀ n, (K n).Nonempty)
    (hdec : ∀ n, K (n + 1) ⊆ K n) : (⋂ n, K n).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hdec hne
    ((pma2_32_reference (K 0)).mp (hK 0)) (fun n => pma2_34 (hK n))

/-! ### PMA-2.37: infinite subsets of compact sets have accumulation points in those compact sets. -/

theorem pma2_37 {X : Type u} [MetricSpace X] {E K : Set X}
    (hE : E.Infinite) (hEK : E ⊆ K) (hK : RudinCompact K) :
    ∃ p ∈ K, AccPt p (𝓟 E) :=
  hE.exists_accPt_of_subset_isCompact ((pma2_32_reference K).mp hK) hEK

/-! ### PMA-2.38: nested nonempty closed intervals have nonempty intersection. -/

theorem pma2_38 (a b : ℕ → ℝ) (hab : ∀ n, a n ≤ b n)
    (hdec : ∀ n, Icc (a (n + 1)) (b (n + 1)) ⊆ Icc (a n) (b n)) :
    (⋂ n, Icc (a n) (b n)).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hdec
    (fun n => Set.nonempty_Icc.mpr (hab n)) isCompact_Icc (fun _ => isClosed_Icc)

/-! ### PMA-2.39: nested nonempty Euclidean cells have nonempty intersection. -/

def ClosedCell (k : ℕ) (a b : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | ∀ j, a j ≤ x j ∧ x j ≤ b j}

theorem closedCell_nonempty {k : ℕ} {a b : Fin k → ℝ} (hab : ∀ j, a j ≤ b j) :
    (ClosedCell k a b).Nonempty :=
  ⟨WithLp.toLp 2 a, fun j => ⟨le_refl _, hab j⟩⟩

theorem closedCell_isClosed {k : ℕ} (a b : Fin k → ℝ) :
    IsClosed (ClosedCell k a b) := by
  have he : ClosedCell k a b = ⋂ j, (fun x : EuclideanSpace ℝ (Fin k) => x j) ⁻¹' Icc (a j) (b j) := by
    ext x; simp [ClosedCell]
  rw [he]
  exact isClosed_iInter fun j => isClosed_Icc.preimage (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) j)

theorem closedCell_isCompact {k : ℕ} (a b : Fin k → ℝ) :
    IsCompact (ClosedCell k a b) := by
  let e := EuclideanSpace.equiv (Fin k) ℝ
  have hc : IsCompact (Set.pi Set.univ (fun j => Icc (a j) (b j))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  convert hc.image e.symm.continuous using 1
  ext x
  constructor
  · intro hx
    refine ⟨e x, ?_, e.symm_apply_apply x⟩
    exact fun j _ => hx j
  · rintro ⟨y, hy, rfl⟩
    exact fun j => hy j (Set.mem_univ j)

theorem pma2_39 {k : ℕ} (_hk : 0 < k) (a b : ℕ → Fin k → ℝ)
    (hab : ∀ n j, a n j ≤ b n j)
    (hdec : ∀ n, ClosedCell k (a (n + 1)) (b (n + 1)) ⊆ ClosedCell k (a n) (b n)) :
    (⋂ n, ClosedCell k (a n) (b n)).Nonempty := by
  exact IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hdec
    (fun n => closedCell_nonempty (hab n)) (closedCell_isCompact (a 0) (b 0))
    (fun n => closedCell_isClosed (a n) (b n))

/-! ### PMA-2.40: every Euclidean cell is compact. -/

theorem pma2_40 {k : ℕ} (_hk : 0 < k) (a b : Fin k → ℝ) (_hab : ∀ j, a j ≤ b j) :
    RudinCompact (ClosedCell k a b) :=
  (pma2_32_reference _).mpr (closedCell_isCompact a b)

/-! ### PMA-2.41: closed and bounded, compact, and the infinite-subset accumulation property agree. -/

def InfiniteSubsetAccumulation {X : Type*} [TopologicalSpace X] (E : Set X) : Prop :=
  ∀ A ⊆ E, A.Infinite → ∃ p ∈ E, AccPt p (𝓟 A)

theorem pma2_41 {k : ℕ} (_hk : 0 < k) (E : Set (EuclideanSpace ℝ (Fin k))) :
    ((IsClosed E ∧ Bornology.IsBounded E) ↔ RudinCompact E) ∧
    (RudinCompact E ↔ InfiniteSubsetAccumulation E) := by
  refine ⟨(Metric.isCompact_iff_isClosed_bounded).symm.trans (pma2_32_reference E).symm, ?_⟩
  rw [pma2_32_reference]
  exact ⟨fun h => fun A hAE hA => hA.exists_accPt_of_subset_isCompact h hAE,
    fun h => (isCountablyCompact_iff_infinite_subset_has_accPt.mpr h).isCompact⟩

end Rudin.PMA.Chapter02
