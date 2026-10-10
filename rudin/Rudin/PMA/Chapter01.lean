import Mathlib

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 1: The Real and Complex Number Systems

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

namespace Rudin.PMA.Chapter01

/-! ### PMA-1.1: rational numbers leave a gap at the square root of two. -/

def rationalBelowSqrtTwo : Set ℚ := {p | 0 < p ∧ p ^ 2 < 2}
def rationalAboveSqrtTwo : Set ℚ := {p | 0 < p ∧ 2 < p ^ 2}

theorem pma1_1_no_rational_square (p : ℚ) : p ^ 2 ≠ 2 := by
  intro h
  have hs : ¬ IsSquare (2 : ℚ) := by
    simpa using (irrational_sqrt_ratCast_iff_of_nonneg (q := 2) (by norm_num)).mp
      irrational_sqrt_two
  exact hs ⟨p, by simpa [sq] using h.symm⟩

theorem pma1_1_no_largest (p : ℚ) (hp : p ∈ rationalBelowSqrtTwo) :
    ∃ q ∈ rationalBelowSqrtTwo, p < q := by
  rcases hp with ⟨hp, hs⟩
  let q := (2 * p + 2) / (p + 2)
  have hd : 0 < p + 2 := by linarith
  have hqp : p < q := by
    dsimp [q]
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have hq : q * (p + 2) = 2 * p + 2 := by
    dsimp [q]
    field_simp
  refine ⟨q, ⟨lt_trans hp hqp, ?_⟩, hqp⟩
  have he : (q ^ 2 - 2) * (p + 2) ^ 2 = 2 * (p ^ 2 - 2) := by
    nlinarith [sq_nonneg (q * (p + 2) - (2 * p + 2))]
  have hd2 : 0 < (p + 2) ^ 2 := sq_pos_of_pos hd
  nlinarith

theorem pma1_1_no_smallest (p : ℚ) (hp : p ∈ rationalAboveSqrtTwo) :
    ∃ q ∈ rationalAboveSqrtTwo, q < p := by
  rcases hp with ⟨hp, hs⟩
  let q := (2 * p + 2) / (p + 2)
  have hd : 0 < p + 2 := by linarith
  have hqp : q < p := by
    dsimp [q]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq : q * (p + 2) = 2 * p + 2 := by dsimp [q]; field_simp
  refine ⟨q, ⟨hqpos, ?_⟩, hqp⟩
  have he : (q ^ 2 - 2) * (p + 2) ^ 2 = 2 * (p ^ 2 - 2) := by
    nlinarith [sq_nonneg (q * (p + 2) - (2 * p + 2))]
  have hd2 : 0 < (p + 2) ^ 2 := sq_pos_of_pos hd
  nlinarith


/-! ### PMA-1.3: elementary set terminology. -/

def IsMember {α : Type*} (x : α) (A : Set α) : Prop := x ∈ A
def IsEmptySet {α : Type*} (A : Set α) : Prop := ∀ x, x ∉ A
def IsSubset {α : Type*} (A B : Set α) : Prop := ∀ x, x ∈ A → x ∈ B
def IsProperSubset {α : Type*} (A B : Set α) : Prop :=
  IsSubset A B ∧ ∃ x, x ∈ B ∧ x ∉ A

theorem pma1_3_reference {α : Type*} (A B : Set α) (x : α) :
    (IsMember x A ↔ x ∈ A) ∧ (IsEmptySet A ↔ A = ∅) ∧
    (IsSubset A B ↔ A ⊆ B) ∧ (IsProperSubset A B ↔ A ⊂ B) ∧
    (A = B ↔ IsSubset A B ∧ IsSubset B A) := by
  refine ⟨Iff.rfl, ?_, Iff.rfl, ?_, ?_⟩
  · simp [IsEmptySet, Set.eq_empty_iff_forall_notMem]
  · simp only [IsProperSubset, IsSubset, Set.ssubset_def, Set.subset_def]
    classical
    simp only [not_forall, exists_prop]
  · exact Set.Subset.antisymm_iff

/-! ### PMA-1.4: the notation for rational numbers. -/

abbrev RationalNumbers := ℚ

theorem pma1_4_fraction (q : RationalNumbers) :
    ∃ a b : ℤ, b ≠ 0 ∧ q = (a : ℚ) / (b : ℚ) := by
  refine ⟨q.num, q.den, by exact_mod_cast q.den_ne_zero, ?_⟩
  simpa using (Rat.num_div_den q).symm

/-! ### PMA-1.5: a strict order is trichotomous and transitive. -/

def OrderAxioms {α : Type*} (r : α → α → Prop) : Prop :=
  (∀ x, ¬ r x x) ∧ (∀ x y, r x y ∨ x = y ∨ r y x) ∧ (∀ ⦃x y z⦄, r x y → r y z → r x z)

theorem pma1_5_exactly_one {α : Type*} {r : α → α → Prop}
    (h : OrderAxioms r) (x y : α) :
    (r x y ∨ x = y ∨ r y x) ∧
    ¬ (r x y ∧ x = y) ∧ ¬ (r x y ∧ r y x) ∧ ¬ (x = y ∧ r y x) := by
  rcases h with ⟨hi, ht, htrans⟩
  refine ⟨ht x y, ?_, ?_, ?_⟩
  · rintro ⟨hxy, rfl⟩; exact hi x hxy
  · rintro ⟨hxy, hyx⟩; exact hi x (htrans hxy hyx)
  · rintro ⟨rfl, hxx⟩; exact hi x hxx

theorem pma1_5_linearOrder (α : Type*) [LinearOrder α] :
    OrderAxioms ((· < ·) : α → α → Prop) :=
  ⟨lt_irrefl, lt_trichotomy, fun {_ _ _} hxy hyz => lt_trans hxy hyz⟩

/-! ### PMA-1.6: an ordered set is a carrier equipped with an order. -/

structure OrderedSet where
  carrier : Type*
  less : carrier → carrier → Prop
  order : OrderAxioms less

def orderedSetOfLinearOrder (α : Type*) [LinearOrder α] : OrderedSet :=
  ⟨α, (· < ·), pma1_5_linearOrder α⟩

theorem pma1_6_rational_order (r s : ℚ) : r < s ↔ 0 < s - r :=
  (sub_pos).symm

/-! ### PMA-1.7: upper/lower bounds and bounded sets. -/

def IsUpperBound {α : Type*} [LE α] (E : Set α) (b : α) : Prop :=
  ∀ x ∈ E, x ≤ b

def IsLowerBound {α : Type*} [LE α] (E : Set α) (b : α) : Prop :=
  ∀ x ∈ E, b ≤ x

def IsBoundedAbove {α : Type*} [LE α] (E : Set α) : Prop := ∃ b, IsUpperBound E b
def IsBoundedBelow {α : Type*} [LE α] (E : Set α) : Prop := ∃ b, IsLowerBound E b

theorem pma1_7_reference {α : Type*} [LE α] (E : Set α) (b : α) :
    (IsUpperBound E b ↔ b ∈ upperBounds E) ∧
    (IsLowerBound E b ↔ b ∈ lowerBounds E) ∧
    (IsBoundedAbove E ↔ BddAbove E) ∧ (IsBoundedBelow E ↔ BddBelow E) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ### PMA-1.8: supremum and infimum by exclusion of better bounds. -/

def IsSupremum {α : Type*} [LT α] [LE α] (E : Set α) (a : α) : Prop :=
  IsUpperBound E a ∧ ∀ b, b < a → ¬ IsUpperBound E b

def IsInfimum {α : Type*} [LT α] [LE α] (E : Set α) (a : α) : Prop :=
  IsLowerBound E a ∧ ∀ b, a < b → ¬ IsLowerBound E b

theorem pma1_8_sup_reference {α : Type*} [LinearOrder α] (E : Set α) (a : α) :
    IsSupremum E a ↔ IsLUB E a := by
  constructor
  · rintro ⟨ha, hmin⟩
    exact ⟨ha, fun b hb => le_of_not_gt (fun hba => hmin b hba hb)⟩
  · rintro ⟨ha, hmin⟩
    exact ⟨ha, fun b hb hbound => (not_le_of_gt hb) (hmin hbound)⟩

theorem pma1_8_inf_reference {α : Type*} [LinearOrder α] (E : Set α) (a : α) :
    IsInfimum E a ↔ IsGLB E a := by
  constructor
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, fun b hb => le_of_not_gt (fun hab => hmax b hab hb)⟩
  · rintro ⟨ha, hmax⟩
    exact ⟨ha, fun b hb hbound => (not_le_of_gt hb) (hmax hbound)⟩

theorem pma1_8_sup_unique {α : Type*} [LinearOrder α] {E : Set α} {a b : α}
    (ha : IsSupremum E a) (hb : IsSupremum E b) : a = b :=
  (pma1_8_sup_reference E a).mp ha |>.unique ((pma1_8_sup_reference E b).mp hb)

theorem pma1_8_inf_unique {α : Type*} [LinearOrder α] {E : Set α} {a b : α}
    (ha : IsInfimum E a) (hb : IsInfimum E b) : a = b :=
  (pma1_8_inf_reference E a).mp ha |>.unique ((pma1_8_inf_reference E b).mp hb)


/-! ### PMA-1.9: examples of suprema and infima. -/

theorem pma1_9_upperBounds : upperBounds rationalBelowSqrtTwo = rationalAboveSqrtTwo := by
  ext p
  constructor
  · intro hp
    have h1 : (1 : ℚ) ∈ rationalBelowSqrtTwo := by constructor <;> norm_num
    have hp0 : 0 < p := lt_of_lt_of_le (by norm_num : (0 : ℚ) < 1) (hp h1)
    refine ⟨hp0, lt_of_not_ge ?_⟩
    intro hs
    have hlt : p ^ 2 < 2 := lt_of_le_of_ne hs (pma1_1_no_rational_square p)
    obtain ⟨q, hq, hpq⟩ := pma1_1_no_largest p ⟨hp0, hlt⟩
    exact (not_le_of_gt hpq) (hp hq)
  · rintro ⟨hp0, hp2⟩ x ⟨hx0, hx2⟩
    by_contra h
    have : p < x := lt_of_not_ge h
    nlinarith

theorem pma1_9_lowerBounds : lowerBounds rationalAboveSqrtTwo =
    rationalBelowSqrtTwo ∪ Set.Iic 0 := by
  ext p
  constructor
  · intro hp
    by_cases hp0 : 0 < p
    · left
      refine ⟨hp0, lt_of_not_ge ?_⟩
      intro hs
      have hlt : 2 < p ^ 2 := lt_of_le_of_ne hs (pma1_1_no_rational_square p).symm
      obtain ⟨q, hq, hqp⟩ := pma1_1_no_smallest p ⟨hp0, hlt⟩
      exact (not_le_of_gt hqp) (hp hq)
    · exact Or.inr (le_of_not_gt hp0)
  · rintro (⟨hp0, hp2⟩ | hp0) x ⟨hx0, hx2⟩
    · by_contra h
      have : x < p := lt_of_not_ge h
      nlinarith
    · exact le_trans hp0 hx0.le

theorem pma1_9_rational_gap :
    BddAbove rationalBelowSqrtTwo ∧ BddBelow rationalAboveSqrtTwo ∧
    ¬ (∃ a : ℚ, IsLUB rationalBelowSqrtTwo a) ∧
    ¬ (∃ b : ℚ, IsGLB rationalAboveSqrtTwo b) := by
  have h2 : (2 : ℚ) ∈ rationalAboveSqrtTwo := by constructor <;> norm_num
  have h1 : (1 : ℚ) ∈ rationalBelowSqrtTwo := by constructor <;> norm_num
  refine ⟨⟨2, by rwa [pma1_9_upperBounds]⟩, ⟨0, ?_⟩, ?_, ?_⟩
  · intro p hp; exact hp.1.le
  · rintro ⟨a, ha⟩
    have haB : a ∈ rationalAboveSqrtTwo := by simpa [pma1_9_upperBounds] using ha.1
    obtain ⟨b, hb, hba⟩ := pma1_1_no_smallest a haB
    have hbU : b ∈ upperBounds rationalBelowSqrtTwo := by simpa [pma1_9_upperBounds] using hb
    exact (not_le_of_gt hba) (ha.2 hbU)
  · rintro ⟨b, hb⟩
    have hbA : b ∈ rationalBelowSqrtTwo ∪ Set.Iic 0 := by
      simpa [pma1_9_lowerBounds] using hb.1
    rcases hbA with hbA | hb0
    · obtain ⟨a, ha, hba⟩ := pma1_1_no_largest b hbA
      have haL : a ∈ lowerBounds rationalAboveSqrtTwo := by
        rw [pma1_9_lowerBounds]; exact Or.inl ha
      exact (not_le_of_gt hba) (hb.2 haL)
    · have h1L : (1 : ℚ) ∈ lowerBounds rationalAboveSqrtTwo := by
        rw [pma1_9_lowerBounds]; exact Or.inl h1
      have := hb.2 h1L
      change b ≤ 0 at hb0
      linarith

theorem pma1_9_membership_examples :
    IsLUB (Set.Iio (0 : ℚ)) 0 ∧ IsLUB (Set.Iic (0 : ℚ)) 0 ∧
    (0 : ℚ) ∉ Set.Iio 0 ∧ (0 : ℚ) ∈ Set.Iic 0 :=
  by
  refine ⟨isLUB_Iio, isLUB_Iic, ?_, ?_⟩ <;> simp

def positiveReciprocals : Set ℚ := {x | ∃ n : ℕ, 0 < n ∧ x = 1 / (n : ℚ)}

theorem pma1_9_reciprocals :
    IsLUB positiveReciprocals 1 ∧ IsGLB positiveReciprocals 0 ∧
    (1 : ℚ) ∈ positiveReciprocals ∧ (0 : ℚ) ∉ positiveReciprocals := by
  have h1 : (1 : ℚ) ∈ positiveReciprocals := ⟨1, by norm_num, by norm_num⟩
  have hpos : ∀ x ∈ positiveReciprocals, 0 < x := by
    rintro x ⟨n, hn, rfl⟩; positivity
  refine ⟨⟨?_, fun b hb => hb h1⟩, ⟨fun x hx => (hpos x hx).le, ?_⟩, h1, ?_⟩
  · rintro x ⟨n, hn, rfl⟩
    have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
    exact (div_le_one (by positivity : (0 : ℚ) < n)).mpr hn1
  · intro b hb
    by_contra h
    have hb0 : 0 < b := lt_of_not_ge h
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℚ) hb0
    have hm : 1 / ((n + 1 : ℕ) : ℚ) ∈ positiveReciprocals :=
      ⟨n + 1, Nat.succ_pos n, rfl⟩
    have hh := hb hm
    push_cast at hh
    exact (not_le_of_gt hn) hh
  · intro h; exact lt_irrefl 0 (hpos 0 h)

end Rudin.PMA.Chapter01
