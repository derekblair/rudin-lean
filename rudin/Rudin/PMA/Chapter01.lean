import Mathlib

noncomputable section

open scoped BigOperators ComplexConjugate

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

/-! ### PMA-1.10: the least-upper-bound property. -/

def HasLUBProperty (α : Type*) [LE α] : Prop :=
  ∀ E : Set α, E.Nonempty → BddAbove E → ∃ a, IsLUB E a

theorem pma1_10_reference (α : Type*) [ConditionallyCompleteLinearOrder α] :
    HasLUBProperty α := by
  intro E hE hb
  exact ⟨sSup E, isLUB_csSup hE hb⟩

theorem pma1_10_rationals_not_complete : ¬ HasLUBProperty ℚ := by
  intro h
  have hE : rationalBelowSqrtTwo.Nonempty := ⟨1, by constructor <;> norm_num⟩
  exact pma1_9_rational_gap.2.2.1 (h _ hE pma1_9_rational_gap.1)

/-! ### PMA-1.11: infima from suprema of lower bounds. -/

theorem pma1_11 {α : Type*} [LinearOrder α] (h : HasLUBProperty α)
    (B : Set α) (hne : B.Nonempty) (hbelow : BddBelow B) :
    ∃ a, IsLUB (lowerBounds B) a ∧ IsGLB B a := by
  obtain ⟨b, hb⟩ := hne
  have hupper : BddAbove (lowerBounds B) := ⟨b, fun a ha => ha hb⟩
  obtain ⟨a, ha⟩ := h (lowerBounds B) hbelow hupper
  exact ⟨a, ha, isLUB_lowerBounds.mp ha⟩
/-! ### PMA-1.12: Field axioms -/

/-- Rudin's field axioms. Closure of the two operations is expressed by their
types; the two identity elements and existence of inverses are explicit. -/
def pmaFieldAxioms (K : Type*) [Add K] [Mul K] [Zero K] [One K] : Prop :=
  (∀ x y : K, x + y = y + x) ∧
  (∀ x y z : K, (x + y) + z = x + (y + z)) ∧
  (∀ x : K, x + 0 = x) ∧
  (∀ x : K, ∃ y : K, x + y = 0) ∧
  (∀ x y : K, x * y = y * x) ∧
  (∀ x y z : K, (x * y) * z = x * (y * z)) ∧
  (1 : K) ≠ 0 ∧
  (∀ x : K, x * 1 = x) ∧
  (∀ x : K, x ≠ 0 → ∃ y : K, x * y = 1) ∧
  (∀ x y z : K, x * (y + z) = x * y + x * z)

/-- Each clause of the stated field axioms holds in a Mathlib field. -/
theorem pma_field_axioms {K : Type*} [Field K] : pmaFieldAxioms K := by
  refine ⟨add_comm, add_assoc, add_zero, ?_, mul_comm, mul_assoc,
    one_ne_zero, mul_one, ?_, mul_add⟩
  · intro x
    exact ⟨-x, add_neg_cancel x⟩
  · intro x hx
    exact ⟨x⁻¹, mul_inv_cancel₀ hx⟩

/-- Conversely, the stated axioms reconstruct a Mathlib field with the same
addition, multiplication, zero, and one. Choosing inverses supplies notation. -/
noncomputable abbrev pmaFieldOfAxioms {K : Type*} [Add K] [Mul K] [Zero K] [One K]
    (h : pmaFieldAxioms K) : Field K := by
  classical
  rcases h with ⟨hac, haa, haz, hai, hmc, hma, h10, hm1, hmi, hd⟩
  letI : Neg K := ⟨fun x => Classical.choose (hai x)⟩
  letI : Inv K := ⟨fun x => if hx : x = 0 then 0 else Classical.choose (hmi x hx)⟩
  refine Field.ofMinimalAxioms K haa ?_ ?_ hma hmc ?_ ?_ ?_ hd ⟨1, 0, h10⟩
  · intro x
    rw [hac]
    exact haz x
  · intro x
    change Classical.choose (hai x) + x = 0
    rw [hac]
    exact Classical.choose_spec (hai x)
  · intro x
    rw [hmc]
    exact hm1 x
  · intro x hx
    change x * (if h : x = 0 then 0 else Classical.choose (hmi x h)) = 1
    rw [dite_eq_right hx]
    exact Classical.choose_spec (hmi x hx)
  · change (if h : (0 : K) = 0 then 0 else Classical.choose (hmi 0 h)) = 0
    rw [dite_eq_left rfl]

theorem pma_field_axioms_operations {K : Type*} [Add K] [Mul K] [Zero K] [One K]
    (h : pmaFieldAxioms K) :
    (pmaFieldOfAxioms h).toAdd = ‹Add K› ∧
    (pmaFieldOfAxioms h).toMul = ‹Mul K› ∧
    (pmaFieldOfAxioms h).toZero = ‹Zero K› ∧
    (pmaFieldOfAxioms h).toOne = ‹One K› := by
  rcases h with ⟨hac, haa, haz, hai, hmc, hma, h10, hm1, hmi, hd⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ### PMA-1.13: Inverses, powers, and the rational field -/

/-- The arithmetic notation introduced in the remarks agrees with the field
operations. Natural powers include the usual zeroth-power convention. -/
theorem pma_field_notation {K : Type*} [Field K] (x y : K) (n : ℕ) :
    x - y = x + (-y) ∧ x / y = x * (1 / y) ∧
    x ^ 2 = x * x ∧ x ^ 3 = (x * x) * x ∧
    (2 : K) * x = x + x ∧ (3 : K) * x = (x + x) + x ∧
    x ^ 0 = 1 ∧ x ^ (n + 1) = x ^ n * x := by
  refine ⟨sub_eq_add_neg x y, ?_, pow_two x, ?_, ?_, ?_, pow_zero x, pow_succ x n⟩
  · simp only [div_eq_mul_inv, one_mul]
  · simp only [pow_succ, pow_zero, one_mul]
  · ring
  · ring

theorem pma_rationals_are_a_field : pmaFieldAxioms ℚ := pma_field_axioms

/-! ### PMA-1.14: Consequences of the addition axioms -/

theorem pma_addition_consequences {K : Type*} [AddCommGroup K] :
    (∀ x y z : K, x + y = x + z → y = z) ∧
    (∀ x y : K, x + y = x → y = 0) ∧
    (∀ x y : K, x + y = 0 → y = -x) ∧
    (∀ x : K, -(-x) = x) := by
  refine ⟨fun _ _ _ h => add_left_cancel h, ?_, ?_, neg_neg⟩
  · intro x y h
    exact add_left_cancel (h.trans (add_zero x).symm)
  · intro x y h
    exact eq_neg_of_add_eq_zero_right h

/-! ### PMA-1.15: Consequences of the multiplication axioms -/

theorem pma_multiplication_consequences {K : Type*} [GroupWithZero K] :
    (∀ x y z : K, x ≠ 0 → x * y = x * z → y = z) ∧
    (∀ x y : K, x ≠ 0 → x * y = x → y = 1) ∧
    (∀ x y : K, x ≠ 0 → x * y = 1 → y = x⁻¹) ∧
    (∀ x : K, x ≠ 0 → (x⁻¹)⁻¹ = x) := by
  refine ⟨fun _ _ _ hx h => mul_left_cancel₀ hx h, ?_, ?_, ?_⟩
  · intro x y hx h
    exact mul_left_cancel₀ hx (h.trans (mul_one x).symm)
  · intro x y hx h
    exact mul_left_cancel₀ hx (h.trans (mul_inv_cancel₀ hx).symm)
  · intro x _
    exact inv_inv x

/-! ### PMA-1.16: Zero products and signs -/

theorem pma_field_sign_consequences {K : Type*} [Field K] :
    (∀ x : K, 0 * x = 0) ∧
    (∀ x y : K, x * y = 0 → x = 0 ∨ y = 0) ∧
    (∀ x y : K, (-x) * y = -(x * y) ∧ -(x * y) = x * (-y)) ∧
    (∀ x y : K, (-x) * (-y) = x * y) := by
  exact ⟨zero_mul, fun _ _ h => mul_eq_zero.mp h,
    fun x y => ⟨neg_mul x y, (mul_neg x y).symm⟩, neg_mul_neg⟩

/-! ### PMA-1.17: Ordered field -/

/-- The order compatibility clauses in the definition of an ordered field.
The `LinearOrder` parameter supplies trichotomy and transitivity. -/
def pmaOrderedFieldAxioms (K : Type*) [Field K] [LinearOrder K] : Prop :=
  (∀ x y z : K, x < y → x + z < y + z) ∧
  (∀ x y : K, 0 < x → 0 < y → 0 < x * y)

def pmaPositive {K : Type*} [Zero K] [LT K] (x : K) : Prop := 0 < x

def pmaNegative {K : Type*} [Zero K] [LT K] (x : K) : Prop := x < 0

theorem pma_ordered_field_axioms {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : pmaOrderedFieldAxioms K := by
  refine ⟨?_, fun _ _ hx hy => mul_pos hx hy⟩
  intro x y z h
  simpa only [add_comm] using add_lt_add_right h z

/-- Reference equivalence with Mathlib's order compatibility class. -/
theorem pma_ordered_field_axioms_iff {K : Type*} [Field K] [LinearOrder K] :
    pmaOrderedFieldAxioms K ↔ IsStrictOrderedRing K := by
  constructor
  · intro h
    let : IsOrderedAddMonoid K := {
      add_le_add_left := fun x y hxy z => by
        rcases hxy.lt_or_eq with hlt | rfl
        · exact (h.1 x y z hlt).le
        · exact le_rfl }
    have h01 : (0 : K) ≤ 1 := by
      by_cases h01 : (0 : K) ≤ 1
      · exact h01
      · have h10 : (1 : K) < 0 := lt_of_not_ge h01
        have hpos : (0 : K) < -1 := neg_pos_of_neg h10
        have hsq : (0 : K) < 1 := by simpa using h.2 (-1) (-1) hpos hpos
        exact hsq.le
    let : ZeroLEOneClass K := ⟨h01⟩
    exact IsStrictOrderedRing.of_mul_pos h.2
  · intro h
    let := h
    exact pma_ordered_field_axioms

/-! ### PMA-1.18: Ordered-field consequences -/

theorem pma_ordered_field_consequences {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    (∀ x : K, 0 < x ↔ -x < 0) ∧
    (∀ x y z : K, x < y → 0 < z → x * z < y * z) ∧
    (∀ x y z : K, x < y → z < 0 → y * z < x * z) ∧
    (∀ x : K, x ≠ 0 → 0 < x ^ 2) ∧
    (0 < (1 : K)) ∧
    (∀ x y : K, 0 < x → x < y → 0 < y⁻¹ ∧ y⁻¹ < x⁻¹) := by
  refine ⟨fun _ => neg_lt_zero.symm, ?_, ?_, ?_, zero_lt_one, ?_⟩
  · intro x y z h hz
    exact mul_lt_mul_of_pos_right h hz
  · intro x y z h hz
    exact mul_lt_mul_of_neg_right h hz
  · intro x hx
    exact sq_pos_of_ne_zero hx
  · intro x y hx hxy
    exact ⟨inv_pos.mpr (hx.trans hxy), (inv_lt_inv₀ (hx.trans hxy) hx).mpr hxy⟩

/-! ### PMA-1.19: Existence of the real number system -/

/-- Mathlib's real numbers provide the complete ordered field in the theorem,
and the rational cast realizes the rational numbers as a subfield. -/
theorem pma_real_number_system :
    pmaFieldAxioms ℝ ∧ pmaOrderedFieldAxioms ℝ ∧ HasLUBProperty ℝ ∧
      ∃ e : ℚ →+* ℝ, Function.Injective e ∧ StrictMono e := by
  refine ⟨pma_field_axioms, pma_ordered_field_axioms, ?_, ?_⟩
  · intro E hE hbounded
    exact ⟨sSup E, isLUB_csSup hE hbounded⟩
  · exact ⟨Rat.castHom ℝ, Rat.cast_injective, fun _ _ h => Rat.cast_lt.mpr h⟩

/-! ### PMA-1.20: Archimedean property and rational density -/

theorem pma_archimedean (x y : ℝ) (hx : 0 < x) :
    ∃ n : ℕ, 0 < n ∧ y < (n : ℝ) * x := by
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  have hn' : y < (n : ℝ) * x := (div_lt_iff₀ hx).mp hn
  have : (n : ℝ) * x < ((n + 1 : ℕ) : ℝ) * x := by
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self n) hx
  exact hn'.trans this

theorem pma_rational_density (x y : ℝ) (hxy : x < y) :
    ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := exists_rat_btwn hxy

/-! ### PMA-1.21: Positive real nth roots -/

/-- The root is uniquely determined among positive reals. The source's printed
uniqueness sentence omits positivity; for even exponents unrestricted uniqueness
is false, so the intended positive-root conclusion is explicit here. -/
theorem pma_positive_nth_root (x : ℝ) (n : ℕ) (hx : 0 < x) (hn : 0 < n) :
    ∃! y : ℝ, 0 < y ∧ y ^ n = x := by
  refine ⟨x ^ ((n : ℝ)⁻¹), ?_, ?_⟩
  · exact ⟨Real.rpow_pos_of_pos hx _, Real.rpow_inv_natCast_pow hx.le hn.ne'⟩
  · intro y hy
    apply (pow_left_inj₀ hy.1.le (Real.rpow_pos_of_pos hx _).le hn.ne').mp
    rw [hy.2, Real.rpow_inv_natCast_pow hx.le hn.ne']

/-- The unnumbered corollary following the nth-root theorem: the positive
nth root of a product is the product of the positive nth roots. -/
theorem pma_positive_nth_root_mul (a b : ℝ) (n : ℕ) (ha : 0 < a) (hb : 0 < b)
    (_hn : 0 < n) :
    (a * b) ^ ((n : ℝ)⁻¹) = a ^ ((n : ℝ)⁻¹) * b ^ ((n : ℝ)⁻¹) :=
  Real.mul_rpow ha.le hb.le
noncomputable section

open scoped BigOperators

/-! ### PMA-1.22: finite decimal truncations and the real number specified by an expansion. -/

def pmaDecimalTruncation (x : ℝ) (n : ℕ) : ℝ :=
  (⌊(10 : ℝ) ^ n * x⌋ : ℝ) / (10 : ℝ) ^ n

theorem pma_decimal_truncation_le (x : ℝ) (n : ℕ) : pmaDecimalTruncation x n ≤ x := by
  unfold pmaDecimalTruncation
  apply (div_le_iff₀ (by positivity : 0 < (10 : ℝ) ^ n)).2
  simpa [mul_comm] using Int.floor_le ((10 : ℝ) ^ n * x)

theorem pma_decimal_truncation_error (x : ℝ) (n : ℕ) :
    x - pmaDecimalTruncation x n < 1 / (10 : ℝ) ^ n := by
  have hp : 0 < (10 : ℝ) ^ n := by positivity
  have hf := Int.lt_floor_add_one ((10 : ℝ) ^ n * x)
  unfold pmaDecimalTruncation
  apply (lt_div_iff₀ hp).2
  rw [sub_mul, div_mul_cancel₀ _ hp.ne']
  linarith

theorem pma_decimal_truncation_isLUB (x : ℝ) (_hx : 0 < x) :
    IsLUB (Set.range (pmaDecimalTruncation x)) x := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact pma_decimal_truncation_le x n
  · intro y hy
    by_contra hxy
    have he : 0 < x - y := sub_pos.mpr (lt_of_not_ge hxy)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 10 : ℝ) ^ n < x - y :=
      exists_pow_lt_of_lt_one he (by norm_num)
    have hn' : 1 / (10 : ℝ) ^ n < x - y := by
      simpa [div_pow] using hn
    have hbound := hy (Set.mem_range_self n)
    have herror := pma_decimal_truncation_error x n
    linarith

def pmaDecimalInitial (x : ℝ) : ℕ := ⌊x⌋.toNat

theorem pma_decimal_initial_spec (x : ℝ) (hx : 0 < x) :
    (pmaDecimalInitial x : ℝ) ≤ x ∧ x < (pmaDecimalInitial x : ℝ) + 1 := by
  have hc : (pmaDecimalInitial x : ℝ) = (⌊x⌋ : ℝ) := by
    unfold pmaDecimalInitial
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx.le)]
  rw [hc]
  exact ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

theorem pma_decimal_initial_maximal (x : ℝ) (hx : 0 < x) (m : ℤ) :
    (m : ℝ) ≤ x ↔ m ≤ (pmaDecimalInitial x : ℤ) := by
  rw [pmaDecimalInitial, Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx.le)]
  exact Int.le_floor.symm

def pmaDecimalDigit (x : ℝ) (n : ℕ) : Fin 10 :=
  ⟨(⌊(10 : ℝ) ^ (n + 1) * x⌋ % 10).toNat,
    (Int.toNat_lt_of_ne_zero (by decide : (10 : ℕ) ≠ 0)).2
      (Int.emod_lt_of_pos _ (by norm_num))⟩

def pmaDecimalPartial (d₀ : ℕ) (d : ℕ → Fin 10) (n : ℕ) : ℝ :=
  d₀ + ∑ j ∈ Finset.range n, (d j : ℝ) / (10 : ℝ) ^ (j + 1)

theorem pma_decimal_digit_cast (x : ℝ) (n : ℕ) :
    (pmaDecimalDigit x n : ℤ) = ⌊(10 : ℝ) ^ (n + 1) * x⌋ % 10 := by
  change ((⌊(10 : ℝ) ^ (n + 1) * x⌋ % 10).toNat : ℤ) = _
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))

theorem pma_decimal_digit_recurrence (x : ℝ) (n : ℕ) :
    ⌊(10 : ℝ) ^ (n + 1) * x⌋ =
      10 * ⌊(10 : ℝ) ^ n * x⌋ + (pmaDecimalDigit x n : ℤ) := by
  have hf : ⌊(10 : ℝ) ^ (n + 1) * x⌋ / 10 = ⌊(10 : ℝ) ^ n * x⌋ := by
    calc
      ⌊(10 : ℝ) ^ (n + 1) * x⌋ / 10 = ⌊((10 : ℝ) ^ (n + 1) * x) / 10⌋ := by
        simpa using (Int.floor_div_natCast ((10 : ℝ) ^ (n + 1) * x) 10).symm
      _ = ⌊(10 : ℝ) ^ n * x⌋ := by
        congr 1
        rw [pow_succ]
        ring
  rw [pma_decimal_digit_cast, ← hf]
  exact (Int.mul_ediv_add_emod _ _).symm

theorem pma_decimal_truncation_succ (x : ℝ) (n : ℕ) :
    pmaDecimalTruncation x (n + 1) =
      pmaDecimalTruncation x n + (pmaDecimalDigit x n : ℝ) / (10 : ℝ) ^ (n + 1) := by
  unfold pmaDecimalTruncation
  rw [pma_decimal_digit_recurrence]
  push_cast
  rw [pow_succ]
  have hp : (10 : ℝ) ^ n ≠ 0 := by positivity
  field_simp

theorem pma_decimal_digit_spec (x : ℝ) (n : ℕ) :
    pmaDecimalTruncation x n + (pmaDecimalDigit x n : ℝ) / (10 : ℝ) ^ (n + 1) ≤ x ∧
    x < pmaDecimalTruncation x n + ((pmaDecimalDigit x n : ℝ) + 1) /
      (10 : ℝ) ^ (n + 1) := by
  constructor
  · rw [← pma_decimal_truncation_succ]
    exact pma_decimal_truncation_le x (n + 1)
  · have he := pma_decimal_truncation_error x (n + 1)
    rw [pma_decimal_truncation_succ] at he
    rw [add_div]
    linarith

theorem pma_decimal_digit_maximal (x : ℝ) (n : ℕ) (m : ℤ) :
    pmaDecimalTruncation x n + (m : ℝ) / (10 : ℝ) ^ (n + 1) ≤ x ↔
      m ≤ (pmaDecimalDigit x n : ℤ) := by
  have hd := pma_decimal_digit_spec x n
  have hp : 0 ≤ (10 : ℝ) ^ (n + 1) := by positivity
  constructor
  · intro hm
    by_contra hle
    have hsucc : (pmaDecimalDigit x n : ℤ) + 1 ≤ m := by omega
    have hc : (pmaDecimalDigit x n : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hsucc
    have ht := add_le_add (le_rfl : pmaDecimalTruncation x n ≤ pmaDecimalTruncation x n)
      (div_le_div_of_nonneg_right hc hp)
    exact (not_le_of_gt hd.2) (ht.trans hm)
  · intro hm
    have hc : (m : ℝ) ≤ (pmaDecimalDigit x n : ℝ) := by exact_mod_cast hm
    exact (add_le_add (le_rfl : pmaDecimalTruncation x n ≤ pmaDecimalTruncation x n)
      (div_le_div_of_nonneg_right hc hp)).trans hd.1

theorem pma_decimal_truncation_eq_partial (x : ℝ) (hx : 0 < x) (n : ℕ) :
    pmaDecimalTruncation x n =
      pmaDecimalPartial (pmaDecimalInitial x) (pmaDecimalDigit x) n := by
  induction n with
  | zero =>
    have hf : 0 ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx.le
    simp only [pmaDecimalTruncation, pow_zero, one_mul, div_one, pmaDecimalPartial,
      Finset.range_zero, Finset.sum_empty, add_zero, pmaDecimalInitial]
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hf]
  | succ n ih =>
    rw [pma_decimal_truncation_succ, ih]
    simp [pmaDecimalPartial, Finset.sum_range_succ, add_assoc]

theorem pma_positive_real_decimal_expansion (x : ℝ) (hx : 0 < x) :
    IsLUB (Set.range (pmaDecimalPartial (pmaDecimalInitial x) (pmaDecimalDigit x))) x := by
  convert pma_decimal_truncation_isLUB x hx using 1
  congr 1
  funext n
  exact (pma_decimal_truncation_eq_partial x hx n).symm

theorem pma_decimal_partial_succ (d₀ : ℕ) (d : ℕ → Fin 10) (n : ℕ) :
    pmaDecimalPartial d₀ d (n + 1) =
      pmaDecimalPartial d₀ d n + (d n : ℝ) / (10 : ℝ) ^ (n + 1) := by
  simp [pmaDecimalPartial, Finset.sum_range_succ, add_assoc]

theorem pma_decimal_partial_nonneg (d₀ : ℕ) (d : ℕ → Fin 10) (n : ℕ) :
    0 ≤ pmaDecimalPartial d₀ d n := by
  unfold pmaDecimalPartial
  positivity

theorem pma_decimal_partial_monotone (d₀ : ℕ) (d : ℕ → Fin 10) :
    Monotone (pmaDecimalPartial d₀ d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [pma_decimal_partial_succ]
  apply le_add_of_nonneg_right
  positivity

theorem pma_decimal_partial_bound (d₀ : ℕ) (d : ℕ → Fin 10) (n : ℕ) :
    pmaDecimalPartial d₀ d n ≤ d₀ + 1 - 1 / (10 : ℝ) ^ n := by
  induction n with
  | zero => simp [pmaDecimalPartial]
  | succ n ih =>
    have hd : (d n : ℝ) ≤ 9 := by
      exact_mod_cast (Nat.le_pred_of_lt (d n).isLt)
    calc
      pmaDecimalPartial d₀ d (n + 1) =
          pmaDecimalPartial d₀ d n + (d n : ℝ) / (10 : ℝ) ^ (n + 1) :=
        pma_decimal_partial_succ d₀ d n
      _ ≤ (d₀ + 1 - 1 / (10 : ℝ) ^ n) + 9 / (10 : ℝ) ^ (n + 1) :=
        add_le_add ih (div_le_div_of_nonneg_right hd (by positivity))
      _ = d₀ + 1 - 1 / (10 : ℝ) ^ (n + 1) := by
        rw [pow_succ]
        have hp : (10 : ℝ) ^ n ≠ 0 := by positivity
        field_simp
        ring

theorem pma_decimal_partials_bounded (d₀ : ℕ) (d : ℕ → Fin 10) :
    BddAbove (Set.range (pmaDecimalPartial d₀ d)) := by
  refine ⟨d₀ + 1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (pma_decimal_partial_bound d₀ d n).trans (sub_le_self _ (by positivity))

def pmaDecimalValue (d₀ : ℕ) (d : ℕ → Fin 10) : ℝ :=
  sSup (Set.range (pmaDecimalPartial d₀ d))

theorem pma_decimal_value_isLUB (d₀ : ℕ) (d : ℕ → Fin 10) :
    IsLUB (Set.range (pmaDecimalPartial d₀ d)) (pmaDecimalValue d₀ d) :=
  isLUB_csSup (Set.range_nonempty _) (pma_decimal_partials_bounded d₀ d)

theorem pma_decimal_value_unique (d₀ : ℕ) (d : ℕ → Fin 10) :
    ∃! x : ℝ, IsLUB (Set.range (pmaDecimalPartial d₀ d)) x := by
  exact ⟨pmaDecimalValue d₀ d, pma_decimal_value_isLUB d₀ d,
    fun _ hx => hx.unique (pma_decimal_value_isLUB d₀ d)⟩

theorem pma_decimal_value_bounds (d₀ : ℕ) (d : ℕ → Fin 10) :
    (d₀ : ℝ) ≤ pmaDecimalValue d₀ d ∧ pmaDecimalValue d₀ d ≤ d₀ + 1 := by
  have h := pma_decimal_value_isLUB d₀ d
  constructor
  · simpa [pmaDecimalPartial] using h.1 (Set.mem_range_self 0)
  · apply h.2
    rintro _ ⟨n, rfl⟩
    exact (pma_decimal_partial_bound d₀ d n).trans (sub_le_self _ (by positivity))

theorem pma_decimal_value_of_positive_real (x : ℝ) (hx : 0 < x) :
    pmaDecimalValue (pmaDecimalInitial x) (pmaDecimalDigit x) = x :=
  (pma_decimal_value_isLUB _ _).unique (pma_positive_real_decimal_expansion x hx)

end

/-! ### PMA-1.23: the extended reals, the order, and the stated infinity conventions. -/

abbrev PMAExtendedReal := EReal

theorem pma_extended_real_cases (x : PMAExtendedReal) :
    x = ⊥ ∨ (∃ r : ℝ, x = r) ∨ x = ⊤ := by
  induction x using EReal.rec with
  | bot => exact Or.inl rfl
  | coe r => exact Or.inr (Or.inl ⟨r, rfl⟩)
  | top => exact Or.inr (Or.inr rfl)

theorem pma_extended_real_order (x : ℝ) :
    (⊥ : PMAExtendedReal) < x ∧ (x : PMAExtendedReal) < ⊤ :=
  ⟨EReal.bot_lt_coe x, EReal.coe_lt_top x⟩

theorem pma_extended_real_arithmetic (x : ℝ) :
    (x : PMAExtendedReal) + ⊤ = ⊤ ∧
    (x : PMAExtendedReal) + ⊥ = ⊥ ∧
    (x : PMAExtendedReal) - ⊤ = ⊥ ∧
    (x : PMAExtendedReal) / ⊤ = 0 ∧
    (x : PMAExtendedReal) / ⊥ = 0 ∧
    (0 < x → (x : PMAExtendedReal) * ⊤ = ⊤ ∧
      (x : PMAExtendedReal) * ⊥ = ⊥) ∧
    (x < 0 → (x : PMAExtendedReal) * ⊤ = ⊥ ∧
      (x : PMAExtendedReal) * ⊥ = ⊤) := by
  refine ⟨EReal.coe_add_top x, EReal.add_bot _, EReal.sub_top _,
    EReal.div_top, EReal.div_bot, ?_, ?_⟩
  · intro hx
    exact ⟨EReal.coe_mul_top_of_pos hx, EReal.coe_mul_bot_of_pos hx⟩
  · intro hx
    exact ⟨EReal.coe_mul_top_of_neg hx, EReal.coe_mul_bot_of_neg hx⟩

theorem pma_extended_real_completeness (E : Set PMAExtendedReal) (_hE : E.Nonempty) :
    (∃ a, IsLUB E a) ∧ (∃ a, IsGLB E a) :=
  ⟨⟨sSup E, isLUB_sSup E⟩, ⟨sInf E, isGLB_sInf E⟩⟩

theorem pma_extended_sup_of_unbounded (E : Set ℝ) (hE : E.Nonempty)
    (h : ¬ BddAbove E) : IsLUB ((fun x : ℝ => (x : PMAExtendedReal)) '' E) ⊤ := by
  refine ⟨fun _ _ => le_top, ?_⟩
  intro z hz
  induction z using EReal.rec with
  | bot =>
    obtain ⟨r, hr⟩ := hE
    exact False.elim ((not_le_of_gt (EReal.bot_lt_coe r))
      (hz (Set.mem_image_of_mem _ hr)))
  | coe r =>
    exact False.elim (h ⟨r, fun y hy =>
      EReal.coe_le_coe_iff.mp (hz (Set.mem_image_of_mem _ hy))⟩)
  | top => exact le_rfl

theorem pma_extended_inf_of_unbounded (E : Set ℝ) (hE : E.Nonempty)
    (h : ¬ BddBelow E) : IsGLB ((fun x : ℝ => (x : PMAExtendedReal)) '' E) ⊥ := by
  refine ⟨fun _ _ => bot_le, ?_⟩
  intro z hz
  induction z using EReal.rec with
  | bot => exact le_rfl
  | coe r =>
    exact False.elim (h ⟨r, fun y hy =>
      EReal.coe_le_coe_iff.mp (hz (Set.mem_image_of_mem _ hy))⟩)
  | top =>
    obtain ⟨r, hr⟩ := hE
    exact False.elim ((not_le_of_gt (EReal.coe_lt_top r))
      (hz (Set.mem_image_of_mem _ hr)))

theorem pma_extended_real_not_field :
    ¬ (∀ x : PMAExtendedReal, ∃ y, x + y = 0) := by
  intro h
  obtain ⟨y, hy⟩ := h ⊤
  induction y using EReal.rec <;> simp at hy

/-! ### PMA-1.24: Mathlib's complex structure is the real ordered-pair construction. -/

def pmaComplexPair (a b : ℝ) : ℂ := ⟨a, b⟩

theorem pma_complex_pair_exhaustive (z : ℂ) : ∃ a b : ℝ, z = pmaComplexPair a b :=
  ⟨z.re, z.im, rfl⟩

theorem pma_complex_pair_eq (a b c d : ℝ) :
    pmaComplexPair a b = pmaComplexPair c d ↔ a = c ∧ b = d :=
  Complex.ext_iff

theorem pma_complex_pair_add (a b c d : ℝ) :
    pmaComplexPair a b + pmaComplexPair c d = pmaComplexPair (a + c) (b + d) := rfl

theorem pma_complex_pair_mul (a b c d : ℝ) :
    pmaComplexPair a b * pmaComplexPair c d =
      pmaComplexPair (a * c - b * d) (a * d + b * c) := rfl

end Rudin.PMA.Chapter01
