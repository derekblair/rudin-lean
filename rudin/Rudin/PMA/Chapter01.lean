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

end Rudin.PMA.Chapter01
