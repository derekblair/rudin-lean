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


end Rudin.PMA.Chapter01
