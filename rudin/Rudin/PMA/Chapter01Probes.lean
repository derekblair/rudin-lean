import Rudin.PMA.Chapter01

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Rudin.PMA.Chapter01Probes

open Rudin.PMA.Chapter01

/-- The rational-gap hypotheses really have elements on both sides. -/
theorem rational_gap_nonvacuous :
    (1 : ℚ) ∈ rationalBelowSqrtTwo ∧ (2 : ℚ) ∈ rationalAboveSqrtTwo := by
  constructor <;> constructor <;> norm_num

/-- Replacing strict order by non-strict order breaks its defining contract. -/
theorem strict_order_rejects_reflexivity :
    ¬ OrderAxioms ((· ≤ ·) : ℚ → ℚ → Prop) := by
  intro h
  exact h.1 0 le_rfl

/-- Source bounds include their endpoints. -/
theorem bound_is_nonstrict : IsUpperBound ({1} : Set ℚ) 1 := by
  simp [IsUpperBound]

theorem proper_subset_irreflexive (A : Set ℚ) : ¬ IsProperSubset A A := by
  rintro ⟨_, x, hx, hnx⟩
  exact hnx hx

/-- The rational example refutes completeness, rather than only one candidate sup. -/
theorem rationals_fail_lub_property : ¬ HasLUBProperty ℚ := by
  intro h
  have hA : rationalBelowSqrtTwo.Nonempty := ⟨1, rational_gap_nonvacuous.1⟩
  exact pma1_9_rational_gap.2.2.1
    (h rationalBelowSqrtTwo hA pma1_9_rational_gap.1)

/-- Nonemptiness in the completeness property is necessary on the real line. -/
theorem empty_real_set_has_no_lub : ¬ ∃ a : ℝ, IsLUB (∅ : Set ℝ) a := by
  rintro ⟨a, ha⟩
  have h : a ≤ a - 1 := ha.2 (by simp [upperBounds])
  linarith

theorem dropping_nonempty_breaks_real_lub_property :
    ¬ (∀ E : Set ℝ, BddAbove E → ∃ a, IsLUB E a) := by
  intro h
  exact empty_real_set_has_no_lub (h ∅ ⟨0, by simp [upperBounds]⟩)

/-- Different membership behavior at the same rational supremum. -/
theorem rational_zero_boundary :
    (0 : ℚ) ∉ Set.Iio 0 ∧ (0 : ℚ) ∈ Set.Iic 0 := by simp

/-- The reciprocal example includes its supremum but excludes its infimum. -/
theorem reciprocal_membership_boundary :
    (1 : ℚ) ∈ positiveReciprocals ∧ (0 : ℚ) ∉ positiveReciprocals :=
  ⟨pma1_9_reciprocals.2.2.1, pma1_9_reciprocals.2.2.2⟩

theorem dropping_nonzero_breaks_cancellation :
    (0 : ℚ) * 1 = 0 * 2 ∧ (1 : ℚ) ≠ 2 := by norm_num

theorem inverse_order_direction :
    (0 : ℚ) < 1 ∧ (1 : ℚ) < 2 ∧ ¬ ((1 : ℚ)⁻¹ < (2 : ℚ)⁻¹) := by norm_num

/-- The source's unrestricted uniqueness sentence is false for even exponents. -/
theorem unrestricted_root_uniqueness_false : ¬ (∃! y : ℝ, y ^ 2 = 1) := by
  rintro ⟨y, _, huniq⟩
  have h1 : (1 : ℝ) = y := huniq 1 (by norm_num)
  have hm1 : (-1 : ℝ) = y := huniq (-1) (by norm_num)
  linarith

theorem conjugate_second_coordinate :
    pmaConjugate (pmaComplexPair 2 3) = pmaComplexPair 2 (-3) := rfl

/-- Concrete values distinguish Euclidean modulus from a coordinate/max norm. -/
theorem complex_modulus_345 : pmaComplexAbs (pmaComplexPair 3 4) = 5 := by
  norm_num [pmaComplexAbs, pmaComplexPair, Complex.normSq_mk]

theorem imaginary_unit_not_real_zero :
    pmaImaginaryUnit ≠ (0 : ℂ) ∧ pmaRealPart pmaImaginaryUnit = 0 := by
  change Complex.I ≠ 0 ∧ Complex.I.re = 0
  simp

theorem conjugated_singleton_sum :
    pmaComplexSum (fun _ : Fin 1 => pmaImaginaryUnit * pmaConjugate pmaImaginaryUnit) = 1 := by
  change (∑ _ : Fin 1, Complex.I * conj Complex.I) = 1
  simp

/-- The exact source Schwarz inequality normalizes to equality for one unit. -/
theorem schwarz_singleton_unit :
    pmaComplexAbs
      (pmaComplexSum (fun _ : Fin 1 => pmaImaginaryUnit * pmaConjugate pmaImaginaryUnit)) ^ 2 =
      (∑ _ : Fin 1, pmaComplexAbs pmaImaginaryUnit ^ 2) *
        (∑ _ : Fin 1, pmaComplexAbs pmaImaginaryUnit ^ 2) := by
  rw [conjugated_singleton_sum]
  change ‖(1 : ℂ)‖ ^ 2 = (∑ _ : Fin 1, ‖Complex.I‖ ^ 2) * (∑ _ : Fin 1, ‖Complex.I‖ ^ 2)
  simp

/-- Unsquared sums on the source's right side would give a false inequality. -/
theorem schwarz_squared_rhs_necessary :
    ¬ (pmaComplexAbs ((2 : ℂ) * pmaConjugate (2 : ℂ)) ^ 2 ≤
      pmaComplexAbs (2 : ℂ) * pmaComplexAbs (2 : ℂ)) := by
  norm_num [pma_complex_abs_eq_norm, pmaConjugate]

/-- Terminating decimals use the source's non-strict greedy convention. -/
theorem decimal_terminating_boundary :
    pmaDecimalTruncation (125 / 100 : ℝ) 2 = 125 / 100 ∧
    pmaDecimalDigit (125 / 100 : ℝ) 0 = 2 ∧
    pmaDecimalDigit (125 / 100 : ℝ) 1 = 5 ∧
    pmaDecimalDigit (125 / 100 : ℝ) 2 = 0 := by
  norm_num [pmaDecimalTruncation, pmaDecimalDigit]

/-- The real plane has the Euclidean norm, not the coordinate maximum norm. -/
theorem euclidean_modulus_345 :
    pmaEuclideanNorm (WithLp.toLp 2 (![3, 4] : Fin 2 → ℝ)) = 5 := by
  rw [pma_euclidean_norm_coordinates]
  norm_num [Fin.sum_univ_two]

/- Negation attempts are deliberately caught by `fail_if_success`: if routine
automation could prove one of these false negations, the probe itself fails. -/

theorem negation_attempt_rational_square (p : ℚ) : p ^ 2 ≠ 2 := by
  fail_if_success (have hbad : p ^ 2 = 2 := by aesop)
  exact pma1_1_no_rational_square p

theorem negation_attempt_positive_root (x : ℝ) (n : ℕ)
    (hx : 0 < x) (hn : 0 < n) : ∃! y : ℝ, 0 < y ∧ y ^ n = x := by
  fail_if_success (have hbad : ¬ (∃! y : ℝ, 0 < y ∧ y ^ n = x) := by aesop)
  exact pma_positive_nth_root x n hx hn

theorem negation_attempt_complex_triangle (z w : ℂ) :
    pmaComplexAbs (z + w) ≤ pmaComplexAbs z + pmaComplexAbs w := by
  fail_if_success (have hbad : pmaComplexAbs z + pmaComplexAbs w <
      pmaComplexAbs (z + w) := by aesop)
  exact (pma_complex_abs_properties z w).2.2.2.2.2

end Rudin.PMA.Chapter01Probes
