import Rudin.PMA.Chapter08.Trigonometric

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Rudin.PMA.Chapter08

/-! PMA 8.8 (pp.184–185): a complex polynomial of positive degree has a root.
The finite coefficient presentation is retained explicitly. -/

def coefficientPolynomial (a : ℕ → ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (n + 1), Polynomial.monomial k (a k)

theorem coefficientPolynomial_eval (a : ℕ → ℂ) (n : ℕ) (z : ℂ) :
    (coefficientPolynomial a n).eval z = ∑ k ∈ Finset.range (n + 1), a k * z ^ k := by
  simp [coefficientPolynomial, Polynomial.eval_finsetSum]

def pma8_8_contract : Prop :=
  ∀ (a : ℕ → ℂ) (n : ℕ), 1 ≤ n → a n ≠ 0 →
    ∃ z : ℂ, ∑ k ∈ Finset.range (n + 1), a k * z ^ k = 0

theorem pma8_8 : pma8_8_contract := by
  intro a n hn ha
  have hc : (coefficientPolynomial a n).coeff n = a n := by
    simp [coefficientPolynomial, Polynomial.coeff_monomial]
  have hd : 0 < (coefficientPolynomial a n).degree := by
    have hle := Polynomial.le_degree_of_ne_zero (hc ▸ ha)
    exact lt_of_lt_of_le (by exact_mod_cast hn) hle
  obtain ⟨z, hz⟩ := Complex.exists_root hd
  exact ⟨z, (coefficientPolynomial_eval a n z).symm.trans hz⟩

end Rudin.PMA.Chapter08
