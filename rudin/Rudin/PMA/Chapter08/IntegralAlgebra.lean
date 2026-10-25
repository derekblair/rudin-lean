import Rudin.PMA.Chapter07.Calculus

set_option autoImplicit false
noncomputable section
open Set

namespace Rudin.PMA.Chapter08
open Chapter06

theorem native_complex_integrable_mul {f g : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexRSIntegrable f id a b) (hg : ComplexRSIntegrable g id a b) :
    ComplexRSIntegrable (fun x => f x * g x) id a b := by
  have hrr := rsIntegrable_mul hf.1 hg.1
  have hii := rsIntegrable_mul hf.2 hg.2
  have hri := rsIntegrable_mul hf.1 hg.2
  have hir := rsIntegrable_mul hf.2 hg.1
  constructor
  · simpa only [Complex.mul_re, sub_eq_add_neg, neg_one_mul] using
      (rsIntegrable_add hrr (rsIntegrable_const_mul hii (-1)).1).1
  · exact (rsIntegrable_add hri hir).1

theorem native_complex_integrable_star {f : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexRSIntegrable f id a b) :
    ComplexRSIntegrable (fun x => star (f x)) id a b := by
  change ComplexRSIntegrable (fun x => (starRingEnd ℂ) (f x)) id a b
  exact ⟨hf.1, by simpa only [Complex.conj_im, neg_one_mul] using
    (rsIntegrable_const_mul hf.2 (-1)).1⟩

end Rudin.PMA.Chapter08
