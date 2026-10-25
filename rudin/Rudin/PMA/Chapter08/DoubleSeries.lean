import Rudin.PMA.Chapter03

set_option autoImplicit false

noncomputable section
open scoped BigOperators
open Filter Topology

namespace Rudin.PMA.Chapter08

/-! ### PMA-8.3: Interchanging the two sums of an absolutely convergent double series.

Internal indices `i, j : ℕ` denote the source's indices `i+1, j+1`.
The hypotheses and conclusions use ordered partial sums from Chapter 3.
In particular, the conclusion supplies all inner sums and both outer sums;
an equality between potentially undefined sums is not substituted for existence.
-/

def pma8_3_contract : Prop :=
  ∀ (a : ℕ → ℕ → ℂ) (b : ℕ → ℝ),
    (∀ i, Chapter03.SeriesHasSum (fun j => ‖a i j‖) (b i)) →
    Chapter03.SeriesConverges b →
    ∃ (rows columns : ℕ → ℂ) (s : ℂ),
      (∀ i, Chapter03.SeriesHasSum (a i) (rows i)) ∧
      (∀ j, Chapter03.SeriesHasSum (fun i => a i j) (columns j)) ∧
      Chapter03.SeriesHasSum rows s ∧ Chapter03.SeriesHasSum columns s

/-- The source's ordered absolute row sums and convergent series of row sums
imply absolute summability on the entire product index set. -/
theorem doubleSeries_summable_norm (a : ℕ → ℕ → ℂ) (b : ℕ → ℝ)
    (hrows : ∀ i, Chapter03.SeriesHasSum (fun j => ‖a i j‖) (b i))
    (hb : Chapter03.SeriesConverges b) :
    Summable (fun p : ℕ × ℕ => ‖a p.1 p.2‖) := by
  have hrows' : ∀ i, HasSum (fun j => ‖a i j‖) (b i) := fun i =>
    (hasSum_iff_tendsto_nat_of_nonneg (fun j => norm_nonneg (a i j)) (b i)).mpr
      (hrows i)
  have hbnonneg : ∀ i, 0 ≤ b i := by
    intro i
    rw [← (hrows' i).tsum_eq]
    exact tsum_nonneg fun j => norm_nonneg (a i j)
  have hb' : Summable b :=
    (Chapter03.seriesConverges_iff_summable_nonneg hbnonneg).mp hb
  apply (summable_prod_of_nonneg (fun p => norm_nonneg (a p.1 p.2))).mpr
  refine ⟨fun i => (hrows' i).summable, ?_⟩
  have heq : (fun i => ∑' j, ‖a i j‖) = b :=
    funext fun i => (hrows' i).tsum_eq
  rw [heq]
  exact hb'

theorem pma8_3 : pma8_3_contract := by
  intro a b hrows hb
  have hsum : Summable (Function.uncurry a) :=
    (doubleSeries_summable_norm a b hrows hb).of_norm
  refine ⟨(fun i => ∑' j, a i j), (fun j => ∑' i, a i j),
    (∑' i, ∑' j, a i j), ?_, ?_, ?_, ?_⟩
  · intro i
    exact (hsum.prod_factor i).hasSum.tendsto_sum_nat
  · intro j
    exact (hsum.prod_symm.prod_factor j).hasSum.tendsto_sum_nat
  · exact hsum.prod.hasSum.tendsto_sum_nat
  · have heq : (∑' j, ∑' i, a i j) = ∑' i, ∑' j, a i j := hsum.tsum_comm
    rw [← heq]
    exact hsum.prod_symm.prod.hasSum.tendsto_sum_nat

end Rudin.PMA.Chapter08
