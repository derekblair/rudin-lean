import Rudin.PMA.Chapter11.LebesgueCriterion

/-!
# PMA 11.33: the forward Lebesgue criterion

A sequence of native Chapter 6 partitions with summable upper/lower gaps
has pointwise gaps tending to zero almost everywhere. Off the countable set
of partition endpoints, each gap controls oscillation on a neighborhood.
No measurability of the original Riemann-integrable function is assumed.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators

namespace Rudin.PMA.Chapter11.SecondHalf
open Rudin.PMA.Chapter06

variable {a b : ℝ}

/-- Small closed-cell Darboux gaps give continuity away from partition endpoints. -/
theorem continuousAt_of_darboux_gaps {f : ℝ → ℝ} (hf : BoundedOn f a b)
    (P : ℕ → Partition a b) {x : ℝ} (hx : x ∈ Ioc a b)
    (hend : ∀ n, ∀ i : Fin ((P n).n + 1), x ≠ (P n).point i)
    (hgap : ∀ ε > 0, ∃ n, upperStep f (P n) x - lowerStep f (P n) x < ε) :
    ContinuousAt f x := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := hgap ε hε
  obtain ⟨i, hi⟩ := partition_cell_exists (P n) hx
  have hr : x < (P n).point i.succ := lt_of_le_of_ne hi.2 (hend n i.succ)
  let δ := min (x - (P n).point i.castSucc) ((P n).point i.succ - x)
  have hδ : 0 < δ := lt_min (sub_pos.mpr hi.1) (sub_pos.mpr hr)
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hy' : |y - x| < δ := by simpa only [Real.dist_eq] using hy
  have hyl := (abs_lt.mp hy').1
  have hyr := (abs_lt.mp hy').2
  have hycell : y ∈ (P n).cell i := by
    constructor
    · have hd : δ ≤ x - (P n).point i.castSucc := min_le_left _ _
      linarith
    · have hd : δ ≤ (P n).point i.succ - x := min_le_right _ _
      linarith
  have hxl := cellLower_le_value hf (P n) i ⟨hi.1.le, hi.2⟩
  have hxu := value_le_cellUpper hf (P n) i ⟨hi.1.le, hi.2⟩
  have hyl' := cellLower_le_value hf (P n) i hycell
  have hyu := value_le_cellUpper hf (P n) i hycell
  simp only [upperStep, lowerStep, partitionStep_eq (P n) _ hi] at hn
  rw [Real.dist_eq]
  apply abs_lt.mpr
  constructor <;> linarith

/-- Summable integral gaps force arbitrarily small pointwise gaps almost everywhere. -/
theorem ae_darboux_gaps_small {f : ℝ → ℝ} (hf : BoundedOn f a b)
    (P : ℕ → Partition a b)
    (hP : ∀ n, upperSum f id (P n) - lowerSum f id (P n) < (1 / 2 : ℝ) ^ n) :
    ∀ᵐ x ∂volume, ∀ ε > 0, ∃ n, upperStep f (P n) x - lowerStep f (P n) x < ε := by
  obtain ⟨M, hM⟩ := hf
  let gap (n : ℕ) (x : ℝ) := upperStep f (P n) x - lowerStep f (P n) x
  have hnonneg (n : ℕ) (x : ℝ) : 0 ≤ gap n x := (step_gap_bounds hM (P n) x).1
  have hmeas (n : ℕ) : Measurable (gap n) :=
    (partitionStep_measurable _ _).sub (partitionStep_measurable _ _)
  have hint (n : ℕ) : Integrable (gap n) volume :=
    (partitionStep_integrable _ _).sub (partitionStep_integrable _ _)
  have hlin (n : ℕ) : (∫⁻ x, ENNReal.ofReal (gap n x)) ≤ ENNReal.ofReal (1 / 2 : ℝ) ^ n := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ (hnonneg n))]
    have heq : (∫ x, gap n x) = upperSum f id (P n) - lowerSum f id (P n) := by
      change (∫ x, upperStep f (P n) x - lowerStep f (P n) x) = _
      have hu : Integrable (upperStep f (P n)) volume := partitionStep_integrable _ _
      have hl : Integrable (lowerStep f (P n)) volume := partitionStep_integrable _ _
      rw [integral_sub hu hl, upperStep_integral, lowerStep_integral]
    rw [heq, ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact ENNReal.ofReal_le_ofReal (hP n).le
  have hfinite : (∫⁻ x, ∑' n, ENNReal.ofReal (gap n x)) < ∞ := by
    rw [lintegral_tsum (fun n => (hmeas n).ennreal_ofReal.aemeasurable)]
    apply lt_of_le_of_lt (ENNReal.tsum_le_tsum hlin)
    rw [ENNReal.tsum_geometric]
    norm_num
  have hae := ae_lt_top (Measurable.tsum fun n => (hmeas n).ennreal_ofReal) hfinite.ne
  filter_upwards [hae] with x hx
  intro ε hε
  have ht := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne
  have he := ht.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal ε from by
    simpa using hε))
  obtain ⟨N, hN⟩ := eventually_atTop.mp he
  exact ⟨N, (ENNReal.ofReal_lt_ofReal_iff hε).mp (hN N le_rfl)⟩

/-- 11.33(b), forward implication, for the exact native closed-cell Darboux
integrability predicate from Chapter 6. -/
theorem pma11_33_ae_continuous_of_riemann {f : ℝ → ℝ} (hf : RIntegrable f a b) :
    ∀ᵐ x ∂volume.restrict (Icc a b), ContinuousWithinAt f (Icc a b) x := by
  have hp : ∀ n : ℕ, ∃ P : Partition a b,
      upperSum f id P - lowerSum f id P < (1 / 2 : ℝ) ^ n := by
    intro n
    exact (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf _ (by positivity)
  choose P hP using hp
  have hend : ∀ᵐ x ∂volume, ∀ n, ∀ i : Fin ((P n).n + 1), x ≠ (P n).point i := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro i
    simp [ae_iff]
  filter_upwards [ae_restrict_of_ae (ae_darboux_gaps_small hf.2.1 P hP),
    ae_restrict_of_ae hend, ae_restrict_mem measurableSet_Icc] with x hgap hxend hx
  have hxa : x ≠ a := by simpa only [(P 0).left] using hxend 0 0
  have hi : x ∈ Ioc a b := ⟨lt_of_le_of_ne hx.1 hxa.symm, hx.2⟩
  exact (continuousAt_of_darboux_gaps hf.2.1 P hi hxend hgap).continuousWithinAt

end Rudin.PMA.Chapter11.SecondHalf
