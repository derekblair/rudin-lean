import Rudin.PMA.Chapter06.Integrability
import Rudin.PMA.Chapter11

/-! Native Chapter 6 partition step functions for the comparison in PMA 11.33.
Half-open cells partition `(a,b]`; changing finitely many endpoints does not
change their Lebesgue integrals. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter11.SecondHalf
open Rudin.PMA.Chapter06

variable {a b : ℝ}

def partitionStep (P : Partition a b) (c : Fin P.n → ℝ) (x : ℝ) : ℝ :=
  ∑ i, (Ioc (P.point i.castSucc) (P.point i.succ)).indicator (fun _ => c i) x

theorem partition_cell_exists (P : Partition a b) {x : ℝ} (hx : x ∈ Ioc a b) :
    ∃ i : Fin P.n, x ∈ Ioc (P.point i.castSucc) (P.point i.succ) := by
  have h : ∀ j : Fin (P.n + 1), x ∈ Ioc a (P.point j) →
      ∃ i : Fin P.n, x ∈ Ioc (P.point i.castSucc) (P.point i.succ) := by
    intro j
    induction j using Fin.induction with
    | zero => simp [P.left]
    | succ i ih =>
      intro hj
      by_cases hle : x ≤ P.point i.castSucc
      · exact ih ⟨hj.1, hle⟩
      · exact ⟨i, lt_of_not_ge hle, hj.2⟩
  exact h (Fin.last P.n) (by simpa [P.right] using hx)

theorem partition_cell_unique (P : Partition a b) {x : ℝ} {i j : Fin P.n}
    (hi : x ∈ Ioc (P.point i.castSucc) (P.point i.succ))
    (hj : x ∈ Ioc (P.point j.castSucc) (P.point j.succ)) : i = j := by
  apply le_antisymm
  · by_contra h
    have hji : j.succ ≤ i.castSucc := by
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt (lt_of_not_ge h)
    exact (not_lt_of_ge (hj.2.trans (P.mono hji))) hi.1
  · by_contra h
    have hij : i.succ ≤ j.castSucc := by
      simp only [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt (lt_of_not_ge h)
    exact (not_lt_of_ge (hi.2.trans (P.mono hij))) hj.1

theorem partitionStep_eq (P : Partition a b) (c : Fin P.n → ℝ)
    {x : ℝ} {i : Fin P.n} (hi : x ∈ Ioc (P.point i.castSucc) (P.point i.succ)) :
    partitionStep P c x = c i := by
  unfold partitionStep
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hj : x ∉ Ioc (P.point j.castSucc) (P.point j.succ) := by
      intro hj
      exact hji (partition_cell_unique P hj hi)
    simp [hj]
  · simp

theorem partitionStep_measurable (P : Partition a b) (c : Fin P.n → ℝ) :
    Measurable (partitionStep P c) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator measurableSet_Ioc)

theorem partitionStep_integrable (P : Partition a b) (c : Fin P.n → ℝ) :
    Integrable (partitionStep P c) volume := by
  apply integrable_finsetSum
  intro i _
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (integrableOn_const (μ := volume) (C := c i)
      (s := Ioc (P.point i.castSucc) (P.point i.succ)) (by simp) (by simp))

theorem partitionStep_integral (P : Partition a b) (c : Fin P.n → ℝ) :
    (∫ x, partitionStep P c x) = ∑ i, c i * P.weight id i := by
  unfold partitionStep
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator_const _ measurableSet_Ioc]
    simp [Real.volume_real_Ioc, smul_eq_mul, Partition.weight, mul_comm,
      max_eq_left (sub_nonneg.mpr (P.cell_order i))]
  · intro i _
    exact (integrable_indicator_iff measurableSet_Ioc).mpr
      (integrableOn_const (μ := volume) (C := c i)
        (s := Ioc (P.point i.castSucc) (P.point i.succ)) (by simp) (by simp))

def lowerStep (f : ℝ → ℝ) (P : Partition a b) := partitionStep P (cellLower f P)
def upperStep (f : ℝ → ℝ) (P : Partition a b) := partitionStep P (cellUpper f P)

theorem lowerStep_integral (f : ℝ → ℝ) (P : Partition a b) :
    (∫ x, lowerStep f P x) = lowerSum f id P := partitionStep_integral P _

theorem upperStep_integral (f : ℝ → ℝ) (P : Partition a b) :
    (∫ x, upperStep f P x) = upperSum f id P := partitionStep_integral P _

theorem step_bounds {f : ℝ → ℝ} (hf : BoundedOn f a b)
    (P : Partition a b) {x : ℝ} (hx : x ∈ Ioc a b) :
    lowerStep f P x ≤ f x ∧ f x ≤ upperStep f P x := by
  obtain ⟨i, hi⟩ := partition_cell_exists P hx
  simp only [lowerStep, upperStep, partitionStep_eq P _ hi]
  exact ⟨cellLower_le_value hf P i ⟨hi.1.le, hi.2⟩,
    value_le_cellUpper hf P i ⟨hi.1.le, hi.2⟩⟩

end Rudin.PMA.Chapter11.SecondHalf
