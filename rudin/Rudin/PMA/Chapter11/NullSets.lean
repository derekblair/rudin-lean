import Rudin.PMA.Chapter11.Foundations
import Rudin.PMA.Chapter02

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace Rudin.PMA.Chapter11

/-- 11.11(e): the null sets of any outer measure form a sigma-ring. -/
theorem pma11_11_null_sigmaRing {X : Type*} (μ : OuterMeasure X) :
    SigmaRing {A : Set X | μ A = 0} where
  union_mem := fun _ _ hA hB => measure_union_null hA hB
  sdiff_mem := fun _ _ hA _ => measure_mono_null sdiff_subset hA
  iUnion_mem := fun _A hA => measure_iUnion_null hA

/-- 11.11(f): countable subsets of positive-dimensional Euclidean space are
Lebesgue null. Positivity of dimension makes explicit the book's convention
`p ≥ 1`; zero-dimensional Euclidean volume assigns mass one to its point. -/
theorem pma11_11_countable_null (p : ℕ) [NeZero p] {A : Set (Fin p → ℝ)}
    (hA : A.Countable) : volume A = 0 := hA.measure_zero volume

/-- 11.11(f): an uncountable perfect null set, reusing the completed construction
of the same Cantor set from 2.44. -/
theorem pma11_11_cantor : Perfect cantorSet ∧
    ¬ cantorSet.Countable ∧ volume cantorSet = 0 :=
  ⟨Chapter02.cantor_perfect,
    Chapter02.perfect_not_countable Chapter02.cantor_perfect ⟨0, zero_mem_cantorSet⟩,
    Chapter02.cantor_volume_zero⟩

private theorem volume_left_third (A : Set ℝ) :
    volume ((fun x : ℝ => x / 3) '' A) = ENNReal.ofReal (1 / 3 : ℝ) * volume A := by
  have he : (fun x : ℝ => x / 3) '' A = (fun x : ℝ => 3 * x) ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change 3 * (y / 3) ∈ A
      convert hy using 1; ring
    · intro hx
      exact ⟨3 * x, hx, by ring⟩
  rw [he, Real.volume_preimage_mul_left (by norm_num)]
  norm_num

private theorem volume_right_third (A : Set ℝ) :
    volume ((fun x : ℝ => (2 + x) / 3) '' A) = ENNReal.ofReal (1 / 3 : ℝ) * volume A := by
  have he : (fun x : ℝ => (2 + x) / 3) '' A =
      (fun x : ℝ => 3 * x) ⁻¹' ((fun x : ℝ => -2 + x) ⁻¹' A) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -2 + 3 * ((2 + y) / 3) ∈ A
      convert hy using 1; ring
    · intro hx
      exact ⟨-2 + 3 * x, hx, by ring⟩
  rw [he, Real.volume_preimage_mul_left (by norm_num), measure_preimage_add]
  norm_num

/-- 11.11(f)'s displayed stage-volume formula. -/
theorem pma11_11_cantor_stage_volume (n : ℕ) :
    volume (preCantorSet n) = (ENNReal.ofReal (2 / 3 : ℝ)) ^ n := by
  induction n with
  | zero => simp [Real.volume_Icc]
  | succ n ih =>
    have hd : Disjoint ((fun x : ℝ => x / 3) '' preCantorSet n)
        ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) := by
      apply disjoint_left.mpr
      rintro x ⟨a, ha, rfl⟩ ⟨b, hb, he⟩
      have ha' := preCantorSet_subset_unitInterval ha
      have hb' := preCantorSet_subset_unitInterval hb
      linarith [ha'.2, hb'.1]
    have hm : MeasurableSet ((fun x : ℝ => (2 + x) / 3) '' preCantorSet n) := by
      have hcomp := (isCompact_Icc.of_isClosed_subset (isClosed_preCantorSet n)
        preCantorSet_subset_unitInterval).image (by fun_prop : Continuous (fun x : ℝ => (2 + x) / 3))
      exact hcomp.measurableSet
    rw [preCantorSet_succ, measure_union hd hm, volume_left_third, volume_right_third, ih]
    rw [← add_mul, pow_succ]
    have hsum : ENNReal.ofReal (1 / 3 : ℝ) + ENNReal.ofReal (1 / 3 : ℝ) =
        ENNReal.ofReal (2 / 3 : ℝ) := by
      rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    rw [hsum, mul_comm]

end Rudin.PMA.Chapter11
