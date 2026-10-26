import Rudin.PMA.Chapter11.Geometry

/-!
# PMA 11.6(b): the Stieltjes example and its endpoint conventions

The one-factor product measure identifies the real line with the Euclidean
space `Fin 1 → ℝ` used by the elementary-set API. The geometric interval
formula below verifies this identification directly.
-/

noncomputable section
open Set MeasureTheory Function
open scoped ENNReal Topology

namespace Rudin.PMA.Chapter11

instance stieltjesMeasure_isLocallyFinite {α : ℝ → ℝ} (hα : Monotone α) :
    IsLocallyFiniteMeasure (stieltjesMeasure α hα) := by
  unfold stieltjesMeasure
  infer_instance

/-- 11.6(b), represented on one-dimensional Euclidean space. -/
def stieltjesEuclideanMeasure (α : ℝ → ℝ) (hα : Monotone α) : Measure (Fin 1 → ℝ) :=
  Measure.pi (fun _ : Fin 1 => stieltjesMeasure α hα)

instance stieltjesEuclideanMeasure_isLocallyFinite {α : ℝ → ℝ} (hα : Monotone α) :
    IsLocallyFiniteMeasure (stieltjesEuclideanMeasure α hα) := by
  unfold stieltjesEuclideanMeasure
  infer_instance

/-- The Euclidean representation has precisely the same interval values as the
Stieltjes measure on `ℝ`; all four endpoint choices are retained. -/
theorem stieltjesEuclideanMeasure_interval {α : ℝ → ℝ} (hα : Monotone α)
    (a b : ℝ) (l r : Bool) :
    stieltjesEuclideanMeasure α hα
      (intervalSet (fun _ => a) (fun _ => b) (fun _ => l) (fun _ => r)) =
      stieltjesMeasure α hα (axisInterval a b l r) := by
  rw [stieltjesEuclideanMeasure, intervalSet, Measure.pi_pi]
  simp

/-- 11.6(b)'s literal real-valued formulas for nondegenerate intervals. The
strict endpoint hypothesis is necessary for the untruncated open-interval
formula at a jump, as explained beside `pma11_6b_interval_formulas`. -/
theorem pma11_6b_real_interval_formulas {α : ℝ → ℝ} (hα : Monotone α)
    {a b : ℝ} (hab : a < b) :
    (stieltjesMeasure α hα (Ico a b)).toReal = leftLim α b - leftLim α a ∧
    (stieltjesMeasure α hα (Icc a b)).toReal = rightLim α b - leftLim α a ∧
    (stieltjesMeasure α hα (Ioc a b)).toReal = rightLim α b - rightLim α a ∧
    (stieltjesMeasure α hα (Ioo a b)).toReal = leftLim α b - rightLim α a := by
  obtain ⟨hco, hcc, hoc, hoo⟩ := pma11_6b_interval_formulas hα a b
  rw [hco, hcc, hoc, hoo]
  exact ⟨ENNReal.toReal_ofReal (sub_nonneg.mpr (hα.leftLim hab.le)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hα.leftLim_le_rightLim hab.le)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hα.rightLim hab.le)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (hα.rightLim_le_leftLim hab))⟩

/-- The closed degenerate interval records the jump; the other three degenerate
intervals are empty. This makes explicit the necessary correction to 11.6(b)
when the degenerate intervals allowed in 11.4 are used. -/
theorem pma11_6b_degenerate_intervals {α : ℝ → ℝ} (hα : Monotone α) (a : ℝ) :
    (stieltjesMeasure α hα (Icc a a)).toReal = rightLim α a - leftLim α a ∧
    stieltjesMeasure α hα (Ico a a) = 0 ∧
    stieltjesMeasure α hα (Ioc a a) = 0 ∧
    stieltjesMeasure α hα (Ioo a a) = 0 := by
  refine ⟨?_, by simp, by simp, by simp⟩
  rw [(pma11_6b_interval_formulas hα a a).2.1]
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (hα.leftLim_le_rightLim le_rfl))

/-- Finite additivity of the Stieltjes example on elementary sets. -/
theorem pma11_6b_additive {α : ℝ → ℝ} (hα : Monotone α)
    {A B : Set (Fin 1 → ℝ)} (_hA : IsElementary A) (hB : IsElementary B)
    (hd : Disjoint A B) :
    stieltjesEuclideanMeasure α hα (A ∪ B) =
      stieltjesEuclideanMeasure α hα A + stieltjesEuclideanMeasure α hα B :=
  measure_union hd hB.measurableSet

end Rudin.PMA.Chapter11
