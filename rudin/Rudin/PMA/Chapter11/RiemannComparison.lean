import Rudin.PMA.Chapter11
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# PMA 11.33: the attached fundamental theorems

The two assertions following the proof of 11.33 are established here for the
Lebesgue integral. The numbered comparison theorem itself remains open: the
Chapter 6 native closed-cell Darboux integrability predicate has not yet been
connected to a.e. continuity or the measure integral. In particular this file
does not replace that predicate by `IntervalIntegrable`, which would change
11.33(b) to a false assertion.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Rudin.PMA.Chapter11.SecondHalf

/-- The assertion following 11.33: an indefinite Lebesgue integral has derivative
equal to its integrand almost everywhere. Endpoint inclusion is immaterial
because singleton sets have Lebesgue measure zero. -/
theorem pma11_33_indefinite_integral {a b : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b) :
    ∀ᵐ x ∂volume, x ∈ Icc a b →
      HasDerivAt (fun y => ∫ t in a..y, f t) (f x) x := by
  filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxab
  apply hx (by simpa [uIcc_of_le hab] using hxab) a
  simp [hab]

/-- The converse assertion following 11.33. The interval-relative derivative
is required at every point, including one-sided endpoint derivatives, while
integrability is the only regularity hypothesis on the derivative. -/
theorem pma11_33_integral_derivative {a b : ℝ} {F F' : ℝ → ℝ}
    (hab : a ≤ b)
    (hF : ∀ x ∈ Icc a b, HasDerivWithinAt F (F' x) (Icc a b) x)
    (hint : IntervalIntegrable F' volume a b) :
    ∀ x ∈ Icc a b, F x - F a = ∫ t in a..x, F' t := by
  intro x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1
  · have hc : ContinuousOn F (Icc a b) := fun y hy => (hF y hy).continuousWithinAt
    exact hc.mono (Icc_subset_Icc_right hx.2)
  · intro y hy
    exact (hF y ⟨hy.1.le, hy.2.le.trans hx.2⟩).hasDerivAt
      (Icc_mem_nhds hy.1 (hy.2.trans_le hx.2))
  · exact hint.mono_set (by
      simpa [uIcc_of_le hab, uIcc_of_le hx.1] using (Icc_subset_Icc_right hx.2))

end Rudin.PMA.Chapter11.SecondHalf
