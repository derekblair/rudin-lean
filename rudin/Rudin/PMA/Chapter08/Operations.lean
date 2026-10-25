import Rudin.PMA.Chapter08.PowerSeries
import Rudin.PMA.Chapter07.Calculus

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Rudin.PMA.Chapter08

/-! Supplementary power-series operations requested in the task brief.
These support the power-series section and are not separately numbered items
in Rudin. Every series statement uses the ordered Chapter 3 convention.
-/

theorem represents_add {c d : ℕ → ℂ} {f g : ℝ → ℂ} {R : ℝ≥0∞}
    (hc : Represents c f R) (hd : Represents d g R) :
    Represents (fun n => c n + d n) (fun x => f x + g x) R := by
  intro x hx
  simpa only [smul_add] using
    (Chapter03.pma3_47 (fun n => x ^ n • c n) (fun n => x ^ n • d n)
      (f x) (g x) 0 (hc x hx) (hd x hx)).1

/-- Interior convergence supplies absolute convergence before multiplication. -/
theorem represents_summable_norm {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hf : Represents c f R) {x : ℝ}
    (hx : (‖x‖₊ : ℝ≥0∞) < R) : Summable (fun n => ‖x ^ n • c n‖) := by
  have hp := represents_hasFPowerSeries hR hf
  have hx' : x ∈ Metric.eball (0 : ℝ) (realSeries c).radius := by
    simpa [enorm_eq_nnnorm] using hx.trans_le hp.r_le
  simpa using (realSeries c).summable_norm_apply hx'

theorem represents_mul {c d : ℕ → ℂ} {f g : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hc : Represents c f R) (hd : Represents d g R) :
    Represents (Chapter03.CauchyProduct c d) (fun x => f x * g x) R := by
  intro x hx
  have habs : Chapter03.SeriesAbsolutelyConverges (fun n => x ^ n • c n) :=
    (Chapter03.seriesAbsolutelyConverges_iff_summable_norm _).mpr
      (represents_summable_norm hR hc hx)
  have hprod := Chapter03.pma3_50 (fun n => x ^ n • c n) (fun n => x ^ n • d n)
    (f x) (g x) (hc x hx) (hd x hx) (Or.inl habs)
  have heq : (fun n => x ^ n • Chapter03.CauchyProduct c d n) =
      Chapter03.CauchyProduct (fun n => x ^ n • c n) (fun n => x ^ n • d n) := by
    simpa only [realSeries_term_reference] using
      Chapter03.powerSeriesTerms_cauchyProduct c d (x : ℂ)
  rw [← heq] at hprod
  exact hprod

/-- Each monomial is integrable in the native Chapter 6 complex theory. -/
theorem powerSeries_term_integrable (c : ℂ) (n : ℕ) {α : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hα : MonotoneOn α (Icc a b)) :
    Chapter06.ComplexRSIntegrable (fun x : ℝ => x ^ n • c) α a b := by
  constructor
  · exact Chapter06.rsIntegrable_of_continuousOn hab (by fun_prop) hα
  · exact Chapter06.rsIntegrable_of_continuousOn hab (by fun_prop) hα

/-- Uniform convergence on a compact interior interval permits native complex
Stieltjes integration term by term, for every monotone integrator. -/
theorem powerSeries_stieltjes_integral {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hf : Represents c f R) {α : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    (hI : Icc a b ⊆ Metric.eball (0 : ℝ) R) :
    Chapter06.ComplexRSIntegrable f α a b ∧
      Chapter03.SeriesHasSum
        (fun n => Chapter06.ComplexRSIntegral (fun x : ℝ => x ^ n • c n) α a b)
        (Chapter06.ComplexRSIntegral f α a b) := by
  have hp := represents_hasFPowerSeries hR hf
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    (hp.tendstoLocallyUniformlyOn.mono hI)
  apply Chapter07.pma7_16.2 (fun n x => x ^ n • c n) f α a b hab hα
    (fun n => powerSeries_term_integrable (c n) n hab hα)
  simpa [FormalMultilinearSeries.partialSum, Chapter03.PartialSums] using hu

/-- Ordinary integration is the identity-integrator specialization of the
native Stieltjes statement. -/
theorem powerSeries_integral {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hf : Represents c f R) {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ Metric.eball (0 : ℝ) R) :
    Chapter06.ComplexRSIntegrable f id a b ∧
      Chapter03.SeriesHasSum
        (fun n => Chapter06.ComplexRSIntegral (fun x : ℝ => x ^ n • c n) id a b)
        (Chapter06.ComplexRSIntegral f id a b) :=
  powerSeries_stieltjes_integral hR hf hab (fun _ _ _ _ h => h) hI

/-- The native integral of a complex coefficient times a real monomial. -/
theorem powerSeries_term_integral (c : ℂ) (n : ℕ) {a b : ℝ} (hab : a ≤ b) :
    Chapter06.ComplexRSIntegral (fun x : ℝ => x ^ n • c) id a b =
      ((b ^ (n + 1) - a ^ (n + 1)) / (n + 1 : ℕ)) • c := by
  rcases hab.eq_or_lt with rfl | hab
  · rw [Chapter06.ComplexRSIntegral, (Chapter06.rsIntegral_same_endpoint _ _ _).2,
      (Chapter06.rsIntegral_same_endpoint _ _ _).2]
    simp
  · have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hd : ∀ x : ℝ,
        HasDerivAt (fun t : ℝ => (t ^ (n + 1) / (n + 1 : ℕ)) • c) (x ^ n • c) x := by
      intro x
      have hdreal : HasDerivAt (fun t : ℝ => t ^ (n + 1) / (n + 1 : ℕ)) (x ^ n) x := by
        simpa only [Nat.add_sub_cancel, mul_div_cancel_left₀ (x ^ n) hn] using
          (hasDerivAt_pow (n + 1) x).div_const ((n + 1 : ℕ) : ℝ)
      exact hdreal.smul_const c
    have hint := Chapter06.complexRSIntegral_ftc hab
      (fun x _ => (hd x).hasDerivWithinAt)
      (powerSeries_term_integrable c n hab.le (fun _ _ _ _ h => h))
    simpa only [← sub_smul, ← sub_div] using hint

/-- The ordinary integral equals the ordered series with the familiar
integrated coefficients, including a degenerate interval. -/
theorem powerSeries_integral_explicit {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hf : Represents c f R) {a b : ℝ} (hab : a ≤ b)
    (hI : Icc a b ⊆ Metric.eball (0 : ℝ) R) :
    Chapter06.ComplexRSIntegrable f id a b ∧
      Chapter03.SeriesHasSum
        (fun n => ((b ^ (n + 1) - a ^ (n + 1)) / (n + 1 : ℕ)) • c n)
        (Chapter06.ComplexRSIntegral f id a b) := by
  have h := powerSeries_integral hR hf hab hI
  exact ⟨h.1, by simpa only [powerSeries_term_integral _ _ hab] using h.2⟩

end Rudin.PMA.Chapter08
