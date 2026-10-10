import Rudin.PMA.Chapter07.Basic

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter07

def pma7_10_contract : Prop :=
  (∀ {X : Type*} (F : ℕ → X → ℂ) (E : Set X) (M : ℕ → ℝ),
    (∀ n x, x ∈ E → ‖F n x‖ ≤ M n) → Chapter03.SeriesConverges M →
      ∃ f : X → ℂ, UniformSeriesConvergesOn F f E) ∧
  (∃ (F : ℕ → Unit → ℂ) (f : Unit → ℂ),
    UniformSeriesConvergesOn F f univ ∧
      ¬ ∃ M : ℕ → ℝ, Chapter03.SeriesConverges M ∧
        ∀ n x, ‖F n x‖ ≤ M n)

/-- On a nonempty domain the norm bound itself makes the majorant nonnegative;
the empty domain imposes no unnecessary sign or summability side condition. -/
theorem mTest_uniform {X : Type*} (F : ℕ → X → ℂ) (E : Set X) (M : ℕ → ℝ)
    (hbound : ∀ n x, x ∈ E → ‖F n x‖ ≤ M n)
    (hM : Chapter03.SeriesConverges M) :
    ∃ f : X → ℂ, UniformSeriesConvergesOn F f E := by
  classical
  by_cases hE : E.Nonempty
  · obtain ⟨x, hx⟩ := hE
    have hn (n : ℕ) : 0 ≤ M n := (norm_nonneg (F n x)).trans (hbound n x hx)
    have hs : Summable M := (Chapter03.seriesConverges_iff_summable_nonneg hn).mp hM
    exact ⟨fun x => ∑' n, F n x, tendstoUniformlyOn_tsum_nat hs hbound⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hE
    subst E
    exact ⟨fun _ => 0, tendstoUniformlyOn_empty⟩

/-- The already verified alternating harmonic series, constant in the domain variable. -/
def mTestConverseTerms (n : ℕ) (_x : Unit) : ℂ := Chapter03.AlternatingHarmonic n

theorem mTest_converse_failure :
    ∃ (F : ℕ → Unit → ℂ) (f : Unit → ℂ),
      UniformSeriesConvergesOn F f univ ∧
        ¬ ∃ M : ℕ → ℝ, Chapter03.SeriesConverges M ∧
          ∀ n x, ‖F n x‖ ≤ M n := by
  obtain ⟨A, hA⟩ := Chapter03.alternatingHarmonic_converges
  have hAc : Tendsto
      (fun N => Chapter03.PartialSums (fun n => (Chapter03.AlternatingHarmonic n : ℂ)) N)
      atTop (𝓝 (A : ℂ)) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp hA
    simpa only [Function.comp_def, Chapter03.PartialSums, Complex.ofReal_sum] using h
  refine ⟨mTestConverseTerms, fun _ => (A : ℂ), ?_, ?_⟩
  · exact hAc.tendstoUniformlyOn_const univ
  · rintro ⟨M, hM, hb⟩
    have hn (n : ℕ) : 0 ≤ M n :=
      (norm_nonneg (mTestConverseTerms n ())).trans (hb n ())
    have hs : Summable M := (Chapter03.seriesConverges_iff_summable_nonneg hn).mp hM
    have ha : Summable (fun n => ‖Chapter03.AlternatingHarmonic n‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
        (fun n => by simpa [mTestConverseTerms] using hb n ()) hs
    exact Chapter03.alternatingHarmonic_not_absolute
      ((Chapter03.seriesAbsolutelyConverges_iff_summable_norm _).mpr ha)

/-- PMA 7.10: uniform convergence from an ordered summable majorant, and failure
of the converse witnessed by a conditionally convergent constant function series. -/
theorem pma7_10 : pma7_10_contract := ⟨mTest_uniform, mTest_converse_failure⟩

#print axioms pma7_10

end Rudin.PMA.Chapter07
