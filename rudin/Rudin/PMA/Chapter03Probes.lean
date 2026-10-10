import Rudin.PMA.Chapter03

/-! Semantic probes for Chapter 3: infinity, indexing, conditional sums,
ratio denominators, and rearrangement multiplicities. -/

noncomputable section
open Set Filter Topology
open scoped BigOperators NNReal ENNReal

namespace Rudin.PMA.Chapter03.FidelityProbes

theorem probe_empty_diameter : RudinDiameter (∅ : Set ℝ) = 0 := by
  simp [RudinDiameter]

theorem probe_unbounded_diameter :
    RudinDiameter (Set.univ : Set ℝ) = ⊤ ∧ Metric.diam (Set.univ : Set ℝ) = 0 := by
  simp [RudinDiameter]

theorem probe_constant_non_strict_monotonicity :
    IncreasingSequence (fun _ : ℕ => (1 : ℝ)) ∧
    DecreasingSequence (fun _ : ℕ => (1 : ℝ)) ∧
    ¬ StrictMono (fun _ : ℕ => (1 : ℝ)) := by
  refine ⟨fun _ => le_rfl, fun _ => le_rfl, ?_⟩
  intro h
  have := h (show (0 : ℕ) < 1 by omega)
  norm_num at this

theorem probe_constant_tail_range (N : ℕ) :
    TailRange (fun _ : ℕ => (1 : ℝ)) N = {1} := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    simp
  · intro hx
    have hx' : x = 1 := Set.mem_singleton_iff.mp hx
    exact ⟨N, Set.mem_Ici.mpr le_rfl, hx'.symm⟩

theorem probe_partial_sum_endpoints :
    PartialSums (fun _ : ℕ => (1 : ℂ)) 0 = 0 ∧
    PartialSums (fun _ : ℕ => (1 : ℂ)) 1 = 1 ∧
    BlockSum (fun _ : ℕ => (1 : ℂ)) 1 0 = 0 := by
  simp [PartialSums, BlockSum]

theorem probe_positive_reciprocal_coefficients :
    ReciprocalCoefficients 1 0 = 0 ∧ ReciprocalCoefficients 1 1 = 1 ∧
    ReciprocalCoefficients 2 0 = 0 ∧ ReciprocalCoefficients 2 1 = 1 := by
  norm_num [ReciprocalCoefficients]

theorem probe_power_series_at_zero (c : ℕ → ℂ) :
    SeriesHasSum (PowerSeriesTerms c 0) (c 0) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  unfold PartialSums PowerSeriesTerms
  rw [Finset.sum_eq_single 0]
  · simp
  · intro n hn hn0
    simp [zero_pow hn0]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (by omega)))

theorem probe_root_ratio_boundary :
    RootLimsup (fun _ : ℕ => (1 : ℂ)) = 1 ∧
    (∀ n : ℕ, RatioNorm (fun _ : ℕ => (1 : ℂ)) n = 1) ∧
    ¬ SeriesConverges (fun _ : ℕ => (1 : ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [RootLimsup, NthRootNorm, Filter.limsup_const]
  · intro n
    simp [RatioNorm]
  · rintro ⟨s, hs⟩
    change Tendsto (fun N => ∑ n ∈ Finset.range N, (1 : ℂ)) atTop (𝓝 s) at hs
    have hs' : Tendsto (fun n : ℕ => (n : ℂ)) atTop (𝓝 s) := by
      simpa using hs
    have hr : Tendsto (fun n : ℕ => (n : ℝ)) atTop (𝓝 s.re) := by
      simpa [Function.comp_def] using Complex.continuous_re.continuousAt.tendsto.comp hs'
    exact not_tendsto_atTop_of_tendsto_nhds hr tendsto_natCast_atTop_atTop

def ProbeZeroOneTerms (n : ℕ) : ℂ := if Even n then 0 else 1

theorem probe_zero_denominator_ratios :
    (∀ n, RatioNorm ProbeZeroOneTerms n = 0) ∧ RatioLimsup ProbeZeroOneTerms = 0 := by
  have h : ∀ n, RatioNorm ProbeZeroOneTerms n = 0 := by
    intro n
    by_cases hn : Even n <;> simp [RatioNorm, ProbeZeroOneTerms, Nat.even_add_one, hn]
  refine ⟨h, ?_⟩
  simp [RatioLimsup, h, Filter.limsup_const]

theorem probe_zero_denominator_terms_do_not_vanish :
    ¬ Tendsto ProbeZeroOneTerms atTop (𝓝 0) := by
  intro h
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) (1 / 2) (by norm_num)
  have hbad := hN (2 * N + 1) (by omega)
  have hodd : ¬ Even (2 * N + 1) := by simp
  norm_num [ProbeZeroOneTerms, hodd] at hbad

theorem probe_totalized_ratio_test_counterexample :
    RatioLimsup ProbeZeroOneTerms < 1 ∧ ¬ SeriesConverges ProbeZeroOneTerms := by
  refine ⟨by rw [probe_zero_denominator_ratios.2]; norm_num, ?_⟩
  rintro ⟨s, hs⟩
  have hs' : Tendsto (PartialSums ProbeZeroOneTerms) atTop (𝓝 s) := hs
  have ht : Tendsto ProbeZeroOneTerms atTop (𝓝 0) := by
    have hdiff := (hs'.comp (tendsto_add_atTop_nat 1)).sub hs'
    have hdiff' : Tendsto
        (fun n => PartialSums ProbeZeroOneTerms (n+1) - PartialSums ProbeZeroOneTerms n)
        atTop (𝓝 0) := by simpa [Function.comp_def] using hdiff
    convert hdiff' using 1
    ext n
    simp [PartialSums, Finset.sum_range_succ]
  exact probe_zero_denominator_terms_do_not_vanish ht

theorem probe_harmonic_ordinary_not_unconditional :
    SeriesConverges AlternatingHarmonic ∧ ¬ Summable AlternatingHarmonic := by
  have hanti : Antitone (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
    intro m n hmn
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have ht : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  constructor
  · obtain ⟨s, hs⟩ := hanti.tendsto_alternating_series_of_tendsto_zero ht
    refine ⟨s, ?_⟩
    change Tendsto (fun N => ∑ n ∈ Finset.range N, AlternatingHarmonic n) atTop (𝓝 s)
    simpa [AlternatingHarmonic, div_eq_mul_inv] using hs
  · intro hs
    have ha : Summable (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
      convert hs.abs using 1
      ext n
      simp [AlternatingHarmonic, abs_div, abs_pow, abs_of_pos (show 0 < (n+1 : ℝ) by positivity)]
    have ha' : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using ha
    exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ha')

theorem probe_two_positive_one_negative_first_indices :
    (List.range 6).map TwoPositiveOneNegative = [0, 2, 1, 4, 6, 3] := by
  norm_num [TwoPositiveOneNegative, List.range_succ]

theorem probe_same_range_is_not_rearrangement :
    ¬ Rearrangement (fun n : ℕ => if n = 0 then (1 : ℝ) else 0)
      (fun n : ℕ => if n ≤ 1 then (1 : ℝ) else 0) := by
  rintro ⟨e, he⟩
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have he0 : e 0 = 0 := by
    by_contra h
    simp [h] at h0
  have he1 : e 1 = 0 := by
    by_contra h
    simp [h] at h1
  have : (0 : ℕ) = 1 := e.injective (he0.trans he1.symm)
  omega

end Rudin.PMA.Chapter03.FidelityProbes
