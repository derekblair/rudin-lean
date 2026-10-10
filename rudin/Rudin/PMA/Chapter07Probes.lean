import Rudin.PMA.Chapter07

/-! Independent boundary clients copied from reviewed external clients. Only
namespace placement/import wiring changes; no mathematical assertions are altered.
Algebra includes seven supporting lemmas for its six boundary assertions. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators BoundedContinuousFunction ENNReal
open Rudin.PMA Rudin.PMA.Chapter07 Rudin.PMA.Chapter06
namespace Rudin.PMA.Chapter07.FidelityProbes

namespace Nowhere

theorem all_real_points : ∃ f : ℝ → ℝ,
    Continuous f ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ f x := pma7_18

theorem derivative_value_rejected (x d : ℝ) :
    ¬ HasDerivAt nowhereWitness d x := by
  intro h
  exact nowhereWitness_not_differentiable x h.differentiableAt

theorem outside_unit_interval_probe :
    ¬ DifferentiableAt ℝ nowhereWitness (-1000000) ∧
    ¬ DifferentiableAt ℝ nowhereWitness (1000000) ∧
    ¬ DifferentiableAt ℝ nowhereWitness 0 ∧
    ¬ DifferentiableAt ℝ nowhereWitness (1 / 3) :=
  ⟨nowhereWitness_not_differentiable _, nowhereWitness_not_differentiable _,
    nowhereWitness_not_differentiable _, nowhereWitness_not_differentiable _⟩

theorem witness_at_origin : nowhereWitness 0 = 0 := by
  simp [nowhereWitness, nowhereTent]

theorem nonzero_arbitrarily_small_steps (x : ℝ) (m : ℕ) :
    ∃ δ : ℝ, δ ≠ 0 ∧ |δ| = (1 / 2 : ℝ) / 4 ^ m ∧
      ((3 : ℝ) ^ m + 1) / 2 * |δ| ≤ |nowhereWitness (x + δ) - nowhereWitness x| := by
  obtain ⟨δ, heq, hdiff⟩ := nowhere_large_difference x m
  refine ⟨δ, ?_, heq, hdiff⟩
  have hpos : 0 < |δ| := by rw [heq]; positivity
  exact abs_pos.mp hpos


end Nowhere

namespace Examples

theorem double_ratio_diagonal (n : ℕ) : doubleRatio n n = 1 / 2 := by
  unfold doubleRatio
  have h : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem zero_index_geometric_sum : geometricFunctionTerm 0 1 = 1 ∧
    Chapter03.SeriesHasSum (fun n => geometricFunctionTerm n 1) 2 := by
  constructor
  · norm_num [geometricFunctionTerm]
  · have h := geometricFunctionTerm_hasSum (1 : ℝ)
    norm_num [geometricFunctionSum] at h
    exact h

theorem sine_first_derivative : deriv (sineOverSqrt 0) 0 = 1 := by
  simpa using (sineOverSqrt_hasDerivAt 0 0).deriv

theorem spike_first_native_integrals :
    Chapter06.RIntegral (IntegralSpikeSquared 0) 0 1 = 1 / 4 ∧
    Chapter06.RIntegral (IntegralSpikeLinear 0) 0 1 = 1 / 4 := by
  constructor
  · have h := (integralSpikeSquared_integral 0).2
    norm_num at h
    exact h
  · have h := (integralSpikeLinear_integral 0).2
    norm_num at h
    exact h

theorem spike_closed_right_endpoint (n : ℕ) :
    IntegralSpikeSquared n 1 = 0 ∧ IntegralSpikeLinear n 1 = 0 := by
  simp [IntegralSpikeSquared, IntegralSpikeLinear]

theorem finite_integral_limit_cannot_be_zero :
    ¬ Tendsto (fun n => Chapter06.RIntegral (IntegralSpikeLinear n) 0 1)
      atTop (𝓝 (0 : ℝ)) := by
  intro h
  have heq := tendsto_nhds_unique h integralSpikeLinear_integrals_limit
  norm_num at heq

theorem rational_indicator_at_integer (z : ℤ) : rationalIndicator z = 1 := by
  exact_mod_cast rationalIndicator_rat (z : ℚ)

theorem rational_indicator_discontinuous_at_zero : ¬ ContinuousAt rationalIndicator 0 :=
  rationalIndicator_discontinuous 0

theorem rational_indicator_native_partition_sums {a b : ℝ} (P : Chapter06.Partition a b) :
    Chapter06.lowerSum rationalIndicator id P = 0 ∧
    Chapter06.upperSum rationalIndicator id P = b - a := rationalIndicator_sums P

theorem rational_indicator_not_native_integrable :
    ¬ Chapter06.RIntegrable rationalIndicator (-2) 3 :=
  rationalIndicator_not_integrable (-2) 3 (by norm_num)


end Examples

namespace MTest

theorem empty_domain_needs_no_positive_majorant :
    ∃ f : ℝ → ℂ, UniformSeriesConvergesOn
      (fun n (x : ℝ) => (((n : ℝ)*x : ℝ) : ℂ)) f ∅ := by
  exact mTest_uniform _ ∅ Rudin.PMA.Chapter03.AlternatingHarmonic
    (by simp) Rudin.PMA.Chapter03.alternatingHarmonic_converges

theorem conditional_uniform_convergence_survives :
    ∃ (F : ℕ → Unit → ℂ) (f : Unit → ℂ),
      UniformSeriesConvergesOn F f univ ∧
      ¬ ∃ M : ℕ → ℝ, Rudin.PMA.Chapter03.SeriesConverges M ∧
        ∀ n x, ‖F n x‖ ≤ M n := mTest_converse_failure


end MTest

namespace NoSubsequence
open Rudin.PMA.Chapter07

theorem no_uniform_subsequence :
    ¬ ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f : ℝ → ℝ,
      TendstoUniformlyOn (fun n x => Real.sin (((σ n : ℝ)+1)*x))
        f atTop (Icc 0 (2*Real.pi)) := by
  rintro ⟨σ, hσ, f, hf⟩
  apply sineSequence_no_pointwise_subsequence
  exact ⟨σ, hσ, f, fun x hx => hf.tendsto_at hx⟩

theorem every_subsequence_misses_some_point (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ x ∈ Icc (0 : ℝ) (2*Real.pi),
      ¬ Tendsto (fun n => Real.sin (((σ n : ℝ)+1)*x)) atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨x, hx, hbad⟩ := sineSequence_subsequence_has_bad_point σ hσ
  exact ⟨x, hx, fun h => hbad ⟨0,h⟩⟩


end NoSubsequence

namespace Calculus


theorem no_positive_mass_assumption {f : ℝ → ℝ} (hf : BoundedOn f 0 1) :
    RSIntegrable f (fun _ => 0) 0 1 ∧
      Tendsto (fun _ : ℕ => RSIntegral f (fun _ => 0) 0 1) atTop (𝓝 0) :=
  uniform_integral_zero_mass_probe hf


theorem complex_limit_existence :
    ∀ (F D : ℕ → ℝ → ℂ) (d : ℝ → ℂ) (a b x₀ : ℝ) (L : ℂ), a < b → x₀ ∈ Icc a b →
      (∀ n, ∀ x ∈ Icc a b, HasDerivWithinAt (F n) (D n x) (Icc a b) x) →
      Tendsto (fun n => F n x₀) atTop (𝓝 L) →
      TendstoUniformlyOn D d atTop (Icc a b) →
      ∃ f : ℝ → ℂ, TendstoUniformlyOn F f atTop (Icc a b) ∧
        ∀ x ∈ Icc a b, HasDerivWithinAt f (d x) (Icc a b) x := by
  intro F D d a b x₀ L hab hx hF hL hD
  obtain ⟨f, hf, _, hdf⟩ := pma7_17.1 F D d a b x₀ L hab hx hF hL hD
  exact ⟨f, hf, fun x hx => (hdf x hx).1⟩


end Calculus

namespace Continuity

theorem limit_outside_domain :
    (0 : ℝ) ∉ Ioi 0 ∧
      ∃ a : ℂ, Tendsto (fun _ : ℕ => Complex.I) atTop (𝓝 a) ∧
        Chapter04.FunctionLimitOn (Ioi 0)
          (fun x : ℝ => if 0 < x then Complex.I else 0) 0 a := by
  have hp : Chapter02.IsLimitPoint (0 : ℝ) (Ioi 0) := by
    intro r hr
    refine ⟨r / 2, by simp; linarith, by linarith, ?_⟩
    rw [Real.dist_eq]
    have he : |0 - r / 2| = r / 2 := by rw [zero_sub, abs_neg, abs_of_pos (by positivity)]
    rw [he]
    linarith
  let f : ℝ → ℂ := fun x => if 0 < x then Complex.I else 0
  have hlim : Chapter04.FunctionLimitOn (Ioi 0) f 0 Complex.I := by
    refine ⟨hp, fun ε hε => ⟨1, by norm_num, ?_⟩⟩
    intro x hx _ _
    simpa [f, show 0 < x from hx] using hε
  have hu : UniformConvergesOn (fun _ : ℕ => f) f (Ioi 0) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
  exact ⟨by simp, pma7_11 (Ioi 0) (fun _ => f) f 0 (fun _ => Complex.I) hu hp (fun _ => hlim)⟩

theorem no_isolated_limit_point : ¬ Chapter02.IsLimitPoint (0 : ℝ) {0} := by
  intro h
  obtain ⟨q, hq, hne, _⟩ := h 1 (by norm_num)
  exact hne (by simpa using hq)

theorem dini_domain_not_compact : ¬ IsCompact (Ioo (0 : ℝ) 1) := by
  intro hK
  obtain ⟨hF, hanti, hpoint, hf, hnot⟩ := pma7_13.{0}.2
  exact hnot (pma7_13.1 _ _ _ hK hF hf hpoint hanti)

abbrev EmptyReal := (∅ : Set ℝ)

theorem empty_bcf_norm (h : EmptyReal →ᵇ ℂ) : ‖h‖ = 0 := by
  apply ((pma7_14 (X := EmptyReal)).2.2.1 h).mpr
  intro x
  exact False.elim x.2

theorem empty_bcf_closure :
    BCFUniformClosure (∅ : Set (EmptyReal →ᵇ ℂ)) = ∅ := by
  simpa using ((pma7_14 (X := EmptyReal)).2.2.2.2.2.1
    (∅ : Set (EmptyReal →ᵇ ℂ))).2

theorem singleton_bcf_imaginary_norm :
    ‖BoundedContinuousFunction.const (Icc (0 : ℝ) 0) Complex.I‖ = 1 := by
  let : Nonempty (Icc (0 : ℝ) 0) := ⟨⟨0, by simp⟩⟩
  rw [(pma7_14 (X := Icc (0 : ℝ) 0)).2.1]
  simp

theorem unbounded_continuous_not_bcf :
    ¬ ∃ h : ℝ →ᵇ ℂ, ∀ x : ℝ, h x = (x : ℂ) := by
  intro hh
  obtain ⟨_, M, hM⟩ := ((pma7_14 (X := ℝ)).1 (fun x => (x : ℂ))).mp hh
  have hm := hM (|M| + 1)
  have hpos : 0 ≤ |M| + 1 := by positivity
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hpos] at hm
  linarith [le_abs_self M]

theorem noncompact_bcf_complete : CompleteSpace (ℝ →ᵇ ℂ) :=
  (pma7_15 (X := ℝ)).1


end Continuity

namespace Equicontinuity

theorem countable_empty_without_topology {X : Type*} (F : ℕ → X → ℂ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
      ∀ x ∈ (∅ : Set X), Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by
  exact pma7_23 ∅ F countable_empty (by intro x hx; exact False.elim hx)

theorem countable_singleton_without_topology {X : Type*} (x₀ : X) (F : ℕ → X → ℂ)
    (hb : ∃ M : ℝ, ∀ n, ‖F n x₀‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z : ℂ,
      Tendsto (fun n => F (φ n) x₀) atTop (𝓝 z) := by
  have hp : PointwiseBoundedOn F {x₀} := by
    intro x hx
    have : x = x₀ := mem_singleton_iff.mp hx
    simpa [this] using hb
  obtain ⟨φ, hφ, f, hf⟩ := pma7_23 {x₀} F (countable_singleton x₀) hp
  exact ⟨φ, hφ, f x₀, hf x₀ (mem_singleton x₀)⟩

theorem continuous_single_family_not_source_equicontinuous :
    ¬ SourceEquicontinuousOn (fun _ : Unit => fun x : ℝ => x^2) univ := by
  intro h
  obtain ⟨δ, hδ, hd⟩ := h 1 (by norm_num)
  have hx : dist δ⁻¹ (δ⁻¹ + δ/2) < δ := by
    rw [Real.dist_eq]
    have he : δ⁻¹ - (δ⁻¹ + δ/2) = -(δ/2) := by ring
    rw [he, abs_neg, abs_of_pos (by positivity)]
    linarith
  have heq : δ * δ⁻¹ = 1 := mul_inv_cancel₀ hδ.ne'
  have hh := hd δ⁻¹ (mem_univ _) (δ⁻¹ + δ/2) (mem_univ _) hx ()
  rw [Real.dist_eq] at hh
  have hl := (abs_lt.mp hh).1
  nlinarith [sq_pos_of_pos hδ]

def earlyMember (n : ℕ) (x : ℝ) : ℂ := if n = 0 then (x : ℂ) else 0

theorem equicontinuity_includes_early_member :
    SourceEquicontinuousOn earlyMember (Icc 0 1) ∧
      dist (earlyMember 0 0) (earlyMember 0 1) = 1 := by
  have hc (n : ℕ) : ContinuousOn (earlyMember n) (Icc 0 1) := by
    by_cases hn : n = 0
    · have he : earlyMember n = Complex.ofReal := by funext x; simp [earlyMember, hn]
      rw [he]
      exact Complex.continuous_ofReal.continuousOn
    · have he : earlyMember n = fun _ => 0 := by funext x; simp [earlyMember, hn]
      rw [he]
      exact continuousOn_const
  have hu : TendstoUniformlyOn earlyMember (fun _ => 0) atTop (Icc 0 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    refine eventually_atTop.mpr ⟨1, fun n hn x _ => ?_⟩
    have hne : n ≠ 0 := by omega
    simpa [earlyMember, hne] using hε
  exact ⟨pma7_24 _ _ _ isCompact_Icc hc hu, by norm_num [earlyMember]⟩

theorem ascoli_empty_domain {X : Type*} [MetricSpace X] (F : ℕ → X → ℂ) :
    UniformlyBoundedOn F ∅ ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
        ContinuousOn f ∅ ∧ TendstoUniformlyOn (fun n x => F (φ n) x) f atTop ∅ := by
  apply pma7_25 ∅ F isCompact_empty (fun n => continuousOn_empty (F n))
  · intro x hx
    exact False.elim hx
  · intro ε _
    exact ⟨1, by norm_num, fun _ hx => False.elim hx⟩

theorem moving_peaks_no_uniform_limit :
    ¬ ∃ f : ℝ → ℝ, TendstoUniformlyOn equicontinuityPeak f atTop (Icc 0 1) := by
  simpa using equicontinuityPeak_no_uniform_subsequence id strictMono_id


end Equicontinuity

namespace Foundations

theorem empty_domain_limit (F : ℕ → ℝ → ℂ) :
    ∃ f : ℝ → ℂ, UniformConvergesOn F f ∅ := by
  apply (pma7_8 F ∅).mpr
  intro ε _
  exact ⟨0, fun _ _ _ _ x hx => False.elim (Set.notMem_empty x hx)⟩

theorem empty_domain_error (g f : ℝ → ℂ) : UniformError g f ∅ = 0 :=
  pma7_9.{0, 0, 0, 0, 0, 0}.2.2 g f

theorem empty_domain_real_sup (g f : ℝ → ℂ) :
    (UniformError g f ∅).toReal = sSup ((fun x => ‖g x - f x‖) '' (∅ : Set ℝ)) := by
  exact (uniformError_eq_real_sup g f ∅ (by simp)).2

def unboundedPrefix (n : ℕ) (x : ℝ) : ℝ := if n = 0 then x else 0

theorem unbounded_prefix_uniform :
    UniformConvergesOn unboundedPrefix (fun _ => 0) univ := by
  apply (uniformConvergesOn_iff_norm_le _ _ _).mpr
  intro ε hε
  refine ⟨1, fun n hn x _ => ?_⟩
  have hn0 : n ≠ 0 := by omega
  simp [unboundedPrefix, hn0, hε.le]

theorem unbounded_prefix_initial_error :
    UniformError (unboundedPrefix 0) (fun _ => 0) univ = ⊤ := by
  by_contra hfinite
  let B := (UniformError (unboundedPrefix 0) (fun _ => 0) univ).toReal
  have hp : ENNReal.ofReal ‖unboundedPrefix 0 (B + 1) - 0‖ ≤
      UniformError (unboundedPrefix 0) (fun _ => 0) univ :=
    le_iSup_of_le (⟨B + 1, mem_univ _⟩ : (univ : Set ℝ)) le_rfl
  have hb := (ENNReal.ofReal_le_iff_le_toReal hfinite).mp hp
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hpref : unboundedPrefix 0 (B + 1) = B + 1 := rfl
  rw [hpref, sub_zero, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ B + 1)] at hb
  change B + 1 ≤ B at hb
  linarith

theorem unbounded_prefix_error_tends_zero :
    Tendsto (fun n => UniformError (unboundedPrefix n) (fun _ => 0) univ)
      atTop (𝓝 0) :=
  (pma7_9.{0, 0, 0, 0, 0, 0}.1 unboundedPrefix (fun _ => 0) univ
    ((pma7_7 unboundedPrefix (fun _ => 0) univ).2.1 unbounded_prefix_uniform)).mp
      unbounded_prefix_uniform

theorem complete_required_for_unit_domain {V : Type*} [NormedAddCommGroup V]
    (h : ∀ F : ℕ → Unit → V, UniformCauchyOn F univ →
      ∃ f : Unit → V, UniformConvergesOn F f univ) : CompleteSpace V := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hc : UniformCauchyOn (fun n (_ : Unit) => u n) univ := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu ε hε
    refine ⟨N, fun m hm n hn _ _ => ?_⟩
    simpa only [dist_eq_norm] using (hN m hm n hn).le
  obtain ⟨f, hf⟩ := h (fun n (_ : Unit) => u n) hc
  exact ⟨f (), hf.tendsto_at (mem_univ ())⟩

theorem incomplete_target_rejects_criterion {V : Type*} [NormedAddCommGroup V]
    (hV : ¬ CompleteSpace V) :
    ¬ (∀ F : ℕ → Unit → V, UniformCauchyOn F univ →
      ∃ f : Unit → V, UniformConvergesOn F f univ) := by
  intro h
  exact hV (complete_required_for_unit_domain h)

theorem imaginary_constant_limit :
    ∃ f : Unit → ℂ, UniformConvergesOn (fun _ _ => Complex.I) f univ := by
  apply (pma7_8 _ _).mpr
  intro ε hε
  refine ⟨0, fun _ _ _ _ _ _ => ?_⟩
  simpa using hε.le

theorem ordered_series_definition (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (E : Set ℝ) :
    PointwiseSeriesConvergesOn F f E ↔
      ∀ x ∈ E, Tendsto (fun N => ∑ n ∈ Finset.range N, F n x) atTop (𝓝 (f x)) :=
  Iff.rfl


end Foundations

namespace Algebra

/-- Infinite-domain algebra with point-dependent nonzero witnesses and no unit. -/
def EventuallyZero (𝕜 : Type*) [Zero 𝕜] : Set (ℕ → 𝕜) :=
  {f | ∃ N, ∀ n ≥ N, f n = 0}

theorem eventuallyZero_algebra (𝕜 : Type*) [Field 𝕜] :
    IsFunctionAlgebra (EventuallyZero 𝕜) := by
  refine ⟨⟨fun _ => 0, 0, fun _ _ => rfl⟩, ?_, ?_, ?_⟩
  · rintro f ⟨N, hN⟩ g ⟨M, hM⟩
    exact ⟨max N M, fun n hn => by
      simp [hN n ((le_max_left N M).trans hn),
        hM n ((le_max_right N M).trans hn)]⟩
  · rintro f ⟨N, hN⟩ g ⟨M, hM⟩
    exact ⟨N, fun n hn => by simp [hN n hn]⟩
  · rintro c f ⟨N, hN⟩
    exact ⟨N, fun n hn => by simp [hN n hn]⟩

theorem eventuallyZero_indicator (𝕜 : Type*) [Field 𝕜] (x : ℕ) :
    (fun n => if n = x then (1 : 𝕜) else 0) ∈ EventuallyZero 𝕜 := by
  refine ⟨x + 1, fun n hn => ?_⟩
  have hne : n ≠ x := by omega
  simp [hne]

theorem eventuallyZero_separates (𝕜 : Type*) [Field 𝕜] :
    SeparatesFunctionPoints (EventuallyZero 𝕜) := by
  intro x y hxy
  exact ⟨_, eventuallyZero_indicator 𝕜 x, by simp [Ne.symm hxy]⟩

theorem eventuallyZero_nonvanishing (𝕜 : Type*) [Field 𝕜] :
    FunctionVanishesNowhere (EventuallyZero 𝕜) := by
  intro x
  exact ⟨_, eventuallyZero_indicator 𝕜 x, by simp⟩

theorem eventuallyZero_no_global_nonzero_member (𝕜 : Type*) [Field 𝕜] :
    ¬ ∃ f ∈ EventuallyZero 𝕜, ∀ n, f n ≠ 0 := by
  rintro ⟨f, ⟨N, hN⟩, hf⟩
  exact hf N (hN N le_rfl)

theorem eventuallyZero_no_unit (𝕜 : Type*) [Field 𝕜] :
    (fun _ : ℕ => (1 : 𝕜)) ∉ EventuallyZero 𝕜 := by
  rintro ⟨N, hN⟩
  exact one_ne_zero (hN N le_rfl)

/-- 7.31 applies to a genuinely nonunital algebra, with no globally nonzero member. -/
theorem nonunital_interpolation_real_complex :
    (∃ f ∈ EventuallyZero ℝ, f 0 = 3 ∧ f 1 = -2) ∧
    (∃ f ∈ EventuallyZero ℂ, f 0 = Complex.I ∧ f 1 = 2 + Complex.I) := by
  constructor
  · exact pma7_31.1 ℕ _ (eventuallyZero_algebra ℝ)
      (eventuallyZero_separates ℝ) (eventuallyZero_nonvanishing ℝ)
      0 1 (by decide) 3 (-2)
  · exact pma7_31.2 ℕ _ (eventuallyZero_algebra ℂ)
      (eventuallyZero_separates ℂ) (eventuallyZero_nonvanishing ℂ)
      0 1 (by decide) Complex.I (2 + Complex.I)

/-- All functions on a singleton are individually bounded, but have no common bound. -/
theorem no_common_bound :
    ¬ ∃ M : ℝ, ∀ f : Unit → ℝ, ∀ x, ‖f x‖ ≤ M := by
  rintro ⟨M, hM⟩
  have h := hM (fun _ => |M| + 1) ()
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at h
  linarith [le_abs_self M]

theorem closure_without_common_bound :
    IsFunctionAlgebra (AlgebraUniformClosure (Set.univ : Set (Unit → ℝ))) ∧
      IsAlgebraUniformlyClosed (AlgebraUniformClosure (Set.univ : Set (Unit → ℝ))) ∧
      ∀ f ∈ AlgebraUniformClosure (Set.univ : Set (Unit → ℝ)),
        AlgebraFunctionBounded f := by
  apply pma7_29.1 Unit Set.univ
  · exact ⟨Set.univ_nonempty, by simp, by simp, by simp⟩
  · intro f _
    exact ⟨‖f ()‖, fun x => by cases x; exact le_rfl⟩

/-- The degenerate compact interval still requires exact zero for every index. -/
theorem zero_radius_exact_normalization :
    ∃ P : ℕ → Polynomial ℝ, (∀ n, (P n).eval 0 = 0) ∧
      TendstoUniformlyOn (fun n x => (P n).eval x) (fun x : ℝ => |x|)
        atTop (Icc (0 : ℝ) 0) := by
  simpa using pma7_27 0 le_rfl

theorem singleton_approximation_without_global_continuity (f : ℝ → ℂ) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Icc 2 2) := by
  apply pma7_26.1 2 2 le_rfl f
  simpa only [Icc_self] using continuousOn_singleton (f := f) (a := (2 : ℝ))

/-- Empty compact metric domains remain covered in the real and complex theorems. -/
theorem empty_compact_density :
    (AlgebraUniformClosure (Set.univ : Set (Icc (1 : ℝ) 0 → ℝ)) =
      {f | Continuous f}) ∧
    (AlgebraUniformClosure (Set.univ : Set (Icc (1 : ℝ) 0 → ℂ)) =
      {f | Continuous f}) := by
  have hempty (x : Icc (1 : ℝ) 0) : False := by
    rcases x.property with ⟨h1, h0⟩
    linarith
  have hcont {Y : Type} [TopologicalSpace Y] (f : Icc (1 : ℝ) 0 → Y) :
      Continuous f := continuous_iff_continuousAt.mpr (fun x => (hempty x).elim)
  constructor
  · apply pma7_32 (Icc (1 : ℝ) 0) Set.univ
    · exact ⟨Set.univ_nonempty, by simp, by simp, by simp⟩
    · exact fun f _ => hcont f
    · exact fun {x} _ _ => (hempty x).elim
    · exact fun x => (hempty x).elim
  · apply pma7_33.2.1 (Icc (1 : ℝ) 0) Set.univ
    · exact ⟨Set.univ_nonempty, by simp, by simp, by simp⟩
    · exact fun f _ => hcont f
    · exact fun {x} _ _ => (hempty x).elim
    · exact fun x => (hempty x).elim
    · exact fun _ _ => Set.mem_univ _

/-- The warning excludes an actual continuous function, not merely a missing hypothesis. -/
theorem actual_complex_obstruction :
    Continuous (fun z : Metric.closedBall (0 : ℂ) 1 => star (z : ℂ)) ∧
    (fun z : Metric.closedBall (0 : ℂ) 1 => star (z : ℂ)) ∉
      AlgebraUniformClosure (PolynomialFunctionFamily
        (fun z : Metric.closedBall (0 : ℂ) 1 => (z : ℂ))) :=
  ⟨continuous_subtype_val.star, polynomial_disk_conj_not_uniformClosure⟩



end Algebra

end Rudin.PMA.Chapter07.FidelityProbes
