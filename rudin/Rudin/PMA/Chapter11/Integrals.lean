import Rudin.PMA.Chapter11
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# PMA 11.24–11.32: countable additivity and convergence

Nonnegative functions take values in `ℝ≥0∞`, retaining infinite values and
infinite integrals. Signed and complex results below use the finite-valued
representatives permitted by 11.25, and the Bochner Lebesgue integral.
The source's measurable subset `E` is represented by replacing `μ` with
`μ.restrict E`; the almost-everywhere and set-local forms impose no conditions
outside `E`. Everywhere formulations can alternatively be applied on the
subtype `E`. No set is assumed to have finite measure unless explicitly stated.
Sequences start at zero, a harmless reindexing.

The unnumbered compatibility theorems below prove that the nonnegative
integral is exactly the supremum of the book's finite, nonnegative simple
function sums. The signed integral is related to its positive-minus-negative
formula by the extended-real representative theorems. Thus these integral
semantics are verified independently of the pending first-half aliases for
11.21–22. A name-level connection to those aliases remains to be added when
they land; no first-half definition or numbered node is duplicated here.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Rudin.PMA.Chapter11.SecondHalf

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Compatibility with the simple-function formula used by the book: the
integral of a finite nonnegative measurable function is the finite sum of its
values times the measures of the corresponding level sets inside `E`.
`SimpleFunc` contains both the finite-range and level-set measurability data. -/
theorem simple_integral_eq_finite_sum (s : MeasureTheory.SimpleFunc X ℝ≥0) (E : Set X) :
    (s.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (μ.restrict E) =
      ∑ c ∈ s.range, (c : ℝ≥0∞) * μ (E ∩ s ⁻¹' {c}) := by
  rw [MeasureTheory.SimpleFunc.map_lintegral]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Measure.restrict_apply (s.measurableSet_preimage {c}), inter_comm]

/-- Compatibility with the nonnegative integral's printed supremum formula.
The approximating simple functions are finite valued (`ℝ≥0`), even when `f`
or its integral is infinite; admitting infinite-valued simple functions is
therefore not an unproved change to the source's definition. This equation is
a compatibility result, not a replacement definition for first-half 11.21. -/
theorem nonnegative_integral_eq_sup_simple_sums (f : X → ℝ≥0∞) (E : Set X) :
    (∫⁻ x in E, f x ∂μ) =
      ⨆ (s : MeasureTheory.SimpleFunc X ℝ≥0) (_ : ∀ x, (s x : ℝ≥0∞) ≤ f x),
        ∑ c ∈ s.range, (c : ℝ≥0∞) * μ (E ∩ s ⁻¹' {c}) := by
  rw [lintegral_eq_nnreal]
  simp_rw [simple_integral_eq_finite_sum]

/-- The simple supremum may equally require domination only on the measurable
integration set. Values of either function outside that set do not affect it. -/
theorem nonnegative_integral_eq_sup_simple_sums_on (f : X → ℝ≥0∞)
    {E : Set X} (hE : MeasurableSet E) :
    (∫⁻ x in E, f x ∂μ) =
      ⨆ (s : MeasureTheory.SimpleFunc X ℝ≥0)
        (_ : ∀ x ∈ E, (s x : ℝ≥0∞) ≤ f x),
        ∑ c ∈ s.range, (c : ℝ≥0∞) * μ (E ∩ s ⁻¹' {c}) := by
  apply le_antisymm
  · rw [nonnegative_integral_eq_sup_simple_sums]
    apply iSup_le
    intro s
    apply iSup_le
    intro hs
    exact le_iSup₂_of_le s (fun x _hx => hs x) le_rfl
  · apply iSup_le
    intro s
    apply iSup_le
    intro hs
    rw [← simple_integral_eq_finite_sum s E,
      ← MeasureTheory.SimpleFunc.lintegral_eq_lintegral]
    exact setLIntegral_mono' hE hs

/-- 11.24(a): countable additivity, including infinite-valued integrals.
The library result even permits nonmeasurable integrands. -/
theorem pma11_24_nonnegative (f : X → ℝ≥0∞) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    ∫⁻ x in ⋃ n, A n, f x ∂μ = ∑' n, ∫⁻ x in A n, f x ∂μ :=
  lintegral_iUnion hA hdisj f

section FiniteValues

variable {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- 11.24(b), including the complex extension on printed p.325.
`HasSum` records convergence, not just equality of totalized sums. -/
theorem pma11_24_integrable {f : X → K} (hf : Integrable f μ)
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    HasSum (fun n => ∫ x in A n, f x ∂μ) (∫ x in ⋃ n, A n, f x ∂μ) :=
  hasSum_integral_iUnion hA hdisj hf.integrableOn

/-- Null deletion in the corollary to 11.24, for signed and complex integrals. -/
theorem pma11_24_corollary (f : X → K) {A B : Set X}
    (hBA : B ⊆ A) (hnull : μ (A \ B) = 0) :
    ∫ x in A, f x ∂μ = ∫ x in B, f x ∂μ := by
  have h : A =ᵐ[μ] B := ae_eq_set.mpr
    ⟨hnull, by simp [sdiff_eq_empty.mpr hBA]⟩
  rw [Measure.restrict_congr_set h]

/-- 11.25: equality almost everywhere preserves all subset integrals. -/
theorem pma11_25_integral_eq {f g : X → K} (h : f =ᵐ[μ] g) (A : Set X) :
    ∫ x in A, f x ∂μ = ∫ x in A, g x ∂μ :=
  integral_congr_ae (ae_restrict_of_ae h)

/-- 11.26, including the complex form: absolute integrability and the bound. -/
theorem pma11_26 {f : X → K} (hf : Integrable f μ) :
    Integrable (fun x => ‖f x‖) μ ∧
      ‖∫ x, f x ∂μ‖ ≤ ∫ x, ‖f x‖ ∂μ :=
  ⟨hf.norm, norm_integral_le_integral_norm f⟩

omit [NormedSpace ℝ K] in
/-- 11.27, with the slightly stronger almost-everywhere hypotheses. -/
theorem pma11_27 {f : X → K} {g : X → ℝ}
    (hf : AEStronglyMeasurable f μ) (hg : Integrable g μ)
    (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) : Integrable f μ :=
  hg.mono' hf hbound

/-- 11.29: closure under addition and additivity, for real or complex functions. -/
theorem pma11_29 {f g : X → K} (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun x => f x + g x) μ ∧
      (∫ x, f x + g x ∂μ) = (∫ x, f x ∂μ) + ∫ x, g x ∂μ :=
  ⟨hf.add hg, integral_add hf hg⟩

/-- 11.32: dominated convergence with its integrability conclusions.
Almost-everywhere convergence is explicitly permitted in the source. -/
theorem pma11_32 {F : ℕ → X → K} {f : X → K} {g : X → ℝ}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ g x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    (∀ n, Integrable (F n) μ) ∧ Integrable f μ ∧
      Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
  refine ⟨fun n => hg.mono' (hF n) (hbound n), ?_,
    tendsto_integral_of_dominated_convergence g hF hg hbound hlim⟩
  exact ⟨aestronglyMeasurable_of_tendsto_ae _ hF hlim,
    hasFiniteIntegral_of_dominated_convergence hg.hasFiniteIntegral hbound hlim⟩

/-- The bounded convergence corollary to 11.32, for any finite measure. -/
theorem pma11_32_bounded [IsFiniteMeasure μ] {F : ℕ → X → K} {f : X → K}
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (C : ℝ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ C)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    (∀ n, Integrable (F n) μ) ∧ Integrable f μ ∧
      Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  pma11_32 hF (integrable_const C) hbound hlim

end FiniteValues

/-- The nonnegative null-deletion corollary retains infinite values. -/
theorem pma11_24_corollary_nonnegative (f : X → ℝ≥0∞) {A B : Set X}
    (hBA : B ⊆ A) (hnull : μ (A \ B) = 0) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in B, f x ∂μ := by
  have h : A =ᵐ[μ] B := ae_eq_set.mpr
    ⟨hnull, by simp [sdiff_eq_empty.mpr hBA]⟩
  rw [Measure.restrict_congr_set h]

/-- 11.25: the source's equality relation on a measurable domain. -/
def AlmostEqualOn {Y : Type*} (μ : Measure X) (E : Set X) (f g : X → Y) : Prop :=
  f =ᵐ[μ.restrict E] g

/-- 11.25: reflexivity, symmetry and transitivity hold for this relation. -/
theorem pma11_25_equivalence {Y : Type*} (E : Set X) :
    Equivalence (AlmostEqualOn (Y := Y) μ E) :=
  ⟨fun _ => Filter.EventuallyEq.rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- 11.25's null exceptional-set definition agrees with the restricted-measure
encoding. No completeness hypothesis is needed for the null outer measure. -/
theorem pma11_25_iff_null {Y : Type*} {E : Set X} (hE : MeasurableSet E)
    {f g : X → Y} :
    AlmostEqualOn μ E f g ↔ μ ({x | f x ≠ g x} ∩ E) = 0 := by
  simp only [AlmostEqualOn, Filter.EventuallyEq, ae_iff, Measure.restrict_apply' hE]

/-- 11.25: both finiteness conditions in 11.22 force an extended-real
integrable function to be finite almost everywhere. The hypotheses retain
the literal positive and negative part integrals, rather than presupposing
an everywhere finite representative. -/
theorem pma11_25_ereal_finite_ae {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) :
    ∀ᵐ x ∂μ, f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  filter_upwards [ae_lt_top hf.ereal_toENNReal hpos.ne,
    ae_lt_top hf.neg.ereal_toENNReal hneg.ne] with x hx hy
  refine ⟨EReal.toENNReal_ne_top_iff.mp hx.ne, ?_⟩
  simpa only [Pi.neg_apply, ne_eq, EReal.neg_eq_top_iff] using
    (EReal.toENNReal_ne_top_iff.mp hy.ne)

/-- 11.25: an integrable extended-real function has a measurable finite-valued
representative. The value zero selected by `toReal` at either infinity changes
the function only on a null set. This choice works even for incomplete measures. -/
theorem pma11_25_ereal_representative {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) :
    Measurable (fun x => (f x).toReal) ∧
      (fun x => ((f x).toReal : EReal)) =ᵐ[μ] f ∧
      Integrable (fun x => (f x).toReal) μ := by
  have hfin := pma11_25_ereal_finite_ae hf hpos hneg
  have hp := integrable_toReal_of_lintegral_ne_top hf.ereal_toENNReal.aemeasurable hpos.ne
  have hn := integrable_toReal_of_lintegral_ne_top hf.neg.ereal_toENNReal.aemeasurable hneg.ne
  refine ⟨hf.ereal_toReal, ?_, ?_⟩
  · filter_upwards [hfin] with x hx
    exact EReal.coe_toReal hx.1 hx.2
  · apply (hp.sub hn).congr
    filter_upwards [hfin] with x hx
    change (f x).toENNReal.toReal - (-f x).toENNReal.toReal = (f x).toReal
    rw [EReal.toENNReal_of_ne_top hx.1,
      EReal.toENNReal_of_ne_top (by simpa using hx.2), EReal.toReal_neg_eq,
      ENNReal.toReal_ofReal', ENNReal.toReal_ofReal']
    exact max_zero_sub_max_neg_zero_eq_self _

/-- The integral of the representative in 11.25 is precisely the difference
of the two finite part integrals from 11.22. This proves that using real
representatives in the signed theorems does not lose infinite-valued inputs
which are integrable in the book's sense. -/
theorem pma11_25_ereal_integral_eq {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) :
    (∫ x, (f x).toReal ∂μ) =
      (∫⁻ x, (f x).toENNReal ∂μ).toReal -
        (∫⁻ x, (-f x).toENNReal ∂μ).toReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (pma11_25_ereal_representative hf hpos hneg).2.2]
  have hfin := pma11_25_ereal_finite_ae hf hpos hneg
  have hp : (∫⁻ x, ENNReal.ofReal (f x).toReal ∂μ) = ∫⁻ x, (f x).toENNReal ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    exact (EReal.toENNReal_of_ne_top hx.1).symm
  have hn : (∫⁻ x, ENNReal.ofReal (-(f x).toReal) ∂μ) =
      ∫⁻ x, (-f x).toENNReal ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    rw [EReal.toENNReal_of_ne_top (by simpa using hx.2), EReal.toReal_neg_eq]
  rw [hp, hn]

/-- The same bridge as an equality in the extended real line, preserving the
source's signed-integral codomain. The two part integrals are finite here. -/
theorem pma11_25_ereal_integral_coe {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) :
    ((∫ x, (f x).toReal ∂μ : ℝ) : EReal) =
      ((∫⁻ x, (f x).toENNReal ∂μ) : EReal) -
        ((∫⁻ x, (-f x).toENNReal ∂μ) : EReal) := by
  rw [pma11_25_ereal_integral_eq hf hpos hneg, EReal.coe_sub]
  congr 1
  · exact EReal.coe_ennreal_toReal hpos.ne
  · exact EReal.coe_ennreal_toReal hneg.ne

/-- The representative bridge holds on every measurable subset (indeed every
subset in mathlib's restricted-measure formulation). Its part integrals stay
finite by monotonicity. -/
theorem pma11_25_ereal_set_integral_eq {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) (A : Set X) :
    (∫ x in A, (f x).toReal ∂μ) =
      (∫⁻ x in A, (f x).toENNReal ∂μ).toReal -
        (∫⁻ x in A, (-f x).toENNReal ∂μ).toReal :=
  pma11_25_ereal_integral_eq hf
    ((setLIntegral_le_lintegral A _).trans_lt hpos)
    ((setLIntegral_le_lintegral A _).trans_lt hneg)

/-- 11.24(b) directly for extended-real integrable inputs. Every subset integral
is the signed difference from 11.22; `HasSum` includes convergence of the series. -/
theorem pma11_24_ereal {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞)
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    HasSum (fun n => (∫⁻ x in A n, (f x).toENNReal ∂μ).toReal -
      (∫⁻ x in A n, (-f x).toENNReal ∂μ).toReal)
      ((∫⁻ x in ⋃ n, A n, (f x).toENNReal ∂μ).toReal -
        (∫⁻ x in ⋃ n, A n, (-f x).toENNReal ∂μ).toReal) := by
  simp_rw [← pma11_25_ereal_set_integral_eq hf hpos hneg]
  exact pma11_24_integrable (pma11_25_ereal_representative hf hpos hneg).2.2 hA hdisj

/-- Conversely, finite almost-everywhere extended-real functions whose real
representatives are integrable have both part integrals finite. Together with
the preceding bridge this is the source's integrability criterion. -/
theorem pma11_25_ereal_parts_finite {f : X → EReal}
    (hfin : ∀ᵐ x ∂μ, f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hf : Integrable (fun x => (f x).toReal) μ) :
    (∫⁻ x, (f x).toENNReal ∂μ) < ∞ ∧
      (∫⁻ x, (-f x).toENNReal ∂μ) < ∞ := by
  have hn : (∫⁻ x, ENNReal.ofReal ‖(f x).toReal‖ ∂μ) < ∞ :=
    (hasFiniteIntegral_iff_norm _).mp hf.hasFiniteIntegral
  constructor
  · refine (lintegral_mono_ae ?_).trans_lt hn
    filter_upwards [hfin] with x hx
    rw [EReal.toENNReal_of_ne_top hx.1]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · refine (lintegral_mono_ae ?_).trans_lt hn
    filter_upwards [hfin] with x hx
    rw [EReal.toENNReal_of_ne_top (by simpa using hx.2), EReal.toReal_neg_eq]
    exact ENNReal.ofReal_le_ofReal (neg_le_abs _)

/-- 11.26 for the source's extended-real inputs: the absolute-value integral
is finite and bounds the absolute value of the signed integral. The signed
integral is written using its equivalent finite representative, with the exact
positive-minus-negative formula supplied by `pma11_25_ereal_integral_eq`. -/
theorem pma11_26_ereal {f : X → EReal} (hf : Measurable f)
    (hpos : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hneg : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) :
    (∫⁻ x, (f x).abs ∂μ) < ∞ ∧
      |∫ x, (f x).toReal ∂μ| ≤ (∫⁻ x, (f x).abs ∂μ).toReal := by
  have hfin := pma11_25_ereal_finite_ae hf hpos hneg
  have hi := (pma11_25_ereal_representative hf hpos hneg).2.2
  have heq : (∫⁻ x, (f x).abs ∂μ) =
      ∫⁻ x, ENNReal.ofReal ‖(f x).toReal‖ ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    conv_lhs => rw [← EReal.coe_toReal hx.1 hx.2]
    rfl
  rw [heq]
  refine ⟨(hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral, ?_⟩
  calc
    |∫ x, (f x).toReal ∂μ| ≤ ∫ x, ‖(f x).toReal‖ ∂μ := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x => (f x).toReal) (μ := μ))
    _ = (∫⁻ x, ENNReal.ofReal ‖(f x).toReal‖ ∂μ).toReal := by
      rw [integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
      simp only [ofReal_norm]

/-- 11.27 for extended-real functions. The hypothesis expresses the book's
absolute-value domination as `max f (-f) ≤ g`. Its proof in fact only needs
finiteness of the positive part integral of the majorant. -/
theorem pma11_27_ereal {f g : X → EReal} (hf : Measurable f)
    (hg : (∫⁻ x, (g x).toENNReal ∂μ) < ∞)
    (hbound : ∀ᵐ x ∂μ, max (f x) (-f x) ≤ g x) :
    (∫⁻ x, (f x).toENNReal ∂μ) < ∞ ∧
      (∫⁻ x, (-f x).toENNReal ∂μ) < ∞ ∧
      Integrable (fun x => (f x).toReal) μ := by
  have hp : (∫⁻ x, (f x).toENNReal ∂μ) < ∞ := by
    refine (lintegral_mono_ae ?_).trans_lt hg
    filter_upwards [hbound] with x hx
    exact EReal.toENNReal_le_toENNReal ((le_max_left _ _).trans hx)
  have hn : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞ := by
    refine (lintegral_mono_ae ?_).trans_lt hg
    filter_upwards [hbound] with x hx
    exact EReal.toENNReal_le_toENNReal ((le_max_right _ _).trans hx)
  exact ⟨hp, hn, (pma11_25_ereal_representative hf hp hn).2.2⟩

/-- 11.29 with extended-real summands. At the null exceptional set EReal's
total addition supplies a representative; no undefined opposite-infinity sum
is used to determine the integral. The conclusion includes both source part
finiteness conditions for the sum. -/
theorem pma11_29_ereal {f g : X → EReal} (hf : Measurable f) (hg : Measurable g)
    (hfp : (∫⁻ x, (f x).toENNReal ∂μ) < ∞)
    (hfn : (∫⁻ x, (-f x).toENNReal ∂μ) < ∞)
    (hgp : (∫⁻ x, (g x).toENNReal ∂μ) < ∞)
    (hgn : (∫⁻ x, (-g x).toENNReal ∂μ) < ∞) :
    (∫⁻ x, (f x + g x).toENNReal ∂μ) < ∞ ∧
      (∫⁻ x, (-(f x + g x)).toENNReal ∂μ) < ∞ ∧
      (∫ x, (f x + g x).toReal ∂μ) =
        (∫ x, (f x).toReal ∂μ) + ∫ x, (g x).toReal ∂μ := by
  have hff := pma11_25_ereal_finite_ae hf hfp hfn
  have hgf := pma11_25_ereal_finite_ae hg hgp hgn
  have hfi := (pma11_25_ereal_representative hf hfp hfn).2.2
  have hgi := (pma11_25_ereal_representative hg hgp hgn).2.2
  have hsum : ∀ᵐ x ∂μ, f x + g x ≠ ⊤ ∧ f x + g x ≠ ⊥ := by
    filter_upwards [hff, hgf] with x hx hy
    exact ⟨EReal.add_ne_top hx.1 hy.1, EReal.add_ne_bot_iff.mpr ⟨hx.2, hy.2⟩⟩
  have heq : (fun x => (f x).toReal + (g x).toReal) =ᵐ[μ]
      (fun x => (f x + g x).toReal) := by
    filter_upwards [hff, hgf] with x hx hy
    exact (EReal.toReal_add hx.1 hx.2 hy.1 hy.2).symm
  have hi := (hfi.add hgi).congr heq
  have hp := pma11_25_ereal_parts_finite hsum hi
  refine ⟨hp.1, hp.2, ?_⟩
  rw [← integral_congr_ae heq, integral_add hfi hgi]

private theorem ereal_finite_of_abs_le_real {a : EReal} {b : ℝ}
    (h : max a (-a) ≤ (b : EReal)) :
    a ≠ ⊤ ∧ a ≠ ⊥ ∧ |a.toReal| ≤ b := by
  have ht : a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) ((le_max_left _ _).trans h)
  have hnt : -a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top b) ((le_max_right _ _).trans h)
  have hb : a ≠ ⊥ := by simpa only [ne_eq, EReal.neg_eq_top_iff] using hnt
  refine ⟨ht, hb, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hh := EReal.toReal_le_toReal ((le_max_right _ _).trans h)
      (by simpa only [ne_eq, EReal.neg_eq_bot_iff] using ht) (EReal.coe_ne_top b)
    have hh' : -a.toReal ≤ b := by simpa only [EReal.toReal_neg_eq, EReal.toReal_coe] using hh
    exact neg_le.mp hh'
  · simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal ((le_max_left _ _).trans h) hb (EReal.coe_ne_top b)

/-- The signed-integral formula also applies to an almost-everywhere measurable
representative, without assuming completeness of the underlying measure. -/
theorem pma11_25_ereal_integral_eq_of_representative {f : X → EReal}
    (hfin : ∀ᵐ x ∂μ, f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hf : Integrable (fun x => (f x).toReal) μ) :
    (∫ x, (f x).toReal ∂μ) =
      (∫⁻ x, (f x).toENNReal ∂μ).toReal -
        (∫⁻ x, (-f x).toENNReal ∂μ).toReal := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  have hp : (∫⁻ x, ENNReal.ofReal (f x).toReal ∂μ) = ∫⁻ x, (f x).toENNReal ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    exact (EReal.toENNReal_of_ne_top hx.1).symm
  have hn : (∫⁻ x, ENNReal.ofReal (-(f x).toReal) ∂μ) = ∫⁻ x, (-f x).toENNReal ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hfin] with x hx
    rw [EReal.toENNReal_of_ne_top (by simpa using hx.2), EReal.toReal_neg_eq]
  rw [hp, hn]

/-- 11.32 for extended-real sequence inputs, with the actual positive-minus-
negative signed integrals. A real integrable majorant suffices by the finite
representative theorem above. For the source's almost-everywhere convergence
variant, the limit has an almost-everywhere measurable representative; arbitrary
values on a null set need not be strictly measurable on an incomplete space.
This qualification repairs that implicit measurability issue in the source. -/
theorem pma11_32_ereal {F : ℕ → X → EReal} {f : X → EReal} {g : X → ℝ}
    (hF : ∀ n, Measurable (F n)) (hg : Integrable g μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, max (F n x) (-F n x) ≤ (g x : EReal))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    (∀ n, (∫⁻ x, (F n x).toENNReal ∂μ) < ∞ ∧
      (∫⁻ x, (-F n x).toENNReal ∂μ) < ∞) ∧
    ((∫⁻ x, (f x).toENNReal ∂μ) < ∞ ∧
      (∫⁻ x, (-f x).toENNReal ∂μ) < ∞) ∧
    Tendsto (fun n => (∫⁻ x, (F n x).toENNReal ∂μ).toReal -
      (∫⁻ x, (-F n x).toENNReal ∂μ).toReal) atTop
      (𝓝 ((∫⁻ x, (f x).toENNReal ∂μ).toReal -
        (∫⁻ x, (-f x).toENNReal ∂μ).toReal)) := by
  have hFnfin : ∀ n, ∀ᵐ x ∂μ, F n x ≠ ⊤ ∧ F n x ≠ ⊥ := by
    intro n
    filter_upwards [hbound n] with x hx
    exact ⟨(ereal_finite_of_abs_le_real hx).1, (ereal_finite_of_abs_le_real hx).2.1⟩
  have hrealbound : ∀ n, ∀ᵐ x ∂μ, ‖(F n x).toReal‖ ≤ g x := by
    intro n
    filter_upwards [hbound n] with x hx
    simpa only [Real.norm_eq_abs] using (ereal_finite_of_abs_le_real hx).2.2
  have hall : ∀ᵐ x ∂μ, ∀ n, max (F n x) (-F n x) ≤ (g x : EReal) :=
    ae_all_iff.mpr hbound
  have hflim : ∀ᵐ x ∂μ, (f x ≠ ⊤ ∧ f x ≠ ⊥) ∧
      Tendsto (fun n => (F n x).toReal) atTop (𝓝 (f x).toReal) := by
    filter_upwards [hall, hlim] with x hx hl
    have hb : max (f x) (-f x) ≤ (g x : EReal) := by
      apply max_le
      · exact le_of_tendsto' hl (fun n => (le_max_left _ _).trans (hx n))
      · exact le_of_tendsto' hl.neg (fun n => (le_max_right _ _).trans (hx n))
    have hf := ereal_finite_of_abs_le_real hb
    exact ⟨⟨hf.1, hf.2.1⟩, (EReal.tendsto_toReal hf.1 hf.2.1).comp hl⟩
  have hdct := pma11_32 (fun n => (hF n).ereal_toReal.aestronglyMeasurable)
    hg hrealbound (hflim.mono (fun _ hx => hx.2))
  have hffin : ∀ᵐ x ∂μ, f x ≠ ⊤ ∧ f x ≠ ⊥ := hflim.mono (fun _ hx => hx.1)
  refine ⟨fun n => pma11_25_ereal_parts_finite (hFnfin n) (hdct.1 n),
    pma11_25_ereal_parts_finite hffin hdct.2.1, ?_⟩
  have heq : (fun n => ∫ x, (F n x).toReal ∂μ) =
      (fun n => (∫⁻ x, (F n x).toENNReal ∂μ).toReal -
        (∫⁻ x, (-F n x).toENNReal ∂μ).toReal) :=
    funext fun n => pma11_25_ereal_integral_eq_of_representative (hFnfin n) (hdct.1 n)
  simpa only [heq, pma11_25_ereal_integral_eq_of_representative hffin hdct.2.1] using hdct.2.2

/-- The signed extended expression from 11.22 is invariant under null deletion,
including cases with one infinite part. The source only defines the signed
integral when the two part integrals are not both infinite; equality of both
parts below also proves this admissibility condition is preserved. -/
theorem pma11_24_corollary_ereal (f : X → EReal) {A B : Set X}
    (hBA : B ⊆ A) (hnull : μ (A \ B) = 0) :
    (((∫⁻ x in A, (f x).toENNReal ∂μ) : EReal) -
      ((∫⁻ x in A, (-f x).toENNReal ∂μ) : EReal)) =
      (((∫⁻ x in B, (f x).toENNReal ∂μ) : EReal) -
        ((∫⁻ x in B, (-f x).toENNReal ∂μ) : EReal)) := by
  rw [pma11_24_corollary_nonnegative (fun x => (f x).toENNReal) hBA hnull,
    pma11_24_corollary_nonnegative (fun x => (-f x).toENNReal) hBA hnull]

/-- 11.25 for the signed extended expression from 11.22: equality almost
everywhere preserves the integral on every subset, including infinite integrals
whenever at least one part integral is finite. -/
theorem pma11_25_ereal_integral_congr {f g : X → EReal} (h : f =ᵐ[μ] g) (A : Set X) :
    (((∫⁻ x in A, (f x).toENNReal ∂μ) : EReal) -
      ((∫⁻ x in A, (-f x).toENNReal ∂μ) : EReal)) =
      (((∫⁻ x in A, (g x).toENNReal ∂μ) : EReal) -
        ((∫⁻ x in A, (-g x).toENNReal ∂μ) : EReal)) := by
  have hp : (∫⁻ x in A, (f x).toENNReal ∂μ) = ∫⁻ x in A, (g x).toENNReal ∂μ :=
    lintegral_congr_ae (ae_restrict_of_ae (h.fun_comp EReal.toENNReal))
  have hn : (∫⁻ x in A, (-f x).toENNReal ∂μ) = ∫⁻ x in A, (-g x).toENNReal ∂μ :=
    lintegral_congr_ae (ae_restrict_of_ae (h.fun_comp (fun a => (-a).toENNReal)))
  rw [hp, hn]

/-- 11.25: nonnegative integrals are also unchanged on every subset. -/
theorem pma11_25_lintegral_eq {f g : X → ℝ≥0∞} (h : f =ᵐ[μ] g) (A : Set X) :
    ∫⁻ x in A, f x ∂μ = ∫⁻ x in A, g x ∂μ :=
  lintegral_congr_ae (ae_restrict_of_ae h)

/-- 11.28: monotone convergence, as a genuine limit in the extended half-line. -/
theorem pma11_28 {F : ℕ → X → ℝ≥0∞} (hF : ∀ n, Measurable (F n))
    (hmono : Monotone F) :
    Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop
      (𝓝 (∫⁻ x, ⨆ n, F n x ∂μ)) := by
  rw [lintegral_iSup hF hmono]
  exact tendsto_atTop_iSup (fun i j hij => lintegral_mono (hmono hij))

/-- The monotone-limit integrand in 11.28 is measurable, including infinite values. -/
theorem pma11_28_measurable_sup {F : ℕ → X → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) : Measurable (fun x => ⨆ n, F n x) :=
  .iSup hF

/-- 11.28 in the book's pointwise-limit formulation. -/
theorem pma11_28_limit {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) (hmono : Monotone F)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ)) := by
  have heq : (fun x => ⨆ n, F n x) = f := funext fun x =>
    tendsto_nhds_unique (tendsto_atTop_iSup (fun i j hij => hmono hij x)) (hlim x)
  simpa only [heq] using pma11_28 (μ := μ) hF hmono

/-- 11.28 with almost-everywhere monotonicity and convergence. This form makes
restriction to the book's integration set explicit: no behavior outside that
set is constrained. -/
theorem pma11_28_ae {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone (fun n => F n x))
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫⁻ x, F n x ∂μ) atTop (𝓝 (∫⁻ x, f x ∂μ)) :=
  lintegral_tendsto_of_tendsto_of_monotone hF hmono hlim

/-- 11.28 with monotonicity and convergence assumed only on the measurable
integration set, as printed in the source. -/
theorem pma11_28_on {E : Set X} (hE : MeasurableSet E)
    {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) (μ.restrict E))
    (hmono : ∀ x ∈ E, Monotone (fun n => F n x))
    (hlim : ∀ x ∈ E, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => ∫⁻ x in E, F n x ∂μ) atTop (𝓝 (∫⁻ x in E, f x ∂μ)) := by
  apply pma11_28_ae hF
  · filter_upwards [ae_restrict_mem hE] with x hx
    exact hmono x hx
  · filter_upwards [ae_restrict_mem hE] with x hx
    exact hlim x hx

/-- 11.30: nonnegative series can be integrated termwise, without finiteness. -/
theorem pma11_30 {F : ℕ → X → ℝ≥0∞} (hF : ∀ n, Measurable (F n)) :
    (∫⁻ x, ∑' n, F n x ∂μ) = ∑' n, ∫⁻ x, F n x ∂μ :=
  lintegral_tsum (fun n => (hF n).aemeasurable)

/-- 11.30 with measure-local measurability, suitable for `μ.restrict E` without
imposing measurability or values outside the source integration set. -/
theorem pma11_30_ae {F : ℕ → X → ℝ≥0∞} (hF : ∀ n, AEMeasurable (F n) μ) :
    (∫⁻ x, ∑' n, F n x ∂μ) = ∑' n, ∫⁻ x, F n x ∂μ :=
  lintegral_tsum hF

/-- The series integrand in 11.30 is measurable. -/
theorem pma11_30_measurable_sum {F : ℕ → X → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) : Measurable (fun x => ∑' n, F n x) :=
  Measurable.tsum hF

/-- 11.31: Fatou's inequality in the extended half-line. -/
theorem pma11_31 {F : ℕ → X → ℝ≥0∞} (hF : ∀ n, Measurable (F n)) :
    (∫⁻ x, liminf (fun n => F n x) atTop ∂μ) ≤
      liminf (fun n => ∫⁻ x, F n x ∂μ) atTop :=
  lintegral_liminf_le hF

/-- 11.31 with measure-local measurability, including restricted measures. -/
theorem pma11_31_ae {F : ℕ → X → ℝ≥0∞} (hF : ∀ n, AEMeasurable (F n) μ) :
    (∫⁻ x, liminf (fun n => F n x) atTop ∂μ) ≤
      liminf (fun n => ∫⁻ x, F n x ∂μ) atTop :=
  lintegral_liminf_le' hF

/-- The lower-limit integrand in 11.31 is measurable. -/
theorem pma11_31_measurable_liminf {F : ℕ → X → ℝ≥0∞}
    (hF : ∀ n, Measurable (F n)) :
    Measurable (fun x => liminf (fun n => F n x) atTop) :=
  .liminf hF

end Rudin.PMA.Chapter11.SecondHalf
