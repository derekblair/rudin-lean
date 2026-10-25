import Mathlib

/-!
# Chapter 11, 11.21–11.23: the Lebesgue integral

Nonnegative quantities use `ℝ≥0∞`; signed integrands and integrals use `EReal`,
including both infinite values. The signed integral is a total Lean expression;
The source takes the integration set `E` to be measurable throughout.
`IntegralDefined` records the integrand conditions on that standing domain.
Native restriction also gives these Lean expressions values for arbitrary `E`;
this extension is not an assertion that the book defines such integrals.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal

namespace Rudin.PMA.Chapter11

variable {X : Type*} [MeasurableSpace X]

/-- 11.21 (52): the integral of a nonnegative measurable simple function. -/
noncomputable def simpleIntegral (μ : Measure X) (E : Set X)
    (s : SimpleFunc X ℝ≥0) : ℝ≥0∞ :=
  (s.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (μ.restrict E)

/-- 11.21 (53): the nonnegative integral, allowing the value infinity.
The native lower-integral expression also evaluates nonmeasurable functions;
agreement with Rudin's definition is asserted on measurable integrands. -/
noncomputable def nonnegativeIntegral (μ : Measure X) (E : Set X)
    (f : X → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ x in E, f x ∂μ

/-- 11.21: the defining supremum uses finite-valued, measurable simple functions. -/
theorem nonnegativeIntegral_eq_sup (μ : Measure X) (E : Set X) (f : X → ℝ≥0∞) :
    nonnegativeIntegral μ E f =
      ⨆ (s : SimpleFunc X ℝ≥0) (_ : ∀ x, (s x : ℝ≥0∞) ≤ f x),
        simpleIntegral μ E s :=
  lintegral_eq_nnreal f (μ.restrict E)

/-- 11.21 (54): the two definitions agree on simple functions. -/
theorem nonnegativeIntegral_simple (μ : Measure X) (E : Set X) (s : SimpleFunc X ℝ≥0) :
    nonnegativeIntegral μ E (fun x => (s x : ℝ≥0∞)) = simpleIntegral μ E s :=
  (s.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral_eq_lintegral (μ.restrict E)

/-- 11.21 (52), in the range/fiber representation of a simple function. -/
theorem simpleIntegral_eq_sum (μ : Measure X) {E : Set X} (_hE : MeasurableSet E)
    (s : SimpleFunc X ℝ≥0) :
    simpleIntegral μ E s = ∑ c ∈ s.range, (c : ℝ≥0∞) * μ (E ∩ s ⁻¹' {c}) := by
  rw [simpleIntegral, SimpleFunc.map_lintegral]
  apply Finset.sum_congr rfl
  intro c hc
  rw [Measure.restrict_apply (s.measurableSet_fiber c), Set.inter_comm]

/-- 11.22: the positive integral of an extended-real function. -/
noncomputable def positiveIntegral (μ : Measure X) (E : Set X) (f : X → EReal) : ℝ≥0∞ :=
  nonnegativeIntegral μ E (fun x => (f x).toENNReal)

/-- 11.22: the negative integral of an extended-real function. -/
noncomputable def negativeIntegral (μ : Measure X) (E : Set X) (f : X → EReal) : ℝ≥0∞ :=
  positiveIntegral μ E (fun x => -f x)

/-- 11.22: at least one part is finite; the integral may itself be infinite.
As throughout the source integration section, `E` is assumed measurable when
interpreting this predicate as Rudin's domain condition. -/
def IntegralDefined (μ : Measure X) (E : Set X) (f : X → EReal) : Prop :=
  Measurable f ∧ (positiveIntegral μ E f ≠ ∞ ∨ negativeIntegral μ E f ≠ ∞)

/-- 11.22 (56): signed extended-real integral. Only `IntegralDefined` values are
assigned mathematical meaning; Lean's total value outside this domain is unused. -/
noncomputable def lebesgueIntegral (μ : Measure X) (E : Set X) (f : X → EReal) : EReal :=
  (positiveIntegral μ E f : EReal) - (negativeIntegral μ E f : EReal)

/-- 11.22: membership in `L(μ)` means measurability and finiteness of both parts. -/
def LebesgueIntegrable (μ : Measure X) (E : Set X) (f : X → EReal) : Prop :=
  Measurable f ∧ positiveIntegral μ E f ≠ ∞ ∧ negativeIntegral μ E f ≠ ∞

theorem LebesgueIntegrable.integralDefined {μ : Measure X} {E : Set X} {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) : IntegralDefined μ E f :=
  ⟨hf.1, Or.inl hf.2.1⟩

/-- 11.22: for an integrable function, the integral is finite. -/
theorem LebesgueIntegrable.integral_finite {μ : Measure X} {E : Set X} {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) :
    lebesgueIntegral μ E f ≠ ⊤ ∧ lebesgueIntegral μ E f ≠ ⊥ := by
  have hp := EReal.coe_ennreal_toReal hf.2.1
  have hn := EReal.coe_ennreal_toReal hf.2.2
  rw [lebesgueIntegral, ← hp, ← hn, ← EReal.coe_sub]
  exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩

private theorem positiveIntegral_mono (μ : Measure X) {E : Set X}
    (hE : MeasurableSet E) {f g : X → EReal} (hfg : ∀ x ∈ E, f x ≤ g x) :
    positiveIntegral μ E f ≤ positiveIntegral μ E g := by
  exact setLIntegral_mono' hE fun x hx => EReal.toENNReal_le_toENNReal (hfg x hx)

private theorem negativeIntegral_antitone (μ : Measure X) {E : Set X}
    (hE : MeasurableSet E) {f g : X → EReal} (hfg : ∀ x ∈ E, f x ≤ g x) :
    negativeIntegral μ E g ≤ negativeIntegral μ E f := by
  exact positiveIntegral_mono μ hE fun x hx => EReal.neg_le_neg_iff.mpr (hfg x hx)

/-- 11.23(c): order preservation for integrable extended-real functions. The
proof also gives order preservation whenever the signed expressions are formed. -/
theorem lebesgueIntegral_mono (μ : Measure X) {E : Set X} (hE : MeasurableSet E)
    {f g : X → EReal} (hfg : ∀ x ∈ E, f x ≤ g x) :
    lebesgueIntegral μ E f ≤ lebesgueIntegral μ E g :=
  EReal.sub_le_sub
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (positiveIntegral_mono μ hE hfg))
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr (negativeIntegral_antitone μ hE hfg))

/-- Integral of a finite real constant over a set of finite measure. -/
theorem lebesgueIntegral_const (μ : Measure X) (E : Set X) (hμ : μ E ≠ ∞) (c : ℝ) :
    lebesgueIntegral μ E (fun _ => (c : EReal)) = (c * (μ E).toReal : ℝ) := by
  simp only [lebesgueIntegral, negativeIntegral, positiveIntegral, nonnegativeIntegral,
    EReal.real_coe_toENNReal, ← EReal.coe_neg, setLIntegral_const]
  rw [← EReal.coe_ennreal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ),
    ← EReal.coe_ennreal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ),
    ← EReal.coe_sub]
  congr 1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal']
  rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]

/-- 11.23(a): bounded measurable extended-real functions on finite-measure sets
are integrable. Boundedness is expressed by finite real lower and upper bounds. -/
theorem lebesgueIntegrable_of_bounded (μ : Measure X) {E : Set X}
    (hE : MeasurableSet E) (hμ : μ E ≠ ∞) {f : X → EReal} (hf : Measurable f)
    {a b : ℝ} (hbound : ∀ x ∈ E, (a : EReal) ≤ f x ∧ f x ≤ (b : EReal)) :
    LebesgueIntegrable μ E f := by
  refine ⟨hf, ne_top_of_le_ne_top ?_ (positiveIntegral_mono μ hE (fun x hx => (hbound x hx).2)),
    ne_top_of_le_ne_top ?_ (negativeIntegral_antitone μ hE (fun x hx => (hbound x hx).1))⟩
  · simpa [positiveIntegral, nonnegativeIntegral] using
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ (a := ENNReal.ofReal b)
  · simpa [negativeIntegral, positiveIntegral, nonnegativeIntegral, ← EReal.coe_neg] using
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ (a := ENNReal.ofReal (-a))

/-- 11.23(b): the integral lies between the constant bounds times the measure. -/
theorem lebesgueIntegral_bounds (μ : Measure X) {E : Set X}
    (hE : MeasurableSet E) (hμ : μ E ≠ ∞) {f : X → EReal} {a b : ℝ}
    (hbound : ∀ x ∈ E, (a : EReal) ≤ f x ∧ f x ≤ (b : EReal)) :
    ((a * (μ E).toReal : ℝ) : EReal) ≤ lebesgueIntegral μ E f ∧
      lebesgueIntegral μ E f ≤ ((b * (μ E).toReal : ℝ) : EReal) := by
  constructor
  · rw [← lebesgueIntegral_const μ E hμ a]
    exact lebesgueIntegral_mono μ hE fun x hx => (hbound x hx).1
  · rw [← lebesgueIntegral_const μ E hμ b]
    exact lebesgueIntegral_mono μ hE fun x hx => (hbound x hx).2

/-- 11.23(e): integration over a null set is zero, including infinite integrands. -/
theorem lebesgueIntegral_null (μ : Measure X) (E : Set X) (hE : μ E = 0)
    (f : X → EReal) : lebesgueIntegral μ E f = 0 := by
  simp [lebesgueIntegral, negativeIntegral, positiveIntegral, nonnegativeIntegral,
    Measure.restrict_eq_zero.mpr hE]

/-- 11.23(f): restriction to a measurable subset preserves integrability.
Generality: the native-restriction proof also covers arbitrary subsets `A`. -/
theorem LebesgueIntegrable.mono_set {μ : Measure X} {A E : Set X} {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) (hAE : A ⊆ E) : LebesgueIntegrable μ A f :=
  ⟨hf.1, ne_top_of_le_ne_top hf.2.1 (lintegral_mono_set hAE),
    ne_top_of_le_ne_top hf.2.2 (lintegral_mono_set hAE)⟩


private theorem positiveIntegral_const_mul_nonneg (μ : Measure X) (E : Set X)
    (f : X → EReal) {c : ℝ} (hc : 0 ≤ c) :
    positiveIntegral μ E (fun x => (c : EReal) * f x) =
      ENNReal.ofReal c * positiveIntegral μ E f := by
  simp only [positiveIntegral, nonnegativeIntegral,
    EReal.toENNReal_mul (EReal.coe_nonneg.mpr hc), EReal.real_coe_toENNReal]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

private theorem negativeIntegral_const_mul_nonneg (μ : Measure X) (E : Set X)
    (f : X → EReal) {c : ℝ} (hc : 0 ≤ c) :
    negativeIntegral μ E (fun x => (c : EReal) * f x) =
      ENNReal.ofReal c * negativeIntegral μ E f := by
  simpa only [negativeIntegral, mul_neg] using
    positiveIntegral_const_mul_nonneg μ E (fun x => -f x) hc

private theorem lebesgueIntegral_const_mul_nonneg (μ : Measure X) (E : Set X)
    (f : X → EReal) {c : ℝ} (hc : 0 ≤ c) :
    lebesgueIntegral μ E (fun x => (c : EReal) * f x) =
      (c : EReal) * lebesgueIntegral μ E f := by
  rw [lebesgueIntegral, positiveIntegral_const_mul_nonneg μ E f hc,
    negativeIntegral_const_mul_nonneg μ E f hc, EReal.coe_ennreal_mul,
    EReal.coe_ennreal_mul, EReal.coe_ennreal_ofReal, max_eq_left hc,
    ← EReal.mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc) (EReal.coe_ne_top c)]
  rfl

private theorem LebesgueIntegrable.neg {μ : Measure X} {E : Set X} {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) : LebesgueIntegrable μ E (fun x => -f x) := by
  exact ⟨hf.1.neg, hf.2.2, by simpa [negativeIntegral] using hf.2.1⟩

private theorem lebesgueIntegral_neg {μ : Measure X} {E : Set X} {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) :
    lebesgueIntegral μ E (fun x => -f x) = -lebesgueIntegral μ E f := by
  simp only [lebesgueIntegral, negativeIntegral, neg_neg]
  rw [EReal.neg_sub (Or.inl (EReal.coe_ennreal_ne_bot _))
    (Or.inl (by simpa using hf.2.1)), sub_eq_add_neg, add_comm]

private theorem LebesgueIntegrable.const_mul_nonneg {μ : Measure X} {E : Set X}
    {f : X → EReal} (hf : LebesgueIntegrable μ E f) {c : ℝ} (hc : 0 ≤ c) :
    LebesgueIntegrable μ E (fun x => (c : EReal) * f x) := by
  refine ⟨measurable_const.mul hf.1, ?_, ?_⟩
  · rw [positiveIntegral_const_mul_nonneg μ E f hc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.1
  · rw [negativeIntegral_const_mul_nonneg μ E f hc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.2

/-- 11.23(d): multiplication by any finite real constant preserves integrability
and commutes with integration, including for extended-real integrands. -/
theorem LebesgueIntegrable.const_mul {μ : Measure X} {E : Set X} {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) (c : ℝ) :
    LebesgueIntegrable μ E (fun x => (c : EReal) * f x) ∧
      lebesgueIntegral μ E (fun x => (c : EReal) * f x) =
        (c : EReal) * lebesgueIntegral μ E f := by
  by_cases hc : 0 ≤ c
  · exact ⟨hf.const_mul_nonneg hc, lebesgueIntegral_const_mul_nonneg μ E f hc⟩
  · have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_not_ge hc)
    have heq : (fun x => (c : EReal) * f x) = fun x => (-c : ℝ) * (-f x) := by
      funext x
      simp only [EReal.coe_neg, neg_mul_neg]
    rw [heq]
    refine ⟨hf.neg.const_mul_nonneg hnc, ?_⟩
    rw [lebesgueIntegral_const_mul_nonneg μ E (fun x => -f x) hnc,
      lebesgueIntegral_neg hf, EReal.coe_neg, neg_mul_neg]


/-- 11.22: within the defined domain, finiteness is exactly integrability. -/
theorem integralDefined_integrable_iff {μ : Measure X} {E : Set X} {f : X → EReal}
    (hf : IntegralDefined μ E f) :
    LebesgueIntegrable μ E f ↔
      lebesgueIntegral μ E f ≠ ⊤ ∧ lebesgueIntegral μ E f ≠ ⊥ := by
  refine ⟨LebesgueIntegrable.integral_finite, fun h => ⟨hf.1, ?_, ?_⟩⟩
  · intro hp
    have hn : negativeIntegral μ E f ≠ ∞ := hf.2.resolve_left (not_not.mpr hp)
    apply h.1
    simp [lebesgueIntegral, hp, sub_eq_add_neg, hn]
  · intro hn
    apply h.2
    simp [lebesgueIntegral, hn, sub_eq_add_neg]

/-- The nonnegative and signed definitions agree on nonnegative extended-real
functions, including at positive infinity. -/
theorem lebesgueIntegral_nonneg (μ : Measure X) (E : Set X) (f : X → EReal)
    (hf : ∀ x, 0 ≤ f x) :
    lebesgueIntegral μ E f = (positiveIntegral μ E f : EReal) := by
  have hn : negativeIntegral μ E f = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    exact Filter.Eventually.of_forall fun x =>
      EReal.toENNReal_of_nonpos (by simpa using EReal.neg_le_neg_iff.mpr (hf x))
  simp [lebesgueIntegral, hn]

private theorem integrable_positive_finite {μ : Measure X} {f : X → ℝ}
    (hf : Integrable f μ) : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≠ ∞ := by
  apply ne_top_of_le_ne_top ((hasFiniteIntegral_iff_norm f).mp hf.2).ne
  exact lintegral_mono fun x => ENNReal.ofReal_le_ofReal (le_abs_self (f x))

/-- For finite real-valued measurable functions, book integrability agrees with
Mathlib integrability. This is a bridge, not a restriction of 11.22's domain. -/
theorem lebesgueIntegrable_real_iff (μ : Measure X) (E : Set X) {f : X → ℝ}
    (hf : Measurable f) :
    LebesgueIntegrable μ E (fun x => (f x : EReal)) ↔ IntegrableOn f E μ := by
  constructor
  · intro h
    have hp := integrable_toReal_of_lintegral_ne_top hf.ennreal_ofReal.aemeasurable h.2.1
    have hn := integrable_toReal_of_lintegral_ne_top hf.neg.ennreal_ofReal.aemeasurable
      (by simpa [negativeIntegral, positiveIntegral, nonnegativeIntegral, ← EReal.coe_neg] using h.2.2)
    have heq : (fun x => (ENNReal.ofReal (f x)).toReal -
        (ENNReal.ofReal (-f x)).toReal) = f := by
      funext x
      simp [ENNReal.toReal_ofReal', max_zero_sub_max_neg_zero_eq_self]
    rw [← heq]
    exact hp.sub hn
  · intro h
    exact ⟨hf.coe_real_ereal, integrable_positive_finite h,
      by simpa [negativeIntegral, positiveIntegral, nonnegativeIntegral, ← EReal.coe_neg]
        using integrable_positive_finite h.neg⟩

/-- Compatibility of the signed integral with the usual native real integral. -/
theorem lebesgueIntegral_real (μ : Measure X) (E : Set X) {f : X → ℝ}
    (hf : IntegrableOn f E μ) :
    lebesgueIntegral μ E (fun x => (f x : EReal)) = ((∫ x in E, f x ∂μ : ℝ) : EReal) := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf]
  simp only [lebesgueIntegral, negativeIntegral, positiveIntegral, nonnegativeIntegral,
    EReal.real_coe_toENNReal, ← EReal.coe_neg]
  have hn := integrable_positive_finite hf.neg
  simp only [Pi.neg_apply] at hn
  rw [EReal.coe_sub, EReal.coe_ennreal_toReal (integrable_positive_finite hf),
    EReal.coe_ennreal_toReal hn]


/-- On a null set every measurable extended-real function is integrable, so
11.23(e) concerns an integral in the domain of Definition 11.22. -/
theorem lebesgueIntegrable_null (μ : Measure X) (E : Set X) (hE : μ E = 0)
    {f : X → EReal} (hf : Measurable f) : LebesgueIntegrable μ E f := by
  refine ⟨hf, ?_, ?_⟩ <;>
    simp [negativeIntegral, positiveIntegral, nonnegativeIntegral, Measure.restrict_eq_zero.mpr hE]

end Rudin.PMA.Chapter11



