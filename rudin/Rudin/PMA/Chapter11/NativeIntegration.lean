import Rudin.PMA.Chapter11.Integrals
import Rudin.PMA.Chapter11.Integration

/-!
# Compatibility with the first-half integral definitions

The first-half definitions of 11.21–11.22 now have explicit connections to the
integral formulas verified in `Integrals`. These are compatibility results and
native-facing second-half theorems; no first-half definition is duplicated.
The almost-everywhere dominated-convergence wrapper states measurability of
the chosen limit explicitly, as required by `LebesgueIntegrable` on a possibly
incomplete measure space. The unrestricted representative form is already in
`pma11_32_ereal`.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace Rudin.PMA.Chapter11.SecondHalf

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {E : Set X}

theorem native_simpleIntegral_compat (s : SimpleFunc X ℝ≥0) :
    simpleIntegral μ E s = (s.map ((↑) : ℝ≥0 → ℝ≥0∞)).lintegral (μ.restrict E) := rfl

theorem native_nonnegativeIntegral_compat (f : X → ℝ≥0∞) :
    nonnegativeIntegral μ E f = ∫⁻ x in E, f x ∂μ := rfl

theorem native_integrable_iff {f : X → EReal} :
    LebesgueIntegrable μ E f ↔ Measurable f ∧
      (∫⁻ x in E, (f x).toENNReal ∂μ) < ∞ ∧
      (∫⁻ x in E, (-f x).toENNReal ∂μ) < ∞ := by
  simp only [LebesgueIntegrable, positiveIntegral, negativeIntegral,
    nonnegativeIntegral, lt_top_iff_ne_top]

theorem native_integralDefined_iff {f : X → EReal} :
    IntegralDefined μ E f ↔ Measurable f ∧
      ((∫⁻ x in E, (f x).toENNReal ∂μ) < ∞ ∨
        (∫⁻ x in E, (-f x).toENNReal ∂μ) < ∞) := by
  simp only [IntegralDefined, positiveIntegral, negativeIntegral,
    nonnegativeIntegral, lt_top_iff_ne_top]

theorem native_lebesgueIntegral_compat (f : X → EReal) :
    lebesgueIntegral μ E f = ((∫⁻ x in E, (f x).toENNReal ∂μ) : EReal) -
      ((∫⁻ x in E, (-f x).toENNReal ∂μ) : EReal) := rfl

/-- 11.25 with the first half's literal integrability predicate. -/
theorem pma11_25_native {f : X → EReal} (hf : LebesgueIntegrable μ E f) :
    (∀ᵐ x ∂μ.restrict E, f x ≠ ⊤ ∧ f x ≠ ⊥) ∧
      Measurable (fun x => (f x).toReal) ∧
      (fun x => ((f x).toReal : EReal)) =ᵐ[μ.restrict E] f ∧
      IntegrableOn (fun x => (f x).toReal) E μ := by
  have h := native_integrable_iff.mp hf
  exact ⟨pma11_25_ereal_finite_ae h.1 h.2.1 h.2.2,
    pma11_25_ereal_representative h.1 h.2.1 h.2.2⟩

/-- The native signed integral equals the integral of the proved real representative. -/
theorem native_integral_eq_representative {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) :
    lebesgueIntegral μ E f = ((∫ x in E, (f x).toReal ∂μ : ℝ) : EReal) := by
  have h := native_integrable_iff.mp hf
  exact (pma11_25_ereal_integral_coe h.1 h.2.1 h.2.2).symm

theorem native_integral_eq_coe_parts {f : X → EReal}
    (hf : LebesgueIntegrable μ E f) :
    lebesgueIntegral μ E f =
      (((positiveIntegral μ E f).toReal - (negativeIntegral μ E f).toReal : ℝ) : EReal) := by
  rw [lebesgueIntegral, ← EReal.coe_ennreal_toReal hf.2.1,
    ← EReal.coe_ennreal_toReal hf.2.2, ← EReal.coe_sub]

/-- 11.24(a) in the native nonnegative integral notation. -/
theorem pma11_24_native_nonnegative (f : X → ℝ≥0∞) {A : ℕ → Set X}
    (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    nonnegativeIntegral μ (⋃ n, A n) f = ∑' n, nonnegativeIntegral μ (A n) f :=
  pma11_24_nonnegative f hA hdisj

/-- 11.24(b): native signed set integrals form a convergent EReal series. -/
theorem pma11_24_native {f : X → EReal} (hf : LebesgueIntegrable μ univ f)
    {A : ℕ → Set X} (hA : ∀ n, MeasurableSet (A n))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    HasSum (fun n => lebesgueIntegral μ (A n) f) (lebesgueIntegral μ (⋃ n, A n) f) := by
  have hi : Integrable (fun x => (f x).toReal) μ := by
    simpa only [IntegrableOn, Measure.restrict_univ] using (pma11_25_native hf).2.2.2
  have hs := pma11_24_integrable hi hA hdisj
  let c : ℝ →+ EReal := ⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩
  have hc : Continuous c := continuous_coe_real_ereal
  have heq (S : Set X) : c (∫ x in S, (f x).toReal ∂μ) = lebesgueIntegral μ S f :=
    (native_integral_eq_representative (hf.mono_set (subset_univ S))).symm
  simpa only [Function.comp_def, heq] using hs.map c hc

/-- 11.26: native absolute integrability and the integral absolute-value bound. -/
theorem pma11_26_native {f : X → EReal} (hf : LebesgueIntegrable μ E f) :
    LebesgueIntegrable μ E (fun x => extendedAbs (f x)) ∧
      (lebesgueIntegral μ E f).abs ≤ nonnegativeIntegral μ E (fun x => (f x).abs) := by
  have h := native_integrable_iff.mp hf
  have ha := pma11_26_ereal h.1 h.2.1 h.2.2
  have hp : positiveIntegral μ E (fun x => extendedAbs (f x)) =
      ∫⁻ x in E, (f x).abs ∂μ := by
    simp only [positiveIntegral, nonnegativeIntegral, extendedAbs_eq, EReal.toENNReal_coe]
  have hn : negativeIntegral μ E (fun x => extendedAbs (f x)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro x
    apply EReal.toENNReal_of_nonpos
    simpa only [neg_zero] using EReal.neg_le_neg_iff.mpr
      (show (0 : EReal) ≤ extendedAbs (f x) by
        rw [extendedAbs_eq]
        exact EReal.coe_ennreal_nonneg _)
  refine ⟨⟨hf.1.max hf.1.neg, by rw [hp]; exact ha.1.ne, by rw [hn]; exact ENNReal.zero_ne_top⟩, ?_⟩
  rw [native_integral_eq_representative hf, EReal.abs_def]
  exact (ENNReal.ofReal_le_ofReal ha.2).trans_eq (ENNReal.ofReal_toReal ha.1.ne)

/-- 11.27: native integrability under an integrable extended-real majorant. -/
theorem pma11_27_native {f g : X → EReal} (hf : Measurable f)
    (hg : LebesgueIntegrable μ E g)
    (hbound : ∀ᵐ x ∂μ.restrict E, extendedAbs (f x) ≤ g x) :
    LebesgueIntegrable μ E f := by
  have h := pma11_27_ereal hf (native_integrable_iff.mp hg).2.1 hbound
  exact native_integrable_iff.mpr ⟨hf, h.1, h.2.1⟩

/-- 11.28 in the first-half nonnegative integral notation, locally on `E`. -/
theorem pma11_28_native {F : ℕ → X → ℝ≥0∞} {f : X → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) (μ.restrict E))
    (hmono : ∀ᵐ x ∂μ.restrict E, Monotone (fun n => F n x))
    (hlim : ∀ᵐ x ∂μ.restrict E, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n => nonnegativeIntegral μ E (F n)) atTop
      (𝓝 (nonnegativeIntegral μ E f)) :=
  pma11_28_ae hF hmono hlim

/-- 11.29: native integrability of the sum and native signed integral additivity. -/
theorem pma11_29_native {f g : X → EReal}
    (hf : LebesgueIntegrable μ E f) (hg : LebesgueIntegrable μ E g) :
    LebesgueIntegrable μ E (fun x => f x + g x) ∧
      lebesgueIntegral μ E (fun x => f x + g x) =
        lebesgueIntegral μ E f + lebesgueIntegral μ E g := by
  have hfp := native_integrable_iff.mp hf
  have hgp := native_integrable_iff.mp hg
  have h := pma11_29_ereal hf.1 hg.1 hfp.2.1 hfp.2.2 hgp.2.1 hgp.2.2
  have hi : LebesgueIntegrable μ E (fun x => f x + g x) :=
    native_integrable_iff.mpr ⟨hf.1.add hg.1, h.1, h.2.1⟩
  refine ⟨hi, ?_⟩
  rw [native_integral_eq_representative hi, native_integral_eq_representative hf,
    native_integral_eq_representative hg, ← EReal.coe_add, h.2.2]

/-- 11.30: native nonnegative integral of a series. -/
theorem pma11_30_native {F : ℕ → X → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) (μ.restrict E)) :
    nonnegativeIntegral μ E (fun x => ∑' n, F n x) =
      ∑' n, nonnegativeIntegral μ E (F n) :=
  pma11_30_ae hF

/-- 11.31: native Fatou inequality. -/
theorem pma11_31_native {F : ℕ → X → ℝ≥0∞}
    (hF : ∀ n, AEMeasurable (F n) (μ.restrict E)) :
    nonnegativeIntegral μ E (fun x => liminf (fun n => F n x) atTop) ≤
      liminf (fun n => nonnegativeIntegral μ E (F n)) atTop :=
  pma11_31_ae hF

/-- 11.32: native signed dominated convergence. The chosen limit is required
to be measurable because the native integrability predicate requires it;
the source's pointwise-limit case has this property by 11.17. The unrestricted
almost-everywhere representative form is `pma11_32_ereal`. -/
theorem pma11_32_native {F : ℕ → X → EReal} {f : X → EReal} {g : X → ℝ}
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f) (hg : IntegrableOn g E μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ.restrict E, extendedAbs (F n x) ≤ (g x : EReal))
    (hlim : ∀ᵐ x ∂μ.restrict E, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    (∀ n, LebesgueIntegrable μ E (F n)) ∧ LebesgueIntegrable μ E f ∧
      Tendsto (fun n => lebesgueIntegral μ E (F n)) atTop (𝓝 (lebesgueIntegral μ E f)) := by
  have h := pma11_32_ereal hF hg hbound hlim
  have hi : ∀ n, LebesgueIntegrable μ E (F n) :=
    fun n => native_integrable_iff.mpr ⟨hF n, h.1 n⟩
  have hfi : LebesgueIntegrable μ E f := native_integrable_iff.mpr ⟨hf, h.2.1⟩
  refine ⟨hi, hfi, ?_⟩
  have ht := continuous_coe_real_ereal.continuousAt.tendsto.comp h.2.2
  have heq (n : ℕ) :
      (((∫⁻ x in E, (F n x).toENNReal ∂μ).toReal -
        (∫⁻ x in E, (-F n x).toENNReal ∂μ).toReal : ℝ) : EReal) =
      lebesgueIntegral μ E (F n) := (native_integral_eq_coe_parts (hi n)).symm
  have heqf : (((∫⁻ x in E, (f x).toENNReal ∂μ).toReal -
      (∫⁻ x in E, (-f x).toENNReal ∂μ).toReal : ℝ) : EReal) =
      lebesgueIntegral μ E f := (native_integral_eq_coe_parts hfi).symm
  simpa only [Function.comp_def, heq, heqf] using ht

/-- The same native DCT with the source's extended-real integrable majorant.
The reduction to its finite representative is justified almost everywhere. -/
theorem pma11_32_native_extended_majorant {F : ℕ → X → EReal} {f g : X → EReal}
    (hF : ∀ n, Measurable (F n)) (hf : Measurable f)
    (hg : LebesgueIntegrable μ E g)
    (hbound : ∀ n, ∀ᵐ x ∂μ.restrict E, extendedAbs (F n x) ≤ g x)
    (hlim : ∀ᵐ x ∂μ.restrict E, Tendsto (fun n => F n x) atTop (𝓝 (f x))) :
    (∀ n, LebesgueIntegrable μ E (F n)) ∧ LebesgueIntegrable μ E f ∧
      Tendsto (fun n => lebesgueIntegral μ E (F n)) atTop (𝓝 (lebesgueIntegral μ E f)) := by
  have hrep := pma11_25_native hg
  apply pma11_32_native hF hf hrep.2.2.2 _ hlim
  intro n
  filter_upwards [hbound n, hrep.2.2.1] with x hx heq
  simpa only [heq] using hx

end Rudin.PMA.Chapter11.SecondHalf
