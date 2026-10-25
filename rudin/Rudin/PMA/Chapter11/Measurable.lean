import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.LiminfLimsup

/-!
# PMA Chapter 11: measurable functions (11.13–11.18)

The domain carries a sigma algebra, as stipulated after 11.12. Extended real
values in 11.13–11.17 are represented by `EReal`, including both infinities.
Real thresholds in the source definition are kept literally; the bridge to
mathlib's Borel measurability is proved below.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Rudin.PMA.Chapter11

variable {X : Type*} [MeasurableSpace X]

/-- 11.13: every strict superlevel set at a real threshold is measurable. -/
def MeasurableFunction (f : X → EReal) : Prop :=
  ∀ a : ℝ, MeasurableSet {x | (a : EReal) < f x}

private theorem measurable_of_real_superlevel {f : X → EReal}
    (hf : ∀ a : ℝ, MeasurableSet {x | (a : EReal) < f x}) : Measurable f := by
  apply measurable_of_Ioi
  intro a
  have heq : f ⁻¹' Ioi a =
      ⋃ q : ℚ, ⋃ (_ : a < ((q : ℝ) : EReal)), {x | ((q : ℝ) : EReal) < f x} := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_ofPred_eq, exists_prop]
    exact EReal.lt_iff_exists_rat_btwn
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => hf (q : ℝ)

private theorem measurable_of_real_sublevel {f : X → EReal}
    (hf : ∀ a : ℝ, MeasurableSet {x | f x < (a : EReal)}) : Measurable f := by
  apply measurable_of_Iio
  intro a
  have heq : f ⁻¹' Iio a =
      ⋃ q : ℚ, ⋃ (_ : ((q : ℝ) : EReal) < a), {x | f x < ((q : ℝ) : EReal)} := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_ofPred_eq, exists_prop]
    exact EReal.lt_iff_exists_rat_btwn.trans (by simp only [and_comm])
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ => hf (q : ℝ)

/-- 11.13's real-threshold definition agrees with Borel measurability on `EReal`. -/
theorem pma11_13_iff_measurable {f : X → EReal} :
    MeasurableFunction f ↔ Measurable f :=
  ⟨measurable_of_real_superlevel, fun hf _a => measurableSet_lt measurable_const hf⟩

/-- The same definition specializes to the ordinary notion for real-valued functions. -/
theorem pma11_13_real_iff_measurable {f : X → ℝ} :
    MeasurableFunction (fun x => (f x : EReal)) ↔ Measurable f := by
  rw [pma11_13_iff_measurable]
  exact ⟨fun h => by simpa using h.ereal_toReal, fun h => h.coe_real_ereal⟩

/-- 11.14. Generality: the continuous example is stated on any space with measurable
open sets; this includes Euclidean space with Lebesgue measurable sets. -/
theorem pma11_14 [TopologicalSpace X] [OpensMeasurableSpace X]
    {f : X → EReal} (hf : Continuous f) : MeasurableFunction f :=
  pma11_13_iff_measurable.mpr hf.measurable

/-- The real-valued form of the continuous example in 11.14. -/
theorem pma11_14_real [TopologicalSpace X] [OpensMeasurableSpace X]
    {f : X → ℝ} (hf : Continuous f) :
    MeasurableFunction (fun x => (f x : EReal)) :=
  pma11_13_real_iff_measurable.mpr hf.measurable

/-- 11.15: the four conditions, with real thresholds, are each equivalent to
measurability. The second displayed condition in the source is `≥`, not equality. -/
theorem pma11_15 {f : X → EReal} :
    (MeasurableFunction f ↔ Measurable f) ∧
    ((∀ a : ℝ, MeasurableSet {x | (a : EReal) ≤ f x}) ↔ Measurable f) ∧
    ((∀ a : ℝ, MeasurableSet {x | f x < (a : EReal)}) ↔ Measurable f) ∧
    ((∀ a : ℝ, MeasurableSet {x | f x ≤ (a : EReal)}) ↔ Measurable f) := by
  refine ⟨pma11_13_iff_measurable, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h
    apply measurable_of_real_sublevel
    intro a
    simpa only [compl_ofPred, not_le] using (h a).compl
  · intro h a
    exact measurableSet_le measurable_const h
  · exact measurable_of_real_sublevel
  · intro h a
    exact measurableSet_lt h measurable_const
  · intro h
    apply measurable_of_real_superlevel
    intro a
    simpa only [compl_ofPred, not_le] using (h a).compl
  · intro h a
    exact measurableSet_le h measurable_const

/-- Extended absolute value, with values in the same extended real line. -/
noncomputable def extendedAbs (a : EReal) : EReal := max a (-a)

/-- This agrees with mathlib's extended absolute value (whose codomain is `ℝ≥0∞`). -/
theorem extendedAbs_eq (a : EReal) : extendedAbs a = (a.abs : EReal) := by
  induction a using EReal.rec with
  | bot => simp [extendedAbs]
  | top => simp [extendedAbs]
  | coe a =>
    rw [extendedAbs, EReal.coe_abs, abs_eq_max_neg]
    by_cases h : a ≤ -a
    · have hc : (a : EReal) ≤ (-a : ℝ) := EReal.coe_le_coe_iff.mpr h
      simp only [max_eq_right h, EReal.coe_neg]
      exact max_eq_right hc
    · have h' : -a ≤ a := le_of_not_ge h
      have hc : ((-a : ℝ) : EReal) ≤ a := EReal.coe_le_coe_iff.mpr h'
      simp only [max_eq_left h']
      simpa using max_eq_left hc

/-- 11.16: the absolute value of an extended-real measurable function is measurable. -/
theorem pma11_16 {f : X → EReal} (hf : MeasurableFunction f) :
    MeasurableFunction (fun x => extendedAbs (f x)) := by
  apply pma11_13_iff_measurable.mpr
  exact (pma11_13_iff_measurable.mp hf).max (pma11_13_iff_measurable.mp hf).neg

/-- 11.17: pointwise supremum and upper limit are measurable. Indexing begins at
zero instead of one, an immaterial reindexing of the sequence. -/
theorem pma11_17 {f : ℕ → X → EReal} (hf : ∀ n, MeasurableFunction (f n)) :
    MeasurableFunction (fun x => ⨆ n, f n x) ∧
      MeasurableFunction (fun x => limsup (fun n => f n x) atTop) := by
  have h : ∀ n, Measurable (f n) := fun n => pma11_13_iff_measurable.mp (hf n)
  exact ⟨pma11_13_iff_measurable.mpr (.iSup h),
    pma11_13_iff_measurable.mpr (.limsup h)⟩

/-- 11.17 also asserts the corresponding statements for infimum and lower limit. -/
theorem pma11_17_inf_liminf {f : ℕ → X → EReal}
    (hf : ∀ n, MeasurableFunction (f n)) :
    MeasurableFunction (fun x => ⨅ n, f n x) ∧
      MeasurableFunction (fun x => liminf (fun n => f n x) atTop) := by
  have h : ∀ n, Measurable (f n) := fun n => pma11_13_iff_measurable.mp (hf n)
  exact ⟨pma11_13_iff_measurable.mpr (.iInf h),
    pma11_13_iff_measurable.mpr (.liminf h)⟩

/-- 11.17(a): maxima and minima of two measurable functions. -/
theorem pma11_17_corollary_a {f g : X → EReal}
    (hf : MeasurableFunction f) (hg : MeasurableFunction g) :
    MeasurableFunction (fun x => max (f x) (g x)) ∧
      MeasurableFunction (fun x => min (f x) (g x)) := by
  have hfm := pma11_13_iff_measurable.mp hf
  have hgm := pma11_13_iff_measurable.mp hg
  exact ⟨pma11_13_iff_measurable.mpr (hfm.max hgm),
    pma11_13_iff_measurable.mpr (hfm.min hgm)⟩

/-- 11.17(a), equation (47): the positive and negative parts are measurable. -/
theorem pma11_17_positive_negative_parts {f : X → EReal} (hf : MeasurableFunction f) :
    MeasurableFunction (fun x => max (f x) 0) ∧
      MeasurableFunction (fun x => -min (f x) 0) := by
  have h := pma11_13_iff_measurable.mp hf
  exact ⟨pma11_13_iff_measurable.mpr (h.max measurable_const),
    pma11_13_iff_measurable.mpr (h.min measurable_const).neg⟩

/-- 11.17(b): every pointwise limit of measurable functions is measurable,
including limits taking either infinite value. -/
theorem pma11_17_corollary_b {f : ℕ → X → EReal} {g : X → EReal}
    (hf : ∀ n, MeasurableFunction (f n))
    (hlim : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    MeasurableFunction g := by
  have heq : (fun x => limsup (fun n => f n x) atTop) = g :=
    funext fun x => (hlim x).limsup_eq
  rw [← heq]
  exact (pma11_17 hf).2

/-- 11.18: continuous functions of a pair of measurable real-valued functions.
Here mathlib `Measurable` is equivalent to 11.13 by `pma11_13_real_iff_measurable`. -/
theorem pma11_18 {f g : X → ℝ} {F : ℝ × ℝ → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hF : Continuous F) :
    Measurable (fun x => F (f x, g x)) :=
  hF.measurable.comp (hf.prodMk hg)

/-- 11.18, in particular: sums and products of measurable real functions. -/
theorem pma11_18_add_mul {f g : X → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x + g x) ∧ Measurable (fun x => f x * g x) :=
  ⟨hf.add hg, hf.mul hg⟩

/- The illustrative example following 11.18, in which a Lebesgue measurable
outer function and a continuous inner function have non-Lebesgue-measurable
composition, is not established in this module. Borel measurability would make
that assertion false, so replacing Lebesgue measurability by Borel measurability
would not be a faithful formalization. This is an explicit coverage gap. -/

end Rudin.PMA.Chapter11
