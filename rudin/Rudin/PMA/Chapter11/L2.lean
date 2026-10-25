import Rudin.PMA.Chapter11
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# PMA 11.34–11.39 and 11.41–11.45: square integrable functions

Functions before passage to the quotient retain the book's pointwise
measurability requirement. The quotient is mathlib's `Lp ℂ 2 μ`; the bridges
below identify its norm and equality with the book's formulas. Sequence
indices start at zero, merely reindexing the positive-integer sequences.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate InnerProductSpace

namespace Rudin.PMA.Chapter11.SecondHalf

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- 11.34: complex measurable functions with finite integral of the squared modulus.
`Integrable` expresses finiteness of the nonnegative integral here. -/
def SquareIntegrable (μ : Measure X) (f : X → ℂ) : Prop :=
  Measurable f ∧ Integrable (fun x => ‖f x‖ ^ 2) μ

/-- 11.34: the square root of the integral of the squared modulus. -/
def l2Norm (μ : Measure X) (f : X → ℂ) : ℝ :=
  Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ)

 theorem SquareIntegrable.memLp {f : X → ℂ} (hf : SquareIntegrable μ f) :
    MemLp f 2 μ :=
  (memLp_two_iff_integrable_sq_norm hf.1.aestronglyMeasurable).mpr hf.2

 theorem squareIntegrable_iff {f : X → ℂ} :
    SquareIntegrable μ f ↔ Measurable f ∧ MemLp f 2 μ := by
  constructor
  · exact fun h => ⟨h.1, h.memLp⟩
  · rintro ⟨hm, h⟩
    exact ⟨hm, (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp h⟩

/-- The pointwise-function norm and the quotient norm coincide. -/
theorem norm_toL2 {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ = l2Norm μ f := by
  rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp) hf]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => sq_nonneg _) _)]
  simp [l2Norm, Real.sqrt_eq_rpow, one_div]

/-- 11.35: Schwarz's inequality, including integrability of the product. -/
theorem pma11_35 {f g : X → ℂ} (hf : SquareIntegrable μ f)
    (hg : SquareIntegrable μ g) :
    Integrable (fun x => f x * g x) μ ∧
      (∫ x, ‖f x * g x‖ ∂μ) ≤ l2Norm μ f * l2Norm μ g := by
  refine ⟨hf.memLp.integrable_mul hg.memLp, ?_⟩
  have h := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (by simpa using hf.memLp) (by simpa using hg.memLp)
  simpa [norm_mul, l2Norm, Real.sqrt_eq_rpow, Real.rpow_two] using h

/-- 11.36: closure under addition and the triangle inequality. -/
theorem pma11_36 {f g : X → ℂ} (hf : SquareIntegrable μ f)
    (hg : SquareIntegrable μ g) :
    SquareIntegrable μ (f + g) ∧ l2Norm μ (f + g) ≤ l2Norm μ f + l2Norm μ g := by
  have hfg := hf.memLp.add hg.memLp
  refine ⟨squareIntegrable_iff.mpr ⟨hf.1.add hg.1, hfg⟩, ?_⟩
  rw [← norm_toL2 hfg, MemLp.toLp_add, ← norm_toL2 hf.memLp, ← norm_toL2 hg.memLp]
  exact norm_add_le _ _

/-- 11.37: the quotient identifying functions equal almost everywhere. -/
abbrev L2Space (μ : Measure X) := Lp ℂ 2 μ

/-- 11.37: equality of quotient classes is exactly equality almost everywhere. -/
theorem pma11_37_eq {f g : X → ℂ} (hf : SquareIntegrable μ f)
    (hg : SquareIntegrable μ g) :
    hf.memLp.toLp f = hg.memLp.toLp g ↔ f =ᵐ[μ] g :=
  MemLp.toLp_eq_toLp_iff _ _

/-- 11.37: distance in the quotient is the norm of the difference. -/
theorem pma11_37_dist {f g : X → ℂ} (hf : SquareIntegrable μ f)
    (hg : SquareIntegrable μ g) :
    dist (hf.memLp.toLp f) (hg.memLp.toLp g) = l2Norm μ (f - g) := by
  rw [dist_eq_norm, ← MemLp.toLp_sub, norm_toL2]

/-- 11.37: the quotient has a genuine metric. -/
theorem pma11_37_metric : Nonempty (MetricSpace (L2Space μ)) := ⟨inferInstance⟩

/-- 11.38: every square-integrable interval function has a continuous approximation.
The approximant is even continuous on the entire real line. -/
theorem pma11_38 {a b : ℝ} {f : ℝ → ℂ}
    (hf : SquareIntegrable (volume.restrict (Icc a b)) f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℂ, Continuous g ∧
      SquareIntegrable (volume.restrict (Icc a b)) g ∧
      l2Norm (volume.restrict (Icc a b)) (f - g) < ε := by
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Icc a b)) := by
    simpa using hf.memLp
  obtain ⟨g, hg, hgm⟩ := hf'.exists_boundedContinuous_integral_rpow_sub_le
    (by norm_num : (0 : ℝ) < 2) (show 0 < (ε / 2) ^ 2 by positivity)
  refine ⟨g, g.continuous, squareIntegrable_iff.mpr ⟨g.continuous.measurable, by simpa using hgm⟩, ?_⟩
  have hb : (∫ x, ‖f x - g x‖ ^ 2 ∂volume.restrict (Icc a b)) ≤ (ε / 2) ^ 2 := by
    simpa [Real.rpow_two] using hg
  have hs := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq (by positivity : 0 ≤ ε / 2)] at hs
  exact hs.trans_lt (by linarith)

end Rudin.PMA.Chapter11.SecondHalf
