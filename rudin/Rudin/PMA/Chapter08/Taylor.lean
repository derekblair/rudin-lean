import Rudin.PMA.Chapter08.PowerSeries

set_option autoImplicit false

noncomputable section
open scoped BigOperators ENNReal NNReal
open Set Filter Topology

namespace Rudin.PMA.Chapter08

/-! ### PMA-8.4: Taylor expansion about any interior point.

The radius is extended nonnegative real, so the statement includes an infinite
original radius. The bound `R - ‖a‖` guarantees convergence; no exact radius is
asserted. Real scalars act on complex coefficients and derivatives.
-/

def pma8_4_contract : Prop :=
  ∀ (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞), 0 < R → Represents c f R →
    ∀ a : ℝ, (‖a‖₊ : ℝ≥0∞) < R →
    ∀ x : ℝ, (‖x - a‖₊ : ℝ≥0∞) < R - (‖a‖₊ : ℝ≥0∞) →
      Chapter03.SeriesHasSum
        (fun n => (((n.factorial : ℝ)⁻¹) * (x - a) ^ n) • iteratedDeriv n f a)
        (f x)

theorem pma8_4 : pma8_4_contract := by
  intro c f R hR hf a ha x hx
  have hfa := (represents_hasFPowerSeries hR hf).changeOrigin ha
  have hsum := hfa.hasSum_iteratedFDeriv (by simpa [enorm_eq_nnnorm] using hx)
  have hs : Chapter03.SeriesHasSum
      (fun n => (n.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ n f (0 + a) (fun _ => x - a))
      (f (0 + a + (x - a))) := hsum.tendsto_sum_nat
  simpa [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Fin.prod_const, smul_smul, mul_assoc]
    using hs

/-! ### PMA-8.5: The identity theorem for power series on a real interval.

Deleting the accumulation point before taking the closure requires distinct
nearby equality points. The point can lie anywhere in the open interval.
Its interior hypothesis makes accumulation of the global equality set
equivalent to accumulation of the equality set restricted to that interval.
-/

def pma8_5_contract : Prop :=
  ∀ (c d : ℕ → ℂ) (f g : ℝ → ℂ) (R : ℝ≥0∞), 0 < R →
    Represents c f R → Represents d g R →
    (∃ a : ℝ, (‖a‖₊ : ℝ≥0∞) < R ∧ a ∈ closure ({x | f x = g x} \ {a})) →
    c = d ∧ ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) < R → f x = g x

theorem pma8_5 : pma8_5_contract := by
  intro c d f g R hR hf hg hacc
  obtain ⟨a, ha, hacc⟩ := hacc
  have heq : EqOn f g (Metric.eball (0 : ℝ) R) :=
    (represents_hasFPowerSeries hR hf).analyticOnNhd.eqOn_of_preconnected_of_mem_closure
      (represents_hasFPowerSeries hR hg).analyticOnNhd Metric.isPreconnected_eball
      (by simpa [enorm_eq_nnnorm] using ha) hacc
  have hd : Represents d f R := by
    intro x hx
    rw [heq (by simpa [enorm_eq_nnnorm] using hx)]
    exact hg x hx
  exact ⟨coefficients_unique hR hf hd,
    fun x hx => heq (by simpa [enorm_eq_nnnorm] using hx)⟩

end Rudin.PMA.Chapter08
