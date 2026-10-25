import Rudin.PMA.Chapter06

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter08

/-!
## PMA 8.6 and its exponential, logarithmic, and real-power development

Mathlib supplies the exponential and logarithm APIs, including the factorial
series identification. Integral assertions below use the native Chapter 6
Darboux/Riemann integral, with an explicit orientation convention. Their proofs
use PMA 6.8 and 6.21; no replacement by a measure-theoretic integral is involved.
-/

/-- The native ordinary Riemann integral with the usual orientation convention. -/
def orientedRIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  if a ≤ b then Chapter06.RIntegral f a b else -Chapter06.RIntegral f b a

theorem positive_native_integrable (f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Chapter06.RIntegrable f a b :=
  Chapter06.pma6_8 f id a b hab
    (hf.mono fun _ hx => ha.trans_le hx.1) (monotone_id.monotoneOn (Icc a b))

theorem orientedRIntegral_of_primitive (F f : ℝ → ℝ)
    (hf : ContinuousOn f (Ioi 0))
    (hF : ∀ x : ℝ, 0 < x → HasDerivAt F (f x) x)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    orientedRIntegral f a b = F b - F a := by
  have hi {u v : ℝ} (hu : 0 < u) (huv : u < v) :
      Chapter06.RIntegral f u v = F v - F u :=
    Chapter06.pma6_21 F f u v huv
      (fun x hx => (hF x (hu.trans_le hx.1)).hasDerivWithinAt)
      (positive_native_integrable f hf hu huv.le)
  rcases lt_trichotomy a b with hab | hab | hab
  · simp only [orientedRIntegral, ite_eq_left hab.le, hi ha hab]
  · subst b
    simp only [orientedRIntegral, le_refl, ite_true, sub_self]
    exact (Chapter06.calculus_singleton_integrals f id a).2
  · simp only [orientedRIntegral, ite_eq_right (not_le.mpr hab), hi hb hab]
    ring

theorem log_native_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    orientedRIntegral (fun x => x⁻¹) a b = Real.log b - Real.log a :=
  orientedRIntegral_of_primitive Real.log (fun x => x⁻¹)
    (continuousOn_id.inv₀ fun _ hx => ne_of_gt hx)
    (fun _ hx => Real.hasDerivAt_log hx.ne') ha hb

theorem log_native_integral_from_one {x : ℝ} (hx : 0 < x) :
    orientedRIntegral (fun t => t⁻¹) 1 x = Real.log x := by
  simpa only [Real.log_one, sub_zero] using log_native_integral zero_lt_one hx

theorem rpow_primitive_derivative (α : ℝ) (hα : α ≠ -1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => t ^ (α + 1) / (α + 1)) (x ^ α) x := by
  have hα' : α + 1 ≠ 0 := by
    intro h
    apply hα
    linarith only [h]
  simpa only [add_sub_cancel_right, mul_div_cancel_left₀ _ hα'] using
    (Real.hasDerivAt_rpow_const (x := x) (p := α + 1) (Or.inl hx.ne')).div_const (α + 1)

theorem rpow_native_integral (α : ℝ) (hα : α ≠ -1)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    orientedRIntegral (fun x : ℝ => x ^ α) a b =
      (b ^ (α + 1) - a ^ (α + 1)) / (α + 1) := by
  rw [orientedRIntegral_of_primitive (fun t : ℝ => t ^ (α + 1) / (α + 1))
    (fun t : ℝ => t ^ α)
    (continuousOn_id.rpow_const fun _ hx => Or.inl (ne_of_gt hx))
    (fun _ hx => rpow_primitive_derivative α hα hx) ha hb]
  ring

/-- Rational powers satisfy the positive-root definition using their numerator
and denominator, including negative numerators. -/
theorem rpow_rational_root {x : ℝ} (hx : 0 < x) (q : ℚ) :
    0 < x ^ (q : ℝ) ∧ (x ^ (q : ℝ)) ^ q.den = x ^ q.num := by
  refine ⟨Real.rpow_pos_of_pos hx _, ?_⟩
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, Rat.cast_def,
    div_mul_cancel₀ _ (show (q.den : ℝ) ≠ 0 by exact_mod_cast q.den_ne_zero),
    Real.rpow_intCast]

/-- The supremum convention for bases greater than one agrees with `rpow`.
This is the convention used to identify `exp x` with powers of `exp 1`. -/
theorem rpow_rational_isLUB {b : ℝ} (hb : 1 < b) (x : ℝ) :
    IsLUB ((fun q : ℚ => b ^ (q : ℝ)) '' {q : ℚ | (q : ℝ) < x}) (b ^ x) := by
  let S : Set ℝ := ((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) < x}
  have hs : IsLUB S x := by
    constructor
    · rintro y ⟨q, hq, rfl⟩
      exact le_of_lt hq
    · intro y hy
      by_contra hxy
      obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn (lt_of_not_ge hxy)
      exact (not_lt_of_ge (hy ⟨q, hqx, rfl⟩)) hyq
  have hSne : S.Nonempty := by
    obtain ⟨q, hq⟩ := exists_rat_lt x
    exact ⟨q, q, hq, rfl⟩
  have hf : MonotoneOn (fun t : ℝ => b ^ t) S :=
    fun _ _ _ _ h => Real.rpow_le_rpow_of_exponent_le hb.le h
  have ht : Tendsto (fun t : ℝ => b ^ t) (𝓝[S] x) (𝓝 (b ^ x)) :=
    (Real.continuous_const_rpow (zero_lt_one.trans hb).ne').continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  simpa only [S, image_image, Function.comp_def] using hs.isLUB_of_tendsto hf hSne ht

theorem rpow_neg_mul_log_limit (α : ℝ) (hα : 0 < α) :
    Tendsto (fun x : ℝ => x ^ (-α) * Real.log x) atTop (𝓝 0) := by
  apply (isLittleO_log_rpow_atTop hα).tendsto_div_nhds_zero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Real.rpow_neg hx.le, div_eq_mul_inv, mul_comm]

def complexExpDevelopment : Prop :=
  (∀ z : ℂ, HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (Complex.exp z)) ∧
  Complex.exp 0 = 1 ∧
  (∀ z : ℂ, Complex.exp z ≠ 0) ∧
  (∀ z w : ℂ, Complex.exp (z + w) = Complex.exp z * Complex.exp w) ∧
  (∀ z : ℂ, Complex.exp (-z) = (Complex.exp z)⁻¹) ∧
  (∀ z : ℂ, HasDerivAt Complex.exp (Complex.exp z) z) ∧
  (∀ (n : ℕ) (z : ℕ → ℂ), Complex.exp (∑ k ∈ Finset.range n, z k) =
    ∏ k ∈ Finset.range n, Complex.exp (z k)) ∧
  (∀ x : ℝ, (Real.exp x : ℂ) = Complex.exp (x : ℂ))

theorem complex_exp_development : complexExpDevelopment := by
  refine ⟨?_, Complex.exp_zero, Complex.exp_ne_zero, Complex.exp_add, Complex.exp_neg,
    Complex.hasDerivAt_exp, ?_, Complex.ofReal_exp⟩
  · intro z
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  · intro n z
    exact Complex.exp_sum (Finset.range n) z

def realExpDevelopment : Prop :=
  Continuous Real.exp ∧
  (∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x) ∧
  StrictMono Real.exp ∧
  (∀ x : ℝ, 0 < Real.exp x) ∧
  (∀ x y : ℝ, Real.exp (x + y) = Real.exp x * Real.exp y) ∧
  Tendsto Real.exp atTop atTop ∧
  Tendsto Real.exp atBot (𝓝 0) ∧
  (∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0)) ∧
  Chapter03.EulerNumber = Real.exp 1 ∧
  (∀ x : ℝ, Chapter03.EulerNumber ^ x = Real.exp x) ∧
  (∀ x : ℝ, IsLUB ((fun q : ℚ => Chapter03.EulerNumber ^ (q : ℝ)) ''
    {q : ℚ | (q : ℝ) < x}) (Real.exp x))

theorem real_exp_development : realExpDevelopment := by
  refine ⟨Real.continuous_exp, Real.hasDerivAt_exp, Real.exp_strictMono, Real.exp_pos,
    Real.exp_add, Real.tendsto_exp_atTop, Real.tendsto_exp_atBot,
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero, Chapter03.eulerNumber_eq_exp_one, ?_, ?_⟩
  · intro x
    rw [Chapter03.eulerNumber_eq_exp_one, Real.exp_one_rpow]
  · intro x
    rw [Chapter03.eulerNumber_eq_exp_one]
    simpa only [Real.exp_one_rpow] using
      rpow_rational_isLUB (Real.one_lt_exp_iff.mpr zero_lt_one) x

def realLogDevelopment : Prop :=
  (∀ x : ℝ, Real.log (Real.exp x) = x) ∧
  (∀ x : ℝ, 0 < x → Real.exp (Real.log x) = x) ∧
  Real.log 1 = 0 ∧
  StrictMonoOn Real.log (Ioi 0) ∧
  (∀ x : ℝ, 0 < x → HasDerivAt Real.log x⁻¹ x) ∧
  (∀ x y : ℝ, 0 < x → 0 < y → Real.log (x * y) = Real.log x + Real.log y) ∧
  Tendsto Real.log atTop atTop ∧
  Tendsto Real.log (𝓝[>] (0 : ℝ)) atBot ∧
  (∀ a b : ℝ, 0 < a → a ≤ b → Chapter06.RIntegrable (fun t => t⁻¹) a b) ∧
  (∀ x : ℝ, 0 < x → orientedRIntegral (fun t => t⁻¹) 1 x = Real.log x)

theorem real_log_development : realLogDevelopment := by
  refine ⟨Real.log_exp, fun _ hx => Real.exp_log hx, Real.log_one,
    Real.strictMonoOn_log, fun _ hx => Real.hasDerivAt_log hx.ne',
    fun _ _ hx hy => Real.log_mul hx.ne' hy.ne', Real.tendsto_log_atTop,
    Real.tendsto_log_nhdsGT_zero, ?_, fun _ hx => log_native_integral_from_one hx⟩
  intro a b ha hab
  exact positive_native_integrable (fun t => t⁻¹)
    (continuousOn_id.inv₀ fun _ hx => ne_of_gt hx) ha hab

def realPowerDevelopment : Prop :=
  (∀ x α : ℝ, 0 < x → x ^ α = Real.exp (α * Real.log x)) ∧
  (∀ (x : ℝ) (n : ℤ), x ^ (n : ℝ) = x ^ n) ∧
  (∀ (x : ℝ) (q : ℚ), 0 < x → 0 < x ^ (q : ℝ) ∧
    (x ^ (q : ℝ)) ^ q.den = x ^ q.num) ∧
  (∀ b x : ℝ, 1 < b →
    IsLUB ((fun q : ℚ => b ^ (q : ℝ)) '' {q : ℚ | (q : ℝ) < x}) (b ^ x)) ∧
  (∀ x α : ℝ, 0 < x → HasDerivAt (fun t : ℝ => t ^ α) (α * x ^ (α - 1)) x) ∧
  (∀ a b α : ℝ, 0 < a → a ≤ b → Chapter06.RIntegrable (fun t : ℝ => t ^ α) a b) ∧
  (∀ a b α : ℝ, 0 < a → 0 < b → α ≠ -1 →
    orientedRIntegral (fun t : ℝ => t ^ α) a b =
      (b ^ (α + 1) - a ^ (α + 1)) / (α + 1)) ∧
  (∀ a b : ℝ, 0 < a → 0 < b →
    orientedRIntegral (fun t : ℝ => t ^ (-1 : ℝ)) a b = Real.log b - Real.log a) ∧
  (∀ α : ℝ, 0 < α → Tendsto (fun x : ℝ => x ^ (-α) * Real.log x) atTop (𝓝 0))

theorem real_power_development : realPowerDevelopment := by
  refine ⟨?_, Real.rpow_intCast, fun _ q hx => rpow_rational_root hx q,
    fun _ x hb => rpow_rational_isLUB hb x,
    fun _ _ hx => Real.hasDerivAt_rpow_const (Or.inl hx.ne'), ?_,
    fun _ _ α ha hb hα => rpow_native_integral α hα ha hb, ?_, rpow_neg_mul_log_limit⟩
  · intro x α hx
    simpa only [mul_comm] using Real.rpow_def_of_pos hx α
  · intro a b α ha hab
    exact positive_native_integrable (fun t : ℝ => t ^ α)
      (continuousOn_id.rpow_const fun _ hx => Or.inl (ne_of_gt hx)) ha hab
  · intro a b ha hb
    simpa only [Real.rpow_neg_one] using log_native_integral ha hb

def pma8_6_contract : Prop :=
  complexExpDevelopment ∧ realExpDevelopment ∧ realLogDevelopment ∧ realPowerDevelopment

theorem pma8_6 : pma8_6_contract :=
  ⟨complex_exp_development, real_exp_development, real_log_development, real_power_development⟩

end Rudin.PMA.Chapter08
