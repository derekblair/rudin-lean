import Mathlib

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Rudin.PMA.Chapter07

/-- PMA 7.18 requires existence, not the book's particular construction. -/
def pma7_18_contract : Prop :=
  ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x : ℝ, ¬ DifferentiableAt ℝ f x

/-- A bounded periodic tent supplied by the quotient norm; proof infrastructure. -/
def nowhereTent (x : ℝ) : ℝ := ‖(x : AddCircle (2 : ℝ))‖

/-- A geometric series of periodic tents. -/
def nowhereWitness (x : ℝ) : ℝ :=
  ∑' n : ℕ, ((3 : ℝ) / 4) ^ n * nowhereTent ((4 : ℝ) ^ n * x)

theorem nowhereTent_nonneg (x : ℝ) : 0 ≤ nowhereTent x := norm_nonneg _

theorem nowhereTent_le_one (x : ℝ) : nowhereTent x ≤ 1 := by
  simpa [nowhereTent] using AddCircle.norm_le_half_period (2 : ℝ) (by norm_num : (2 : ℝ) ≠ 0)
    (x := (x : AddCircle (2 : ℝ)))

theorem nowhereTent_continuous : Continuous nowhereTent :=
  continuous_norm.comp (AddCircle.continuous_mk' (2 : ℝ))

theorem nowhereTent_lipschitz (x y : ℝ) : |nowhereTent x - nowhereTent y| ≤ |x - y| := by
  apply (abs_norm_sub_norm_le (x : AddCircle (2 : ℝ)) (y : AddCircle (2 : ℝ))).trans
  rw [← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem nowhereTent_add_even_int (x : ℝ) (z : ℤ) :
    nowhereTent (x + (z : ℝ) * 2) = nowhereTent x := by
  simp [nowhereTent, ← zsmul_eq_mul]

theorem nowhereTent_center (x : ℝ) :
    ∃ r : ℝ, |r| ≤ 1 ∧ (r : AddCircle (2 : ℝ)) = (x : AddCircle (2 : ℝ)) := by
  let z : ℤ := round ((2 : ℝ)⁻¹ * x)
  let r : ℝ := x - (z : ℝ) * 2
  have hr : (r : AddCircle (2 : ℝ)) = (x : AddCircle (2 : ℝ)) := by
    simp only [r, ← zsmul_eq_mul, AddCircle.coe_sub, AddCircle.coe_zsmul, AddCircle.coe_period, zsmul_zero, sub_zero]
  refine ⟨r, ?_, hr⟩
  have h := nowhereTent_le_one x
  simpa only [nowhereTent, AddCircle.norm_eq, z, r] using h

theorem nowhereTent_half_step (x : ℝ) :
    ∃ σ : ℝ, (σ = -(1/2 : ℝ) ∨ σ = 1/2) ∧
      |nowhereTent (x + σ) - nowhereTent x| = 1/2 := by
  obtain ⟨r, hr, heq⟩ := nowhereTent_center x
  have hvalue : nowhereTent x = |r| := by
    unfold nowhereTent
    rw [← heq]
    exact (AddCircle.norm_coe_eq_abs_iff (2 : ℝ) (by norm_num : (2 : ℝ) ≠ 0)).mpr (by simpa using hr)
  have hshift (σ : ℝ) (hs : |r + σ| ≤ 1) : nowhereTent (x + σ) = |r + σ| := by
    unfold nowhereTent
    rw [AddCircle.coe_add, ← heq, ← AddCircle.coe_add]
    exact (AddCircle.norm_coe_eq_abs_iff (2 : ℝ) (by norm_num : (2 : ℝ) ≠ 0)).mpr (by simpa using hs)
  obtain ⟨hrl, hru⟩ := abs_le.mp hr
  by_cases h0 : 0 ≤ r
  · by_cases hh : r ≤ 1/2
    · refine ⟨1/2, Or.inr rfl, ?_⟩
      rw [hshift _ (abs_le.mpr ⟨by linarith, by linarith⟩), hvalue,
        abs_of_nonneg (by linarith : 0 ≤ r + 1/2), abs_of_nonneg h0]
      norm_num
    · refine ⟨-(1/2), Or.inl rfl, ?_⟩
      rw [hshift _ (abs_le.mpr ⟨by linarith, by linarith⟩), hvalue,
        abs_of_nonneg (by linarith : 0 ≤ r + -(1/2)), abs_of_nonneg h0]
      norm_num
  · by_cases hh : -(1/2 : ℝ) ≤ r
    · refine ⟨-(1/2), Or.inl rfl, ?_⟩
      rw [hshift _ (abs_le.mpr ⟨by linarith, by linarith⟩), hvalue,
        abs_of_nonpos (by linarith : r + -(1/2) ≤ 0), abs_of_nonpos (le_of_lt (lt_of_not_ge h0))]
      norm_num
    · refine ⟨1/2, Or.inr rfl, ?_⟩
      rw [hshift _ (abs_le.mpr ⟨by linarith, by linarith⟩), hvalue,
        abs_of_nonpos (by linarith : r + 1/2 ≤ 0), abs_of_nonpos (le_of_lt (lt_of_not_ge h0))]
      norm_num

theorem nowhere_geometric_summable : Summable (fun n : ℕ => ((3 : ℝ)/4)^n) := by
  exact summable_geometric_of_abs_lt_one (by norm_num)

theorem nowhere_term_bound (n : ℕ) (x : ℝ) :
    ‖((3 : ℝ)/4)^n * nowhereTent ((4 : ℝ)^n*x)‖ ≤ ((3 : ℝ)/4)^n := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (nowhereTent_nonneg _))]
  exact mul_le_of_le_one_right (by positivity) (nowhereTent_le_one _)

theorem nowhereWitness_summable (x : ℝ) :
    Summable (fun n : ℕ => ((3 : ℝ)/4)^n * nowhereTent ((4 : ℝ)^n*x)) :=
  Summable.of_norm_bounded nowhere_geometric_summable (fun n => nowhere_term_bound n x)

theorem nowhereWitness_continuous : Continuous nowhereWitness := by
  apply continuous_tsum
  · intro n
    exact continuous_const.mul (nowhereTent_continuous.comp (continuous_const.mul continuous_id))
  · exact nowhere_geometric_summable
  · exact nowhere_term_bound

theorem nowhere_scale (n : ℕ) : ((3 : ℝ)/4)^n * (4 : ℝ)^n = (3 : ℝ)^n := by
  rw [← mul_pow]
  norm_num

theorem nowhere_tail_shift (x σ : ℝ) (hσ : σ = -(1/2 : ℝ) ∨ σ = 1/2) (m k : ℕ) :
    nowhereTent ((4 : ℝ)^(m+1+k) * (x + σ/(4 : ℝ)^m)) =
      nowhereTent ((4 : ℝ)^(m+1+k) * x) := by
  rcases hσ with rfl | rfl
  · convert nowhereTent_add_even_int ((4 : ℝ)^(m+1+k)*x) (-(4 : ℤ)^k) using 1
    congr 1
    push_cast
    simp only [pow_add, pow_one]
    field_simp
    ring
  · convert nowhereTent_add_even_int ((4 : ℝ)^(m+1+k)*x) ((4 : ℤ)^k) using 1
    congr 1
    push_cast
    simp only [pow_add, pow_one]
    field_simp
    ring

theorem nowhere_difference_finite (x σ : ℝ)
    (hσ : σ = -(1/2 : ℝ) ∨ σ = 1/2) (m : ℕ) :
    nowhereWitness (x + σ/(4 : ℝ)^m) - nowhereWitness x =
      ∑ k ∈ Finset.range (m+1), ((3 : ℝ)/4)^k *
        (nowhereTent ((4 : ℝ)^k*(x+σ/(4 : ℝ)^m)) - nowhereTent ((4 : ℝ)^k*x)) := by
  unfold nowhereWitness
  rw [← (nowhereWitness_summable _).tsum_sub (nowhereWitness_summable _)]
  simp_rw [← mul_sub]
  apply tsum_eq_sum
  intro k hk
  have hmk : m + 1 ≤ k := by simpa using hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hmk
  rw [nowhere_tail_shift x σ hσ m j, sub_self, mul_zero]

theorem nowhere_term_difference_bound (x δ : ℝ) (k : ℕ) :
    |((3 : ℝ)/4)^k *
      (nowhereTent ((4 : ℝ)^k*(x+δ)) - nowhereTent ((4 : ℝ)^k*x))| ≤
      (3 : ℝ)^k * |δ| := by
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((3 : ℝ)/4)^k)]
  calc
    _ ≤ ((3 : ℝ)/4)^k * |(4 : ℝ)^k*(x+δ) - (4 : ℝ)^k*x| :=
      mul_le_mul_of_nonneg_left (nowhereTent_lipschitz _ _) (by positivity)
    _ = ((3 : ℝ)/4)^k * ((4 : ℝ)^k * |δ|) := by
      rw [← mul_sub, add_sub_cancel_left, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (4 : ℝ)^k)]
    _ = (3 : ℝ)^k * |δ| := by rw [← mul_assoc, nowhere_scale]

theorem nowhere_geometric_finite (m : ℕ) :
    ∑ k ∈ Finset.range m, (3 : ℝ)^k = ((3 : ℝ)^m - 1)/2 := by
  induction m with
  | zero => norm_num
  | succ m ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring

theorem nowhere_step_abs (σ : ℝ) (hσ : σ = -(1/2 : ℝ) ∨ σ = 1/2) (m : ℕ) :
    |σ/(4 : ℝ)^m| = (1/2 : ℝ)/(4 : ℝ)^m := by
  rcases hσ with rfl | rfl <;> simp [abs_div, abs_of_nonneg (le_of_lt (pow_pos (by norm_num : (0 : ℝ)<4) m))]

theorem nowhere_last_difference (x σ : ℝ)
    (hσ : σ = -(1/2 : ℝ) ∨ σ = 1/2) (m : ℕ)
    (hs : |nowhereTent ((4 : ℝ)^m*x+σ) - nowhereTent ((4 : ℝ)^m*x)| = 1/2) :
    |((3 : ℝ)/4)^m *
      (nowhereTent ((4 : ℝ)^m*(x+σ/(4 : ℝ)^m)) - nowhereTent ((4 : ℝ)^m*x))| =
      (3 : ℝ)^m * |σ/(4 : ℝ)^m| := by
  have hn : (4 : ℝ)^m ≠ 0 := by positivity
  have he : (4 : ℝ)^m*(x+σ/(4 : ℝ)^m) = (4 : ℝ)^m*x+σ := by field_simp
  rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ((3 : ℝ)/4)^m), hs, nowhere_step_abs σ hσ]
  rw [div_pow]
  ring

theorem nowhere_difference_lower (x σ : ℝ)
    (hσ : σ = -(1/2 : ℝ) ∨ σ = 1/2) (m : ℕ)
    (hs : |nowhereTent ((4 : ℝ)^m*x+σ) - nowhereTent ((4 : ℝ)^m*x)| = 1/2) :
    ((3 : ℝ)^m + 1)/2 * |σ/(4 : ℝ)^m| ≤
      |nowhereWitness (x+σ/(4 : ℝ)^m) - nowhereWitness x| := by
  let δ := σ/(4 : ℝ)^m
  let d := fun k : ℕ => ((3 : ℝ)/4)^k *
    (nowhereTent ((4 : ℝ)^k*(x+δ)) - nowhereTent ((4 : ℝ)^k*x))
  have hb : |∑ k ∈ Finset.range m, d k| ≤ ((3 : ℝ)^m - 1)/2 * |δ| := by
    calc
      _ ≤ ∑ k ∈ Finset.range m, |d k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range m, (3 : ℝ)^k * |δ| :=
        Finset.sum_le_sum (fun k _ => nowhere_term_difference_bound x δ k)
      _ = _ := by rw [← Finset.sum_mul, nowhere_geometric_finite]
  have hl : |d m| = (3 : ℝ)^m * |δ| := nowhere_last_difference x σ hσ m hs
  have ht : |d m| ≤ |(∑ k ∈ Finset.range m, d k) + d m| + |∑ k ∈ Finset.range m, d k| := by
    simpa only [add_sub_cancel_left] using
      (abs_sub ((∑ k ∈ Finset.range m, d k) + d m) (∑ k ∈ Finset.range m, d k))
  rw [nowhere_difference_finite x σ hσ m, Finset.sum_range_succ]
  change ((3 : ℝ)^m+1)/2 * |δ| ≤ |(∑ k ∈ Finset.range m, d k) + d m|
  nlinarith

theorem nowhere_large_difference (x : ℝ) (m : ℕ) :
    ∃ δ : ℝ, |δ| = (1/2 : ℝ)/(4 : ℝ)^m ∧
      ((3 : ℝ)^m+1)/2 * |δ| ≤ |nowhereWitness (x+δ) - nowhereWitness x| := by
  obtain ⟨σ, hσ, hs⟩ := nowhereTent_half_step ((4 : ℝ)^m*x)
  exact ⟨σ/(4 : ℝ)^m, nowhere_step_abs σ hσ m, nowhere_difference_lower x σ hσ m hs⟩

theorem nowhereWitness_not_differentiable (x : ℝ) :
    ¬ DifferentiableAt ℝ nowhereWitness x := by
  intro hd
  obtain ⟨C, hC⟩ := hd.isBigO_sub.bound
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hC
  have hsmall : Tendsto (fun m : ℕ => (1/2 : ℝ)/(4 : ℝ)^m) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num : (1 : ℝ)/4 < 1)).const_mul (1/2 : ℝ)
    simpa [div_pow, div_eq_mul_inv] using h
  have hlarge : Tendsto (fun m : ℕ => (3 : ℝ)^m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsmall' : ∀ᶠ m : ℕ in atTop, (1/2 : ℝ)/(4 : ℝ)^m < ε :=
    (tendsto_order.mp hsmall).2 ε hε
  have hlarge' : ∀ᶠ m : ℕ in atTop, 2*C < (3 : ℝ)^m :=
    hlarge.eventually_gt_atTop (2*C)
  obtain ⟨m, hmSmall, hmLarge⟩ := (hsmall'.and hlarge').exists
  obtain ⟨δ, hδ, hdiff⟩ := nowhere_large_difference x m
  have hδpos : 0 < |δ| := by rw [hδ]; positivity
  have hdist : dist (x+δ) x < ε := by simpa [Real.dist_eq, hδ] using hmSmall
  have hu : |nowhereWitness (x+δ) - nowhereWitness x| ≤ C * |δ| := by
    simpa [Real.norm_eq_abs] using hnear hdist
  nlinarith

/-- PMA-7.18: a continuous real function differentiable at no real point. -/
theorem pma7_18 : pma7_18_contract :=
  ⟨nowhereWitness, nowhereWitness_continuous, nowhereWitness_not_differentiable⟩

end Rudin.PMA.Chapter07
