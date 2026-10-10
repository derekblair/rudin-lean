import Mathlib

open Set Filter MeasureTheory
open scoped Topology Interval

noncomputable section
namespace Rudin.PMA.Chapter07

/-- Positive frequencies indexed from zero: the source's term `n + 1`. -/
def sineSequence (n : ℕ) (x : ℝ) : ℝ := Real.sin (((n : ℝ) + 1) * x)

/-- The exact interval from the source counterexample. -/
def sineSequenceDomain : Set ℝ := Icc 0 (2 * Real.pi)

/-- PMA 7.20: continuous, uniformly bounded, and no everywhere-pointwise
convergent subsequence. The strict index map is shared by all domain points. -/
def PMA7_20_Contract : Prop :=
  (∀ n : ℕ, ContinuousOn (sineSequence n) sineSequenceDomain) ∧
  (∀ n : ℕ, ∀ x ∈ sineSequenceDomain, |sineSequence n x| ≤ 1) ∧
  ¬ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℝ → ℝ, ∀ x ∈ sineSequenceDomain,
        Tendsto (fun n : ℕ => sineSequence (σ n) x) atTop (𝓝 (f x))

theorem sineSequence_continuous (n : ℕ) : Continuous (sineSequence n) := by
  unfold sineSequence
  fun_prop

theorem sineSequence_abs_le_one (n : ℕ) (x : ℝ) : |sineSequence n x| ≤ 1 :=
  Real.abs_sin_le_one _

/-- Integer cosine modes of nonzero frequency have zero interval integral. -/
theorem integer_cos_integral_zero (k : ℤ) (hk : k ≠ 0) :
    (∫ x in (0 : ℝ)..2 * Real.pi, Real.cos ((k : ℝ) * x)) = 0 := by
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hs : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    have he : (k : ℝ) * (2 * Real.pi) = ((2 * k : ℤ) : ℝ) * Real.pi := by
      push_cast
      ring
    rw [he, Real.sin_int_mul_pi]
  rw [intervalIntegral.integral_comp_mul_left Real.cos hkr, integral_cos]
  simp [hs]

/-- Each positive sine mode has squared integral exactly π. -/
theorem sineSequence_square_integral (n : ℕ) :
    (∫ x in (0 : ℝ)..2 * Real.pi, sineSequence n x ^ 2) = Real.pi := by
  have hc : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hs : Real.sin (((n : ℝ) + 1) * (2 * Real.pi)) = 0 := by
    have he : ((n : ℝ) + 1) * (2 * Real.pi) =
        ((2 * (n + 1) : ℕ) : ℝ) * Real.pi := by push_cast; ring
    rw [he, Real.sin_nat_mul_pi]
  change (∫ x in (0 : ℝ)..2 * Real.pi,
    (fun y : ℝ => Real.sin y ^ 2) (((n : ℝ) + 1) * x)) = Real.pi
  rw [intervalIntegral.integral_comp_mul_left (fun y : ℝ => Real.sin y ^ 2) hc, integral_sin_sq]
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, zero_mul, hs, sub_zero, sub_self,
    zero_add, smul_eq_mul]
  field_simp

/-- Orthogonality is proved through cosine product-to-sum on the exact interval. -/
theorem sineSequence_product_integral (n m : ℕ) (hnm : n ≠ m) :
    (∫ x in (0 : ℝ)..2 * Real.pi, sineSequence n x * sineSequence m x) = 0 := by
  have hd : (n : ℤ) - m ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hnm)
  have ha : (n : ℤ) + m + 2 ≠ 0 := ne_of_gt (by positivity)
  have hi (x : ℝ) : sineSequence n x * sineSequence m x =
      (Real.cos ((((n : ℤ) - m : ℤ) : ℝ) * x) -
        Real.cos ((((n : ℤ) + m + 2 : ℤ) : ℝ) * x)) / 2 := by
    have hdarg : ((((n : ℤ) - m : ℤ) : ℝ) * x) =
        ((n : ℝ) + 1) * x - ((m : ℝ) + 1) * x := by push_cast; ring
    have haarg : ((((n : ℤ) + m + 2 : ℤ) : ℝ) * x) =
        ((n : ℝ) + 1) * x + ((m : ℝ) + 1) * x := by push_cast; ring
    rw [hdarg, haarg]
    unfold sineSequence
    nlinarith [Real.two_mul_sin_mul_sin (((n : ℝ) + 1) * x) (((m : ℝ) + 1) * x)]
  have hcont (k : ℤ) : Continuous (fun x : ℝ => Real.cos ((k : ℝ) * x)) := by
    fun_prop
  simp_rw [hi]
  rw [intervalIntegral.integral_div]
  rw [intervalIntegral.integral_sub
    ((hcont ((n : ℤ) - m)).intervalIntegrable 0 (2 * Real.pi))
    ((hcont ((n : ℤ) + m + 2)).intervalIntegrable 0 (2 * Real.pi))]
  rw [integer_cos_integral_zero _ hd, integer_cos_integral_zero _ ha]
  norm_num

/-- Distinct modes are separated by a fixed positive squared integral. -/
theorem sineSequence_difference_square_integral (n m : ℕ) (hnm : n ≠ m) :
    (∫ x in (0 : ℝ)..2 * Real.pi, (sineSequence n x - sineSequence m x) ^ 2) =
      2 * Real.pi := by
  have hi (x : ℝ) : (sineSequence n x - sineSequence m x) ^ 2 =
      sineSequence n x ^ 2 + sineSequence m x ^ 2 -
        2 * (sineSequence n x * sineSequence m x) := by ring
  simp_rw [hi]
  have hn : IntervalIntegrable (fun x => sineSequence n x ^ 2) volume 0 (2 * Real.pi) :=
    ((sineSequence_continuous n).pow 2).intervalIntegrable _ _
  have hm : IntervalIntegrable (fun x => sineSequence m x ^ 2) volume 0 (2 * Real.pi) :=
    ((sineSequence_continuous m).pow 2).intervalIntegrable _ _
  have hp : IntervalIntegrable (fun x => 2 * (sineSequence n x * sineSequence m x))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul ((sineSequence_continuous n).mul (sineSequence_continuous m))
  rw [intervalIntegral.integral_sub (hn.add hm) hp,
    intervalIntegral.integral_add hn hm]
  rw [intervalIntegral.integral_const_mul, sineSequence_square_integral,
    sineSequence_square_integral, sineSequence_product_integral n m hnm]
  ring

/-- The contradiction uses measure-integral dominated convergence internally;
it asserts no replacement or completion of a Chapter 6/11 integral statement. -/
theorem sineSequence_no_pointwise_subsequence :
    ¬ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ℝ → ℝ, ∀ x ∈ sineSequenceDomain,
        Tendsto (fun n : ℕ => sineSequence (σ n) x) atTop (𝓝 (f x)) := by
  rintro ⟨σ, hσ, f, hf⟩
  let F : ℕ → ℝ → ℝ := fun n x =>
    (sineSequence (σ (n + 1)) x - sineSequence (σ n) x) ^ 2
  have hcont (n : ℕ) : Continuous (F n) :=
    ((sineSequence_continuous (σ (n + 1))).sub (sineSequence_continuous (σ n))).pow 2
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ 4 := by
    have hb : |sineSequence (σ (n + 1)) x - sineSequence (σ n) x| ≤ 2 := by
      calc
        _ ≤ |sineSequence (σ (n + 1)) x| + |sineSequence (σ n) x| := abs_sub _ _
        _ ≤ 2 := by linarith [sineSequence_abs_le_one (σ (n + 1)) x,
          sineSequence_abs_le_one (σ n) x]
    have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
    norm_num only [sq_abs] at hs
    simpa only [F, Real.norm_eq_abs, abs_pow, sq_abs] using hs
  have hlim (x : ℝ) (hx : x ∈ sineSequenceDomain) :
      Tendsto (fun n => F n x) atTop (𝓝 0) := by
    have h := hf x hx
    simpa [F] using ((h.comp (tendsto_add_atTop_nat 1)).sub h).pow 2
  have hD : Tendsto (fun n => ∫ x in (0 : ℝ)..2 * Real.pi, F n x)
      atTop (𝓝 (∫ _x in (0 : ℝ)..2 * Real.pi, (0 : ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ : ℝ => (4 : ℝ))
    · exact Eventually.of_forall fun n => (hcont n).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun x _hx => hbound n x
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro x hx
      apply hlim x
      rw [uIoc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at hx
      exact ⟨hx.1.le, hx.2⟩
  have hint (n : ℕ) : (∫ x in (0 : ℝ)..2 * Real.pi, F n x) = 2 * Real.pi :=
    sineSequence_difference_square_integral (σ (n + 1)) (σ n)
      (hσ (Nat.lt_succ_self n)).ne'
  have hzero : Tendsto (fun _ : ℕ => 2 * Real.pi) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hint, intervalIntegral.integral_zero] using hD
  have heq : 2 * Real.pi = 0 := tendsto_nhds_unique tendsto_const_nhds hzero
  nlinarith [Real.pi_pos]

/-- PMA 7.20, with all three accepted source assertions. -/
theorem pma7_20 : PMA7_20_Contract := by
  exact ⟨fun n => (sineSequence_continuous n).continuousOn,
    fun n x _hx => sineSequence_abs_le_one n x,
    sineSequence_no_pointwise_subsequence⟩

/-- Equivalent pointwise failure formulation: every strict subsequence has a bad point. -/
theorem sineSequence_subsequence_has_bad_point (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ x ∈ sineSequenceDomain, ¬ ∃ l : ℝ,
      Tendsto (fun n => sineSequence (σ n) x) atTop (𝓝 l) := by
  classical
  by_contra h
  push Not at h
  let f : ℝ → ℝ := fun x =>
    if hx : x ∈ sineSequenceDomain then Classical.choose (h x hx) else 0
  apply sineSequence_no_pointwise_subsequence
  refine ⟨σ, hσ, f, ?_⟩
  intro x hx
  simpa only [f, dite_eq_left hx] using Classical.choose_spec (h x hx)

/-- Repetition would trivially converge, so strict subsequence indices are essential. -/
theorem sineSequence_constant_index_probe :
    (∀ x : ℝ, Tendsto (fun _n : ℕ => sineSequence 0 x) atTop (𝓝 (sineSequence 0 x))) ∧
      ¬ StrictMono (fun _n : ℕ => (0 : ℕ)) := by
  refine ⟨fun _ => tendsto_const_nhds, ?_⟩
  intro h
  have hh := h (by norm_num : (0 : ℕ) < 1)
  exact (lt_irrefl 0) hh

/-- Every reindexing still has a limit at the left endpoint; failure is not at every point. -/
theorem sineSequence_endpoint_probe (σ : ℕ → ℕ) :
    Tendsto (fun n => sineSequence (σ n) 0) atTop (𝓝 (0 : ℝ)) := by
  have heq : (fun n => sineSequence (σ n) 0) = fun _n : ℕ => (0 : ℝ) := by
    funext n
    simp [sineSequence]
  rw [heq]
  exact tendsto_const_nhds

#print axioms pma7_20
#print axioms sineSequence_subsequence_has_bad_point

end Rudin.PMA.Chapter07
