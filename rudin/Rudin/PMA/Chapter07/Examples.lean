import Rudin.PMA.Chapter06
import Rudin.PMA.Chapter07.Basic

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter07

/-!
The positive source indices are represented by n+1 (and m+1).
The geometric series in 7.3 retains its source index starting at zero.
The complete contracts were independently accepted before these proofs.
PMA-7.4 is developed in the separate rational-indicator module.
-/

def doubleRatio (m n : ℕ) : ℝ := (m + 1 : ℝ) / ((m + 1 : ℝ) + (n + 1 : ℝ))

/-! ### PMA-7.2: Two different iterated limits. -/
def pma7_2_contract : Prop :=
  (∀ n : ℕ, Tendsto (fun m => doubleRatio m n) atTop (𝓝 1)) ∧
  (∀ m : ℕ, Tendsto (fun n => doubleRatio m n) atTop (𝓝 0)) ∧
  Tendsto (fun n : ℕ => limUnder atTop (fun m => doubleRatio m n)) atTop (𝓝 1) ∧
  Tendsto (fun m : ℕ => limUnder atTop (fun n => doubleRatio m n)) atTop (𝓝 0) ∧
  (1 : ℝ) ≠ 0

def geometricFunctionTerm (n : ℕ) (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2) ^ n

def geometricFunctionSum (x : ℝ) : ℝ := if x = 0 then 0 else 1 + x ^ 2

/-! ### PMA-7.3: A discontinuous sum of continuous functions. -/
def pma7_3_contract : Prop :=
  (∀ n : ℕ, Continuous (geometricFunctionTerm n)) ∧
  (∀ x : ℝ, Chapter03.SeriesHasSum (fun n => geometricFunctionTerm n x)
    (geometricFunctionSum x)) ∧
  ¬ ContinuousAt geometricFunctionSum 0

def sineOverSqrt (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin ((n + 1 : ℝ) * x) / Real.sqrt (n + 1 : ℝ)

/-! ### PMA-7.5: Uniform function convergence without derivative convergence. -/
def pma7_5_contract : Prop :=
  TendstoUniformly sineOverSqrt (fun _ => 0) atTop ∧
  (∀ x : ℝ, Tendsto (fun n => sineOverSqrt n x) atTop (𝓝 0)) ∧
  (∀ (n : ℕ) (x : ℝ), HasDerivAt (sineOverSqrt n)
    (Real.sqrt (n + 1 : ℝ) * Real.cos ((n + 1 : ℝ) * x)) x) ∧
  (∀ x : ℝ, HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 x) ∧
  Tendsto (fun n : ℕ => deriv (sineOverSqrt n) 0) atTop atTop

/-! ### PMA-7.6: Divergent and finite failures of exchanging limit and integral. -/
def pma7_6_contract : Prop :=
  let F : ℕ → ℝ → ℝ := fun n x => (n + 1 : ℝ)^2 * x * (1 - x^2)^(n+1)
  let G : ℕ → ℝ → ℝ := fun n x => (n + 1 : ℝ) * x * (1 - x^2)^(n+1)
  (∀ n : ℕ, Continuous (F n) ∧ Continuous (G n)) ∧
  (∀ x ∈ Icc (0 : ℝ) 1, Tendsto (fun n => F n x) atTop (𝓝 0) ∧
    Tendsto (fun n => G n x) atTop (𝓝 0)) ∧
  (∀ n : ℕ, Chapter06.RIntegrable (F n) 0 1 ∧
    Chapter06.RIntegral (F n) 0 1 = (n + 1 : ℝ)^2 / (2*(n+1 : ℝ)+2) ∧
    Chapter06.RIntegrable (G n) 0 1 ∧
    Chapter06.RIntegral (G n) 0 1 = (n + 1 : ℝ) / (2*(n+1 : ℝ)+2)) ∧
  Tendsto (fun n => Chapter06.RIntegral (F n) 0 1) atTop atTop ∧
  Tendsto (fun n => Chapter06.RIntegral (G n) 0 1) atTop (𝓝 (1/2)) ∧
  Chapter06.RIntegrable (fun _ => 0) 0 1 ∧
  Chapter06.RIntegral (fun _ => 0) 0 1 = 0

theorem examples_nat_succ_atTop :
    Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
  tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop

theorem doubleRatio_left_limit (n : ℕ) :
    Tendsto (fun m => doubleRatio m n) atTop (𝓝 1) := by
  have ht := (tendsto_atTop_add_const_right atTop (n + 1 : ℝ)
    examples_nat_succ_atTop).const_div_atTop (n + 1 : ℝ)
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub ht
  convert hh using 1
  · ext m
    dsimp only [doubleRatio]
    have hn : (m + 1 : ℝ) + (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · norm_num

theorem doubleRatio_right_limit (m : ℕ) :
    Tendsto (fun n => doubleRatio m n) atTop (𝓝 0) := by
  exact (tendsto_atTop_add_const_left atTop (m + 1 : ℝ)
    examples_nat_succ_atTop).const_div_atTop (m + 1 : ℝ)

theorem pma7_2 : pma7_2_contract := by
  refine ⟨doubleRatio_left_limit, doubleRatio_right_limit, ?_, ?_, by norm_num⟩
  · simpa only [(doubleRatio_left_limit _).limUnder_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  · simpa only [(doubleRatio_right_limit _).limUnder_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem geometricFunctionTerm_continuous (n : ℕ) : Continuous (geometricFunctionTerm n) := by
  apply Continuous.div (continuous_id.pow 2) ((continuous_const.add (continuous_id.pow 2)).pow n)
  intro x
  exact pow_ne_zero _ (by positivity : (1 : ℝ) + x^2 ≠ 0)

theorem geometricFunctionTerm_hasSum (x : ℝ) :
    Chapter03.SeriesHasSum (fun n => geometricFunctionTerm n x) (geometricFunctionSum x) := by
  by_cases hx : x = 0
  · subst x
    change Tendsto (fun N => ∑ n ∈ Finset.range N, geometricFunctionTerm n 0)
      atTop (𝓝 (geometricFunctionSum 0))
    simp [geometricFunctionTerm, geometricFunctionSum]
  · have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx
    have hden : 0 < 1 + x^2 := by positivity
    have hgeom := (hasSum_geometric_of_lt_one (by positivity : 0 ≤ (1+x^2)⁻¹)
      (inv_lt_one_of_one_lt₀ (by linarith : 1 < 1+x^2))).mul_left (x^2)
    have hs : HasSum (fun n => geometricFunctionTerm n x) (geometricFunctionSum x) := by
      convert hgeom using 1
      · ext n
        simp [geometricFunctionTerm, div_eq_mul_inv, inv_pow]
      · simp only [geometricFunctionSum, hx, ↓reduceIte]
        have hh : 1 - (1+x^2)⁻¹ ≠ 0 := by
          have := inv_lt_one_of_one_lt₀ (by linarith : 1 < 1+x^2)
          linarith
        field_simp
        ring
    exact hs.tendsto_sum_nat

theorem geometricFunctionSum_discontinuous : ¬ ContinuousAt geometricFunctionSum 0 := by
  intro hc
  have heq : geometricFunctionSum =ᶠ[𝓝[≠] (0 : ℝ)] (fun x => 1+x^2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [mem_compl_iff, mem_singleton_iff] at hx
    simp [geometricFunctionSum, hx]
  have h1 : Tendsto geometricFunctionSum (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have hh : Tendsto (fun x : ℝ => 1+x^2) (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
      have hc' : Continuous (fun x : ℝ => 1+x^2) :=
        continuous_const.add (continuous_id.pow 2)
      simpa using (hc'.tendsto 0).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    exact hh.congr' heq.symm
  have h0 : Tendsto geometricFunctionSum (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa [geometricFunctionSum] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique h0 h1
  norm_num at this

theorem pma7_3 : pma7_3_contract :=
  ⟨geometricFunctionTerm_continuous, geometricFunctionTerm_hasSum,
    geometricFunctionSum_discontinuous⟩

theorem sineOverSqrt_uniform : TendstoUniformly sineOverSqrt (fun _ => 0) atTop := by
  have ht : Tendsto (fun n : ℕ => 1 / Real.sqrt (n+1 : ℝ)) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp examples_nat_succ_atTop).const_div_atTop 1
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  intro x
  calc
    dist 0 (sineOverSqrt n x) =
        |Real.sin ((n+1 : ℝ)*x)| / Real.sqrt (n+1 : ℝ) := by
      simp [Real.dist_eq, sineOverSqrt, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    _ ≤ 1 / Real.sqrt (n+1 : ℝ) :=
      div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)
    _ < ε := hn

theorem sineOverSqrt_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (sineOverSqrt n)
      (Real.sqrt (n+1 : ℝ) * Real.cos ((n+1 : ℝ)*x)) x := by
  have hpos : (0 : ℝ) < n+1 := by positivity
  have hs : Real.sqrt (n+1 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  convert (((hasDerivAt_id x).const_mul (n+1 : ℝ)).sin).div_const
    (Real.sqrt (n+1 : ℝ)) using 1
  · rfl
  · simp only [id_eq, mul_one]
    apply (eq_div_iff hs).mpr
    calc
      Real.sqrt (n+1 : ℝ) * Real.cos ((n+1 : ℝ)*x) * Real.sqrt (n+1 : ℝ) =
          Real.cos ((n+1 : ℝ)*x) * (Real.sqrt (n+1 : ℝ))^2 := by ring
      _ = Real.cos ((n+1 : ℝ)*x) * (n+1 : ℝ) := by rw [Real.sq_sqrt hpos.le]

theorem pma7_5 : pma7_5_contract := by
  refine ⟨sineOverSqrt_uniform, fun x => sineOverSqrt_uniform.tendsto_at x,
    sineOverSqrt_hasDerivAt, fun x => hasDerivAt_const x 0, ?_⟩
  have heq : (fun n : ℕ => deriv (sineOverSqrt n) 0) =
      (fun n : ℕ => Real.sqrt (n+1 : ℝ)) := by
    funext n
    simp [(sineOverSqrt_hasDerivAt n 0).deriv]
  rw [heq]
  exact Real.tendsto_sqrt_atTop.comp examples_nat_succ_atTop

theorem integralSpikeSquared_continuous (n : ℕ) : Continuous (IntegralSpikeSquared n) := by
  exact (continuous_const.mul continuous_id).mul
    ((continuous_const.sub (continuous_id.pow 2)).pow (n+1))

theorem integralSpikeLinear_continuous (n : ℕ) : Continuous (IntegralSpikeLinear n) := by
  exact (continuous_const.mul continuous_id).mul
    ((continuous_const.sub (continuous_id.pow 2)).pow (n+1))

theorem integralSpike_pointwise (p : ℕ) (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n : ℕ => (n+1 : ℝ)^p*x*(1-x^2)^(n+1)) atTop (𝓝 0) := by
  by_cases hz : x = 0
  · simp [hz]
  have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hz)
  have hl : 0 ≤ 1-x^2 := by nlinarith [hx.2]
  have hu : 1-x^2 < 1 := by nlinarith [sq_pos_of_ne_zero hz]
  have ht := ((tendsto_pow_const_mul_const_pow_of_lt_one p hl hu).comp
    (tendsto_add_atTop_nat 1)).mul_const x
  convert ht using 1
  · ext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  · simp

theorem integralSpikeSquared_pointwise (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => IntegralSpikeSquared n x) atTop (𝓝 0) :=
  integralSpike_pointwise 2 x hx

theorem integralSpikeLinear_pointwise (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => IntegralSpikeLinear n x) atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (n+1 : ℝ)*x*(1-x^2)^(n+1)) atTop (𝓝 0)
  simpa only [pow_one] using integralSpike_pointwise 1 x hx

theorem integralSpike_base_integral (n : ℕ) :
    Chapter06.RIntegrable (fun x : ℝ => x*(1-x^2)^(n+1)) 0 1 ∧
    Chapter06.RIntegral (fun x : ℝ => x*(1-x^2)^(n+1)) 0 1 = 1/(2*(n+1 : ℝ)+2) := by
  have hc : Continuous (fun x : ℝ => x*(1-x^2)^(n+1)) :=
    continuous_id.mul ((continuous_const.sub (continuous_id.pow 2)).pow (n+1))
  have hi := Chapter06.rsIntegrable_of_continuousOn (by norm_num : (0:ℝ) ≤ 1)
    hc.continuousOn (fun _ _ _ _ h => h)
  refine ⟨hi, ?_⟩
  let A : ℝ → ℝ := fun x => -(1-x^2)^(n+2)/(2*(n+2 : ℝ))
  have hA : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt A (x*(1-x^2)^(n+1)) (Icc (0 : ℝ) 1) x := by
    intro x _
    apply HasDerivAt.hasDerivWithinAt
    have hd : HasDerivAt (fun y : ℝ => 1-y^2) (-2*x) x := by
      convert (hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2) using 1
      · rfl
      · simp only [id_eq, Nat.cast_ofNat]
        ring
    convert (hd.pow (n+2)).neg.div_const (2*(n+2 : ℝ)) using 1
    have hn : n+2-1 = n+1 := by omega
    rw [hn]
    push_cast
    have hden : (2 : ℝ)*(n+2) ≠ 0 := by positivity
    field_simp
  change Chapter06.RSIntegral (fun x : ℝ => x*(1-x^2)^(n+1)) (fun x => x) 0 1 = _
  rw [Chapter06.pma6_21 A _ 0 1 (by norm_num) hA hi]
  simp [A]
  ring

theorem integralSpikeSquared_integral (n : ℕ) :
    Chapter06.RIntegrable (IntegralSpikeSquared n) 0 1 ∧
    Chapter06.RIntegral (IntegralSpikeSquared n) 0 1 = (n+1 : ℝ)^2/(2*(n+1 : ℝ)+2) := by
  have h := Chapter06.rsIntegrable_const_mul (integralSpike_base_integral n).1 ((n+1 : ℝ)^2)
  change Chapter06.RSIntegrable (fun x => (n+1 : ℝ)^2*x*(1-x^2)^(n+1)) id 0 1 ∧
    Chapter06.RSIntegral (fun x => (n+1 : ℝ)^2*x*(1-x^2)^(n+1)) id 0 1 = _
  simpa only [mul_assoc, (integralSpike_base_integral n).2, mul_one_div] using h

theorem integralSpikeLinear_integral (n : ℕ) :
    Chapter06.RIntegrable (IntegralSpikeLinear n) 0 1 ∧
    Chapter06.RIntegral (IntegralSpikeLinear n) 0 1 = (n+1 : ℝ)/(2*(n+1 : ℝ)+2) := by
  have h := Chapter06.rsIntegrable_const_mul (integralSpike_base_integral n).1 (n+1 : ℝ)
  change Chapter06.RSIntegrable (fun x => (n+1 : ℝ)*x*(1-x^2)^(n+1)) id 0 1 ∧
    Chapter06.RSIntegral (fun x => (n+1 : ℝ)*x*(1-x^2)^(n+1)) id 0 1 = _
  simpa only [mul_assoc, (integralSpike_base_integral n).2, mul_one_div] using h

theorem integralSpikeLinear_coefficient_limit :
    Tendsto (fun n : ℕ => (n+1 : ℝ)/(2*(n+1 : ℝ)+2)) atTop (𝓝 (1/2)) := by
  have ht := examples_nat_succ_atTop.const_div_atTop 2
  have hd : Tendsto (fun n : ℕ => 2+2/(n+1 : ℝ)) atTop (𝓝 2) := by
    simpa using ht.const_add 2
  have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
    hd (by norm_num : (2 : ℝ) ≠ 0)
  convert hh using 1
  ext n
  change (n+1 : ℝ)/(2*(n+1 : ℝ)+2) = 1/(2+2/(n+1 : ℝ))
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have hd' : 2*(n+1 : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem integralSpikeSquared_integrals_atTop :
    Tendsto (fun n => Chapter06.RIntegral (IntegralSpikeSquared n) 0 1) atTop atTop := by
  have ht := Filter.Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1/2)
    examples_nat_succ_atTop integralSpikeLinear_coefficient_limit
  convert ht using 1
  ext n
  rw [(integralSpikeSquared_integral n).2]
  ring

theorem integralSpikeLinear_integrals_limit :
    Tendsto (fun n => Chapter06.RIntegral (IntegralSpikeLinear n) 0 1) atTop (𝓝 (1/2)) := by
  convert integralSpikeLinear_coefficient_limit using 1
  ext n
  exact (integralSpikeLinear_integral n).2

theorem pma7_6 : pma7_6_contract := by
  refine ⟨fun n => ⟨integralSpikeSquared_continuous n, integralSpikeLinear_continuous n⟩,
    fun x hx => ⟨integralSpikeSquared_pointwise x hx, integralSpikeLinear_pointwise x hx⟩,
    fun n => ⟨(integralSpikeSquared_integral n).1, (integralSpikeSquared_integral n).2,
      (integralSpikeLinear_integral n).1, (integralSpikeLinear_integral n).2⟩,
    integralSpikeSquared_integrals_atTop, integralSpikeLinear_integrals_limit, ?_, ?_⟩
  · exact (Chapter06.rsIntegral_const (c := 0) (by norm_num : (0:ℝ) ≤ 1)
      (fun _ _ _ _ h => h)).1
  · simpa using (Chapter06.rsIntegral_const (c := 0) (by norm_num : (0:ℝ) ≤ 1)
      (α := id) (fun _ _ _ _ h => h)).2

end Rudin.PMA.Chapter07
