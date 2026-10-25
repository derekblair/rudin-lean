import Rudin.PMA.Chapter08.Gamma

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory

namespace Rudin.PMA.Chapter08

/-- Logarithm of the main term in Stirling's formula. -/
def stirlingMainLog (x : ℝ) : ℝ :=
  x * Real.log x - x + Real.log x / 2 + Real.log (2 * Real.pi) / 2

def gammaStirlingLogError (x : ℝ) : ℝ :=
  Real.log (Real.Gamma (x + 1)) - stirlingMainLog x

theorem stirlingMainLog_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt stirlingMainLog (Real.log x + 1 / (2 * x)) x := by
  convert ((((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).sub
    (hasDerivAt_id x)).add ((Real.hasDerivAt_log hx.ne').div_const 2)).add_const
    (Real.log (2 * Real.pi) / 2) using 1
  · rfl
  · simp only [id_eq]
    field_simp
    ring

private theorem logGamma_recurrence {x : ℝ} (hx : 0 < x) :
    (Real.log ∘ Real.Gamma) (x + 1) = (Real.log ∘ Real.Gamma) x + Real.log x := by
  simp only [Function.comp_apply, Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

/-- A uniform estimate between consecutive integers, obtained from log-convexity
of Gamma and the mean value theorem. This is what extends factorial Stirling
to the positive real argument of PMA 8.22. -/
theorem gammaStirlingLogError_between {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hnx : (n : ℝ) ≤ x) (hxn : x ≤ n + 1) :
    |gammaStirlingLogError x - gammaStirlingLogError n| ≤
      (Real.log (n + 1) - Real.log n) + 1 / (2 * n) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n + 1) - Real.log n := by
    exact sub_nonneg.mpr (Real.log_le_log hnpos (by linarith))
  rcases hnx.eq_or_lt with rfl | hnx
  · simp only [sub_self, abs_zero]
    positivity
  have ht : 0 < x - n := sub_pos.mpr hnx
  have ht1 : x - n ≤ 1 := by linarith
  have hupper := Real.BohrMollerup.f_add_nat_le Real.convexOn_log_Gamma
    (fun hy => logGamma_recurrence hy) (n := n + 1) (by omega) ht ht1
  have hlower := Real.BohrMollerup.f_add_nat_ge Real.convexOn_log_Gamma
    (fun hy => logGamma_recurrence hy) (n := n + 1) (by omega) ht
  simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hupper hlower
  rw [show (n : ℝ) + 1 + (x - n) = x + 1 by ring] at hupper hlower
  rw [show (n : ℝ) + 1 - 1 = n by ring] at hlower
  obtain ⟨c, hc, hder⟩ := exists_hasDerivAt_eq_slope stirlingMainLog
    (fun u => Real.log u + 1 / (2 * u)) hnx
    (fun u hu => (stirlingMainLog_hasDerivAt (hnpos.trans_le hu.1)).continuousAt.continuousWithinAt)
    (fun u hu => stirlingMainLog_hasDerivAt (hnpos.trans hu.1))
  have hdiff : stirlingMainLog x - stirlingMainLog n =
      (x - n) * (Real.log c + 1 / (2 * c)) := by
    exact ((eq_div_iff (sub_pos.mpr hnx).ne').mp hder).symm.trans (by ring)
  have hcloglo : Real.log n ≤ Real.log c := Real.log_le_log hnpos hc.1.le
  have hcloghi : Real.log c ≤ Real.log (n + 1) :=
    Real.log_le_log (hnpos.trans hc.1) (hc.2.le.trans hxn)
  have hcinv : 1 / (2 * c) ≤ 1 / (2 * n) := by
    exact one_div_le_one_div_of_le (by positivity) (by linarith [hc.1])
  have hcpos : 0 ≤ 1 / (2 * c) := by
    have : 0 < c := hnpos.trans hc.1
    positivity
  have hrem0 : 0 ≤ (x - n) * (Real.log c - Real.log n + 1 / (2 * c)) := by
    exact mul_nonneg ht.le (by linarith)
  have hrem1 : (x - n) * (Real.log c - Real.log n + 1 / (2 * c)) ≤
      Real.log (n + 1) - Real.log n + 1 / (2 * n) := by
    calc
      _ ≤ (x - n) * (Real.log (n + 1) - Real.log n + 1 / (2 * n)) :=
        mul_le_mul_of_nonneg_left (by linarith) ht.le
      _ ≤ _ := mul_le_of_le_one_left (by positivity) ht1
  have hglim : (x - n) * (Real.log (n + 1) - Real.log n) ≤
      Real.log (n + 1) - Real.log n := mul_le_of_le_one_left hlog ht1
  rw [abs_le]
  dsimp only [gammaStirlingLogError]
  constructor <;> nlinarith [hrem0, hrem1, hglim]

theorem gammaStirlingLogError_nat (n : ℕ) (hn : 1 ≤ n) :
    gammaStirlingLogError n = Real.log (Stirling.stirlingSeq n) -
      Real.log (Real.sqrt Real.pi) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [gammaStirlingLogError, Real.Gamma_nat_eq_factorial,
    Stirling.log_stirlingSeq_formula, stirlingMainLog]
  rw [Real.log_div hnpos.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hnpos.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) Real.pi_pos.ne', Real.log_sqrt Real.pi_pos.le]
  ring

theorem gammaStirlingLogError_nat_limit :
    Tendsto (fun n : ℕ => gammaStirlingLogError n) atTop (𝓝 0) := by
  have h := ((Real.continuousAt_log (by positivity : Real.sqrt Real.pi ≠ 0)).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi).sub_const (Real.log (Real.sqrt Real.pi))
  simp only [sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (gammaStirlingLogError_nat n hn).symm

theorem gammaStirlingLogError_limit :
    Tendsto gammaStirlingLogError atTop (𝓝 0) := by
  let B : ℕ → ℝ := fun n => Real.log (n + 1) - Real.log n + 1 / (2 * n)
  have hB : Tendsto B atTop (𝓝 0) := by
    have hi := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).div_const 2
    have hi' : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * n)) atTop (𝓝 0) := by
      convert hi using 1
      · funext n; ring
      · simp
    simpa only [zero_add] using Real.tendsto_log_nat_add_one_sub_log.add hi'
  have hfloor : Tendsto (fun x : ℝ => ⌊x⌋₊) atTop atTop := tendsto_nat_floor_atTop
  have he := gammaStirlingLogError_nat_limit.comp hfloor
  have hb := hB.comp hfloor
  have hs : ∀ᶠ x : ℝ in atTop,
      gammaStirlingLogError (⌊x⌋₊ : ℝ) - B ⌊x⌋₊ ≤ gammaStirlingLogError x ∧
      gammaStirlingLogError x ≤ gammaStirlingLogError (⌊x⌋₊ : ℝ) + B ⌊x⌋₊ := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hn : 1 ≤ ⌊x⌋₊ := by exact Nat.le_floor (by simpa using hx)
    have h := abs_le.mp (gammaStirlingLogError_between hn (Nat.floor_le (by linarith))
      (Nat.lt_floor_add_one x).le)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using he.sub hb) (by simpa using he.add hb)
    (hs.mono fun _ h => h.1) (hs.mono fun _ h => h.2)

def gammaStirlingRatio (x : ℝ) : ℝ :=
  gamma (x + 1) / ((x / Real.exp 1) ^ x * Real.sqrt (2 * Real.pi * x))

theorem gammaStirlingRatio_eq_exp {x : ℝ} (hx : 0 < x) :
    gammaStirlingRatio x = Real.exp (gammaStirlingLogError x) := by
  have hg : 0 < gamma (x + 1) := by
    rw [gamma_eq_realGamma (by linarith)]
    exact Real.Gamma_pos_of_pos (by linarith)
  have hp : 0 < (x / Real.exp 1) ^ x := Real.rpow_pos_of_pos (by positivity) x
  have hs : 0 < Real.sqrt (2 * Real.pi * x) := by positivity
  have hr : 0 < gammaStirlingRatio x := div_pos hg (mul_pos hp hs)
  rw [← Real.exp_log hr]
  congr 1
  rw [gammaStirlingRatio, Real.log_div hg.ne' (mul_pos hp hs).ne',
    Real.log_mul hp.ne' hs.ne', Real.log_rpow (by positivity : 0 < x / Real.exp 1),
    Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_sqrt (by positivity), Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hx.ne',
    gammaStirlingLogError, stirlingMainLog, gamma_eq_realGamma (by linarith)]
  ring

/-- PMA 8.22: the limit is along all positive real arguments, rather than only
the factorial subsequence. -/
def pma8_22_contract : Prop :=
  Tendsto gammaStirlingRatio atTop (𝓝 1) ∧
  Tendsto (fun n : ℕ => (n.factorial : ℝ) /
    (((n : ℝ) / Real.exp 1) ^ n * Real.sqrt (2 * Real.pi * n))) atTop (𝓝 1)

theorem pma8_22 : pma8_22_contract := by
  have h : Tendsto gammaStirlingRatio atTop (𝓝 1) := by
    have he := Real.continuous_exp.continuousAt.tendsto.comp gammaStirlingLogError_limit
    simp only [Real.exp_zero] at he
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (gammaStirlingRatio_eq_exp hx).symm
  refine ⟨h, ?_⟩
  have hn : Tendsto (fun n : ℕ => gammaStirlingRatio (n : ℝ)) atTop (𝓝 1) :=
    h.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply hn.congr
  intro n
  rw [gammaStirlingRatio, pma8_18.2.1 n, Real.rpow_natCast]

end Rudin.PMA.Chapter08
