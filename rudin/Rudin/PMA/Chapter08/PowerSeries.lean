import Rudin.PMA.Chapter03

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal NNReal ContDiff

namespace Rudin.PMA.Chapter08

/-- Real arguments and complex coefficients, with the usual ordered series.
The extended radius includes infinity; no endpoint convergence is assumed. -/
def Represents (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞) : Prop :=
  ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) < R →
    Chapter03.SeriesHasSum (fun n => x ^ n • c n) (f x)

/-- The multilinear encoding of an ordinary real-parameter power series. -/
def realSeries (c : ℕ → ℂ) : FormalMultilinearSeries ℝ ℝ ℂ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℝ (Fin n) (c n)

@[simp] theorem realSeries_coeff (c : ℕ → ℂ) (n : ℕ) :
    (realSeries c).coeff n = c n := by
  simp [realSeries, FormalMultilinearSeries.coeff]

@[simp] theorem realSeries_apply (c : ℕ → ℂ) (n : ℕ) (x : ℝ) :
    realSeries c n (fun _ => x) = x ^ n • c n := by
  simp

/-- Explicit comparison with the coefficient-left convention used in Chapter 3. -/
theorem realSeries_term_reference (c : ℕ → ℂ) (x : ℝ) (n : ℕ) :
    x ^ n • c n = Chapter03.PowerSeriesTerms c (x : ℂ) n := by
  simp [Chapter03.PowerSeriesTerms, Complex.real_smul, mul_comm]

/-- Ordinary convergence throughout a ball implies the analytic representation;
this bridge does not assume absolute convergence in its input. -/
theorem represents_hasFPowerSeries {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (h : Represents c f R) :
    HasFPowerSeriesOnBall f (realSeries c) 0 R := by
  have hr : R ≤ (realSeries c).radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have ht := (Chapter03.seriesHasSum_term_tendsto_zero
      (h r (by simpa using hr))).norm
    apply (realSeries c).le_radius_of_tendsto (r := r)
    simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg r.coe_nonneg,
      mul_comm] using ht
  refine ⟨hr, hR, ?_⟩
  intro x hx
  have hx' : (‖x‖₊ : ℝ≥0∞) < R := by simpa [enorm_eq_nnnorm] using hx
  have hs := (realSeries c).hasSum (show x ∈ Metric.eball 0 (realSeries c).radius from
    by simpa [enorm_eq_nnnorm] using hx'.trans_le hr)
  have hs' : HasSum (fun n => x ^ n • c n) ((realSeries c).sum x) := by
    simpa only [realSeries_apply] using hs
  have heq := tendsto_nhds_unique hs'.tendsto_sum_nat (h x hx')
  simpa [heq] using hs

/-- One formal differentiation of the coefficient sequence. -/
def diffCoeffs (c : ℕ → ℂ) (n : ℕ) : ℂ := (n + 1) • c (n + 1)

/-- Iterating termwise differentiation, with order zero retained. -/
def derivedCoeffs (c : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => c
  | k + 1 => diffCoeffs (derivedCoeffs c k)

theorem derivedCoeffs_eq (c : ℕ → ℂ) (k n : ℕ) :
    derivedCoeffs c k n = (n + 1).ascFactorial k • c (n + k) := by
  induction k generalizing n with
  | zero => simp [derivedCoeffs]
  | succ k ih =>
    simp only [derivedCoeffs, diffCoeffs, ih, ← mul_smul]
    rw [Nat.succ_ascFactorial, ← Nat.ascFactorial_succ]
    congr 2; omega

/-- Formal and ordinary differentiation agree on the full original open ball. -/
theorem hasFPowerSeries_deriv {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (realSeries c) 0 R) :
    HasFPowerSeriesOnBall (deriv f) (realSeries (diffCoeffs c)) 0 R := by
  convert (ContinuousLinearMap.apply ℝ ℂ (1 : ℝ)).comp_hasFPowerSeriesOnBall h.fderiv using 1
  · rfl
  · ext n
    simp [diffCoeffs]

theorem hasFPowerSeries_iteratedDeriv {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (h : HasFPowerSeriesOnBall f (realSeries c) 0 R) (k : ℕ) :
    HasFPowerSeriesOnBall (iteratedDeriv k f) (realSeries (derivedCoeffs c k)) 0 R := by
  induction k with
  | zero => simpa [derivedCoeffs] using h
  | succ k ih => simpa [iteratedDeriv_succ, derivedCoeffs] using hasFPowerSeries_deriv ih

theorem coefficient_formula {c : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (h : Represents c f R) (k : ℕ) :
    iteratedDeriv k f 0 = k.factorial • c k := by
  simpa [iteratedDeriv_eq_iteratedFDeriv] using
    ((represents_hasFPowerSeries hR h).factorial_smul 1 k).symm

theorem coefficients_unique {c d : ℕ → ℂ} {f : ℝ → ℂ} {R : ℝ≥0∞}
    (hR : 0 < R) (hc : Represents c f R) (hd : Represents d f R) : c = d := by
  funext n
  have he := (coefficient_formula hR hc n).symm.trans (coefficient_formula hR hd n)
  apply mul_left_cancel₀ (show (n.factorial : ℂ) ≠ 0 by
    exact_mod_cast n.factorial_ne_zero)
  simpa only [nsmul_eq_mul] using he

/-- The full source contract, including all derivative orders, coefficient
uniqueness, and the attached smoothness-versus-analyticity warning. -/
def pma8_1_contract : Prop :=
  (∀ (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞), 0 < R → Represents c f R →
    (∀ r : ℝ≥0, (r : ℝ≥0∞) < R →
      TendstoUniformlyOn (fun N x => Chapter03.PartialSums (fun n => x ^ n • c n) N)
        f atTop (Icc (-(r : ℝ)) r)) ∧
    ContinuousOn f (Metric.eball 0 R) ∧
    (∀ k : ℕ, ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) < R →
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x ∧
      Chapter03.SeriesHasSum
        (fun n => x ^ n • ((n + 1).ascFactorial k • c (n + k)))
        (iteratedDeriv k f x)) ∧
    (∀ k, iteratedDeriv k f 0 = k.factorial • c k) ∧
    (∀ d, Represents d f R → c = d)) ∧
  (∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ ¬ AnalyticAt ℝ g 0)

theorem pma8_1 : pma8_1_contract := by
  refine ⟨?_, ⟨expNegInvGlue, expNegInvGlue.contDiff, expNegInvGlue.not_analyticAt_zero⟩⟩
  intro c f R hR h
  have hp := represents_hasFPowerSeries hR h
  refine ⟨?_, hp.continuousOn, ?_, coefficient_formula hR h, fun d hd =>
    coefficients_unique hR h hd⟩
  · intro r hr
    have hsub : Icc (-(r : ℝ)) r ⊆ Metric.eball (0 : ℝ) R := by
      intro x hx
      have hn : ‖x‖₊ ≤ r := by
        exact_mod_cast (show ‖x‖ ≤ (r : ℝ) from (abs_le.mpr hx))
      simpa [enorm_eq_nnnorm] using (ENNReal.coe_le_coe.mpr hn).trans_lt hr
    have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
      (hp.tendstoLocallyUniformlyOn.mono hsub)
    simpa [FormalMultilinearSeries.partialSum, Chapter03.PartialSums] using hu
  · intro k x hx
    have hk := hasFPowerSeries_iteratedDeriv hp k
    have hmem : x ∈ Metric.eball (0 : ℝ) R := by simpa [enorm_eq_nnnorm] using hx
    refine ⟨?_, ?_⟩
    · simpa [iteratedDeriv_succ] using
        (hk.analyticAt_of_mem hmem).differentiableAt.hasDerivAt
    · have hh : Chapter03.SeriesHasSum
          (fun n => realSeries (derivedCoeffs c k) n (fun _ => x))
          (iteratedDeriv k f (0 + x)) := (hk.hasSum hmem).tendsto_sum_nat
      simpa only [realSeries_apply, derivedCoeffs_eq, zero_add] using hh

end Rudin.PMA.Chapter08
