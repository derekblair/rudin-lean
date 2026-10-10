import Rudin.PMA.Chapter07.Examples

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Rudin.PMA.Chapter07

def factorialCosinePower (m n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (((m + 1).factorial : ℝ) * Real.pi * x) ^ (2 * (n + 1))

def factorialGridIndicator (m : ℕ) (x : ℝ) : ℝ := by
  classical
  exact if ∃ k : ℤ, ((m + 1).factorial : ℝ) * x = k then 1 else 0

def rationalIndicator (x : ℝ) : ℝ := by
  classical
  exact if ∃ q : ℚ, (q : ℝ) = x then 1 else 0

/-! ### PMA-7.4: A double limit producing the rational indicator. -/
def pma7_4_contract : Prop :=
  (∀ m n : ℕ, Continuous (factorialCosinePower m n)) ∧
  (∀ (m : ℕ) (x : ℝ), Tendsto (fun n => factorialCosinePower m n x)
    atTop (𝓝 (factorialGridIndicator m x))) ∧
  (∀ x : ℝ, Tendsto (fun m => factorialGridIndicator m x)
    atTop (𝓝 (rationalIndicator x))) ∧
  (∀ x : ℝ, Tendsto
    (fun m : ℕ => limUnder atTop (fun n => factorialCosinePower m n x))
    atTop (𝓝 (rationalIndicator x))) ∧
  (∀ x : ℝ, ¬ ContinuousAt rationalIndicator x) ∧
  (∀ a b : ℝ, a < b → ¬ Chapter06.RIntegrable rationalIndicator a b)


theorem rationalIndicator_rat (q : ℚ) : rationalIndicator q = 1 := by
  classical
  simp [rationalIndicator]

theorem rationalIndicator_irrational {x : ℝ} (hx : Irrational x) : rationalIndicator x = 0 := by
  classical
  have h : ¬ ∃ q : ℚ, (q : ℝ) = x := hx
  simp [rationalIndicator, h]

theorem rationalIndicator_bounds (x : ℝ) : 0 ≤ rationalIndicator x ∧ rationalIndicator x ≤ 1 := by
  classical
  unfold rationalIndicator
  split <;> norm_num

theorem rationalIndicator_bounded (a b : ℝ) : Chapter06.BoundedOn rationalIndicator a b := by
  refine ⟨1, ?_⟩
  intro x _
  rw [abs_of_nonneg (rationalIndicator_bounds x).1]
  exact (rationalIndicator_bounds x).2

theorem rationalIndicator_discontinuous (x : ℝ) : ¬ ContinuousAt rationalIndicator x := by
  intro hc
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  by_cases hr : ∃ q : ℚ, (q : ℝ) = x
  · obtain ⟨y, hy, hxy, hyδ⟩ := exists_irrational_btwn (show x < x+δ/2 by linarith)
    have hdist : dist y x < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxy)]
      linarith
    have h := hd hdist
    rcases hr with ⟨q, rfl⟩
    rw [rationalIndicator_irrational hy, rationalIndicator_rat] at h
    norm_num at h
  · obtain ⟨q, hxq, hqδ⟩ := exists_rat_btwn (show x < x+δ/2 by linarith)
    have hdist : dist (q : ℝ) x < δ := by
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hxq)]
      linarith
    have h := hd hdist
    have hi : Irrational x := hr
    rw [rationalIndicator_rat, rationalIndicator_irrational hi] at h
    norm_num at h

theorem rationalIndicator_cell_extrema {a b : ℝ} (P : Chapter06.Partition a b)
    (i : Fin P.n) (hi : P.point i.castSucc < P.point i.succ) :
    Chapter06.cellLower rationalIndicator P i = 0 ∧
      Chapter06.cellUpper rationalIndicator P i = 1 := by
  have hb := rationalIndicator_bounded a b
  obtain ⟨y, hy, hyl, hyr⟩ := exists_irrational_btwn hi
  obtain ⟨q, hql, hqr⟩ := exists_rat_btwn hi
  constructor
  · apply le_antisymm
    · have h := Chapter06.cellLower_le_value hb P i (show y ∈ P.cell i from ⟨hyl.le, hyr.le⟩)
      simpa only [rationalIndicator_irrational hy] using h
    · apply le_csInf ((P.cell_nonempty i).image rationalIndicator)
      rintro _ ⟨x, _, rfl⟩
      exact (rationalIndicator_bounds x).1
  · apply le_antisymm
    · apply csSup_le ((P.cell_nonempty i).image rationalIndicator)
      rintro _ ⟨x, _, rfl⟩
      exact (rationalIndicator_bounds x).2
    · have h := Chapter06.value_le_cellUpper hb P i
        (show (q : ℝ) ∈ P.cell i from ⟨hql.le, hqr.le⟩)
      simpa only [rationalIndicator_rat] using h

theorem rationalIndicator_sums {a b : ℝ} (P : Chapter06.Partition a b) :
    Chapter06.lowerSum rationalIndicator id P = 0 ∧
      Chapter06.upperSum rationalIndicator id P = b-a := by
  constructor
  · change (∑ i : Fin P.n, Chapter06.cellLower rationalIndicator P i * P.weight id i) = 0
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : P.point i.castSucc < P.point i.succ
    · rw [(rationalIndicator_cell_extrema P i hi).1, zero_mul]
    · have heq := le_antisymm (P.cell_order i) (le_of_not_gt hi)
      simp [Chapter06.Partition.weight, heq]
  · calc
      Chapter06.upperSum rationalIndicator id P = ∑ i : Fin P.n, P.weight id i := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : P.point i.castSucc < P.point i.succ
        · rw [(rationalIndicator_cell_extrema P i hi).2, one_mul]
        · have heq := le_antisymm (P.cell_order i) (le_of_not_gt hi)
          simp [Chapter06.Partition.weight, heq]
      _ = b-a := P.sum_weights id

theorem rationalIndicator_not_integrable (a b : ℝ) (hab : a < b) :
    ¬ Chapter06.RIntegrable rationalIndicator a b := by
  intro hi
  obtain ⟨P, hP⟩ := (Chapter06.rsIntegrable_iff_gap hab.le
    (rationalIndicator_bounded a b) (fun _ _ _ _ h => h)).mp hi (b-a) (sub_pos.mpr hab)
  change Chapter06.upperSum rationalIndicator id P - Chapter06.lowerSum rationalIndicator id P < b-a at hP
  rw [(rationalIndicator_sums P).1, (rationalIndicator_sums P).2] at hP
  linarith

theorem factorialCosinePower_continuous (m n : ℕ) :
    Continuous (factorialCosinePower m n) := by
  have hc : Continuous (fun x : ℝ => ((m+1).factorial : ℝ)*Real.pi*x) :=
    continuous_const.mul continuous_id
  exact (Real.continuous_cos.comp hc).pow (2*(n+1))

theorem factorialCosinePower_inner (m : ℕ) (x : ℝ) :
    Tendsto (fun n => factorialCosinePower m n x) atTop (𝓝 (factorialGridIndicator m x)) := by
  classical
  let θ : ℝ := ((m+1).factorial : ℝ)*Real.pi*x
  by_cases hi : ∃ k : ℤ, ((m+1).factorial : ℝ)*x = k
  · obtain ⟨k, hk⟩ := hi
    have hs : Real.sin θ = 0 := Real.sin_eq_zero_iff.mpr ⟨k, by dsimp [θ]; rw [← hk]; ring⟩
    have hc : (Real.cos θ)^2 = 1 := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [hs] at h
      simpa using h
    have hv : ∀ n : ℕ, factorialCosinePower m n x = 1 := by
      intro n
      change (Real.cos θ)^(2*(n+1)) = 1
      rw [pow_mul, hc, one_pow]
    have hgrid : factorialGridIndicator m x = 1 := by
      simp [factorialGridIndicator, show ∃ k : ℤ, ((m+1).factorial : ℝ)*x = k from ⟨k, hk⟩]
    rw [hgrid]
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall (fun n => (hv n).symm))
  · have hs : Real.sin θ ≠ 0 := by
      intro hz
      obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hz
      apply hi
      refine ⟨k, ?_⟩
      apply mul_right_cancel₀ Real.pi_ne_zero
      calc
        (((m+1).factorial : ℝ)*x)*Real.pi = θ := by dsimp [θ]; ring
        _ = (k : ℝ)*Real.pi := hk.symm
    have hc : (Real.cos θ)^2 < 1 := by
      have h := Real.sin_sq_add_cos_sq θ
      nlinarith [sq_pos_of_ne_zero hs]
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg (Real.cos θ)) hc).comp
      (tendsto_add_atTop_nat 1)
    have hgrid : factorialGridIndicator m x = 0 := by simp [factorialGridIndicator, hi]
    rw [hgrid]
    convert ht using 1
    ext n
    change (Real.cos θ)^(2*(n+1)) = ((Real.cos θ)^2)^(n+1)
    exact pow_mul _ _ _

theorem factorialGridIndicator_outer (x : ℝ) :
    Tendsto (fun m => factorialGridIndicator m x) atTop (𝓝 (rationalIndicator x)) := by
  classical
  by_cases hr : ∃ q : ℚ, (q : ℝ) = x
  · obtain ⟨q, rfl⟩ := hr
    rw [rationalIndicator_rat]
    have hv : ∀ᶠ m : ℕ in atTop, factorialGridIndicator m q = 1 := by
      filter_upwards [eventually_ge_atTop q.den] with m hm
      have hd : q.den ∣ (m+1).factorial := Nat.dvd_factorial q.pos (by omega)
      obtain ⟨k, hk⟩ := hd
      have hi : ∃ z : ℤ, ((m+1).factorial : ℝ)*(q : ℝ) = z := by
        refine ⟨(k : ℤ)*q.num, ?_⟩
        rw [hk, Rat.cast_def]
        push_cast
        have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
        field_simp
      simp [factorialGridIndicator, hi]
    exact tendsto_const_nhds.congr' (hv.mono (fun _ h => h.symm))
  · have hx : Irrational x := hr
    rw [rationalIndicator_irrational hx]
    have hv : ∀ m : ℕ, factorialGridIndicator m x = 0 := by
      intro m
      have hi : ¬ ∃ k : ℤ, ((m+1).factorial : ℝ)*x = k := by
        rintro ⟨k, hk⟩
        exact (hx.natCast_mul (Nat.factorial_ne_zero _)).ne_int k hk
      simp [factorialGridIndicator, hi]
    exact tendsto_const_nhds.congr' (Filter.Eventually.of_forall (fun m => (hv m).symm))

theorem pma7_4 : pma7_4_contract := by
  refine ⟨factorialCosinePower_continuous, factorialCosinePower_inner,
    factorialGridIndicator_outer, ?_, rationalIndicator_discontinuous, rationalIndicator_not_integrable⟩
  intro x
  simpa only [(factorialCosinePower_inner _ x).limUnder_eq] using factorialGridIndicator_outer x

end Rudin.PMA.Chapter07
