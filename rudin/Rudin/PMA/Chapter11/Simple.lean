import Mathlib

/-!
# Chapter 11, 11.19–11.20: simple functions and approximation

Rudin's `simple` means finite range, with no measurability assumption. Accordingly
`IsSimple` is separate from Mathlib's bundled measurable `SimpleFunc`.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace Rudin.PMA.Chapter11

variable {X : Type*}

/-- 11.19: a real function is simple exactly when its range is finite. -/
def IsSimple (s : X → ℝ) : Prop := (Set.range s).Finite

/-- 11.19 (48): the characteristic function of an arbitrary set. -/
noncomputable def characteristic (E : Set X) : X → ℝ := E.indicator (fun _ => 1)

@[simp] theorem characteristic_of_mem {E : Set X} {x : X} (hx : x ∈ E) :
    characteristic E x = 1 := by simp [characteristic, hx]

@[simp] theorem characteristic_of_not_mem {E : Set X} {x : X} (hx : x ∉ E) :
    characteristic E x = 0 := by simp [characteristic, hx]

theorem characteristic_isSimple (E : Set X) : IsSimple (characteristic E) := by
  classical
  apply (Set.toFinite ({0, 1} : Set ℝ)).subset
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ E <;> simp [characteristic, hx]

/-- 11.19 (49): decomposition into the characteristic functions of the fibers. -/
theorem simple_eq_sum_characteristic {s : X → ℝ} (hs : IsSimple s) (x : X) :
    s x = ∑ c ∈ hs.toFinset, c * characteristic (s ⁻¹' {c}) x := by
  classical
  rw [Finset.sum_eq_single (s x)]
  · simp
  · intro b hb hbx
    simp [characteristic, hbx.symm]
  · simp [hs.mem_toFinset]

/-- 11.19: a simple function is measurable iff each fiber is measurable. -/
theorem simple_measurable_iff [MeasurableSpace X] {s : X → ℝ} (hs : IsSimple s) :
    Measurable s ↔ ∀ c, MeasurableSet (s ⁻¹' {c}) := by
  constructor
  · intro h c
    exact h (measurableSet_singleton c)
  · intro h
    exact (SimpleFunc.mk s h hs).measurable

/-- The faithful bridge from a finite-range measurable function to Mathlib's
bundled measurable simple functions. -/
def measurableSimple [MeasurableSpace X] {s : X → ℝ} (hs : IsSimple s)
    (hm : Measurable s) : SimpleFunc X ℝ :=
  ⟨s, fun c => hm (measurableSet_singleton c), hs⟩

/-- 11.20: even an arbitrary, nonmeasurable real function is a pointwise limit of
simple functions. The auxiliary top sigma algebra imposes no restriction on `f`. -/
theorem exists_simple_pointwise (f : X → ℝ) :
    ∃ s : ℕ → X → ℝ, (∀ n, IsSimple (s n)) ∧
      ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
  let : MeasurableSpace X := ⊤
  have hf : Measurable f := Measurable.of_comap_le le_top
  refine ⟨fun n => SimpleFunc.approxOn f hf Set.univ 0 (mem_univ _) n,
    fun n => (SimpleFunc.approxOn f hf Set.univ 0 (mem_univ _) n).finite_range, ?_⟩
  intro x
  exact SimpleFunc.tendsto_approxOn hf (mem_univ _) (by simp)

/-- 11.20: measurable functions have measurable simple approximants. -/
theorem exists_measurable_simple_pointwise [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) :
    ∃ s : ℕ → SimpleFunc X ℝ, ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
  exact ⟨SimpleFunc.approxOn f hf Set.univ 0 (mem_univ _),
    fun x => SimpleFunc.tendsto_approxOn hf (mem_univ _) (by simp)⟩

/-- 11.20: nonnegative measurable functions have increasing nonnegative simple
approximants, converging at every point. -/
theorem exists_measurable_simple_monotone [MeasurableSpace X] {f : X → ℝ}
    (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x) :
    ∃ s : ℕ → SimpleFunc X ℝ, (∀ n x, 0 ≤ s n x) ∧
      (∀ x, Monotone (fun n => s n x)) ∧
      ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
  let g : X → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  have hg : Measurable g := hf.ennreal_ofReal
  refine ⟨fun n => (SimpleFunc.eapprox g n).map ENNReal.toReal,
    fun n x => ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro x n m hnm
    exact ENNReal.toReal_mono (SimpleFunc.eapprox_lt_top g m x).ne
      (SimpleFunc.monotone_eapprox g hnm x)
  · intro x
    have h := (ENNReal.continuousAt_toReal (by simp [g])).tendsto.comp
      (SimpleFunc.tendsto_eapprox hg x)
    simpa only [SimpleFunc.coe_map, Function.comp_def, g, ENNReal.toReal_ofReal (hpos x)] using h

/-- 11.20: the increasing approximation clause also applies without measurability. -/
theorem exists_simple_monotone {f : X → ℝ} (hpos : ∀ x, 0 ≤ f x) :
    ∃ s : ℕ → X → ℝ, (∀ n, IsSimple (s n)) ∧ (∀ n x, 0 ≤ s n x) ∧
      (∀ x, Monotone (fun n => s n x)) ∧
      ∀ x, Tendsto (fun n => s n x) atTop (𝓝 (f x)) := by
  let : MeasurableSpace X := ⊤
  obtain ⟨s, hspos, hsmono, hslim⟩ :=
    exists_measurable_simple_monotone (Measurable.of_comap_le le_top) hpos
  exact ⟨fun n => s n, fun n => (s n).finite_range, hspos, hsmono, hslim⟩

/-- Rational grid approximation used for the bounded/uniform clause of 11.20. -/
noncomputable def gridApprox (f : X → ℝ) (n : ℕ) (x : X) : ℝ :=
  (⌊((n : ℝ) + 1) * f x⌋ : ℝ) / ((n : ℝ) + 1)

private theorem gridApprox_error (f : X → ℝ) (n : ℕ) (x : X) :
    0 ≤ f x - gridApprox f n x ∧
      f x - gridApprox f n x < 1 / ((n : ℝ) + 1) := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  constructor
  · rw [sub_nonneg, gridApprox, div_le_iff₀ hn]
    simpa only [mul_comm] using Int.floor_le (((n : ℝ) + 1) * f x)
  · rw [gridApprox, sub_div' hn.ne']
    rw [div_lt_div_iff_of_pos_right hn]
    have h := Int.lt_floor_add_one (((n : ℝ) + 1) * f x)
    nlinarith

private theorem gridApprox_simple {f : X → ℝ} {a b : ℝ}
    (hb : ∀ x, a ≤ f x ∧ f x ≤ b) (n : ℕ) : IsSimple (gridApprox f n) := by
  have hn : 0 ≤ (n : ℝ) + 1 := by positivity
  have hfin : (Set.range (fun x => ⌊((n : ℝ) + 1) * f x⌋)).Finite := by
    apply (Set.finite_Icc ⌊((n : ℝ) + 1) * a⌋ ⌊((n : ℝ) + 1) * b⌋).subset
    rintro _ ⟨x, rfl⟩
    exact ⟨Int.floor_mono (mul_le_mul_of_nonneg_left (hb x).1 hn),
      Int.floor_mono (mul_le_mul_of_nonneg_left (hb x).2 hn)⟩
  exact hfin.image (fun z : ℤ => (z : ℝ) / ((n : ℝ) + 1)) |>.subset (by
    rintro _ ⟨x, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩)

private theorem gridApprox_uniform (f : X → ℝ) :
    TendstoUniformly (gridApprox f) f atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  filter_upwards [(tendsto_order.mp hlim).2 ε hε] with n hn x
  rw [Real.dist_eq, abs_of_nonneg (gridApprox_error f n x).1]
  linarith [(gridApprox_error f n x).2]

/-- 11.20, bounded/uniform clause: bounded functions, including nonmeasurable
ones, have uniformly convergent simple approximants. If `f` is measurable the
same approximants are measurable. -/
theorem exists_simple_uniform [MeasurableSpace X] {f : X → ℝ} {a b : ℝ}
    (hb : ∀ x, a ≤ f x ∧ f x ≤ b) :
    ∃ s : ℕ → X → ℝ, (∀ n, IsSimple (s n)) ∧
      (Measurable f → ∀ n, Measurable (s n)) ∧ TendstoUniformly s f atTop := by
  refine ⟨gridApprox f, gridApprox_simple hb, ?_, gridApprox_uniform f⟩
  intro hf n
  exact ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (measurable_const.mul hf).floor).div_const _


private noncomputable def runningMax (s : ℕ → X → ℝ) : ℕ → X → ℝ
  | 0 => s 0
  | n + 1 => fun x => max (runningMax s n x) (s (n + 1) x)

private theorem runningMax_ge (s : ℕ → X → ℝ) (n : ℕ) (x : X) :
    s n x ≤ runningMax s n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

private theorem runningMax_le (s : ℕ → X → ℝ) {f : X → ℝ}
    (hf : ∀ n x, s n x ≤ f x) (n : ℕ) (x : X) : runningMax s n x ≤ f x := by
  induction n with
  | zero => exact hf 0 x
  | succ n ih => exact max_le ih (hf (n + 1) x)

private theorem runningMax_simple (s : ℕ → X → ℝ) (hs : ∀ n, IsSimple (s n))
    (n : ℕ) : IsSimple (runningMax s n) := by
  induction n with
  | zero => exact hs 0
  | succ n ih =>
    apply ((ih.prod (hs (n + 1))).image (fun p : ℝ × ℝ => max p.1 p.2)).subset
    rintro _ ⟨x, rfl⟩
    exact ⟨(runningMax s n x, s (n + 1) x), ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩, rfl⟩

private theorem runningMax_measurable [MeasurableSpace X] (s : ℕ → X → ℝ)
    (hs : ∀ n, Measurable (s n)) (n : ℕ) : Measurable (runningMax s n) := by
  induction n with
  | zero => exact hs 0
  | succ n ih => exact ih.max (hs (n + 1))

/-- 11.20: when the boundedness and nonnegativity clauses both apply, all the
conclusions hold for one sequence: simple, nonnegative, increasing, uniformly
convergent, and measurable whenever the original function is measurable. -/
theorem exists_simple_monotone_uniform [MeasurableSpace X] {f : X → ℝ} {b : ℝ}
    (hb : ∀ x, 0 ≤ f x ∧ f x ≤ b) :
    ∃ s : ℕ → X → ℝ, (∀ n, IsSimple (s n)) ∧ (∀ n x, 0 ≤ s n x) ∧
      (∀ x, Monotone (fun n => s n x)) ∧
      (Measurable f → ∀ n, Measurable (s n)) ∧ TendstoUniformly s f atTop := by
  have hle (n : ℕ) (x : X) : gridApprox f n x ≤ f x :=
    sub_nonneg.mp (gridApprox_error f n x).1
  refine ⟨runningMax (gridApprox f), runningMax_simple _ (gridApprox_simple hb), ?_, ?_, ?_, ?_⟩
  · intro n x
    apply le_trans _ (runningMax_ge _ n x)
    apply div_nonneg
    · exact_mod_cast (Int.floor_nonneg.mpr (mul_nonneg (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity) (hb x).1))
    · positivity
  · intro x
    exact monotone_nat_of_le_succ fun n => le_max_left _ _
  · intro hf
    exact runningMax_measurable _ fun n =>
      ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp
        (measurable_const.mul hf).floor).div_const _
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [(Metric.tendstoUniformly_iff.mp (gridApprox_uniform f)) ε hε] with n hn x
    have hu := runningMax_le _ hle n x
    have hl := runningMax_ge (gridApprox f) n x
    have hx := hn x
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hu)]
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hle n x))] at hx
    linarith

end Rudin.PMA.Chapter11
