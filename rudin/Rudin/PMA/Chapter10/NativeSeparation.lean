import Rudin.PMA.Chapter10.IntegrationMeasure

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

namespace Rudin.PMA.Chapter10

/-- A strictly positive continuous function has positive native integral on every
cell whose coordinate sides all have positive length. This also covers dimension zero. -/
theorem iteratedRIntegral_pos {k : ℕ} {C : Cell k} {f : Coord k → ℝ}
    (hf : ContinuousOn f C.carrier) (hside : ∀ i, C.lower i < C.upper i)
    (hpos : ∀ x ∈ C.carrier, 0 < f x) : 0 < iteratedRIntegral C f := by
  rw [iteratedRIntegral_eq_setIntegral hf]
  have hae : 0 ≤ᵐ[volume.restrict C.carrier] f :=
    (ae_restrict_mem C.isClosed_carrier.measurableSet).mono fun x hx => (hpos x hx).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae (Cell.integrable_measure hf)]
  have hs : Function.support f ∩ C.carrier = C.carrier := by
    apply inter_eq_right.mpr
    intro x hx
    exact (hpos x hx).ne'
  rw [hs]
  change 0 < volume (Icc C.lower C.upper)
  rw [Real.volume_Icc_pi]
  exact pos_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
    (fun i _ => (ENNReal.ofReal_pos.mpr (sub_pos.mpr (hside i))).ne'))

/-- Coordinate cube centered at the origin. -/
def centeredCell (k : ℕ) (r : ℝ) (hr : 0 ≤ r) : Cell k :=
  ⟨fun _ => -r, fun _ => r, fun _ => neg_le_self hr⟩

theorem centeredCell_contains_zero (k : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (0 : Coord k) ∈ (centeredCell k r hr).carrier := by
  rw [Cell.mem_carrier]
  intro i
  exact ⟨neg_nonpos.mpr hr, hr⟩

theorem centeredCell_subset_ball {k : ℕ} {r ε : ℝ} (hr : 0 ≤ r) (hrε : r < ε) :
    (centeredCell k r hr).carrier ⊆ Metric.ball (0 : Coord k) ε := by
  intro x hx
  have hn : ‖x‖ ≤ r := by
    rw [pi_norm_le_iff_of_nonneg hr]
    intro i
    exact abs_le.mpr (Cell.mem_carrier.mp hx i)
  simpa only [Metric.mem_ball, dist_zero_right] using hn.trans_lt hrε

/-- A positive coefficient stays positive on an actual finite rectangle inside
an arbitrary open parameter neighborhood. -/
theorem exists_positive_native_cell {k : ℕ} {U : Set (Coord k)} {f : Coord k → ℝ}
    (hU : IsOpen U) (h0 : (0 : Coord k) ∈ U) (hf : ContinuousOn f U) (hf0 : 0 < f 0) :
    ∃ C : Cell k, (0 : Coord k) ∈ C.carrier ∧ C.carrier ⊆ U ∧
      (∀ i, C.lower i < C.upper i) ∧
      (∀ x ∈ C.carrier, 0 < f x) ∧
      IteratedRIntegrable C f ∧ 0 < iteratedRIntegral C f := by
  have hfc : ContinuousAt f 0 := (hf 0 h0).continuousAt (hU.mem_nhds h0)
  have hmem : ∀ᶠ x in 𝓝 (0 : Coord k), x ∈ U := hU.mem_nhds h0
  have hnear : ∀ᶠ x in 𝓝 (0 : Coord k), x ∈ U ∧ 0 < f x :=
    hmem.and (hfc.eventually (isOpen_Ioi.mem_nhds hf0))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  let C := centeredCell k r hr.le
  have hC : C.carrier ⊆ {x | x ∈ U ∧ 0 < f x} :=
    (centeredCell_subset_ball hr.le (half_lt_self hε)).trans hball
  have hCU : C.carrier ⊆ U := fun x hx => (hC hx).1
  have hpos : ∀ x ∈ C.carrier, 0 < f x := fun x hx => (hC hx).2
  have hside : ∀ i, C.lower i < C.upper i := fun _ => neg_lt_self hr
  exact ⟨C, centeredCell_contains_zero k r hr.le, hCU, hside, hpos,
    iteratedRIntegrable_of_continuousOn (hf.mono hCU),
    iteratedRIntegral_pos (hf.mono hCU) hside hpos⟩

/-- A nonzero coefficient has a nonzero integral on a small native cell. -/
theorem exists_nonzero_native_cell {k : ℕ} {U : Set (Coord k)} {f : Coord k → ℝ}
    (hU : IsOpen U) (h0 : (0 : Coord k) ∈ U) (hf : ContinuousOn f U) (hf0 : f 0 ≠ 0) :
    ∃ C : Cell k, (0 : Coord k) ∈ C.carrier ∧ C.carrier ⊆ U ∧
      (∀ i, C.lower i < C.upper i) ∧
      IteratedRIntegrable C f ∧ iteratedRIntegral C f ≠ 0 := by
  rcases lt_or_gt_of_ne hf0 with hneg | hpos
  · obtain ⟨C, hC0, hCU, hside, _, _, hI⟩ :=
      exists_positive_native_cell hU h0 hf.neg (neg_pos.mpr hneg)
    refine ⟨C, hC0, hCU, hside, iteratedRIntegrable_of_continuousOn (hf.mono hCU), ?_⟩
    have he : iteratedRIntegral C (-f) = -iteratedRIntegral C f := by
      rw [iteratedRIntegral_eq_setIntegral (hf.neg.mono hCU),
        iteratedRIntegral_eq_setIntegral (hf.mono hCU)]
      simp only [Pi.neg_apply, integral_neg]
    rw [he] at hI
    exact (neg_pos.mp hI).ne
  · obtain ⟨C, hC0, hCU, hside, _, hi, hI⟩ := exists_positive_native_cell hU h0 hf hpos
    exact ⟨C, hC0, hCU, hside, hi, hI.ne'⟩

/-- Parameter-space version used by coordinate surfaces, without an injectivity
or immersion assumption on the parameterization. -/
theorem exists_nonzero_native_pullback {k n : ℕ} {E : Set (Chapter09.Euclidean n)}
    {φ : Coord k → Chapter09.Euclidean n} {f : Chapter09.Euclidean n → ℝ}
    (hE : IsOpen E) (hφ : Continuous φ) (hφ0 : φ 0 ∈ E)
    (hf : ContinuousOn f E) (hf0 : f (φ 0) ≠ 0) :
    ∃ C : Cell k, (0 : Coord k) ∈ C.carrier ∧ MapsTo φ C.carrier E ∧
      (∀ i, C.lower i < C.upper i) ∧
      IteratedRIntegrable C (fun t => f (φ t)) ∧
      iteratedRIntegral C (fun t => f (φ t)) ≠ 0 := by
  have hc : ContinuousOn (fun t => f (φ t)) (φ ⁻¹' E) :=
    hf.comp hφ.continuousOn (fun _ hx => hx)
  exact exists_nonzero_native_cell (hE.preimage hφ) hφ0 hc hf0

/-- Affine coordinate plane, including the zero-dimensional point surface. -/
def axisParameterization {k n : ℕ} (x : Chapter09.Euclidean n) (I : Fin k → Fin n)
    (t : Coord k) : Chapter09.Euclidean n :=
  x + ∑ j, t j • Chapter09.coordinateVector n (I j)

@[simp] theorem axisParameterization_zero {k n : ℕ} (x : Chapter09.Euclidean n)
    (I : Fin k → Fin n) : axisParameterization x I 0 = x := by
  simp [axisParameterization]

theorem axisParameterization_contDiff {k n : ℕ} (x : Chapter09.Euclidean n)
    (I : Fin k → Fin n) (r : ℕ∞ω) : ContDiff ℝ r (axisParameterization x I) := by
  unfold axisParameterization
  fun_prop

theorem exists_nonzero_axis_cell {k n : ℕ} {E : Set (Chapter09.Euclidean n)}
    {f : Chapter09.Euclidean n → ℝ} {x : Chapter09.Euclidean n}
    (hE : IsOpen E) (hx : x ∈ E) (hf : ContinuousOn f E) (hfx : f x ≠ 0)
    (I : Fin k → Fin n) :
    ∃ C : Cell k, (0 : Coord k) ∈ C.carrier ∧ MapsTo (axisParameterization x I) C.carrier E ∧
      (∀ i, C.lower i < C.upper i) ∧
      IteratedRIntegrable C (fun t => f (axisParameterization x I t)) ∧
      iteratedRIntegral C (fun t => f (axisParameterization x I t)) ≠ 0 := by
  apply exists_nonzero_native_pullback hE (axisParameterization_contDiff x I 0).continuous
  · simpa only [axisParameterization_zero] using hx
  · exact hf
  · simpa only [axisParameterization_zero] using hfx

@[simp] theorem zero_dimensional_axis_integral {n : ℕ} (C : Cell 0)
    (x : Chapter09.Euclidean n) (I : Fin 0 → Fin n) (f : Chapter09.Euclidean n → ℝ) :
    iteratedRIntegral C (fun t => f (axisParameterization x I t)) = f x := by
  simp [iteratedRIntegral, axisParameterization]

end Rudin.PMA.Chapter10
