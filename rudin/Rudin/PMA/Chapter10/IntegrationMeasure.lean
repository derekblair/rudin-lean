import Rudin.PMA.Chapter10.IntegrationProofs

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

namespace Cell

def measure {n : ℕ} (C : Cell n) : Measure (Coord n) := volume.restrict C.carrier

instance instSFinite {n : ℕ} (C : Cell n) : SFinite C.measure := by
  unfold measure
  infer_instance

theorem measure_eq_pi {n : ℕ} (C : Cell n) :
    C.measure = Measure.pi (fun i => volume.restrict (Icc (C.lower i) (C.upper i))) := by
  change (Measure.pi (fun _ : Fin n => (volume : Measure ℝ))).restrict (Icc C.lower C.upper) = _
  rw [← pi_univ_Icc]
  exact Measure.restrict_pi_pi _ _

theorem integrable_measure {n : ℕ} {C : Cell n} {f : Coord n → ℝ}
    (hf : ContinuousOn f C.carrier) : Integrable f C.measure :=
  hf.integrableOn_compact C.isCompact_carrier

end Cell

theorem integral_cell_snoc {n : ℕ} (C : Cell (n + 1)) (f : Coord (n + 1) → ℝ)
    (hf : Integrable f C.measure) :
    (∫ x, f x ∂C.measure) =
      ∫ x, (∫ t in Icc (C.lower (Fin.last n)) (C.upper (Fin.last n)), f (Fin.snoc x t))
        ∂C.init.measure := by
  let μ : Fin (n + 1) → Measure ℝ :=
    fun i => volume.restrict (Icc (C.lower i) (C.upper i))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hm := (measurePreserving_piFinSuccAbove μ (Fin.last n)).symm
  have hi : Integrable f (Measure.pi μ) := by simpa only [C.measure_eq_pi] using hf
  have hi' := (hm.integrable_comp_emb e.symm.measurableEmbedding).mpr hi
  have hsplit := (hm.integral_comp' f).symm
  have hsimp : (fun p : ℝ × Coord n => f (e.symm p)) =
      (fun p : ℝ × Coord n => f (Fin.snoc p.2 p.1)) := by
    funext p
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_last']
    rfl
  have hμ : Measure.pi (fun j => μ ((Fin.last n).succAbove j)) = C.init.measure := by
    rw [C.init.measure_eq_pi]
    congr 1
    funext j
    simp only [μ, Fin.succAbove_last_apply, Cell.init]
  change Integrable (fun p : ℝ × Coord n => f (e.symm p))
    ((μ (Fin.last n)).prod (Measure.pi (fun j => μ ((Fin.last n).succAbove j)))) at hi'
  rw [hsimp, hμ] at hi'
  change (∫ x, f x ∂Measure.pi μ) =
    ∫ p : ℝ × Coord n, f (e.symm p)
      ∂((μ (Fin.last n)).prod (Measure.pi (fun j => μ ((Fin.last n).succAbove j)))) at hsplit
  rw [hsimp, hμ, integral_prod_symm _ hi'] at hsplit
  simpa only [C.measure_eq_pi, μ] using hsplit

theorem nativeSliceIntegral_eq_setIntegral {n : ℕ} {C : Cell (n + 1)}
    {f : Coord (n + 1) → ℝ} (hf : ContinuousOn f C.carrier)
    {x : Coord n} (hx : x ∈ C.init.carrier) :
    nativeSliceIntegral C f x =
      ∫ t in Icc (C.lower (Fin.last n)) (C.upper (Fin.last n)), f (Fin.snoc x t) := by
  rw [nativeSliceIntegral,
    rIntegral_eq_intervalIntegral_of_continuousOn (C.lower_le_upper _) (continuousOn_slice hf hx),
    intervalIntegral.integral_of_le (C.lower_le_upper _), integral_Icc_eq_integral_Ioc]

theorem iteratedRIntegral_eq_setIntegral {n : ℕ} {C : Cell n} {f : Coord n → ℝ}
    (hf : ContinuousOn f C.carrier) : iteratedRIntegral C f = ∫ x in C.carrier, f x := by
  induction n with
  | zero =>
      have hC : C.carrier = univ := by
        ext x
        simp only [Cell.mem_carrier, mem_univ, iff_true]
        intro i
        exact Fin.elim0 i
      rw [hC, Measure.restrict_univ, Measure.volume_pi_eq_dirac (0 : Coord 0)]
      simp only [integral_dirac, iteratedRIntegral]
  | succ n ih =>
      change iteratedRIntegral C.init (nativeSliceIntegral C f) = ∫ x, f x ∂C.measure
      rw [ih (nativeSliceIntegral_continuousOn hf), integral_cell_snoc C f (Cell.integrable_measure hf)]
      apply setIntegral_congr_fun C.init.isClosed_carrier.measurableSet
      intro x hx
      exact nativeSliceIntegral_eq_setIntegral hf hx

theorem continuous_unpermute {n : ℕ} (σ : Equiv.Perm (Fin n)) : Continuous (unpermute σ) := by
  unfold unpermute
  exact continuous_pi fun i => continuous_apply (σ.symm i)

theorem unpermute_mem {n : ℕ} (C : Cell n) (σ : Equiv.Perm (Fin n)) {x : Coord n}
    (hx : x ∈ (C.permute σ).carrier) : unpermute σ x ∈ C.carrier := by
  rw [Cell.mem_carrier] at hx ⊢
  intro i
  simpa only [Cell.permute, unpermute, Equiv.apply_symm_apply] using hx (σ.symm i)

theorem integral_cell_permute {n : ℕ} (C : Cell n) (σ : Equiv.Perm (Fin n))
    (f : Coord n → ℝ) :
    (∫ x in (C.permute σ).carrier, f (unpermute σ x)) = ∫ x in C.carrier, f x := by
  have hm := measurePreserving_piCongrLeft
    (fun i : Fin n => volume.restrict (Icc (C.lower i) (C.upper i))) σ
  have h := hm.integral_comp' f
  have he : (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) σ : Coord n → Coord n) =
      unpermute σ := by
    funext x i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, unpermute]
  change (∫ x, f (unpermute σ x) ∂(C.permute σ).measure) = ∫ x, f x ∂C.measure
  simpa only [he, Cell.measure_eq_pi, Cell.permute] using h

theorem pma10_1 : pma10_1_contract := by
  exact ⟨fun _ _ _ hf => iteratedRIntegrable_of_continuousOn hf,
    fun _ _ _ hf => nativeSliceIntegral_continuousOn hf, fun _ _ _ => rfl,
    fun _ C _ hf => ⟨hf.integrableOn_compact C.isCompact_carrier,
      iteratedRIntegral_eq_setIntegral hf⟩⟩

theorem pma10_2 : pma10_2_contract := by
  intro n C f hf σ
  have hc : ContinuousOn (fun x => f (unpermute σ x)) (C.permute σ).carrier :=
    hf.comp (continuous_unpermute σ).continuousOn (fun x hx => unpermute_mem C σ hx)
  refine ⟨iteratedRIntegrable_of_continuousOn hc, ?_⟩
  rw [iteratedRIntegral_eq_setIntegral hc, iteratedRIntegral_eq_setIntegral hf]
  exact integral_cell_permute C σ f

theorem exists_cell_of_compact {n : ℕ} {s : Set (Coord n)} (hs : IsCompact s) :
    ∃ C : Cell n, s ⊆ C.carrier := by
  obtain ⟨R, hR, hsR⟩ := hs.isBounded.subset_closedBall_lt 0 (0 : Coord n)
  let C : Cell n := ⟨fun _ => -R, fun _ => R, fun _ => by linarith⟩
  refine ⟨C, ?_⟩
  intro x hx
  rw [Cell.mem_carrier]
  intro i
  have hnorm : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hsR hx
  have hi : |x i| ≤ R := (norm_le_pi_norm x i).trans hnorm
  exact abs_le.mp hi

theorem supportCell_contains {n : ℕ} {f : Coord n → ℝ} (hs : HasCompactSupport f) :
    tsupport f ⊆ (supportCell f).carrier := by
  have hex := exists_cell_of_compact hs
  simp only [supportCell, dite_eq_left hex]
  exact Classical.choose_spec hex

theorem setIntegral_eq_integral_of_tsupport_subset {n : ℕ} {f : Coord n → ℝ}
    {C : Cell n} (hs : tsupport f ⊆ C.carrier) :
    (∫ x in C.carrier, f x) = ∫ x, f x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hfx
  exact hx (hs (subset_tsupport f hfx))

theorem wholeRIntegral_eq_integral {n : ℕ} {f : Coord n → ℝ}
    (hf : Continuous f) (hs : HasCompactSupport f) : wholeRIntegral f = ∫ x, f x := by
  rw [wholeRIntegral, iteratedRIntegral_eq_setIntegral hf.continuousOn]
  exact setIntegral_eq_integral_of_tsupport_subset (supportCell_contains hs)

theorem wholeRIntegral_eq_cell {n : ℕ} {f : Coord n → ℝ} {C : Cell n}
    (hf : Continuous f) (hs : HasCompactSupport f) (hC : tsupport f ⊆ C.carrier) :
    wholeRIntegral f = iteratedRIntegral C f := by
  rw [wholeRIntegral_eq_integral hf hs, iteratedRIntegral_eq_setIntegral hf.continuousOn,
    setIntegral_eq_integral_of_tsupport_subset hC]

theorem complex_component_supports {n : ℕ} (f : Coord n → ℂ) :
    tsupport (fun x => (f x).re) ⊆ tsupport f ∧
    tsupport (fun x => (f x).im) ⊆ tsupport f := by
  constructor <;> apply closure_mono <;> intro x hx
  · contrapose! hx
    simp [Function.mem_support, Function.notMem_support.mp hx]
  · contrapose! hx
    simp [Function.mem_support, Function.notMem_support.mp hx]

theorem complexWholeRIntegral_eq_integral {n : ℕ} {f : Coord n → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) : complexWholeRIntegral f = ∫ x, f x := by
  have hr : HasCompactSupport (fun x => (f x).re) := hs.comp_left Complex.zero_re
  have hi : HasCompactSupport (fun x => (f x).im) := hs.comp_left Complex.zero_im
  have hrc : Continuous (fun x => (f x).re) := Complex.continuous_re.comp hf
  have hic : Continuous (fun x => (f x).im) := Complex.continuous_im.comp hf
  rw [complexWholeRIntegral, wholeRIntegral_eq_integral hrc hr,
    wholeRIntegral_eq_integral hic hi]
  exact integral_re_add_im (hf.integrable_of_hasCompactSupport hs)

theorem pma10_3 : pma10_3_contract := by
  refine ⟨fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro n f hf hs
    exact ⟨exists_cell_of_compact hs, hf.integrable_of_hasCompactSupport hs,
      wholeRIntegral_eq_integral hf hs⟩
  · intro n f C hf hs hC
    exact ⟨iteratedRIntegrable_of_continuousOn hf.continuousOn, wholeRIntegral_eq_cell hf hs hC⟩
  · intro n f hf hs
    exact ⟨exists_cell_of_compact hs, hf.integrable_of_hasCompactSupport hs,
      complexWholeRIntegral_eq_integral hf hs⟩
  · intro n f C hf hs hC
    have hr : HasCompactSupport (fun x => (f x).re) := hs.comp_left Complex.zero_re
    have hi : HasCompactSupport (fun x => (f x).im) := hs.comp_left Complex.zero_im
    have hrc : Continuous (fun x => (f x).re) := Complex.continuous_re.comp hf
    have hic : Continuous (fun x => (f x).im) := Complex.continuous_im.comp hf
    refine ⟨⟨iteratedRIntegrable_of_continuousOn hrc.continuousOn,
      iteratedRIntegrable_of_continuousOn hic.continuousOn⟩, ?_⟩
    rw [complexWholeRIntegral, complexIteratedRIntegral,
      wholeRIntegral_eq_cell hrc hr ((complex_component_supports f).1.trans hC),
      wholeRIntegral_eq_cell hic hi ((complex_component_supports f).2.trans hC)]

end Rudin.PMA.Chapter10
