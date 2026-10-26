import Rudin.PMA.Chapter11.GeometryRing

noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology BigOperators ENNReal

namespace Rudin.PMA.Chapter11

/-- A mixed-endpoint interval is the intersection of a closed elementary box and
an open box. This representation retains any mass carried by boundary faces. -/
lemma IsInterval.closed_inter_open {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsInterval A) :
    ∃ C U, IsElementary C ∧ IsClosed C ∧ IsOpen U ∧ A = C ∩ U := by
  obtain ⟨a, b, l, r, hab, rfl⟩ := hA
  let C := intervalSet a b (fun _ => true) (fun _ => true)
  let U := intervalSet (fun i => if l i then a i - 1 else a i)
    (fun i => if r i then b i + 1 else b i) (fun _ => false) (fun _ => false)
  refine ⟨C, U, IsInterval.isElementary ⟨a, b, _, _, hab, rfl⟩,
    isClosed_set_pi (fun _ _ => isClosed_Icc),
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo), ?_⟩
  ext x
  change (∀ i ∈ univ, x i ∈ axisInterval (a i) (b i) (l i) (r i)) ↔
    (∀ i ∈ univ, x i ∈ axisInterval (a i) (b i) true true) ∧
      (∀ i ∈ univ, x i ∈ axisInterval (if l i then a i - 1 else a i)
        (if r i then b i + 1 else b i) false false)
  simp only [mem_univ, forall_const, ← forall_and]
  apply forall_congr'
  intro i
  cases l i <;> cases r i <;> simp [axisInterval] <;> grind

/-- Closed elementary inner approximations for a single mixed interval, valid
for every locally finite measure and including atomic boundary mass. -/
lemma IsInterval.exists_closed_elementary_sdiff_lt {p : ℕ}
    (μ : Measure (Fin p → ℝ)) [IsLocallyFiniteMeasure μ]
    {A : Set (Fin p → ℝ)} (hA : IsInterval A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F, IsElementary F ∧ IsClosed F ∧ F ⊆ A ∧ μ (A \ F) < ε := by
  obtain ⟨C, U, hC, hCc, hUo, hAeq⟩ := hA.closed_inter_open
  obtain ⟨K, hKA, hK, hμK⟩ := hA.measurableSet.exists_isCompact_sdiff_lt
    (μ := μ) hA.isBounded.measure_lt_top.ne hε.ne'
  have hKU : K ⊆ U := by rw [hAeq] at hKA; exact hKA.trans inter_subset_right
  obtain ⟨D, G, hD, _, hDc, _, hKG, hGD, hDU⟩ := compact_elementary_sandwich hK hUo hKU
  have hFA : C ∩ D ⊆ A := by rw [hAeq]; exact inter_subset_inter_right C hDU
  have hKF : K ⊆ C ∩ D := by
    apply subset_inter
    · rw [hAeq] at hKA
      exact hKA.trans inter_subset_left
    · exact hKG.trans hGD
  exact ⟨C ∩ D, hC.inter hD, hCc.inter hDc, hFA,
    (measure_mono (sdiff_subset_sdiff subset_rfl hKF)).trans_lt hμK⟩

/-- Closed elementary inner approximations extend to finite unions. -/
lemma IsElementary.exists_closed_elementary_sdiff_lt {p : ℕ}
    (μ : Measure (Fin p → ℝ)) [IsLocallyFiniteMeasure μ]
    {A : Set (Fin p → ℝ)} (hA : IsElementary A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F, IsElementary F ∧ IsClosed F ∧ F ⊆ A ∧ μ (A \ F) < ε := by
  classical
  obtain ⟨I, hI, rfl⟩ := hA
  induction I using Finset.induction generalizing ε with
  | empty =>
    refine ⟨∅, isElementary_empty p, isClosed_empty, by simp, ?_⟩
    simpa using hε
  | @insert A I hAI ih =>
    have he : 0 < ε / 2 := ENNReal.half_pos hε.ne'
    obtain ⟨F, hF, hFc, hFA, hμF⟩ :=
      (hI A (by simp)).exists_closed_elementary_sdiff_lt μ he
    obtain ⟨G, hG, hGc, hGI, hμG⟩ :=
      ih he (fun B hB => hI B (Finset.mem_insert_of_mem hB))
    have heq : Set.sUnion (↑(insert A I) : Set (Set (Fin p → ℝ))) =
        A ∪ Set.sUnion (↑I : Set (Set (Fin p → ℝ))) := by simp
    rw [heq]
    refine ⟨F ∪ G, hF.union hG, hFc.union hGc, union_subset_union hFA hGI, ?_⟩
    calc
      μ ((A ∪ ⋃₀ ↑I) \ (F ∪ G)) ≤ μ ((A \ F) ∪ ((⋃₀ ↑I) \ G)) := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_sdiff, mem_union, not_or] at hx ⊢
        tauto
      _ ≤ μ (A \ F) + μ ((⋃₀ ↑I) \ G) := measure_union_le _ _
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hμF hμG
      _ = ε := ENNReal.add_halves ε

/-- 11.5–11.6: any locally finite measure is regular on the elementary sets,
with both approximants elementary. For the examples this applies to Lebesgue
measure and to the Stieltjes measures, without assuming non-atomicity.
This result verifies the examples; the general extension theorem in Construction
starts independently from a finite additive content. -/
theorem elementary_measure_regular {p : ℕ} (μ : Measure (Fin p → ℝ))
    [IsLocallyFiniteMeasure μ] {A : Set (Fin p → ℝ)} (hA : IsElementary A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F G, IsElementary F ∧ IsElementary G ∧ IsClosed F ∧ IsOpen G ∧
      F ⊆ A ∧ A ⊆ G ∧ μ G < μ A + ε ∧ μ A < μ F + ε := by
  obtain ⟨F, hF, hFc, hFA, hμF⟩ := hA.exists_closed_elementary_sdiff_lt μ hε
  obtain ⟨r, hr, hAB⟩ := hA.isBounded.subset_ball_lt 0 (0 : Fin p → ℝ)
  let B := Metric.ball (0 : Fin p → ℝ) r
  have hB : IsElementary B := isElementary_ball _ hr
  obtain ⟨D, hD, hDc, hDBA, hμD⟩ := (hB.sdiff hA).exists_closed_elementary_sdiff_lt μ hε
  have hAG : A ⊆ B \ D := by
    intro x hx
    exact ⟨hAB hx, fun hd => (hDBA hd).2 hx⟩
  have hGdiff : (B \ D) \ A = (B \ A) \ D := by ext x; simp only [Set.mem_sdiff]; tauto
  refine ⟨F, B \ D, hF, hB.sdiff hD, hFc, Metric.isOpen_ball.sdiff hDc, hFA, hAG, ?_, ?_⟩
  · calc
      μ (B \ D) ≤ μ A + μ ((B \ D) \ A) := by
        have hcover : B \ D ⊆ A ∪ ((B \ D) \ A) := by
          intro x hx
          by_cases ha : x ∈ A
          · exact Or.inl ha
          · exact Or.inr ⟨hx, ha⟩
        exact (measure_mono hcover).trans (measure_union_le _ _)
      _ < μ A + ε := ENNReal.add_lt_add_left hA.isBounded.measure_lt_top.ne (hGdiff ▸ hμD)
  · calc
      μ A ≤ μ F + μ (A \ F) := by
        simpa only [inter_eq_right.mpr hFA] using measure_le_inter_add_sdiff μ A F
      _ < μ F + ε := ENNReal.add_lt_add_left hF.isBounded.measure_lt_top.ne hμF

end Rudin.PMA.Chapter11
