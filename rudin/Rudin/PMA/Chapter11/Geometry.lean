import Mathlib

/-!
# PMA 11.4 and 11.6: intervals, elementary sets, and their volumes

Intervals retain independently open or closed endpoints in every coordinate.
The function `elementaryVolume` is represented using the existing Lebesgue
measure; the interval and disjoint-union formulas below prove agreement with
Rudin's definition, rather than selecting a decomposition.
-/

noncomputable section
open Set Filter MeasureTheory Function
open scoped Topology BigOperators ENNReal

namespace Rudin.PMA.Chapter11

/-- An axis interval with independently optional endpoints. -/
def axisInterval (a b : ℝ) (leftClosed rightClosed : Bool) : Set ℝ :=
  {x | (if leftClosed then a ≤ x else a < x) ∧
    (if rightClosed then x ≤ b else x < b)}

/-- 11.4, (10): the rectangular interval in Euclidean `p`-space. -/
def intervalSet {p : ℕ} (a b : Fin p → ℝ) (leftClosed rightClosed : Fin p → Bool) :
    Set (Fin p → ℝ) :=
  Set.pi univ (fun i => axisInterval (a i) (b i) (leftClosed i) (rightClosed i))

/-- The family of intervals from 11.4, with nonnegative side lengths. -/
def IsInterval {p : ℕ} (A : Set (Fin p → ℝ)) : Prop :=
  ∃ (a b : Fin p → ℝ) (leftClosed rightClosed : Fin p → Bool),
    a ≤ b ∧ A = intervalSet a b leftClosed rightClosed

/-- 11.4: an elementary set is a finite union of intervals. -/
def IsElementary {p : ℕ} (A : Set (Fin p → ℝ)) : Prop :=
  ∃ I : Finset (Set (Fin p → ℝ)), (∀ s ∈ I, IsInterval s) ∧ A = Set.sUnion (↑I : Set (Set (Fin p → ℝ)))

/-- The nonnegative volume in 11.4. Its defining geometric formulas are proved below. -/
def elementaryVolume {p : ℕ} (A : Set (Fin p → ℝ)) : ℝ≥0∞ := volume A

lemma axisInterval_subset_Icc (a b : ℝ) (l r : Bool) :
    axisInterval a b l r ⊆ Icc a b := by
  cases l <;> cases r <;> intro x hx
  · exact ⟨hx.1.le, hx.2.le⟩
  · exact ⟨hx.1.le, hx.2⟩
  · exact ⟨hx.1, hx.2.le⟩
  · exact hx

lemma measurableSet_axisInterval (a b : ℝ) (l r : Bool) :
    MeasurableSet (axisInterval a b l r) := by
  cases l <;> cases r
  · exact measurableSet_Ioo
  · exact measurableSet_Ioc
  · exact measurableSet_Ico
  · exact measurableSet_Icc

lemma volume_axisInterval (a b : ℝ) (l r : Bool) :
    volume (axisInterval a b l r) = ENNReal.ofReal (b - a) := by
  cases l <;> cases r
  · exact Real.volume_Ioo
  · exact Real.volume_Ioc
  · exact Real.volume_Ico
  · exact Real.volume_Icc

/-- 11.4: the endpoint choices do not affect volume. -/
theorem pma11_4_interval_volume {p : ℕ} (a b : Fin p → ℝ)
    (l r : Fin p → Bool) :
    elementaryVolume (intervalSet a b l r) = ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [elementaryVolume, intervalSet, volume_pi_pi]
  exact Finset.prod_congr rfl fun i _ => volume_axisInterval _ _ _ _

/-- The book's real product formula, when the side lengths are nonnegative. -/
theorem pma11_4_interval_volume_real {p : ℕ} (a b : Fin p → ℝ)
    (l r : Fin p → Bool) (hab : a ≤ b) :
    (elementaryVolume (intervalSet a b l r)).toReal = ∏ i, (b i - a i) := by
  rw [pma11_4_interval_volume, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (sub_nonneg.mpr (hab i))

lemma IsInterval.measurableSet {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsInterval A) :
    MeasurableSet A := by
  obtain ⟨a, b, l, r, _, rfl⟩ := hA
  exact MeasurableSet.univ_pi fun i => measurableSet_axisInterval _ _ _ _

lemma IsInterval.isBounded {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsInterval A) :
    Bornology.IsBounded A := by
  obtain ⟨a, b, l, r, _, rfl⟩ := hA
  apply (isCompact_Icc (a := a) (b := b)).isBounded.subset
  intro x hx
  exact ⟨fun i => (axisInterval_subset_Icc _ _ _ _ (hx i (mem_univ i))).1,
    fun i => (axisInterval_subset_Icc _ _ _ _ (hx i (mem_univ i))).2⟩

lemma IsInterval.isElementary {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsInterval A) :
    IsElementary A := by
  refine ⟨{A}, ?_, by simp⟩
  simpa using hA

lemma isElementary_empty (p : ℕ) : IsElementary (∅ : Set (Fin p → ℝ)) :=
  ⟨∅, by simp, by simp⟩

lemma IsElementary.union {p : ℕ} {A B : Set (Fin p → ℝ)}
    (hA : IsElementary A) (hB : IsElementary B) : IsElementary (A ∪ B) := by
  classical
  obtain ⟨I, hI, rfl⟩ := hA
  obtain ⟨J, hJ, rfl⟩ := hB
  refine ⟨I ∪ J, ?_, by simp [Set.sUnion_union]⟩
  intro s hs
  rcases Finset.mem_union.mp hs with hs | hs
  · exact hI s hs
  · exact hJ s hs

lemma IsElementary.measurableSet {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsElementary A) :
    MeasurableSet A := by
  obtain ⟨I, hI, rfl⟩ := hA
  exact MeasurableSet.sUnion I.countable_toSet fun s hs => (hI s hs).measurableSet

lemma IsElementary.isBounded {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsElementary A) :
    Bornology.IsBounded A := by
  obtain ⟨I, hI, rfl⟩ := hA
  exact (Bornology.isBounded_sUnion I.finite_toSet).mpr fun s hs => (hI s hs).isBounded

/-- The geometric compactness fact used in the proof of 11.8(a). -/
theorem IsElementary.isCompact_of_isClosed {p : ℕ} {A : Set (Fin p → ℝ)}
    (hA : IsElementary A) (hc : IsClosed A) : IsCompact A :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc, hA.isBounded⟩

lemma IsElementary.volume_ne_top {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsElementary A) :
    elementaryVolume A ≠ ∞ :=
  hA.isBounded.measure_lt_top.ne

/-- 11.4, (11): the volume of any specified disjoint interval decomposition. -/
theorem pma11_4_disjoint_volume {p : ℕ} (I : Finset (Set (Fin p → ℝ)))
    (hI : ∀ s ∈ I, IsInterval s) (hd : (↑I : Set (Set (Fin p → ℝ))).PairwiseDisjoint id) :
    elementaryVolume (Set.sUnion (↑I : Set (Set (Fin p → ℝ)))) = ∑ s ∈ I, elementaryVolume s := by
  simpa only [elementaryVolume, Set.sUnion_eq_biUnion, Finset.mem_coe, id_eq] using
    measure_biUnion_finset hd (fun s hs => (hI s hs).measurableSet)

/-- 11.4, (14): two disjoint interval decompositions give the same value. -/
theorem pma11_4_well_defined {p : ℕ} (I J : Finset (Set (Fin p → ℝ)))
    (hI : ∀ s ∈ I, IsInterval s) (hJ : ∀ s ∈ J, IsInterval s)
    (hdI : (↑I : Set (Set (Fin p → ℝ))).PairwiseDisjoint id) (hdJ : (↑J : Set (Set (Fin p → ℝ))).PairwiseDisjoint id)
    (heq : Set.sUnion (↑I : Set (Set (Fin p → ℝ))) = Set.sUnion (↑J : Set (Set (Fin p → ℝ)))) :
    (∑ s ∈ I, elementaryVolume s) = ∑ s ∈ J, elementaryVolume s := by
  rw [← pma11_4_disjoint_volume I hI hdI, heq, pma11_4_disjoint_volume J hJ hdJ]

/-- 11.4, (15): finite additivity of volume on elementary sets. -/
theorem pma11_4_additive {p : ℕ} {A B : Set (Fin p → ℝ)}
    (_hA : IsElementary A) (hB : IsElementary B) (hd : Disjoint A B) :
    elementaryVolume (A ∪ B) = elementaryVolume A + elementaryVolume B :=
  measure_union hd hB.measurableSet

/-- The closed cubes used to cover Euclidean space countably. -/
def elementaryCube (p n : ℕ) : Set (Fin p → ℝ) :=
  Icc (fun _ => -(n : ℝ)) (fun _ => (n : ℝ))

lemma elementaryCube_isElementary (p n : ℕ) : IsElementary (elementaryCube p n) := by
  apply IsInterval.isElementary
  refine ⟨fun _ => -(n : ℝ), fun _ => (n : ℝ), fun _ => true, fun _ => true, ?_, ?_⟩
  · intro i
    exact neg_nonpos.mpr (Nat.cast_nonneg n) |>.trans (Nat.cast_nonneg n)
  · ext x
    simp [elementaryCube, intervalSet, axisInterval, Set.mem_Icc, Pi.le_def, forall_and]

lemma iUnion_elementaryCube (p : ℕ) : (⋃ n, elementaryCube p n) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
  refine mem_iUnion.mpr ⟨n, ?_⟩
  constructor <;> intro i
  · exact neg_le.mp ((neg_le_abs (x i)).trans ((norm_le_pi_norm x i).trans hn.le))
  · exact (le_abs_self (x i)).trans ((norm_le_pi_norm x i).trans hn.le)

/-- 11.4 explicitly includes the empty interval. Positive dimension is
needed here: the empty product in dimension zero is a singleton. -/
theorem pma11_4_empty_interval {p : ℕ} (hp : 0 < p) :
    IsInterval (∅ : Set (Fin p → ℝ)) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => false, fun _ => false, le_rfl, ?_⟩
  symm
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := hx ⟨0, hp⟩ (mem_univ _)
  exact lt_asymm hh.1 hh.2

/-- 11.4, (12): in positive dimension Euclidean space is not elementary. -/
theorem pma11_4_univ_not_elementary {p : ℕ} (hp : 0 < p) :
    ¬ IsElementary (univ : Set (Fin p → ℝ)) := by
  intro h
  obtain ⟨R, hR, hb⟩ := h.isBounded.exists_pos_norm_le
  have hi : Fin p := ⟨0, hp⟩
  have hh := (norm_le_pi_norm (fun _ : Fin p => R + 1) hi).trans
    (hb (fun _ : Fin p => R + 1) (mem_univ _))
  have hh' : |R + 1| ≤ R := hh
  linarith [le_abs_self (R + 1)]

/-- 11.4, (12): the explicit countable union witnessing failure of sigma closure. -/
theorem pma11_4_not_countable_union_closed {p : ℕ} (hp : 0 < p) :
    ∃ A : ℕ → Set (Fin p → ℝ), (∀ n, IsElementary (A n)) ∧
      ¬ IsElementary (⋃ n, A n) := by
  refine ⟨elementaryCube p, elementaryCube_isElementary p, ?_⟩
  rw [iUnion_elementaryCube]
  exact pma11_4_univ_not_elementary hp

lemma IsElementary.biUnion {p : ℕ} {ι : Type*} (I : Finset ι)
    (A : ι → Set (Fin p → ℝ)) (hA : ∀ i ∈ I, IsElementary (A i)) :
    IsElementary (⋃ i ∈ I, A i) := by
  classical
  induction I using Finset.induction with
  | empty => simpa using isElementary_empty p
  | @insert i I hi ih =>
    rw [Finset.set_biUnion_insert]
    exact (hA i (Finset.mem_insert_self _ _)).union
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

lemma isElementary_ball {p : ℕ} (x : Fin p → ℝ) {r : ℝ} (hr : 0 < r) :
    IsElementary (Metric.ball x r) := by
  apply IsInterval.isElementary
  refine ⟨fun i => x i - r, fun i => x i + r, fun _ => false, fun _ => false, ?_, ?_⟩
  · intro i
    linarith
  · rw [intervalSet, ball_pi x hr]
    congr 1
    funext i
    exact Real.ball_eq_Ioo _ _

lemma isElementary_closedBall {p : ℕ} (x : Fin p → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IsElementary (Metric.closedBall x r) := by
  apply IsInterval.isElementary
  refine ⟨fun i => x i - r, fun i => x i + r, fun _ => true, fun _ => true, ?_, ?_⟩
  · intro i
    linarith
  · rw [intervalSet, closedBall_pi x hr]
    congr 1
    funext i
    exact Real.closedBall_eq_Icc

/-- A compact set inside an open set has both a closed elementary neighborhood
and an open elementary neighborhood contained in that open set. -/
theorem compact_elementary_sandwich {p : ℕ} {K U : Set (Fin p → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ F G, IsElementary F ∧ IsElementary G ∧ IsClosed F ∧ IsOpen G ∧
      K ⊆ G ∧ G ⊆ F ∧ F ⊆ U := by
  classical
  have hloc : ∀ x : K, ∃ r : ℝ, 0 < r ∧ Metric.closedBall x.val r ⊆ U :=
    fun x => Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds (hKU x.property))
  choose r hr hsub using hloc
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => Metric.ball x.val (r x))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  refine ⟨⋃ x ∈ I, Metric.closedBall x.val (r x), ⋃ x ∈ I, Metric.ball x.val (r x),
    IsElementary.biUnion I _ (fun x _ => isElementary_closedBall x.val (hr x).le),
    IsElementary.biUnion I _ (fun x _ => isElementary_ball x.val (hr x)),
    isClosed_biUnion_finset (fun _ _ => Metric.isClosed_closedBall),
    isOpen_iUnion (fun _ => isOpen_iUnion (fun _ => Metric.isOpen_ball)), hI, ?_, ?_⟩
  · exact iUnion₂_mono fun _ _ => Metric.ball_subset_closedBall
  · exact iUnion₂_subset fun x _ => hsub x

lemma axisInterval_open_subset (a b : ℝ) (l r : Bool) :
    Ioo a b ⊆ axisInterval a b l r := by
  cases l <;> cases r <;> intro x hx
  · exact hx
  · exact ⟨hx.1, hx.2.le⟩
  · exact ⟨hx.1.le, hx.2⟩
  · exact ⟨hx.1.le, hx.2.le⟩

/-- Every elementary set has an open elementary subset and a closed elementary
superset differing only by Lebesgue null sets. This is specific to volume. -/
theorem IsElementary.open_closed_envelopes {p : ℕ} {A : Set (Fin p → ℝ)}
    (hA : IsElementary A) :
    ∃ U C, IsElementary U ∧ IsElementary C ∧ IsOpen U ∧ IsClosed C ∧
      U ⊆ A ∧ A ⊆ C ∧ U =ᵐ[volume] A ∧ A =ᵐ[volume] C := by
  classical
  have hi : ∀ B : Set (Fin p → ℝ), IsInterval B →
      ∃ U C, IsElementary U ∧ IsElementary C ∧ IsOpen U ∧ IsClosed C ∧
        U ⊆ B ∧ B ⊆ C ∧ U =ᵐ[volume] B ∧ B =ᵐ[volume] C := by
    rintro B ⟨a, b, l, r, hab, rfl⟩
    let U := intervalSet a b (fun _ => false) (fun _ => false)
    let C := intervalSet a b (fun _ => true) (fun _ => true)
    have hU : IsInterval U := ⟨a, b, _, _, hab, rfl⟩
    have hC : IsInterval C := ⟨a, b, _, _, hab, rfl⟩
    have hUA : U ⊆ intervalSet a b l r := by
      intro x hx i hi
      exact axisInterval_open_subset _ _ _ _ (hx i hi)
    have hAC : intervalSet a b l r ⊆ C := by
      intro x hx i hi
      exact axisInterval_subset_Icc _ _ _ _ (hx i hi)
    have hae : U =ᵐ[volume] C := by
      change (univ.pi (fun i => Ioo (a i) (b i))) =ᵐ[volume]
        (univ.pi (fun i => Icc (a i) (b i)))
      rw [volume_pi]
      exact Measure.pi_Ioo_ae_eq_pi_Icc
    refine ⟨U, C, hU.isElementary, hC.isElementary, ?_, ?_, hUA, hAC, ?_, ?_⟩
    · exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo
    · exact isClosed_set_pi fun _ _ => isClosed_Icc
    · filter_upwards [hae] with x hx
      exact propext ⟨fun h => hUA h, fun h => (congrArg (fun P : Prop => P) hx).mpr (hAC h)⟩
    · filter_upwards [hae] with x hx
      exact propext ⟨fun h => hAC h, fun h => hUA (hx.mpr h)⟩
  obtain ⟨I, hI, rfl⟩ := hA
  induction I using Finset.induction with
  | empty =>
    refine ⟨∅, ∅, isElementary_empty p, isElementary_empty p, isOpen_empty,
      isClosed_empty, ?_, ?_, ?_, ?_⟩ <;> simp
  | @insert B I hBI ih =>
    obtain ⟨U, C, hU, hC, hUo, hCc, hUB, hBC, hUae, hCae⟩ := hi B (hI B (by simp))
    obtain ⟨V, D, hV, hD, hVo, hDc, hVI, hID, hVae, hDae⟩ :=
      ih (fun s hs => hI s (Finset.mem_insert_of_mem hs))
    have heq : Set.sUnion (↑(insert B I) : Set (Set (Fin p → ℝ))) =
        B ∪ Set.sUnion (↑I : Set (Set (Fin p → ℝ))) := by simp
    rw [heq]
    exact ⟨U ∪ V, C ∪ D, hU.union hV, hC.union hD, hUo.union hVo, hCc.union hDc,
      union_subset_union hUB hVI, union_subset_union hBC hID, hUae.union hVae, hCae.union hDae⟩

/-- 11.6(a): volume is regular, with the closed and open approximants themselves
elementary, exactly as required by 11.5. -/
theorem pma11_6a {p : ℕ} {A : Set (Fin p → ℝ)} (hA : IsElementary A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F G, IsElementary F ∧ IsElementary G ∧ IsClosed F ∧ IsOpen G ∧
      F ⊆ A ∧ A ⊆ G ∧ volume G < volume A + ε ∧ volume A < volume F + ε := by
  obtain ⟨U, C, hU, hC, hUo, hCc, hUA, hAC, hUae, hCae⟩ := hA.open_closed_envelopes
  obtain ⟨K, hKU, hK, hμK⟩ := hU.measurableSet.exists_isCompact_lt_add
    hU.volume_ne_top hε.ne'
  obtain ⟨F, V, hF, _, hFc, _, hKV, hVF, hFU⟩ := compact_elementary_sandwich hK hUo hKU
  obtain ⟨O, hCO, hOo, hμO⟩ := C.exists_isOpen_lt_add hC.volume_ne_top hε.ne'
  obtain ⟨D, G, _, hG, _, hGo, hCG, hGD, hDO⟩ :=
    compact_elementary_sandwich (hC.isCompact_of_isClosed hCc) hOo hCO
  refine ⟨F, G, hF, hG, hFc, hGo, hFU.trans hUA, hAC.trans hCG, ?_, ?_⟩
  · calc volume G ≤ volume O := measure_mono (hGD.trans hDO)
      _ < volume C + ε := hμO
      _ = volume A + ε := by rw [measure_congr hCae]
  · calc volume A = volume U := (measure_congr hUae).symm
      _ < volume K + ε := hμK
      _ ≤ volume F + ε := add_le_add (measure_mono (hKV.trans hVF)) le_rfl

/-- 11.6(b): the Stieltjes measure associated to an arbitrary monotone function. -/
def stieltjesMeasure (α : ℝ → ℝ) (hα : Monotone α) : Measure ℝ :=
  hα.stieltjesFunction.measure

private lemma stieltjes_leftLim {α : ℝ → ℝ} (hα : Monotone α) (a : ℝ) :
    leftLim hα.stieltjesFunction a = leftLim α a :=
  leftLim_rightLim (hα.tendsto_leftLim a)

/-- 11.6(b): all four endpoint formulas, in nonnegative extended reals.
Repair of the degenerate open-interval case: `ofReal` truncates negative
values to zero, so `(a,a)` remains empty even when `α` has a jump at `a`.
The source's untruncated open formula requires `a < b`. -/
theorem pma11_6b_interval_formulas {α : ℝ → ℝ} (hα : Monotone α) (a b : ℝ) :
    stieltjesMeasure α hα (Ico a b) = ENNReal.ofReal (leftLim α b - leftLim α a) ∧
    stieltjesMeasure α hα (Icc a b) = ENNReal.ofReal (rightLim α b - leftLim α a) ∧
    stieltjesMeasure α hα (Ioc a b) = ENNReal.ofReal (rightLim α b - rightLim α a) ∧
    stieltjesMeasure α hα (Ioo a b) = ENNReal.ofReal (leftLim α b - rightLim α a) := by
  dsimp [stieltjesMeasure]
  simp only [StieltjesFunction.measure_Ico, StieltjesFunction.measure_Icc,
    StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioo,
    stieltjes_leftLim hα, Monotone.stieltjesFunction_eq]
  trivial

end Rudin.PMA.Chapter11
