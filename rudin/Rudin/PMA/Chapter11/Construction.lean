import Mathlib
import Rudin.PMA.Chapter11.Foundations

noncomputable section
open Set Filter Topology MeasureTheory Function
open scoped ENNReal NNReal BigOperators symmDiff

namespace Rudin.PMA.Chapter11

/-! The construction is proved for a ring `C` whose closed members are compact.
For Rudin's elementary subsets of Euclidean space this is precisely the geometric
input to the compact-subcover argument. No countably additive measure is assumed. -/

/-- 11.5: regularity of a finite nonnegative additive set function on `C`.
The inequalities are written without subtraction in the nonnegative extended reals. -/
def ContentRegular {X : Type*} [TopologicalSpace X] {C : Set (Set X)}
    (μ : AddContent ℝ≥0∞ C) : Prop :=
  ∀ A ∈ C, ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ F ∈ C, ∃ G ∈ C, IsClosed F ∧ IsOpen G ∧ F ⊆ A ∧ A ⊆ G ∧
      μ G < μ A + ε ∧ μ A < μ F + ε

/-- The hypotheses in 11.7, together with the geometric ring and compactness
properties of the elementary sets used in the proof. -/
structure RegularContent (X : Type*) [TopologicalSpace X] (C : Set (Set X)) where
  content : AddContent ℝ≥0∞ C
  ring : IsSetRing C
  finite : ∀ A ∈ C, content A ≠ ∞
  regular : ContentRegular content
  compact : ∀ A ∈ C, IsClosed A → IsCompact A

namespace RegularContent
variable {X : Type*} [TopologicalSpace X] {C : Set (Set X)} (μ : RegularContent X C)

/-- 11.7: the outer measure obtained from countable open elementary covers. -/
def outer : OuterMeasure X :=
  inducedOuterMeasure (P := fun A => A ∈ C ∧ IsOpen A) (fun A _ => μ.content A)
    ⟨μ.ring.empty_mem, isOpen_empty⟩ (by simp)

/-- The countable-cover infimum in (17), with no change of covering class. -/
theorem outer_eq_iInf (A : Set X) :
    μ.outer A = ⨅ (G : ℕ → Set X) (_ : ∀ n, G n ∈ C ∧ IsOpen (G n))
      (_ : A ⊆ ⋃ n, G n), ∑' n, μ.content (G n) := by
  unfold outer inducedOuterMeasure
  rw [OuterMeasure.ofFunction_eq_iInf_mem (P := fun A => A ∈ C ∧ IsOpen A)
    _ _ (fun s h => extend_eq_top (fun A (_ : A ∈ C ∧ IsOpen A) => μ.content A) h)]
  refine iInf_congr fun G => iInf_congr fun hG => iInf_congr fun _ => ?_
  exact tsum_congr fun n =>
    extend_eq (fun A (_ : A ∈ C ∧ IsOpen A) => μ.content A) (hG n)

/-- 11.7, (18): monotonicity. -/
theorem outer_mono {A B : Set X} (h : A ⊆ B) : μ.outer A ≤ μ.outer B :=
  measure_mono h

/-- The easy half of 11.8(a), using outer regularity. -/
theorem outer_le_content {A : Set X} (hA : A ∈ C) : μ.outer A ≤ μ.content A := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨F, hF, G, hG, _, hGo, _, hAG, hμG, _⟩ :=
    μ.regular A hA ε (ENNReal.coe_pos.mpr hε)
  apply (measure_mono hAG).trans
  have hbound : μ.outer G ≤ μ.content G :=
    (le_inducedOuterMeasure (m := fun A (_ : A ∈ C ∧ IsOpen A) => μ.content A)
      (P0 := ⟨μ.ring.empty_mem, isOpen_empty⟩) (m0 := by simp)).mp le_rfl G ⟨hG, hGo⟩
  exact hbound.trans hμG.le

/-- A compact elementary set is controlled by every countable open elementary cover. -/
theorem content_le_cover {A : Set X} (hA : A ∈ C) (hAc : IsCompact A)
    (G : ℕ → Set X) (hG : ∀ n, G n ∈ C ∧ IsOpen (G n)) (hAG : A ⊆ ⋃ n, G n) :
    μ.content A ≤ ∑' n, μ.content (G n) := by
  classical
  obtain ⟨s, hs⟩ := hAc.elim_finite_subcover G (fun n => (hG n).2) hAG
  have hm := addContent_mono (m := μ.content) μ.ring.isSetSemiring hA
    (μ.ring.biUnion_mem s (fun n _ => (hG n).1)) hs
  exact hm.trans <| (addContent_biUnion_le μ.ring (fun n _ => (hG n).1)).trans
    (ENNReal.sum_le_tsum s)

/-- 11.8(a): the countable-cover construction extends the original content. -/
theorem outer_eq_content {A : Set X} (hA : A ∈ C) : μ.outer A = μ.content A := by
  apply le_antisymm (μ.outer_le_content hA)
  rw [μ.outer_eq_iInf]
  refine le_iInf fun G => le_iInf fun hG => le_iInf fun hAG => ?_
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨F, hF, U, hU, hFc, _, hFA, _, _, hμF⟩ :=
    μ.regular A hA ε (ENNReal.coe_pos.mpr hε)
  exact hμF.le.trans <| add_le_add
    (μ.content_le_cover hF (μ.compact F hF hFc) G hG (hFA.trans hAG)) le_rfl

/-- 11.8(b): countable subadditivity for arbitrary sets. -/
theorem outer_iUnion_le (A : ℕ → Set X) :
    μ.outer (⋃ n, A n) ≤ ∑' n, μ.outer (A n) := measure_iUnion_le A

/-- A useful equivalent construction, using all elementary covers. -/
def elementaryOuter : OuterMeasure X :=
  inducedOuterMeasure (fun A (_ : A ∈ C) => μ.content A) μ.ring.empty_mem (by simp)

/-- Regularity makes open elementary covers and arbitrary elementary covers equivalent. -/
theorem outer_eq_elementaryOuter : μ.outer = μ.elementaryOuter := by
  apply le_antisymm
  · exact le_inducedOuterMeasure.mpr fun A hA => μ.outer_le_content hA
  · apply le_inducedOuterMeasure.mpr
    intro A hA
    exact (le_inducedOuterMeasure (m := fun A (_ : A ∈ C) => μ.content A)
      (P0 := μ.ring.empty_mem) (m0 := by simp)).mp le_rfl A hA.1

/-- Every elementary set satisfies Carathéodory's criterion. -/
theorem elementary_caratheodory {A : Set X} (hA : A ∈ C) :
    MeasurableSet[μ.outer.caratheodory] A := by
  rw [μ.outer_eq_elementaryOuter]
  exact μ.content.isCaratheodory_inducedOuterMeasure_of_mem μ.ring.isSetSemiring hA

/-- Regular finite contents are countably subadditive on their original ring. -/
theorem sigmaSubadditive : μ.content.IsSigmaSubadditive := by
  intro A hA hU
  rw [← μ.outer_eq_content hU]
  simpa only [μ.outer_eq_content (hA _)] using μ.outer_iUnion_le A

/-- The measure produced by the construction, on its Carathéodory measurable space. -/
def extension : @Measure X μ.outer.caratheodory :=
  @OuterMeasure.toMeasure X μ.outer.caratheodory μ.outer le_rfl

/-- The extension agrees with the constructed outer measure on all sets. -/
theorem extension_apply (A : Set X) : μ.extension A = μ.outer A := by
  let : MeasurableSpace X := μ.outer.caratheodory
  apply le_antisymm
  · change μ.outer.trim A ≤ μ.outer A
    have h : μ.outer.trim ≤ μ.elementaryOuter := le_inducedOuterMeasure.mpr fun B hB => by
      rw [OuterMeasure.trim_eq _ (μ.elementary_caratheodory hB), μ.outer_eq_content hB]
    exact (h A).trans_eq (congrArg (fun m : OuterMeasure X => m A) μ.outer_eq_elementaryOuter.symm)
  · exact le_toMeasure_apply _ _ A

/-- 11.11(b), outer regularity: unions of the defining open covers approximate every set. -/
instance outerRegular_extension : @Measure.OuterRegular X μ.outer.caratheodory _ μ.extension := by
  let : MeasurableSpace X := μ.outer.caratheodory
  constructor
  · intro A _ r hr
    rw [μ.extension_apply, μ.outer_eq_iInf] at hr
    obtain ⟨G, hr⟩ := iInf_lt_iff.mp hr
    obtain ⟨hG, hr⟩ := iInf_lt_iff.mp hr
    obtain ⟨hAG, hsum⟩ := iInf_lt_iff.mp hr
    refine ⟨⋃ n, G n, hAG, isOpen_iUnion (fun n => (hG n).2), ?_⟩
    rw [μ.extension_apply]
    exact (μ.outer_iUnion_le G).trans_lt (by simpa only [μ.outer_eq_content (hG _).1] using hsum)

/-- 11.9, (22)–(23): symmetric-difference distance, allowed to be infinite. -/
def setDistance (A B : Set X) : ℝ≥0∞ := μ.outer (A ∆ B)

/-- 11.9: convergence in symmetric-difference outer measure. -/
def SetConverges (A : ℕ → Set X) (B : Set X) : Prop :=
  Tendsto (fun n => μ.setDistance B (A n)) atTop (𝓝 0)

/-- 11.9: Rudin's definition by elementary approximations. -/
def FinitelyMeasurable (A : Set X) : Prop :=
  ∃ E : ℕ → Set X, (∀ n, E n ∈ C) ∧ μ.SetConverges E A

/-- 11.9: countable unions of finitely measurable sets. -/
def RudinMeasurable (A : Set X) : Prop :=
  ∃ E : ℕ → Set X, (∀ n, μ.FinitelyMeasurable (E n)) ∧ A = ⋃ n, E n

/-- 11.10, (27). -/
theorem setDistance_comm (A B : Set X) : μ.setDistance A B = μ.setDistance B A := by
  simp only [setDistance, symmDiff_comm]

@[simp] theorem setDistance_self (A : Set X) : μ.setDistance A A = 0 := by
  simp [setDistance]

/-- 11.10, (28). -/
theorem setDistance_triangle (A B D : Set X) :
    μ.setDistance A D ≤ μ.setDistance A B + μ.setDistance B D := by
  let : MeasurableSpace X := μ.outer.caratheodory
  simpa only [setDistance, μ.extension_apply] using
    measure_symmDiff_le (μ := μ.extension) A B D

/-- 11.10, (30), in a subtraction-free form also valid at infinite values. -/
theorem outer_le_outer_add_distance (A B : Set X) :
    μ.outer A ≤ μ.outer B + μ.setDistance A B := by
  have h : A ⊆ B ∪ (A ∆ B) := by intro x hx; by_cases hB : x ∈ B <;> simp [*, mem_symmDiff]
  exact (measure_mono h).trans (measure_union_le _ _)

/-- 11.10, (29), union case. -/
theorem setDistance_union (A B D E : Set X) :
    μ.setDistance (A ∪ B) (D ∪ E) ≤ μ.setDistance A D + μ.setDistance B E :=
  (measure_mono union_symmDiff_union_subset).trans (measure_union_le _ _)

/-- 11.10, (29), intersection case. -/
theorem setDistance_inter (A B D E : Set X) :
    μ.setDistance (A ∩ B) (D ∩ E) ≤ μ.setDistance A D + μ.setDistance B E := by
  apply (measure_mono (show (A ∩ B) ∆ (D ∩ E) ⊆ (A ∆ D) ∪ (B ∆ E) by
    intro x; simp only [mem_symmDiff, mem_inter_iff, mem_union]; tauto)).trans
    (measure_union_le _ _)

/-- 11.10, (29), difference case. -/
theorem setDistance_diff (A B D E : Set X) :
    μ.setDistance (A \ B) (D \ E) ≤ μ.setDistance A D + μ.setDistance B E := by
  apply (measure_mono (show (A \ B) ∆ (D \ E) ⊆ (A ∆ D) ∪ (B ∆ E) by
    intro x; simp only [mem_symmDiff, Set.mem_sdiff, mem_union]; tauto)).trans
    (measure_union_le _ _)

/-- 11.10, (31). -/
theorem SetConverges.union {A B : ℕ → Set X} {D E : Set X}
    (hA : μ.SetConverges A D) (hB : μ.SetConverges B E) :
    μ.SetConverges (fun n => A n ∪ B n) (D ∪ E) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hA.add hB) (fun _ => zero_le) (fun n => μ.setDistance_union _ _ _ _)

/-- 11.10, (32). -/
theorem SetConverges.inter {A B : ℕ → Set X} {D E : Set X}
    (hA : μ.SetConverges A D) (hB : μ.SetConverges B E) :
    μ.SetConverges (fun n => A n ∩ B n) (D ∩ E) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hA.add hB) (fun _ => zero_le) (fun n => μ.setDistance_inter _ _ _ _)

/-- 11.10, (33). -/
theorem SetConverges.diff {A B : ℕ → Set X} {D E : Set X}
    (hA : μ.SetConverges A D) (hB : μ.SetConverges B E) :
    μ.SetConverges (fun n => A n \ B n) (D \ E) := by
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using hA.add hB) (fun _ => zero_le) (fun n => μ.setDistance_diff _ _ _ _)

/-- The zero-distance relation in the discussion following (29) is an equivalence relation.
Correction to that discussion: on all subsets, `d` can be infinite, so the unrestricted
quotient has an extended metric. The finite-measure component has an ordinary metric. -/
def zeroDistanceSetoid : Setoid (Set X) where
  r A B := μ.setDistance A B = 0
  iseqv := ⟨fun A => μ.setDistance_self A,
    fun {A B} h => (μ.setDistance_comm B A).trans h,
    fun {A B D} h₁ h₂ => le_antisymm
      (by simpa only [h₁, h₂, add_zero] using μ.setDistance_triangle A B D) zero_le⟩

/-- Each elementary set is finitely measurable. -/
theorem finitelyMeasurable_of_mem {A : Set X} (hA : A ∈ C) : μ.FinitelyMeasurable A :=
  ⟨fun _ => A, fun _ => hA, by simp [SetConverges]⟩

/-- The Carathéodory condition is closed under convergence in symmetric-difference measure. -/
theorem caratheodory_of_setConverges {E : ℕ → Set X} {A : Set X}
    (hE : ∀ n, MeasurableSet[μ.outer.caratheodory] (E n)) (h : μ.SetConverges E A) :
    MeasurableSet[μ.outer.caratheodory] A := by
  apply (OuterMeasure.isCaratheodory_iff_le _).mpr
  intro T
  have hb (n : ℕ) : μ.outer (T ∩ A) + μ.outer (T \ A) ≤
      μ.outer T + (μ.setDistance A (E n) + μ.setDistance A (E n)) := by
    have hi : T ∩ A ⊆ (T ∩ E n) ∪ (A ∆ E n) := by
      intro x hx; by_cases he : x ∈ E n <;> simp_all [mem_symmDiff]
    have hd : T \ A ⊆ (T \ E n) ∪ (A ∆ E n) := by
      intro x hx; by_cases he : x ∈ E n <;> simp_all [mem_symmDiff]
    calc
      _ ≤ (μ.outer (T ∩ E n) + μ.setDistance A (E n)) +
          (μ.outer (T \ E n) + μ.setDistance A (E n)) :=
        add_le_add ((measure_mono hi).trans (measure_union_le _ _))
          ((measure_mono hd).trans (measure_union_le _ _))
      _ = μ.outer T + (μ.setDistance A (E n) + μ.setDistance A (E n)) := by
        rw [(OuterMeasure.isCaratheodory_iff _).mp (hE n) T]
        ac_rfl
  have hl : Tendsto (fun n => μ.outer T +
      (μ.setDistance A (E n) + μ.setDistance A (E n))) atTop (𝓝 (μ.outer T)) := by
    simpa using tendsto_const_nhds.add (h.add h)
  exact ge_of_tendsto hl (Eventually.of_forall hb)

/-- 11.10, (34): outer measure is continuous along measurable set approximations. -/
theorem SetConverges.measure {E : ℕ → Set X} {A : Set X}
    (h : μ.SetConverges E A) (hE : ∀ n, MeasurableSet[μ.outer.caratheodory] (E n)) :
    Tendsto (fun n => μ.outer (E n)) atTop (𝓝 (μ.outer A)) := by
  let : MeasurableSpace X := μ.outer.caratheodory
  let F (n : ℕ) : MeasuredSets μ.extension := ⟨E n, hE n⟩
  let B : MeasuredSets μ.extension := ⟨A, μ.caratheodory_of_setConverges hE h⟩
  have hf : Tendsto F atTop (𝓝 B) := by
    apply tendsto_iff_edist_tendsto_0.mpr
    change Tendsto (fun n => μ.extension (E n ∆ A)) atTop (𝓝 0)
    simpa only [SetConverges, μ.extension_apply, setDistance, symmDiff_comm] using h
  have hh := MeasuredSets.continuous_measure.continuousAt.tendsto.comp hf
  change Tendsto (fun n => μ.extension (E n)) atTop (𝓝 (μ.extension A)) at hh
  simpa only [μ.extension_apply] using hh

/-- Finitely measurable sets satisfy the Carathéodory condition. -/
theorem FinitelyMeasurable.caratheodory {A : Set X} (hA : μ.FinitelyMeasurable A) :
    MeasurableSet[μ.outer.caratheodory] A := by
  obtain ⟨E, hE, hlim⟩ := hA
  exact μ.caratheodory_of_setConverges (fun n => μ.elementary_caratheodory (hE n)) hlim

/-- Finitely measurable sets have finite outer measure. -/
theorem FinitelyMeasurable.finite {A : Set X} (hA : μ.FinitelyMeasurable A) : μ.outer A ≠ ∞ := by
  obtain ⟨E, hE, hlim⟩ := hA
  obtain ⟨n, hn⟩ := ((tendsto_order.mp hlim).2 1 zero_lt_one).exists
  apply ne_top_of_le_ne_top _ (μ.outer_le_outer_add_distance A (E n))
  exact ENNReal.add_ne_top.mpr ⟨by rw [μ.outer_eq_content (hE n)]; exact μ.finite _ (hE n),
    ne_top_of_lt hn⟩

/-- Rudin-measurable sets satisfy the Carathéodory condition. -/
theorem RudinMeasurable.caratheodory {A : Set X} (hA : μ.RudinMeasurable A) :
    MeasurableSet[μ.outer.caratheodory] A := by
  obtain ⟨E, hE, rfl⟩ := hA
  exact MeasurableSet.iUnion fun n => (hE n).caratheodory μ

/-- A finite Carathéodory set admits arbitrarily close elementary approximations.
This uses the defining open covers and their finite partial unions. -/
theorem exists_elementary_approx {A : Set X}
    (hA : MeasurableSet[μ.outer.caratheodory] A) (hfin : μ.outer A ≠ ∞)
    (ε : ℝ≥0) (hε : 0 < ε) : ∃ B ∈ C, μ.setDistance A B < ε := by
  let δ : ℝ≥0∞ := (ε : ℝ≥0∞) / 2
  have hδ : 0 < δ := ENNReal.half_pos (ENNReal.coe_pos.mpr hε).ne'
  have hlt : μ.outer A < μ.outer A + δ := ENNReal.lt_add_right hfin hδ.ne'
  conv_lhs at hlt => rw [μ.outer_eq_iInf]
  obtain ⟨G, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hG, hlt⟩ := iInf_lt_iff.mp hlt
  obtain ⟨hAG, hsum⟩ := iInf_lt_iff.mp hlt
  have hsumfin : (∑' n, μ.content (G n)) ≠ ∞ :=
    ne_top_of_lt hsum
  have hout : μ.outer ((⋃ n, G n) \ A) < δ := by
    apply (ENNReal.add_lt_add_iff_right hfin).mp
    have heq := (OuterMeasure.isCaratheodory_iff _).mp hA (⋃ n, G n)
    rw [inter_eq_right.mpr hAG] at heq
    calc
      μ.outer ((⋃ n, G n) \ A) + μ.outer A = μ.outer (⋃ n, G n) := by
        rw [heq, add_comm]
      _ ≤ ∑' n, μ.content (G n) := by
        simpa only [μ.outer_eq_content (hG _).1] using μ.outer_iUnion_le G
      _ < δ + μ.outer A := by simpa only [add_comm] using hsum
  obtain ⟨N, hN⟩ := ((tendsto_order.mp
    (ENNReal.tendsto_sum_nat_add (fun n => μ.content (G n)) hsumfin)).2 δ hδ).exists
  let B : Set X := ⋃ n ∈ Finset.range N, G n
  refine ⟨B, μ.ring.biUnion_mem _ (fun n _ => (hG n).1), ?_⟩
  have hB : B ⊆ ⋃ n, G n := by
    intro x hx
    obtain ⟨n, _, hxn⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨n, hxn⟩
  have hs : A ∆ B ⊆ ((⋃ n, G n) \ A) ∪ ⋃ k, G (k + N) := by
    intro x hx
    rcases mem_symmDiff.mp hx with h | h
    · obtain ⟨n, hn⟩ := mem_iUnion.mp (hAG h.1)
      have hnN : N ≤ n := by
        by_contra hnN
        have : x ∈ B := mem_iUnion₂.mpr ⟨n, Finset.mem_range.mpr (by omega), hn⟩
        exact h.2 this
      exact Or.inr (mem_iUnion.mpr ⟨n - N, by simpa [Nat.sub_add_cancel hnN] using hn⟩)
    · exact Or.inl ⟨hB h.1, h.2⟩
  calc
    μ.setDistance A B ≤ μ.outer ((⋃ n, G n) \ A) + μ.outer (⋃ k, G (k + N)) :=
      (measure_mono hs).trans (measure_union_le _ _)
    _ ≤ μ.outer ((⋃ n, G n) \ A) + ∑' k, μ.content (G (k + N)) := by
      gcongr
      simpa only [μ.outer_eq_content (hG _).1] using μ.outer_iUnion_le (fun k => G (k + N))
    _ < δ + δ := ENNReal.add_lt_add hout hN
    _ = (ε : ℝ≥0∞) := ENNReal.add_halves _

/-- 11.10: finite Carathéodory sets are finitely measurable in Rudin's sense. -/
theorem finitelyMeasurable_of_caratheodory {A : Set X}
    (hA : MeasurableSet[μ.outer.caratheodory] A) (hfin : μ.outer A ≠ ∞) :
    μ.FinitelyMeasurable A := by
  have hε (n : ℕ) : (0 : ℝ≥0) < ((n : ℝ≥0) + 1)⁻¹ := by positivity
  choose B hB hdist using fun n => μ.exists_elementary_approx hA hfin _ (hε n)
  refine ⟨B, hB, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n : ℕ => ((((n : ℝ≥0) + 1)⁻¹ : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) from ?_)
    (fun _ => zero_le) (fun n => (hdist n).le)
  convert ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1) using 1
  simp [ENNReal.coe_inv, ENNReal.coe_add, Function.comp_def]

/-- Finite measurability is exactly the finite-measure part of Carathéodory measurability. -/
theorem finitelyMeasurable_iff {A : Set X} : μ.FinitelyMeasurable A ↔
    MeasurableSet[μ.outer.caratheodory] A ∧ μ.outer A ≠ ∞ :=
  ⟨fun h => ⟨h.caratheodory μ, h.finite μ⟩,
    fun h => μ.finitelyMeasurable_of_caratheodory h.1 h.2⟩

/-- 11.10: the finitely measurable sets form a ring. -/
theorem finitelyMeasurable_ring : IsSetRing {A | μ.FinitelyMeasurable A} where
  empty_mem := μ.finitelyMeasurable_of_mem μ.ring.empty_mem
  union_mem := by
    intro A B hA hB
    apply μ.finitelyMeasurable_of_caratheodory ((hA.caratheodory μ).union (hB.caratheodory μ))
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hA.finite μ, hB.finite μ⟩)
      (measure_union_le _ _)
  sdiff_mem := by
    intro A B hA hB
    apply μ.finitelyMeasurable_of_caratheodory ((hA.caratheodory μ).diff (hB.caratheodory μ))
    exact ne_top_of_le_ne_top (hA.finite μ) (measure_mono sdiff_subset)

/-- Under an elementary exhaustion, Rudin's measurable sets coincide with the
Carathéodory measurable sets. Euclidean cubes provide this exhaustion. -/
theorem rudinMeasurable_iff (K : ℕ → Set X) (hK : ∀ n, K n ∈ C)
    (hKU : (⋃ n, K n) = univ) {A : Set X} : μ.RudinMeasurable A ↔
    MeasurableSet[μ.outer.caratheodory] A := by
  refine ⟨fun h => h.caratheodory μ, fun h => ?_⟩
  refine ⟨fun n => A ∩ K n, fun n => ?_, ?_⟩
  · apply μ.finitelyMeasurable_of_caratheodory (h.inter (μ.elementary_caratheodory (hK n)))
    apply ne_top_of_le_ne_top (b := μ.content (K n)) (μ.finite _ (hK n))
    rw [← μ.outer_eq_content (hK n)]
    exact measure_mono inter_subset_right
  · simp only [← inter_iUnion, hKU, inter_univ]

/-- Countable-union closure does not require an exhaustion. -/
theorem RudinMeasurable.iUnion {A : ℕ → Set X} (hA : ∀ n, μ.RudinMeasurable (A n)) :
    μ.RudinMeasurable (⋃ n, A n) := by
  choose E hE hAE using hA
  refine ⟨fun n => E n.unpair.1 n.unpair.2, fun n => hE _ _, ?_⟩
  simp only [hAE, iUnion_unpair]

/-- 11.10: difference closure. -/
theorem RudinMeasurable.diff {A B : Set X} (hA : μ.RudinMeasurable A)
    (hB : μ.RudinMeasurable B) : μ.RudinMeasurable (A \ B) := by
  obtain ⟨E, hE, rfl⟩ := hA
  refine ⟨fun n => E n \ B, fun n => ?_, iUnion_sdiff _ _⟩
  apply μ.finitelyMeasurable_of_caratheodory ((hE n).caratheodory μ |>.diff (hB.caratheodory μ))
  exact ne_top_of_le_ne_top ((hE n).finite μ) (measure_mono sdiff_subset)

/-- Finitely measurable sets are measurable under Definition 11.9. -/
theorem FinitelyMeasurable.rudinMeasurable {A : Set X} (hA : μ.FinitelyMeasurable A) :
    μ.RudinMeasurable A := ⟨fun (_ : ℕ) => A, fun _ => hA, by simp only [iUnion_const]⟩

/-- Binary unions in the measurable family. -/
theorem RudinMeasurable.union {A B : Set X} (hA : μ.RudinMeasurable A)
    (hB : μ.RudinMeasurable B) : μ.RudinMeasurable (A ∪ B) := by
  obtain ⟨E, hE, rfl⟩ := hA
  obtain ⟨F, hF, rfl⟩ := hB
  refine ⟨fun n => E n ∪ F n,
    fun n => μ.finitelyMeasurable_ring.union_mem (hE n) (hF n), ?_⟩
  exact (iUnion_union_distrib E F).symm

/-- 11.10: the family defined by elementary approximation is a sigma-ring. -/
theorem rudinMeasurable_sigmaRing : SigmaRing {A | μ.RudinMeasurable A} where
  union_mem := fun {_A _B} hA hB => RudinMeasurable.union μ hA hB
  sdiff_mem := fun {_A _B} hA hB => RudinMeasurable.diff μ hA hB
  iUnion_mem := fun _ hA => RudinMeasurable.iUnion μ hA

/-- 11.10: countable additivity on precisely the sets defined in 11.9. -/
theorem rudinMeasurable_iUnion_measure (A : ℕ → Set X)
    (hA : ∀ n, μ.RudinMeasurable (A n)) (hd : Pairwise (Disjoint on A)) :
    μ.outer (⋃ n, A n) = ∑' n, μ.outer (A n) :=
  μ.outer.iUnion_eq_of_caratheodory (fun n => (hA n).caratheodory μ) hd

end RegularContent
end Rudin.PMA.Chapter11
