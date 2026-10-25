import Rudin.PMA.Chapter11.Construction

noncomputable section
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped ENNReal

namespace Rudin.PMA.Chapter11
namespace RegularContent

variable {X : Type*} [TopologicalSpace X] {C : Set (Set X)} (μ : RegularContent X C)

/-- 11.11(b), outer approximation, including measurable sets of infinite measure.
The finite pieces in Rudin's definition allow a summable error budget. -/
theorem exists_open_sdiff_lt {A : Set X} (hA : μ.RudinMeasurable A)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ G, A ⊆ G ∧ IsOpen G ∧ μ.outer (G \ A) < ε := by
  let : MeasurableSpace X := μ.outer.caratheodory
  let : μ.extension.OuterRegular := μ.outerRegular_extension
  obtain ⟨E, hE, rfl⟩ := hA
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  have happrox : ∀ n, ∃ G, E n ⊆ G ∧ IsOpen G ∧ μ.outer (G \ E n) < δ n := by
    intro n
    obtain ⟨G, hEG, hGo, _, hdiff⟩ :=
      ((hE n).caratheodory μ).exists_isOpen_sdiff_lt (μ := μ.extension)
        (by simpa only [μ.extension_apply] using (hE n).finite μ) (hδ n).ne'
    exact ⟨G, hEG, hGo, by simpa only [μ.extension_apply] using hdiff⟩
  choose G hEG hGo hdiff using happrox
  refine ⟨⋃ n, G n, iUnion_mono hEG, isOpen_iUnion hGo, ?_⟩
  have hsub : (⋃ n, G n) \ (⋃ n, E n) ⊆ ⋃ n, (G n \ E n) := by
    rintro x ⟨hx, hn⟩
    obtain ⟨n, hxn⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨n, hxn, fun h => hn (mem_iUnion.mpr ⟨n, h⟩)⟩
  exact ((measure_mono hsub).trans (measure_iUnion_le _)).trans_lt
    ((ENNReal.tsum_le_tsum fun n => (hdiff n).le).trans_lt hsum)

/-- 11.11(b): closed inner and open outer approximation with both difference
measures small. The elementary exhaustion is explicit and exists in Euclidean space. -/
theorem pma11_11b (K : ℕ → Set X) (hK : ∀ n, K n ∈ C) (hKU : (⋃ n, K n) = univ)
    {A : Set X} (hA : μ.RudinMeasurable A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F G, F ⊆ A ∧ A ⊆ G ∧ IsClosed F ∧ IsOpen G ∧
      μ.outer (G \ A) < ε ∧ μ.outer (A \ F) < ε := by
  have hAc : μ.RudinMeasurable Aᶜ :=
    (μ.rudinMeasurable_iff K hK hKU).mpr (hA.caratheodory μ).compl
  obtain ⟨G, hAG, hGo, hGA⟩ := μ.exists_open_sdiff_lt hA hε
  obtain ⟨U, hAcU, hUo, hUAc⟩ := μ.exists_open_sdiff_lt hAc hε
  refine ⟨Uᶜ, G, ?_, hAG, hUo.isClosed_compl, hGo, hGA, ?_⟩
  · exact compl_subset_comm.mp hAcU
  · have heq : A \ Uᶜ = U \ Aᶜ := by ext x; simp only [Set.mem_sdiff, mem_compl_iff, not_not]; tauto
    simpa only [heq] using hUAc

/-- 11.11(d): Borel inner and outer envelopes, modulo null sets. -/
theorem pma11_11d (K : ℕ → Set X) (hK : ∀ n, K n ∈ C) (hKU : (⋃ n, K n) = univ)
    {A : Set X} (hA : μ.RudinMeasurable A) :
    ∃ F G, F ⊆ A ∧ A ⊆ G ∧ MeasurableSet[borel X] F ∧ MeasurableSet[borel X] G ∧
      μ.outer (G \ A) = 0 ∧ μ.outer (A \ F) = 0 := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let ε : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def, ε] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose F G hFA hAG hFc hGo hGA hAF using fun n => μ.pma11_11b K hK hKU hA (hε n)
  refine ⟨⋃ n, F n, ⋂ n, G n, iUnion_subset hFA, subset_iInter hAG, ?_, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun n => (hFc n).measurableSet
  · exact MeasurableSet.iInter fun n => (hGo n).measurableSet
  · apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun n =>
      (measure_mono (sdiff_subset_sdiff_left (iInter_subset G n))).trans (hGA n).le
  · apply le_antisymm _ bot_le
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun n =>
      (measure_mono (sdiff_subset_sdiff_right (subset_iUnion F n))).trans (hAF n).le

/-- The decomposition following (40): a Borel set together with a null remainder. -/
theorem pma11_11d_decomposition (K : ℕ → Set X) (hK : ∀ n, K n ∈ C)
    (hKU : (⋃ n, K n) = univ) {A : Set X} (hA : μ.RudinMeasurable A) :
    ∃ F N, MeasurableSet[borel X] F ∧ μ.outer N = 0 ∧ A = F ∪ N := by
  obtain ⟨F, G, hFA, _, hF, _, _, hnull⟩ := μ.pma11_11d K hK hKU hA
  refine ⟨F, A \ F, hF, hnull, ?_⟩
  ext x
  simp only [mem_union, Set.mem_sdiff]
  constructor
  · intro hx
    by_cases h : x ∈ F <;> aesop
  · rintro (hx | hx)
    · exact hFA hx
    · exact hx.1

end RegularContent

end Rudin.PMA.Chapter11
