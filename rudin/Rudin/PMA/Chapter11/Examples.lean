import Rudin.PMA.Chapter11.Euclidean
import Rudin.PMA.Chapter11.GeometryApproximation
import Rudin.PMA.Chapter11.StieltjesExample

/-!
# PMA 11.6 examples as inputs to the construction in 11.7

The examples are packaged as `RegularContent`. The native measure used to verify
the example is then identified on every set with the outer measure constructed
from the original countable open elementary covers. Thus later native-measure
statements can be transported back to Rudin's construction.
-/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Rudin.PMA.Chapter11

/-- A measure restricted to elementary sets is a finitely additive content. -/
def elementaryMeasureContent {p : ℕ} (ν : Measure (Fin p → ℝ)) :
    AddContent ℝ≥0∞ {A : Set (Fin p → ℝ) | IsElementary A} where
  toFun := ν
  empty' := measure_empty
  sUnion' I hI hd _ := by
    simpa only [Set.sUnion_eq_biUnion, Finset.mem_coe, id_eq] using
      measure_biUnion_finset hd (fun s hs => (hI hs).measurableSet)

/-- 11.6(a) supplies a regular content to the construction of 11.7. -/
def volumeRegularContent (p : ℕ) : RegularContent (Fin p → ℝ) {A | IsElementary A} where
  content := elementaryMeasureContent volume
  ring := isSetRing_isElementary p
  finite := fun _ hA => hA.volume_ne_top
  compact := fun _ hA hc => hA.isCompact_of_isClosed hc
  regular := by
    intro A hA ε hε
    obtain ⟨F, G, hF, hG, hc, ho, hFA, hAG, hGv, hFv⟩ := pma11_6a hA hε
    exact ⟨F, hF, G, hG, hc, ho, hFA, hAG, hGv, hFv⟩

/-- Generality: every locally finite Borel measure gives a regular elementary
content. This is used only to verify the examples; the extension theorem itself
starts from finite additivity, independently of this construction. -/
def measureRegularContent {p : ℕ} (ν : Measure (Fin p → ℝ)) [IsLocallyFiniteMeasure ν] :
    RegularContent (Fin p → ℝ) {A | IsElementary A} where
  content := elementaryMeasureContent ν
  ring := isSetRing_isElementary p
  finite := fun _ hA => hA.isBounded.measure_lt_top.ne
  compact := fun _ hA hc => hA.isCompact_of_isClosed hc
  regular := by
    intro A hA ε hε
    obtain ⟨F, G, hF, hG, hc, ho, hFA, hAG, hGv, hFv⟩ :=
      elementary_measure_regular ν hA hε
    exact ⟨F, hF, G, hG, hc, ho, hFA, hAG, hGv, hFv⟩

/-- 11.6(b): the Stieltjes example as a regular content on elementary subsets
of the real line, represented by the equivalent space `Fin 1 → ℝ`. -/
def stieltjesRegularContent (α : ℝ → ℝ) (hα : Monotone α) :
    RegularContent (Fin 1 → ℝ) {A | IsElementary A} :=
  measureRegularContent (stieltjesEuclideanMeasure α hα)

/-- 11.6(b): the asserted regularity, including elementary approximants and
possible positive mass at the endpoints. -/
theorem pma11_6b_regular {α : ℝ → ℝ} (hα : Monotone α)
    {A : Set (Fin 1 → ℝ)} (hA : IsElementary A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F G, IsElementary F ∧ IsElementary G ∧ IsClosed F ∧ IsOpen G ∧
      F ⊆ A ∧ A ⊆ G ∧ stieltjesEuclideanMeasure α hα G <
        stieltjesEuclideanMeasure α hα A + ε ∧
      stieltjesEuclideanMeasure α hα A < stieltjesEuclideanMeasure α hα F + ε :=
  elementary_measure_regular (stieltjesEuclideanMeasure α hα) hA hε

namespace RegularContent

variable {p : ℕ} (μ : RegularContent (Fin p → ℝ) {A | IsElementary A})
    (ν : Measure (Fin p → ℝ))
    (heq : ∀ A, IsElementary A → μ.content A = ν A)

include heq

/-- Agreement on elementary sets propagates to open sets by increasing finite
unions from a countable elementary basis cover. -/
theorem outer_eq_measure_of_isOpen {U : Set (Fin p → ℝ)} (hU : IsOpen U) :
    μ.outer U = ν U := by
  classical
  obtain ⟨S, hS, hc, hUS⟩ :=
    (isTopologicalBasis_openElementary p).exists_countable_biUnion_of_isOpen hU
  rcases S.eq_empty_or_nonempty with hSE | hSne
  · simp only [hSE, mem_empty_iff_false, iUnion_of_empty, iUnion_empty] at hUS
    rw [hUS]
    simp
  obtain ⟨f, hf⟩ := hc.exists_eq_range hSne
  have hfc : ∀ n, IsElementary (f n) := fun n =>
    (hS (hf ▸ mem_range_self n)).1
  have hUf : U = ⋃ n, f n := by
    rw [hUS, hf]
    simp
  have hac : ∀ n, IsElementary (accumulate f n) :=
    fun n => (isSetRing_isElementary p).accumulate_mem hfc n
  have hh (n : ℕ) : μ.extension (accumulate f n) = ν (accumulate f n) := by
    rw [μ.extension_apply, μ.outer_eq_content (hac n), heq _ (hac n)]
  have hm : Monotone (accumulate f) := monotone_accumulate
  calc μ.outer U
      = μ.extension (⋃ n, accumulate f n) := by rw [iUnion_accumulate, ← hUf, μ.extension_apply]
    _ = ⨆ n, μ.extension (accumulate f n) := hm.measure_iUnion
    _ = ⨆ n, ν (accumulate f n) := iSup_congr hh
    _ = ν (⋃ n, accumulate f n) := hm.measure_iUnion.symm
    _ = ν U := by rw [iUnion_accumulate, ← hUf]

/-- The constructed outer measure dominates the native measure, directly from
countable subadditivity for every defining elementary cover. -/
theorem measure_le_outer (A : Set (Fin p → ℝ)) : ν A ≤ μ.outer A := by
  rw [μ.outer_eq_iInf]
  refine le_iInf fun G => le_iInf fun hG => le_iInf fun hAG => ?_
  calc ν A ≤ ν (⋃ n, G n) := measure_mono hAG
    _ ≤ ∑' n, ν (G n) := measure_iUnion_le G
    _ = ∑' n, μ.content (G n) := tsum_congr fun n => (heq _ (hG n).1).symm

/-- Identification on all sets, including nonmeasurable sets, of the construction
from an outer regular native measure with that measure's outer values. -/
theorem outer_eq_measure [ν.OuterRegular] (A : Set (Fin p → ℝ)) : μ.outer A = ν A := by
  apply le_antisymm _ (μ.measure_le_outer ν heq A)
  by_cases htop : ν A = ∞
  · simp [htop]
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨U, hAU, hUo, hUν⟩ := A.exists_isOpen_lt_add (μ := ν) htop
    (ENNReal.coe_pos.mpr hε).ne'
  exact (μ.outer_mono hAU).trans <|
    (μ.outer_eq_measure_of_isOpen ν heq hUo).le.trans hUν.le

end RegularContent

/-- The Lebesgue outer measure constructed in 11.7 agrees on every set with
mathlib's Lebesgue outer values, not only on Borel sets. -/
theorem volumeRegularContent_outer (p : ℕ) (A : Set (Fin p → ℝ)) :
    (volumeRegularContent p).outer A = volume A :=
  (volumeRegularContent p).outer_eq_measure volume (fun _ _ => rfl) A

/-- The Stieltjes outer measure from 11.7 agrees on every set with the native
Stieltjes measure's outer values under the one-dimensional coordinate identification. -/
theorem stieltjesRegularContent_outer {α : ℝ → ℝ} (hα : Monotone α)
    (A : Set (Fin 1 → ℝ)) :
    (stieltjesRegularContent α hα).outer A = stieltjesEuclideanMeasure α hα A :=
  (stieltjesRegularContent α hα).outer_eq_measure (stieltjesEuclideanMeasure α hα)
    (fun _ _ => rfl) A

end Rudin.PMA.Chapter11
