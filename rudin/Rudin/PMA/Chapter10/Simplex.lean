import Rudin.PMA.Chapter10.SimplexSlices

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

open Chapter06

theorem stoppedSlice_setIntegral {g : ℝ → ℝ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ t in Icc (0 : ℝ) 1, stoppedSlice g c t) = ∫ t in 0..c, g t := by
  have he : stoppedSlice g c = (Iic c).indicator g := by
    funext t
    rfl
  have hs : Icc (0 : ℝ) 1 ∩ Iic c = Icc 0 c := by
    ext t
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · intro ht
      exact ⟨⟨ht.1, ht.2.trans hc1⟩, ht.2⟩
  rw [he, setIntegral_indicator measurableSet_Iic, hs,
    intervalIntegral.integral_of_le hc0, integral_Icc_eq_integral_Ioc]

theorem simplex_slice_eq_setIntegral {n : ℕ} {f : Coord (n + 1) → ℝ}
    (hf : ContinuousOn f (standardSimplex (n + 1)))
    {x : Coord n} (hx : x ∈ (Cell.unit n).carrier) :
    nativeSliceIntegral (Cell.unit (n + 1)) (simplexExtension f) x =
      ∫ t in Icc (0 : ℝ) 1, simplexExtension f (Fin.snoc x t) := by
  obtain ⟨g, hg, he⟩ := exists_continuous_extension (isClosed_standardSimplex (n + 1)) hf
  rw [(simplex_slice_integrable_formula hg he hx).2]
  have hx0 : ∀ i, 0 ≤ x i := fun i => (Cell.mem_carrier.mp hx i).1
  have hs0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx0 i)
  by_cases hsum : (∑ i, x i) ≤ 1
  · have hc0 : 0 ≤ 1 - ∑ i, x i := sub_nonneg.mpr hsum
    have hc1 : 1 - (∑ i, x i) ≤ 1 := by linarith
    have heq : EqOn (fun t => simplexExtension f (Fin.snoc x t))
        (stoppedSlice (fun t => g (Fin.snoc x t)) (1 - ∑ i, x i)) (Icc 0 1) := by
      intro t ht
      by_cases htc : t ≤ 1 - ∑ i, x i
      · have hm : Fin.snoc x t ∈ standardSimplex (n + 1) :=
          mem_standardSimplex_snoc.mpr ⟨hx0, ht.1, by linarith⟩
        simp only [simplexExtension, Set.indicator_of_mem hm, stoppedSlice, if_pos htc, he hm]
      · have hm : Fin.snoc x t ∉ standardSimplex (n + 1) := by
          intro hm
          exact htc (by linarith [(mem_standardSimplex_snoc.mp hm).2.2])
        simp only [simplexExtension, Set.indicator_of_notMem hm, stoppedSlice, if_neg htc]
    rw [setIntegral_congr_fun measurableSet_Icc heq, stoppedSlice_setIntegral hc0 hc1]
    simp only [simplexSliceFormula, max_eq_right hc0]
  · have heq : EqOn (fun t => simplexExtension f (Fin.snoc x t)) (fun _ => 0) (Icc 0 1) := by
      intro t ht
      have hm : Fin.snoc x t ∉ standardSimplex (n + 1) := by
        intro hm
        exact hsum (by linarith [(mem_standardSimplex_snoc.mp hm).2.2, ht.1])
      exact Set.indicator_of_notMem hm f
    rw [setIntegral_congr_fun measurableSet_Icc heq]
    have hc : 1 - (∑ i, x i) ≤ 0 := by linarith [lt_of_not_ge hsum]
    simp only [simplexSliceFormula, max_eq_left hc, intervalIntegral.integral_same, integral_zero]

theorem simplexRIntegral_eq_cubeIntegral {n : ℕ} {f : Coord n → ℝ}
    (hf : ContinuousOn f (standardSimplex n)) :
    simplexRIntegral f = ∫ x in (Cell.unit n).carrier, simplexExtension f x := by
  cases n with
  | zero =>
      have hs : (Cell.unit 0).carrier.Subsingleton := fun _ _ _ _ => Subsingleton.elim _ _
      exact iteratedRIntegral_eq_setIntegral (hs.continuousOn _)
  | succ n =>
      have hi : Integrable (simplexExtension f) :=
        (hf.integrableOn_compact (isCompact_standardSimplex (n + 1))).integrable_indicator
          (isClosed_standardSimplex (n + 1)).measurableSet
      change iteratedRIntegral (Cell.unit n)
        (nativeSliceIntegral (Cell.unit (n + 1)) (simplexExtension f)) = _
      rw [iteratedRIntegral_eq_setIntegral (simplex_nativeSlice_continuousOn hf)]
      change _ = ∫ x, simplexExtension f x ∂(Cell.unit (n + 1)).measure
      rw [integral_cell_snoc _ _ hi.restrict]
      apply setIntegral_congr_fun (Cell.unit n).isClosed_carrier.measurableSet
      intro x hx
      exact simplex_slice_eq_setIntegral hf hx

theorem simplexRIntegral_eq_integral {n : ℕ} {f : Coord n → ℝ}
    (hf : ContinuousOn f (standardSimplex n)) :
    simplexRIntegral f = ∫ x in standardSimplex n, f x := by
  rw [simplexRIntegral_eq_cubeIntegral hf]
  change (∫ x in (Cell.unit n).carrier, (standardSimplex n).indicator f x) = _
  rw [setIntegral_indicator (isClosed_standardSimplex n).measurableSet,
    inter_eq_right.mpr (standardSimplex_subset_unit n)]

theorem mem_standardSimplex_unpermute {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Coord n) :
    unpermute σ x ∈ standardSimplex n ↔ x ∈ standardSimplex n := by
  have hs : (∑ i, unpermute σ x i) = ∑ i, x i := σ.symm.sum_comp x
  constructor
  · intro hx
    refine ⟨fun i => ?_, ?_⟩
    · simpa only [unpermute, Equiv.symm_apply_apply] using hx.1 (σ i)
    · simpa only [hs] using hx.2
  · intro hx
    exact ⟨fun i => hx.1 (σ.symm i), by simpa only [hs] using hx.2⟩

theorem simplexExtension_unpermute {n : ℕ} (σ : Equiv.Perm (Fin n)) (f : Coord n → ℝ) :
    (fun x => simplexExtension f (unpermute σ x)) =
      simplexExtension (fun x => f (unpermute σ x)) := by
  funext x
  by_cases hx : x ∈ standardSimplex n
  · simp only [simplexExtension, Set.indicator_of_mem hx,
      Set.indicator_of_mem ((mem_standardSimplex_unpermute σ x).mpr hx)]
  · simp only [simplexExtension, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem (fun h => hx ((mem_standardSimplex_unpermute σ x).mp h))]

theorem pma10_4 : pma10_4_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro n f hf
    exact ⟨simplex_iteratedRIntegrable hf,
      hf.integrableOn_compact (isCompact_standardSimplex n), simplexRIntegral_eq_integral hf⟩
  · intro n f hf
    exact simplex_nativeSlice_continuousOn hf
  · intro n f hf σ
    have hc : ContinuousOn (fun x => f (unpermute σ x)) (standardSimplex n) :=
      hf.comp (continuous_unpermute σ).continuousOn
        (fun x hx => (mem_standardSimplex_unpermute σ x).mpr hx)
    rw [simplexExtension_unpermute]
    refine ⟨simplex_iteratedRIntegrable hc, ?_⟩
    change simplexRIntegral (fun x => f (unpermute σ x)) = simplexRIntegral f
    rw [simplexRIntegral_eq_cubeIntegral hc, simplexRIntegral_eq_cubeIntegral hf,
      ← simplexExtension_unpermute]
    exact integral_cell_permute (Cell.unit n) σ (simplexExtension f)

end Rudin.PMA.Chapter10
