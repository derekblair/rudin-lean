import Rudin.PMA.Chapter10.IntegrationMeasure

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

open Chapter06

theorem rIntegrable_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hg : RIntegrable g a b) (he : EqOn f g (Icc a b)) : RIntegrable f a b := by
  have hcell (P : Partition a b) (i : Fin P.n) : f '' P.cell i = g '' P.cell i :=
    Set.image_congr (fun x hx => he (P.cell_subset i hx))
  have hl : (lowerSum f id : Partition a b → ℝ) = lowerSum g id := by
    funext P
    simp only [lowerSum, cellLower, hcell]
  have hu : (upperSum f id : Partition a b → ℝ) = upperSum g id := by
    funext P
    simp only [upperSum, cellUpper, hcell]
  refine ⟨hg.1, ?_, hg.2.2.1, ?_⟩
  · obtain ⟨M, hM⟩ := hg.2.1
    exact ⟨M, fun x hx => by rw [he hx]; exact hM x hx⟩
  · simpa only [lowerIntegral, upperIntegral, hl, hu] using hg.2.2.2

/-- Native Riemann integration ignores endpoint values. The proof uses the native
indefinite integral and the mean value theorem, rather than assuming a measure bridge. -/
theorem rIntegral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : RIntegrable f a b) (hg : RIntegrable g a b)
    (hfc : ContinuousOn f (Ioo a b)) (hgc : ContinuousOn g (Ioo a b))
    (he : EqOn f g (Ioo a b)) : RIntegral f a b = RIntegral g a b := by
  rcases hab.eq_or_lt with rfl | hab
  · exact (calculus_singleton_integrals f id a).2.trans
      (calculus_singleton_integrals g id a).2.symm
  have hF := pma6_20 f a b hab hf
  have hG := pma6_20 g a b hab hg
  let H : ℝ → ℝ := fun x => RIntegral f a x - RIntegral g a x
  have hc : ContinuousOn H (Icc a b) := hF.1.sub hG.1
  have hd : ∀ x ∈ Ioo a b, HasDerivAt H 0 x := by
    intro x hx
    have hfd := (hF.2.2 x ⟨hx.1.le, hx.2.le⟩
      ((hfc x hx).continuousAt (isOpen_Ioo.mem_nhds hx)).continuousWithinAt).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
    have hgd := (hG.2.2 x ⟨hx.1.le, hx.2.le⟩
      ((hgc x hx).continuousAt (isOpen_Ioo.mem_nhds hx)).continuousWithinAt).hasDerivAt
        (Icc_mem_nhds hx.1 hx.2)
    simpa only [H, RIntegral, id, Pi.sub_apply, he hx, sub_self] using! hfd.sub hgd
  obtain ⟨x, hx, h⟩ := exists_hasDerivAt_eq_slope H (fun _ => 0) hab hc hd
  have hzero : H b - H a = 0 := (div_eq_zero_iff.mp h.symm).resolve_right (sub_ne_zero.mpr hab.ne')
  have ha : H a = 0 := by
    simp only [H, RIntegral, (calculus_singleton_integrals f id a).2,
      (calculus_singleton_integrals g id a).2, sub_self]
  exact sub_eq_zero.mp (by simpa only [ha, sub_zero, H] using hzero)

/-- One continuous slice stopped at a moving endpoint; its value at the cutoff is retained. -/
def stoppedSlice (g : ℝ → ℝ) (c : ℝ) : ℝ → ℝ := fun t => if t ≤ c then g t else 0

theorem stoppedSlice_integrable_and_value {g : ℝ → ℝ} (hg : Continuous g)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    RIntegrable (stoppedSlice g c) 0 1 ∧
      RIntegral (stoppedSlice g c) 0 1 = ∫ t in 0..c, g t := by
  have hleft_eq : EqOn (stoppedSlice g c) g (Icc 0 c) := by
    intro t ht
    simp only [stoppedSlice, ite_eq_left ht.2]
  have hleft_cont : ContinuousOn (stoppedSlice g c) (Icc 0 c) :=
    hg.continuousOn.congr hleft_eq
  have hleft : RIntegrable (stoppedSlice g c) 0 c :=
    pma6_8 _ id _ _ hc0 hleft_cont (monotone_id.monotoneOn _)
  have hright_eq : EqOn (stoppedSlice g c) (fun _ => 0) (Ioo c 1) := by
    intro t ht
    simp only [stoppedSlice, ite_eq_right (not_le.mpr ht.1)]
  have hright_cont : ContinuousOn (stoppedSlice g c) (Ioo c 1) :=
    continuousOn_const.congr hright_eq
  have hright : RIntegrable (stoppedSlice g c) c 1 := by
    rcases hc1.eq_or_lt with rfl | hc1
    · exact (calculus_singleton_integrals _ id 1).1
    · obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Icc c 1)).bddAbove_image hg.norm.continuousOn
      have hb : BoundedOn (stoppedSlice g c) c 1 := by
        refine ⟨max M 0, ?_⟩
        intro t ht
        dsimp [stoppedSlice]
        split_ifs
        · exact (hM ⟨t, ht, rfl⟩).trans (le_max_left _ _)
        · simpa only [abs_zero] using le_max_right M 0
      exact rsIntegrable_of_continuousOn_Ioo hc1 hb (monotone_id.monotoneOn _)
        hright_cont (Or.inr continuous_id.continuousWithinAt)
        (Or.inr continuous_id.continuousWithinAt)
  have hi := split_rsIntegrable_append hleft hright
  refine ⟨hi, ?_⟩
  have hz := rsIntegral_const (c := 0) hc1 (monotone_id.monotoneOn (Icc c 1))
  have hright_zero : RIntegral (stoppedSlice g c) c 1 = 0 := by
    calc
      _ = RIntegral (fun _ => 0) c 1 :=
        rIntegral_congr_Ioo hc1 hright hz.1 hright_cont continuousOn_const hright_eq
      _ = 0 := by simpa only [RIntegral, id_eq, zero_mul] using hz.2
  calc
    _ = RIntegral (stoppedSlice g c) 0 c + RIntegral (stoppedSlice g c) c 1 :=
      (split_ordered hc0 hc1 hi).2.2
    _ = RIntegral g 0 c := by
      rw [hright_zero, add_zero]
      exact rIntegral_congr_of_integrable hleft
        (pma6_8 _ id _ _ hc0 hg.continuousOn (monotone_id.monotoneOn _)) hleft_eq
    _ = ∫ t in 0..c, g t := rIntegral_eq_intervalIntegral_of_continuousOn hc0 hg.continuousOn

theorem isClosed_standardSimplex (n : ℕ) : IsClosed (standardSimplex n) := by
  have he : standardSimplex n = (⋂ i : Fin n, {x : Coord n | 0 ≤ x i}) ∩
      {x : Coord n | ∑ i, x i ≤ 1} := by
    ext x
    simp [standardSimplex]
  rw [he]
  exact (isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)).inter
    (isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)

theorem standardSimplex_subset_unit (n : ℕ) : standardSimplex n ⊆ (Cell.unit n).carrier := by
  intro x hx
  rw [Cell.mem_carrier]
  intro i
  exact ⟨hx.1 i, (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2⟩

theorem isCompact_standardSimplex (n : ℕ) : IsCompact (standardSimplex n) :=
  (Cell.unit n).isCompact_carrier.of_isClosed_subset (isClosed_standardSimplex n)
    (standardSimplex_subset_unit n)

theorem mem_standardSimplex_snoc {n : ℕ} {x : Coord n} {t : ℝ} :
    Fin.snoc x t ∈ standardSimplex (n + 1) ↔
      (∀ i, 0 ≤ x i) ∧ 0 ≤ t ∧ (∑ i, x i) + t ≤ 1 := by
  simp only [standardSimplex, mem_ofPred_eq, Fin.forall_fin_succ', Fin.sum_univ_castSucc,
    Fin.snoc_castSucc, Fin.snoc_last]
  tauto

/-- The simplex fiber integral has a continuous formula even where the fiber collapses. -/
def simplexSliceFormula {n : ℕ} (g : Coord (n + 1) → ℝ) (x : Coord n) : ℝ :=
  ∫ t in 0..max 0 (1 - ∑ i, x i), g (Fin.snoc x t)

theorem continuous_simplexSliceFormula {n : ℕ} {g : Coord (n + 1) → ℝ}
    (hg : Continuous g) : Continuous (simplexSliceFormula g) := by
  have hj : Continuous (Function.uncurry (fun x : Coord n => fun t : ℝ => g (Fin.snoc x t))) :=
    hg.comp (continuous_snoc n)
  have h := intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (f := fun x : Coord n => fun t : ℝ => g (Fin.snoc x t)) (a₀ := 0) hj
  exact h.comp (continuous_id.prodMk (by fun_prop))

/-- Every simplex fiber is genuinely Riemann integrable, including collapsed fibers. -/
theorem simplex_slice_integrable_formula {n : ℕ} {f g : Coord (n + 1) → ℝ}
    (hg : Continuous g) (he : EqOn g f (standardSimplex (n + 1)))
    {x : Coord n} (hx : x ∈ (Cell.unit n).carrier) :
    RIntegrable (fun t => simplexExtension f (Fin.snoc x t)) 0 1 ∧
      nativeSliceIntegral (Cell.unit (n + 1)) (simplexExtension f) x =
        simplexSliceFormula g x := by
  have hx0 : ∀ i, 0 ≤ x i := fun i => (Cell.mem_carrier.mp hx i).1
  have hs0 : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx0 i)
  have hgc : Continuous (fun t => g (Fin.snoc x t)) :=
    hg.comp (Continuous.finSnoc (A := fun _ : Fin (n + 1) => ℝ)
      (f := fun _ : ℝ => x) continuous_const continuous_id)
  by_cases hsum : (∑ i, x i) ≤ 1
  · have hc0 : 0 ≤ 1 - ∑ i, x i := sub_nonneg.mpr hsum
    have hc1 : 1 - (∑ i, x i) ≤ 1 := by linarith
    have hi := stoppedSlice_integrable_and_value hgc hc0 hc1
    have heq : EqOn (fun t => simplexExtension f (Fin.snoc x t))
        (stoppedSlice (fun t => g (Fin.snoc x t)) (1 - ∑ i, x i)) (Icc 0 1) := by
      intro t ht
      by_cases htc : t ≤ 1 - ∑ i, x i
      · have hm : Fin.snoc x t ∈ standardSimplex (n + 1) :=
          mem_standardSimplex_snoc.mpr ⟨hx0, ht.1, by linarith⟩
        simp only [simplexExtension, Set.indicator_of_mem hm, stoppedSlice, ite_eq_left htc, he hm]
      · have hm : Fin.snoc x t ∉ standardSimplex (n + 1) := by
          intro hm
          exact htc (by linarith [(mem_standardSimplex_snoc.mp hm).2.2])
        simp only [simplexExtension, Set.indicator_of_notMem hm, stoppedSlice, ite_eq_right htc]
    have hfi := rIntegrable_congr hi.1 heq
    refine ⟨hfi, ?_⟩
    change RIntegral (fun t => simplexExtension f (Fin.snoc x t)) 0 1 = _
    rw [rIntegral_congr_of_integrable hfi hi.1 heq, hi.2]
    simp only [simplexSliceFormula, max_eq_right hc0]
  · have hz := rsIntegral_const (c := 0) (show (0 : ℝ) ≤ 1 by norm_num)
      (monotone_id.monotoneOn (Icc 0 1))
    have heq : EqOn (fun t => simplexExtension f (Fin.snoc x t)) (fun _ => 0) (Icc 0 1) := by
      intro t ht
      have hm : Fin.snoc x t ∉ standardSimplex (n + 1) := by
        intro hm
        exact hsum (by linarith [(mem_standardSimplex_snoc.mp hm).2.2, ht.1])
      exact Set.indicator_of_notMem hm f
    have hfi := rIntegrable_congr hz.1 heq
    refine ⟨hfi, ?_⟩
    change RIntegral (fun t => simplexExtension f (Fin.snoc x t)) 0 1 = _
    rw [rIntegral_congr_of_integrable hfi hz.1 heq]
    have hc : 1 - (∑ i, x i) ≤ 0 := by linarith [lt_of_not_ge hsum]
    simpa only [RIntegral, id_eq, zero_mul, simplexSliceFormula, max_eq_left hc,
      intervalIntegral.integral_same] using hz.2

theorem simplex_nativeSlice_continuousOn {n : ℕ} {f : Coord (n + 1) → ℝ}
    (hf : ContinuousOn f (standardSimplex (n + 1))) :
    ContinuousOn (nativeSliceIntegral (Cell.unit (n + 1)) (simplexExtension f))
      (Cell.unit n).carrier := by
  obtain ⟨g, hg, he⟩ := exists_continuous_extension (isClosed_standardSimplex (n + 1)) hf
  exact (continuous_simplexSliceFormula hg).continuousOn.congr
    (fun x hx => (simplex_slice_integrable_formula hg he hx).2)

theorem simplex_iteratedRIntegrable {n : ℕ} {f : Coord n → ℝ}
    (hf : ContinuousOn f (standardSimplex n)) :
    IteratedRIntegrable (Cell.unit n) (simplexExtension f) := by
  cases n with
  | zero => trivial
  | succ n =>
      obtain ⟨g, hg, he⟩ := exists_continuous_extension (isClosed_standardSimplex (n + 1)) hf
      exact ⟨fun x hx => (simplex_slice_integrable_formula hg he hx).1,
        iteratedRIntegrable_of_continuousOn (simplex_nativeSlice_continuousOn hf)⟩

end Rudin.PMA.Chapter10
