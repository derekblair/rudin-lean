import Rudin.PMA.Chapter10.CellNormalization
import Rudin.PMA.Chapter10.StaircaseIntegrals

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma cellNormalize_image {n : ℕ} (C : Cell n) :
    cellNormalize C '' (Cell.unit n).carrier = C.carrier := by
  apply Subset.antisymm (cellNormalize_mapsTo C).image_subset
  intro y hy
  have hy' := Cell.mem_carrier.mp hy
  let u : Coord n := fun i => if C.upper i = C.lower i then 0
    else (y i - C.lower i) / (C.upper i - C.lower i)
  refine ⟨u, ?_, ?_⟩
  · rw [Cell.mem_carrier]
    intro i
    change 0 ≤ u i ∧ u i ≤ 1
    dsimp only [u]
    split_ifs with he
    · exact ⟨le_rfl, zero_le_one⟩
    · have hw : 0 < C.upper i - C.lower i :=
        sub_pos.mpr (lt_of_le_of_ne (C.lower_le_upper i) (Ne.symm he))
      exact ⟨div_nonneg (sub_nonneg.mpr (hy' i).1) hw.le,
        (div_le_one hw).mpr (sub_le_sub_right (hy' i).2 _)⟩
  · ext i
    dsimp only [cellNormalize, u]
    split_ifs with he
    · have hi := hy' i
      rw [he] at hi
      simp only [mul_zero, add_zero]
      exact le_antisymm hi.1 hi.2
    · have hw : C.upper i - C.lower i ≠ 0 := sub_ne_zero.mpr he
      field_simp
      ring

lemma cellNormalize_injective {n : ℕ} (C : Cell n)
    (hw : ∀ i, C.lower i < C.upper i) : Injective (cellNormalize C) := by
  intro u v he
  ext i
  have h := congrFun he i
  change C.lower i + (C.upper i - C.lower i) * u i =
    C.lower i + (C.upper i - C.lower i) * v i at h
  exact (mul_left_cancel₀ (sub_pos.mpr (hw i)).ne') (add_left_cancel h)

lemma cell_volume_zero_of_degenerate {n : ℕ} (C : Cell n) (i : Fin n)
    (hi : C.lower i = C.upper i) : volume C.carrier = 0 := by
  rw [Cell.carrier, Real.volume_Icc_pi]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

/-- Affine normalization of an arbitrary closed cell, including collapsed
sides, for the native iterated Riemann integral. -/
lemma cellNormalize_integral {n : ℕ} (C : Cell n) {f : Coord n → ℝ}
    (hf : ContinuousOn f C.carrier) :
    iteratedRIntegral C f = iteratedRIntegral (Cell.unit n)
      (fun u => (∏ i, (C.upper i - C.lower i)) * f (cellNormalize C u)) := by
  have hc : ContinuousOn (fun u => (∏ i, (C.upper i - C.lower i)) * f (cellNormalize C u))
      (Cell.unit n).carrier := continuousOn_const.mul
    (hf.comp (cellNormalize_contDiff C 1).continuous.continuousOn (cellNormalize_mapsTo C))
  rw [iteratedRIntegral_eq_setIntegral hf, iteratedRIntegral_eq_setIntegral hc]
  by_cases hw : ∀ i, C.lower i < C.upper i
  · rw [← cellNormalize_image C]
    rw [integral_image_eq_integral_abs_det_fderiv_smul volume
      (Cell.unit n).isCompact_carrier.isClosed.measurableSet
      (fun u hu => (cellNormalize_hasFDerivAt C u).hasFDerivWithinAt)
      (cellNormalize_injective C hw).injOn]
    have hn : 0 ≤ ∏ i, (C.upper i - C.lower i) :=
      Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (C.lower_le_upper i))
    have he : LinearMap.det (cellNormalizeLinear C).toLinearMap =
        ∏ i, (C.upper i - C.lower i) := by
      simpa only [(cellNormalize_hasFDerivAt C 0).fderiv] using cellNormalize_det C 0
    simp only [he, abs_of_nonneg hn, smul_eq_mul]
  · push_neg at hw
    obtain ⟨i, hi⟩ := hw
    have he : C.lower i = C.upper i := le_antisymm (C.lower_le_upper i) hi
    have hp : (∏ j, (C.upper j - C.lower j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [he]
    rw [hp]
    simp only [zero_mul, integral_zero]
    rw [Measure.restrict_eq_zero.mpr (cell_volume_zero_of_degenerate C i he), integral_zero_measure]

/-- Each affine staircase chart in the original cell. -/
def cellStaircase {n : ℕ} (C : Cell n) (σ : Equiv.Perm (Fin n)) : Coord n → Coord n :=
  cellNormalize C ∘ staircaseLinear σ

lemma cellStaircase_contDiff {n : ℕ} (C : Cell n) (σ : Equiv.Perm (Fin n)) (r : WithTop ENat) :
    ContDiff ℝ r (cellStaircase C σ) :=
  (cellNormalize_contDiff C r).comp (staircaseLinear σ).contDiff

lemma cellStaircase_mapsTo {n : ℕ} (C : Cell n) (σ : Equiv.Perm (Fin n)) :
    MapsTo (cellStaircase C σ) (standardSimplex n) C.carrier := by
  intro u hu
  apply cellNormalize_mapsTo C
  exact (show staircaseLinear σ u ∈ staircaseChamber σ by
    rw [← staircaseLinear_image]; exact mem_image_of_mem _ hu).1

lemma cellStaircases_cover {n : ℕ} (C : Cell n) :
    (⋃ σ : Equiv.Perm (Fin n), cellStaircase C σ '' standardSimplex n) = C.carrier := by
  simp only [cellStaircase, image_comp, staircaseLinear_image, ← image_iUnion,
    staircaseChambers_cover, cellNormalize_image]

lemma cell_integral_staircase {n : ℕ} (C : Cell n) {f : Coord n → ℝ}
    (hf : ContinuousOn f C.carrier) :
    iteratedRIntegral C f = ∑ σ : Equiv.Perm (Fin n), simplexRIntegral
      (fun u => (∏ i, (C.upper i - C.lower i)) * f (cellStaircase C σ u)) := by
  rw [cellNormalize_integral C hf]
  exact (unitCell_integral_staircase (continuousOn_const.mul
    (hf.comp (cellNormalize_contDiff C 1).continuous.continuousOn (cellNormalize_mapsTo C)))).2.2

end Rudin.PMA.Chapter10
