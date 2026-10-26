import Rudin.PMA.Chapter10.PositiveRegionUnions
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Fin.Tuple.Sort

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The staircase chart sends simplex increments to cumulative coordinates. -/
def cumulativeCoordinates (n : ℕ) : Coord n →L[ℝ] Coord n :=
  ContinuousLinearMap.pi (fun i => ∑ j ∈ Finset.Iic i, ContinuousLinearMap.proj j)

lemma cumulativeCoordinates_apply {n : ℕ} (u : Coord n) (i : Fin n) :
    cumulativeCoordinates n u i = ∑ j ∈ Finset.Iic i, u j := by
  simp [cumulativeCoordinates]

def coordinateIncrements {n : ℕ} (y : Coord n) : Coord n :=
  fun i => (Fin.cons (0 : ℝ) y : Fin (n+1) → ℝ) i.succ - (Fin.cons (0 : ℝ) y : Fin (n+1) → ℝ) i.castSucc

lemma cumulativeCoordinates_increments {n : ℕ} (y : Coord n) :
    cumulativeCoordinates n (coordinateIncrements y) = y := by
  ext i
  rw [cumulativeCoordinates_apply]
  simpa only [coordinateIncrements, Fin.cons_succ, Fin.cons_zero, sub_zero] using
    Fin.sum_Iic_sub i (Fin.cons (0 : ℝ) y : Fin (n+1) → ℝ)

lemma cumulativeCoordinates_det (n : ℕ) :
    LinearMap.det (cumulativeCoordinates n).toLinearMap = 1 := by
  rw [← LinearMap.det_toMatrix']
  have he : LinearMap.toMatrix' (cumulativeCoordinates n).toLinearMap =
      (fun i j : Fin n => if j ≤ i then (1 : ℝ) else 0) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, cumulativeCoordinates_apply, Pi.single_apply, eq_comm]
  rw [he]
  have ht : Matrix.IsLowerTriangular (fun i j : Fin n => if j ≤ i then (1 : ℝ) else 0) := by
    intro i j hij
    exact if_neg (not_le.mpr hij)
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp

lemma cumulativeCoordinates_injective (n : ℕ) : Injective (cumulativeCoordinates n) := by
  apply LinearMap.ker_eq_bot.mp
  by_contra h
  have hd := LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h
  rw [cumulativeCoordinates_det] at hd
  exact one_ne_zero hd

lemma coordinateIncrements_cumulative {n : ℕ} (u : Coord n) :
    coordinateIncrements (cumulativeCoordinates n u) = u :=
  cumulativeCoordinates_injective n (cumulativeCoordinates_increments _)

lemma cumulativeCoordinates_monotone {n : ℕ} {u : Coord n} (hu : ∀ i, 0 ≤ u i) :
    Monotone (cumulativeCoordinates n u) := by
  intro i j hij
  simp only [cumulativeCoordinates_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Iic_subset_Iic.mpr hij)
    (fun a _ _ => hu a)

lemma cumulativeCoordinates_unit {n : ℕ} {u : Coord n} (hu : u ∈ standardSimplex n) :
    cumulativeCoordinates n u ∈ (Cell.unit n).carrier := by
  rw [Cell.mem_carrier]
  intro i
  change 0 ≤ cumulativeCoordinates n u i ∧ cumulativeCoordinates n u i ≤ 1
  rw [cumulativeCoordinates_apply]
  exact ⟨Finset.sum_nonneg (fun j _ => hu.1 j),
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hu.1 j)).trans hu.2⟩

lemma coordinateIncrements_nonneg {n : ℕ} {y : Coord n}
    (hy : ∀ i, 0 ≤ y i) (hm : Monotone y) : ∀ i, 0 ≤ coordinateIncrements y i := by
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [coordinateIncrements] using hy 0
    · simpa only [coordinateIncrements, Fin.cons_succ, Fin.castSucc_succ] using
        sub_nonneg.mpr (hm (Fin.castSucc_le_succ j))

lemma coordinateIncrements_simplex {n : ℕ} {y : Coord n}
    (hy : y ∈ (Cell.unit n).carrier) (hm : Monotone y) :
    coordinateIncrements y ∈ standardSimplex n := by
  have hy' : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := by simpa [Cell.mem_carrier, Cell.unit] using hy
  refine ⟨coordinateIncrements_nonneg (fun i => (hy' i).1) hm, ?_⟩
  cases n with
  | zero => simp
  | succ n =>
    have he := congrFun (cumulativeCoordinates_increments y) (Fin.last n)
    rw [cumulativeCoordinates_apply] at he
    have hall : Finset.Iic (Fin.last n) = Finset.univ := by ext i; simp [Fin.le_last]
    rw [hall] at he
    exact he.le.trans (hy' (Fin.last n)).2

lemma cumulativeCoordinates_image (n : ℕ) :
    cumulativeCoordinates n '' standardSimplex n =
      {y | y ∈ (Cell.unit n).carrier ∧ Monotone y} := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨cumulativeCoordinates_unit hu, cumulativeCoordinates_monotone hu.1⟩
  · rintro ⟨hy, hm⟩
    exact ⟨coordinateIncrements y, coordinateIncrements_simplex hy hm,
      cumulativeCoordinates_increments y⟩

end Rudin.PMA.Chapter10
