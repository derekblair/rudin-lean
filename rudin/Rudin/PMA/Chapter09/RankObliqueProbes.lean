import Rudin.PMA.Chapter09.AlgebraProbes

set_option autoImplicit false
noncomputable section
open Set

namespace Rudin.PMA.Chapter09.FidelityProbes

/-- A genuine rank-one map with a nontrivial kernel. -/
def axisMap : Operator 2 2 :=
  (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).smulRight (coordinateVector 2 0)

private theorem first_axis_ne_zero : coordinateVector 2 0 ≠ 0 := by
  intro h
  have hh := congrArg (fun x : Euclidean 2 => x 0) h
  norm_num [coordinateVector, EuclideanSpace.basisFun_apply] at hh

theorem axisMap_range :
    axisMap.toLinearMap.range = Submodule.span ℝ {coordinateVector 2 0} := by
  apply ContinuousLinearMap.range_smulRight_apply
  intro h
  have hh := congrArg (fun L : Euclidean 2 →L[ℝ] ℝ => L (coordinateVector 2 0)) h
  norm_num [coordinateVector, EuclideanSpace.basisFun_apply] at hh

theorem axisMap_rank : operatorRank axisMap = 1 := by
  rw [operatorRank, axisMap_range]
  exact finrank_span_singleton first_axis_ne_zero

theorem oblique_range_eq_axisMap : obliqueProjection.toLinearMap.range = axisMap.toLinearMap.range := by
  rw [axisMap_range]
  apply ContinuousLinearMap.range_smulRight_apply
  intro h
  have hh := congrArg (fun L : Euclidean 2 →L[ℝ] ℝ => L (coordinateVector 2 0)) h
  norm_num [coordinateVector, EuclideanSpace.basisFun_apply] at hh

/-- The requested projection is not the orthogonal projection onto the image axis. -/
theorem obliqueProjection_ne_axisMap : obliqueProjection ≠ axisMap := by
  intro h
  have hh := congrArg (fun L : Operator 2 2 => L (coordinateVector 2 1) 0) h
  norm_num [obliqueProjection, axisMap, coordinateVector, EuclideanSpace.basisFun_apply] at hh

/-- Exercise the full rank theorem at intermediate rank, retaining the selected
oblique projection and both its image-bijection and kernel-dimension conclusions. -/
theorem rank_one_oblique_normal_form :
    ∃ N : RankNormalForm axisMap univ 0 obliqueProjection,
      Module.finrank ℝ axisMap.toLinearMap.ker = 1 ∧
      BijOn obliqueProjection (axisMap '' N.H.target) (axisMap '' N.H.source) := by
  have hc : C1On axisMap univ :=
    (c1On_iff_contDiffOn isOpen_univ).mpr axisMap.contDiff.contDiffOn
  have hr : ∀ x ∈ (univ : Set (Euclidean 2)),
      operatorRank (fderiv ℝ axisMap x) = 1 := by
    intro x _
    simpa only [ContinuousLinearMap.fderiv] using axisMap_rank
  have hP : obliqueProjection.toLinearMap.range =
      (fderiv ℝ axisMap 0).toLinearMap.range := by
    simpa only [ContinuousLinearMap.fderiv] using oblique_range_eq_axisMap
  obtain ⟨N, _, hker, _, hbij, _⟩ := pma9_32 2 2 1 univ axisMap 0 obliqueProjection
    isOpen_univ (mem_univ _) hc hr oblique_is_projection hP
  refine ⟨N, ?_, ?_⟩
  · have hd : fderiv ℝ axisMap (0 : Euclidean 2) = axisMap := axisMap.hasFDerivAt.fderiv
    rw [hd] at hker
    norm_num at hker
    exact hker
  · simpa only [ContinuousLinearMap.fderiv] using hbij

end Rudin.PMA.Chapter09.FidelityProbes
