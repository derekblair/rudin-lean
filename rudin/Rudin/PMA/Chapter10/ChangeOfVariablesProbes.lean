import Rudin.PMA.Chapter10.ChangeOfVariables

set_option autoImplicit false
noncomputable section
open Set

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def reflection (x : Coord 1) : Coord 1 := -x
private def positiveRay : Set (Coord 1) := {x | 0 < x 0}

/-- This admissible coordinate change reverses orientation everywhere. -/
theorem reflection_negative_jacobian (x : Coord 1) :
    coordinateJacobian reflection x = -1 := by
  have hd : HasFDerivAt reflection (-ContinuousLinearMap.id ℝ (Coord 1)) x :=
    (hasFDerivAt_id x).neg
  rw [coordinateJacobian_eq_matrix, hd.fderiv, Matrix.det_fin_one]
  simp [LinearMap.toMatrix'_apply]

/-- On a proper open domain, the absolute determinant removes the negative
orientation sign, and the transformed integrand is zero off that domain. -/
theorem reflection_on_positive_ray (f : Coord 1 → ℝ) (hf : Continuous f)
    (hs : HasCompactSupport f) (hnegative : tsupport f ⊆ {x | x 0 < 0}) :
    wholeRIntegral f =
      wholeRIntegral (fun x : Coord 1 => if 0 < x 0 then f (-x) else 0) ∧
    (∀ x : Coord 1, x 0 ≤ 0 → zeroExtendedPullback positiveRay reflection f x = 0) := by
  have hE : IsOpen positiveRay := isOpen_lt continuous_const (continuous_apply 0)
  have hT : C1On reflection positiveRay :=
    (c1On_iff_contDiffOn hE).mpr contDiff_id.neg.contDiffOn
  have hi : InjOn reflection positiveRay := fun x _ y _ h => neg_injective h
  have hJ : ∀ x ∈ positiveRay, coordinateJacobian reflection x ≠ 0 := by
    intro x _
    rw [reflection_negative_jacobian]
    norm_num
  have hsub : tsupport f ⊆ reflection '' positiveRay := by
    intro y hy
    refine ⟨-y, ?_, ?_⟩
    · change 0 < -y 0
      exact neg_pos.mpr (hnegative hy)
    · simp [reflection]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hval⟩ :=
    pma10_9.2.2 1 positiveRay reflection f hE hT hi hJ hf hs hsub
  have he : zeroExtendedPullback positiveRay reflection f =
      fun x : Coord 1 => if 0 < x 0 then f (-x) else 0 := by
    funext x
    unfold zeroExtendedPullback
    simp only [reflection_negative_jacobian, abs_neg, abs_one, mul_one]
    by_cases hx : 0 < x 0 <;> simp [positiveRay, reflection, hx]
  refine ⟨hval.trans (congrArg wholeRIntegral he), ?_⟩
  intro x hx
  rw [he]
  exact if_neg (not_lt.mpr hx)

end Rudin.PMA.Chapter10.FidelityProbes
