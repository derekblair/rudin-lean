import Mathlib

/-!
# The continuous counterexample attached to PMA 9.16

PMA observes that continuity together with existence of every partial derivative
does not imply total differentiability. We give an explicit witness
`f(x,y) = xy / sqrt(x²+y²)`, with value zero at the origin. This is a convenient
alternative to the exercises referenced in the book, not a formalization of the
full exercises. Euclidean space supplies the displayed square root as its norm.
-/

noncomputable section
open scoped Topology

namespace Rudin.PMA.Chapter09

/-- An explicit witness for the second observation in 9.16. Division by zero
defines the value at the origin to be zero. -/
def pma9_16_continuousCounterexample (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * x 1 / ‖x‖

theorem pma9_16_continuousCounterexample_zero :
    pma9_16_continuousCounterexample 0 = 0 := by
  simp [pma9_16_continuousCounterexample]

/-- This bound proves continuity at the only point where the denominator vanishes. -/
theorem pma9_16_continuousCounterexample_bound (x : EuclideanSpace ℝ (Fin 2)) :
    ‖pma9_16_continuousCounterexample x‖ ≤ ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, pma9_16_continuousCounterexample_zero]
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [pma9_16_continuousCounterexample, norm_div, norm_mul, norm_norm,
    div_le_iff₀ hnorm]
  exact mul_le_mul (PiLp.norm_apply_le x 0) (PiLp.norm_apply_le x 1)
    (norm_nonneg _) (norm_nonneg _)

theorem pma9_16_continuousCounterexample_differentiable_off_zero
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    DifferentiableAt ℝ pma9_16_continuousCounterexample x := by
  have h0 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 0) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 1) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1).differentiableAt
  have hn : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => ‖y‖) x :=
    (differentiableAt_id (𝕜 := ℝ) (x := x)).norm ℝ hx
  convert! (h0.mul h1).mul (hn.inv (norm_ne_zero_iff.mpr hx)) using 1

theorem pma9_16_continuousCounterexample_continuous :
    Continuous pma9_16_continuousCounterexample := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    change Filter.Tendsto pma9_16_continuousCounterexample (𝓝 0)
      (𝓝 (pma9_16_continuousCounterexample 0))
    rw [pma9_16_continuousCounterexample_zero]
    exact squeeze_zero_norm pma9_16_continuousCounterexample_bound
      (by simpa using continuous_norm.tendsto (0 : EuclideanSpace ℝ (Fin 2)))
  · exact (pma9_16_continuousCounterexample_differentiable_off_zero hx).continuousAt

/-- Both coordinate partials at the origin are zero. -/
theorem pma9_16_continuousCounterexample_partial_zero (j : Fin 2) :
    HasLineDerivAt ℝ pma9_16_continuousCounterexample 0 0
      (EuclideanSpace.basisFun (Fin 2) ℝ j) := by
  have haxis (t : ℝ) :
      pma9_16_continuousCounterexample
        (0 + t • EuclideanSpace.basisFun (Fin 2) ℝ j) = 0 := by
    fin_cases j <;>
      simp [pma9_16_continuousCounterexample, EuclideanSpace.basisFun_apply]
  simp only [HasLineDerivAt, haxis]
  exact hasDerivAt_const _ _

/-- All coordinate partial derivatives exist at every point. -/
theorem pma9_16_continuousCounterexample_all_partials (x : EuclideanSpace ℝ (Fin 2))
    (j : Fin 2) :
    ∃ d : ℝ, HasLineDerivAt ℝ pma9_16_continuousCounterexample d x
      (EuclideanSpace.basisFun (Fin 2) ℝ j) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, pma9_16_continuousCounterexample_partial_zero j⟩
  · exact ⟨_, (pma9_16_continuousCounterexample_differentiable_off_zero hx).hasFDerivAt.hasLineDerivAt _⟩

/-- The diagonal restriction is a nonzero multiple of absolute value, so the
function cannot have a total derivative at the origin. -/
theorem pma9_16_continuousCounterexample_not_differentiable :
    ¬DifferentiableAt ℝ pma9_16_continuousCounterexample 0 := by
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![1, 1]
  have hv : v ≠ 0 := by
    intro h
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 2) => x 0) h
    norm_num [v] at this
  have hdiag (t : ℝ) : pma9_16_continuousCounterexample (t • v) * ‖v‖ = |t| := by
    rw [pma9_16_continuousCounterexample, norm_smul, Real.norm_eq_abs]
    change (t * 1 * (t * 1) / (|t| * ‖v‖)) * ‖v‖ = |t|
    by_cases ht : t = 0
    · simp [ht]
    · field_simp [abs_ne_zero.mpr ht, norm_ne_zero_iff.mpr hv]
      nlinarith [sq_abs t]
  intro hf
  have hline : DifferentiableAt ℝ (fun t : ℝ => t • v) 0 :=
    differentiableAt_id.smul_const v
  have hcomp := ((by simpa using hf :
    DifferentiableAt ℝ pma9_16_continuousCounterexample ((0 : ℝ) • v)).comp 0 hline).mul_const ‖v‖
  have heq : (fun t : ℝ => pma9_16_continuousCounterexample (t • v) * ‖v‖) = abs :=
    funext hdiag
  exact not_differentiableAt_abs_zero (heq ▸ hcomp)

/-- The complete second counterexample assertion attached to 9.16. -/
theorem pma9_16_continuous_partials_not_differentiable :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      Continuous f ∧
      (∀ x j, ∃ d : ℝ, HasLineDerivAt ℝ f d x (EuclideanSpace.basisFun (Fin 2) ℝ j)) ∧
      ¬DifferentiableAt ℝ f 0 :=
  ⟨pma9_16_continuousCounterexample, pma9_16_continuousCounterexample_continuous,
    pma9_16_continuousCounterexample_all_partials,
    pma9_16_continuousCounterexample_not_differentiable⟩

end Rudin.PMA.Chapter09
