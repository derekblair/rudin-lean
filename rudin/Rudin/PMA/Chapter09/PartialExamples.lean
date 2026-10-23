import Rudin.PMA.Chapter09.Differentiation

/-! # PMA 9.16: partial derivatives do not imply total differentiability.

Both examples have every coordinate partial at every point. The second is
continuous everywhere. Neither example relies on totalized derivative values.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter09

def discontinuousPartialsExample (x : Euclidean 2) : ℝ := x 0 * x 1 / ‖x‖ ^ 2

def continuousPartialsExample (x : Euclidean 2) : ℝ := x 0 * x 1 / ‖x‖

def diagonalVector : Euclidean 2 := coordinateVector 2 0 + coordinateVector 2 1

@[simp] theorem diagonalVector_zero : diagonalVector 0 = 1 := by
  simp [diagonalVector, coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] theorem diagonalVector_one : diagonalVector 1 = 1 := by
  simp [diagonalVector, coordinateVector, EuclideanSpace.basisFun_apply]

theorem diagonalVector_ne_zero : diagonalVector ≠ 0 := by
  intro h
  have := congrArg (fun x : Euclidean 2 => x 0) h
  simpa using this

theorem partialExamples_axis_zero (j : Fin 2) :
    (fun t : ℝ => discontinuousPartialsExample (t • coordinateVector 2 j)) = (fun _ => 0) ∧
    (fun t : ℝ => continuousPartialsExample (t • coordinateVector 2 j)) = (fun _ => 0) := by
  constructor <;> funext t <;> fin_cases j <;>
    simp [discontinuousPartialsExample, continuousPartialsExample, coordinateVector,
      EuclideanSpace.basisFun_apply]

theorem partialExamples_partials_zero (j : Fin 2) :
    HasCoordinatePartial discontinuousPartialsExample 0 j 0 ∧
      HasCoordinatePartial continuousPartialsExample 0 j 0 := by
  simp only [HasCoordinatePartial, zero_add]
  rw [(partialExamples_axis_zero j).1, (partialExamples_axis_zero j).2]
  exact ⟨hasDerivAt_const 0 0, hasDerivAt_const 0 0⟩

theorem partialExamples_differentiable_off_zero {x : Euclidean 2} (hx : x ≠ 0) :
    DifferentiableAt ℝ discontinuousPartialsExample x ∧
      DifferentiableAt ℝ continuousPartialsExample x := by
  have h0 : DifferentiableAt ℝ (fun y : Euclidean 2 => y 0) x :=
    (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : Euclidean 2 => y 1) x :=
    (EuclideanSpace.proj 1 : Euclidean 2 →L[ℝ] ℝ).differentiableAt
  have hn : DifferentiableAt ℝ (fun y : Euclidean 2 => ‖y‖) x :=
    differentiableAt_id.norm ℝ hx
  constructor
  · change DifferentiableAt ℝ (fun y : Euclidean 2 => y 0 * y 1 / ‖y‖ ^ 2) x
    simpa only [div_eq_mul_inv] using
      (h0.fun_mul h1).fun_mul ((hn.fun_pow 2).fun_inv (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)))
  · change DifferentiableAt ℝ (fun y : Euclidean 2 => y 0 * y 1 / ‖y‖) x
    simpa only [div_eq_mul_inv] using
      (h0.fun_mul h1).fun_mul (hn.fun_inv (norm_ne_zero_iff.mpr hx))

theorem partialExamples_partials_everywhere (x : Euclidean 2) (j : Fin 2) :
    (∃ d, HasCoordinatePartial discontinuousPartialsExample x j d) ∧
      (∃ d, HasCoordinatePartial continuousPartialsExample x j d) := by
  by_cases hx : x = 0
  · subst x
    exact ⟨⟨0, (partialExamples_partials_zero j).1⟩,
      ⟨0, (partialExamples_partials_zero j).2⟩⟩
  · obtain ⟨h0, h1⟩ := partialExamples_differentiable_off_zero hx
    exact ⟨⟨_, hasCoordinatePartial_of_hasFDerivAt h0.hasFDerivAt j⟩,
      ⟨_, hasCoordinatePartial_of_hasFDerivAt h1.hasFDerivAt j⟩⟩

theorem discontinuousPartialsExample_diagonal {t : ℝ} (ht : t ≠ 0) :
    discontinuousPartialsExample (t • diagonalVector) = 1 / ‖diagonalVector‖ ^ 2 := by
  have hn := norm_ne_zero_iff.mpr diagonalVector_ne_zero
  simp only [discontinuousPartialsExample, PiLp.smul_apply, smul_eq_mul,
    diagonalVector_zero, diagonalVector_one, mul_one, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  field_simp

theorem discontinuousPartialsExample_not_continuous :
    ¬ ContinuousAt discontinuousPartialsExample 0 := by
  intro hc
  have hpath : Tendsto (fun t : ℝ => t • diagonalVector) (𝓝[≠] 0) (𝓝 0) := by
    have hcpath : Continuous (fun t : ℝ => t • diagonalVector) := by fun_prop
    simpa using (hcpath.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => discontinuousPartialsExample (t • diagonalVector))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [Function.comp_def,
      show discontinuousPartialsExample 0 = 0 by simp [discontinuousPartialsExample]] using
      hc.tendsto.comp hpath
  have he : (fun t : ℝ => discontinuousPartialsExample (t • diagonalVector)) =ᶠ[𝓝[≠] 0]
      (fun _ => 1 / ‖diagonalVector‖ ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact discontinuousPartialsExample_diagonal ht
  have heq : (0 : ℝ) = 1 / ‖diagonalVector‖ ^ 2 :=
    tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)
  have hn := norm_ne_zero_iff.mpr diagonalVector_ne_zero
  exact (one_div_ne_zero (pow_ne_zero 2 hn)) heq.symm

theorem continuousPartialsExample_norm_le (x : Euclidean 2) :
    ‖continuousPartialsExample x‖ ≤ ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, continuousPartialsExample]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    rw [continuousPartialsExample, norm_div, norm_mul, Real.norm_eq_abs (‖x‖),
      abs_of_nonneg hn.le, div_le_iff₀ hn]
    exact mul_le_mul (PiLp.norm_apply_le x 0) (PiLp.norm_apply_le x 1)
      (norm_nonneg _) (norm_nonneg _)

theorem continuousPartialsExample_continuous : Continuous continuousPartialsExample := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hlim : Tendsto continuousPartialsExample (𝓝 0) (𝓝 0) :=
      squeeze_zero_norm continuousPartialsExample_norm_le (by simpa using
        (continuous_norm.continuousAt : ContinuousAt (fun x : Euclidean 2 => ‖x‖) 0).tendsto)
    simpa [ContinuousAt, continuousPartialsExample] using hlim
  · exact (partialExamples_differentiable_off_zero hx).2.continuousAt

theorem continuousPartialsExample_diagonal (t : ℝ) :
    ‖diagonalVector‖ * continuousPartialsExample (t • diagonalVector) = |t| := by
  have hn := norm_ne_zero_iff.mpr diagonalVector_ne_zero
  by_cases ht : t = 0
  · simp [ht, continuousPartialsExample]
  · simp only [continuousPartialsExample, PiLp.smul_apply, smul_eq_mul,
      diagonalVector_zero, diagonalVector_one, mul_one, norm_smul, Real.norm_eq_abs]
    have ha : |t| ≠ 0 := abs_ne_zero.mpr ht
    field_simp
    nlinarith [sq_abs t]

theorem continuousPartialsExample_not_differentiable :
    ¬ DifferentiableAt ℝ continuousPartialsExample 0 := by
  intro hd
  have hpath : DifferentiableAt ℝ (fun t : ℝ => t • diagonalVector) 0 :=
    differentiableAt_id.smul_const diagonalVector
  have hd' : DifferentiableAt ℝ continuousPartialsExample ((fun t : ℝ => t • diagonalVector) 0) := by
    simpa only [zero_smul] using hd
  have hcomp : DifferentiableAt ℝ
      (fun t : ℝ => ‖diagonalVector‖ * continuousPartialsExample (t • diagonalVector)) 0 :=
    (hd'.comp 0 hpath).const_mul _
  have he : (fun t : ℝ => ‖diagonalVector‖ *
      continuousPartialsExample (t • diagonalVector)) = abs :=
    funext continuousPartialsExample_diagonal
  rw [he] at hcomp
  exact not_differentiableAt_abs_zero hcomp

theorem pma9_16 : pma9_16_contract := by
  refine ⟨fun _ f x j d => hasCoordinatePartial_iff_quotient f x j d, ?_, ?_⟩
  · exact ⟨discontinuousPartialsExample,
      fun x j => (partialExamples_partials_everywhere x j).1,
      fun j => (partialExamples_partials_zero j).1,
      discontinuousPartialsExample_not_continuous⟩
  · exact ⟨continuousPartialsExample, continuousPartialsExample_continuous,
      fun x j => (partialExamples_partials_everywhere x j).2,
      fun j => (partialExamples_partials_zero j).2,
      continuousPartialsExample_not_differentiable⟩

end Rudin.PMA.Chapter09
