import Rudin.PMA.Chapter09.Differentiation

/-!
# PMA 9.16: partial derivatives do not imply continuity

The example `xy/(x²+y²)`, with value zero at the origin, witnesses the
warning in 9.16. This is an explicit witness for the assertion there; it is
not an additional claim that the chapter's referenced exercises are solved.
-/

noncomputable section

open Filter
open scoped Topology

namespace Rudin.PMA.Chapter09

/-- **9.16**, the discontinuous example witnessing the warning about partials.
Lean's division convention gives its prescribed value zero at the origin. -/
def pma9_16_discontinuous (x : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  x 0 * x 1 / ((x 0) ^ 2 + (x 1) ^ 2)

theorem pma9_16_discontinuous_differentiable_off_zero
    {x : EuclideanSpace ℝ (Fin 2)} (hx : x ≠ 0) :
    DifferentiableAt ℝ pma9_16_discontinuous x := by
  have h0 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 0) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0).differentiableAt
  have h1 : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin 2) => y 1) x :=
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1).differentiableAt
  have hd : (x 0) ^ 2 + (x 1) ^ 2 ≠ 0 := by
    intro hd
    have h0z : x 0 = 0 := by nlinarith [sq_nonneg (x 1)]
    have h1z : x 1 = 0 := by nlinarith [sq_nonneg (x 0)]
    apply hx
    apply PiLp.ext
    intro i
    fin_cases i
    · exact h0z
    · exact h1z
  convert! (h0.mul h1).mul (((h0.pow 2).add (h1.pow 2)).inv hd) using 1

/-- Every coordinate partial derivative of the example exists, including at zero. -/
theorem pma9_16_discontinuous_partials
    (x : EuclideanSpace ℝ (Fin 2)) (j : Fin 2) :
    LineDifferentiableAt ℝ pma9_16_discontinuous x (pma9_coordinate 2 j) := by
  by_cases hx : x = 0
  · subst x
    have hline : (fun t : ℝ =>
        pma9_16_discontinuous (0 + t • pma9_coordinate 2 j)) = fun _ => 0 := by
      funext t
      fin_cases j <;>
        simp [pma9_16_discontinuous, pma9_coordinate, EuclideanSpace.basisFun_apply]
    change DifferentiableAt ℝ _ 0
    rw [hline]
    exact differentiableAt_const 0
  · exact (pma9_16_discontinuous_differentiable_off_zero hx).lineDifferentiableAt

/-- The same example is not continuous at the origin. -/
theorem pma9_16_discontinuous_not_continuous :
    ¬ ContinuousAt pma9_16_discontinuous 0 := by
  intro hc
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun _ => 1)
  have hv : Tendsto (fun t : ℝ => t • v) (𝓝[≠] 0) (𝓝 0) := by
    have hcont : Continuous (fun t : ℝ => t • v) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left
      nhdsWithin_le_nhds
  have hzero : Tendsto (fun t : ℝ => pma9_16_discontinuous (t • v))
      (𝓝[≠] 0) (𝓝 0) := by
    have hc0 : Tendsto pma9_16_discontinuous (𝓝 0) (𝓝 0) := by
      simpa only [pma9_16_discontinuous, PiLp.zero_apply, zero_mul, zero_pow,
        zero_add, zero_div] using hc.tendsto
    exact hc0.comp hv
  have heq : (fun t : ℝ => pma9_16_discontinuous (t • v)) =ᶠ[𝓝[≠] 0]
      (fun _ => (1 / 2 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : t ≠ 0 := ht
    simp only [pma9_16_discontinuous, v, PiLp.smul_apply,
      smul_eq_mul, mul_one]
    have hd : t ^ 2 + t ^ 2 ≠ 0 := by positivity
    field_simp [hd]
    ring
  have hhalf : Tendsto (fun t : ℝ => pma9_16_discontinuous (t • v))
      (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds.congr' heq.symm
  have : (0 : ℝ) = 1 / 2 := tendsto_nhds_unique hzero hhalf
  norm_num at this

/-- **9.16**, first warning: existence of all partial derivatives everywhere
does not imply continuity. -/
theorem pma9_16_partials_not_imply_continuity :
    ∃ f : EuclideanSpace ℝ (Fin 2) → ℝ,
      (∀ x j, LineDifferentiableAt ℝ f x (pma9_coordinate 2 j)) ∧
      ¬ ContinuousAt f 0 :=
  ⟨pma9_16_discontinuous, pma9_16_discontinuous_partials,
    pma9_16_discontinuous_not_continuous⟩

end Rudin.PMA.Chapter09
