import Rudin.PMA.Chapter09.ParameterIntegrals

/-! Independent clients for discontinuous integrators, singleton intervals,
and independently moving endpoints of native improper integrals. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter09.FidelityProbes

private def jumpIntegrator (x : ℝ) : ℝ := if x < 0 then 0 else 1

private theorem jumpIntegrator_monotone : Monotone jumpIntegrator := by
  intro x y hxy
  dsimp only [jumpIntegrator]
  split_ifs <;> norm_num <;> linarith

/-- A jump integrator is allowed; parameter differentiation gives its full mass. -/
theorem parameter_square_with_jump (s : ℝ) :
    HasDerivAt (fun t => Chapter06.RSIntegral (fun _ => t ^ 2)
      jumpIntegrator (-1) 1) (2 * s) s := by
  have hα := jumpIntegrator_monotone.monotoneOn (Icc (-1) 1)
  have h := pma9_42.2 (fun _ t => t ^ 2) (fun _ t => 2 * t)
    jumpIntegrator (-1) 1 (s - 1) (s + 1) s (by norm_num)
    (by constructor <;> linarith) hα
    (fun t _ => (Chapter06.rsIntegral_const (c := t ^ 2) (by norm_num) hα).1)
    (fun _ _ t _ => by simpa using hasDerivAt_pow 2 t)
    (by fun_prop)
  have hi := (Chapter06.rsIntegral_const (c := 2 * s) (by norm_num) hα).2
  have hi' : Chapter06.RSIntegral (fun _ => 2 * s) jumpIntegrator (-1) 1 = 2 * s := by
    norm_num [jumpIntegrator] at hi
    exact hi
  simpa only [hi'] using h.2

/-- No regularity of the spatial coefficient or integrator is needed on a singleton. -/
theorem parameter_singleton_arbitrary_coefficient (ψ α : ℝ → ℝ) (a : ℝ) :
    HasDerivAt (fun t => Chapter06.RSIntegral (fun x => ψ x * t) α a a) 0 0 := by
  have hα : MonotoneOn α (Icc a a) :=
    (Chapter06.calculus_singleton_integrals ψ α a).1.2.2.1
  have hu : TendstoUniformlyOn (fun _ : ℝ => ψ) ψ (𝓝 (0 : ℝ)) (Icc a a) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall fun _ _ _ => by simpa using hε
  have h := pma9_42.1 (fun x t => ψ x * t) (fun x _ => ψ x)
    α a a (-1) 1 0 le_rfl (by norm_num) hα
    (fun t _ => (Chapter06.calculus_singleton_integrals (fun x => ψ x * t) α a).1)
    (Eventually.of_forall fun t x _ => by simpa using (hasDerivAt_id t).const_mul (ψ x)) hu
  simpa only [(Chapter06.calculus_singleton_integrals ψ α a).2] using h.2

/-- The Gaussian integral converges along independently chosen lower and upper windows. -/
theorem gaussian_native_independent_windows (t : ℝ) (a b : ℕ → ℝ)
    (ha : Tendsto a atTop atBot) (hb : Tendsto b atTop atTop) :
    Tendsto (fun k => Chapter08.orientedRIntegral (gaussianCosIntegrand t) (a k) (b k))
      atTop (𝓝 (Real.sqrt Real.pi * Real.exp (-(t ^ 2) / 4))) := by
  have h := ((pma9_43.2.1 t).1.2).comp (ha.prodMk hb)
  simpa only [Function.comp_def, pma9_43.2.2.2.2 t] using h

/-- Improper absolute convergence includes actual native integrability on each compact interval. -/
theorem gaussian_absolute_native_compacts (t a b : ℝ) (hab : a ≤ b) :
    Chapter06.RIntegrable (fun x => |gaussianCosIntegrand t x|) a b := by
  obtain ⟨I, hI⟩ := (pma9_43.1 t).1
  exact hI.1 a b hab

end Rudin.PMA.Chapter09.FidelityProbes
