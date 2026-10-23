import Rudin.PMA.Chapter09.PartialExamples
import Rudin.PMA.Chapter09.C1Partials

set_option autoImplicit false
noncomputable section
open Set Filter Topology
namespace Rudin.PMA.Chapter09.FidelityProbes

theorem constant_total_derivative (n m : ℕ) (c : Euclidean m) (x : Euclidean n) :
    HasTotalDerivative (fun _ : Euclidean n => c) 0 x :=
  hasTotalDerivative_iff.mpr (hasFDerivAt_const c x)

theorem identity_cannot_have_zero_derivative (x : Euclidean 1) :
    ¬ HasTotalDerivative (id : Euclidean 1 → Euclidean 1) 0 x := by
  intro h
  have he := pma9_12 1 1 id 0 (ContinuousLinearMap.id ℝ (Euclidean 1)) x h
    (hasTotalDerivative_iff.mpr (hasFDerivAt_id x))
  have ht := congrArg (fun A : Operator 1 1 => A (coordinateVector 1 0) 0) he
  simp [coordinateVector, EuclideanSpace.basisFun_apply] at ht

/-- No coordinate derivatives exist to test in dimension zero; every function
on that domain is indeed continuously differentiable. -/
theorem zero_input_dimension_c1 (m : ℕ) (f : Euclidean 0 → Euclidean m) : C1On f univ := by
  apply (pma9_21 0 m f univ isOpen_univ).mpr
  exact ⟨fun _ _ _ j => Fin.elim0 j, fun _ j => Fin.elim0 j⟩

theorem zero_output_dimension_c1 (n : ℕ) (f : Euclidean n → Euclidean 0) : C1On f univ := by
  apply (pma9_21 n 0 f univ isOpen_univ).mpr
  exact ⟨fun _ _ i => Fin.elim0 i, fun i => Fin.elim0 i⟩

theorem empty_domain_c1 (n m : ℕ) (f : Euclidean n → Euclidean m) : C1On f ∅ := by
  exact ⟨fun _ hx => False.elim hx, continuousOn_empty _⟩

/-- Existence of partials everywhere really fails to force even continuity. -/
theorem partials_everywhere_without_continuity :
    ∃ f : Euclidean 2 → ℝ, (∀ x j, ∃ d, HasCoordinatePartial f x j d) ∧
      ¬ ContinuousAt f 0 := by
  obtain ⟨f,hp,_,hc⟩ := pma9_16.2.1
  exact ⟨f,hp,hc⟩

theorem continuous_partials_example_not_total :
    ∃ f : Euclidean 2 → ℝ, Continuous f ∧
      (∀ x j, ∃ d, HasCoordinatePartial f x j d) ∧ ¬ DifferentiableAt ℝ f 0 := by
  obtain ⟨f,hc,hp,_,hd⟩ := pma9_16.2.2
  exact ⟨f,hc,hp,hd⟩

/-- The derivative bound zero forces constancy on a nonempty convex domain. -/
theorem zero_bound_forces_equality (f : Euclidean 2 → Euclidean 3)
    (hd : ∀ x, DifferentiableAt ℝ f x) (hb : ∀ x, ‖fderiv ℝ f x‖ ≤ 0)
    (x y : Euclidean 2) : f x = f y := by
  have h := pma9_19.1 2 3 f univ 0 isOpen_univ convex_univ
    (fun z _ => hd z) (fun z _ => hb z) x (mem_univ _) y (mem_univ _)
  have hz : ‖f y-f x‖ = 0 := le_antisymm (by simpa using h) (norm_nonneg _)
  exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm

end Rudin.PMA.Chapter09.FidelityProbes
