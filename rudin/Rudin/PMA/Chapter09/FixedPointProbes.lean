import Rudin.PMA.Chapter09.FixedPoint

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped NNReal

namespace Rudin.PMA.Chapter09.FidelityProbes

/-- A signed contraction coefficient on a degenerate metric space must still
normalize to the nonnegative Mathlib convention. -/
theorem singleton_negative_constant_normalizes (X : Type*) [MetricSpace X]
    [Subsingleton X] : ∃ c : ℝ≥0, ContractingWith c (id : X → X) := by
  apply (pma9_22 X id).1.mp
  refine ⟨-1, by norm_num, ?_⟩
  intro x y
  have hxy : x = y := Subsingleton.elim _ _
  simp [hxy]

/-- The strict constant bound must exclude the identity on the real line. -/
theorem real_identity_not_contraction : ¬ IsContraction (id : ℝ → ℝ) := by
  rintro ⟨c, hc, hd⟩
  have h := hd 0 1
  norm_num [Real.dist_eq] at h
  linarith

private theorem affine_contraction : IsContraction (fun x : ℝ => x / 2 + 3) := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro x y
  simp only [Real.dist_eq]
  have he : x / 2 + 3 - (y / 2 + 3) = (x - y) / 2 := by ring
  rw [he, abs_div]
  norm_num
  ring_nf
  exact le_rfl

/-- All starting points converge to the actual affine fixed point, rather than
merely to an unnamed limit supplied by existence. -/
theorem affine_iterates_converge_to_six (x : ℝ) :
    Tendsto (fun n : ℕ => (fun y : ℝ => y / 2 + 3)^[n] x) atTop (𝓝 6) := by
  obtain ⟨p, hp, _, ht⟩ := pma9_23 ℝ (fun y : ℝ => y / 2 + 3) affine_contraction
  have hp6 : p = 6 := by linarith
  simpa only [hp6] using ht x

/-- The zero contraction constant is included, and its unique limit is the
chosen point even when that point is not zero. -/
theorem constant_iterates_converge (X : Type*) [MetricSpace X] [CompleteSpace X]
    (c x : X) : Tendsto (fun n : ℕ => (fun _ : X => c)^[n] x) atTop (𝓝 c) := by
  letI : Nonempty X := ⟨c⟩
  have hc : IsContraction (fun _ : X => c) := by
    refine ⟨0, by norm_num, ?_⟩
    intro y z
    simp
  obtain ⟨p, _, hu, ht⟩ := pma9_23 X (fun _ : X => c) hc
  have he : c = p := hu c rfl
  simpa only [← he] using ht x

end Rudin.PMA.Chapter09.FidelityProbes
