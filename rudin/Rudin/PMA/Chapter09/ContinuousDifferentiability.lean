import Mathlib

/-!
# PMA 9.19–9.22: continuous differentiability and contractions

Functions on open sets are represented by arbitrary total extensions; all
hypotheses and conclusions are local to the given set. Nodes 9.19 and 9.20
are generalized from Euclidean spaces to real normed spaces. No additional
hypothesis is imposed on the Euclidean instances in the book.
-/

noncomputable section
open Set Filter
open scoped Topology BigOperators NNReal ContDiff

namespace Rudin.PMA.Chapter09

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- PMA 9.19: the derivative bound implies the same Lipschitz bound.
Generalization: openness is unnecessary when differentiability at every point
of the convex set is assumed explicitly. -/
theorem pma9_19 {f : V → W} {E : Set V} {M : ℝ}
    (hE : Convex ℝ E) (hf : ∀ x ∈ E, DifferentiableAt ℝ f x)
    (hM : ∀ x ∈ E, ‖fderiv ℝ f x‖ ≤ M) {a b : V} (ha : a ∈ E) (hb : b ∈ E) :
    ‖f b - f a‖ ≤ M * ‖b - a‖ :=
  hE.norm_image_sub_le_of_norm_fderiv_le hf hM ha hb

/-- PMA 9.19, attached corollary: zero derivative gives constancy. -/
theorem pma9_19_corollary {f : V → W} {E : Set V}
    (hE : Convex ℝ E) (hf : ∀ x ∈ E, DifferentiableAt ℝ f x)
    (hzero : ∀ x ∈ E, fderiv ℝ f x = 0) {a b : V} (ha : a ∈ E) (hb : b ∈ E) :
    f a = f b := by
  have h := pma9_19 hE hf (M := 0) (fun x hx => by simp [hzero x hx]) ha hb
  have hab : f b = f a := by simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using h
  exact hab.symm

/-- PMA 9.20: differentiable on the domain with a continuous derivative map. -/
def IsC1On (f : V → W) (E : Set V) : Prop :=
  (∀ x ∈ E, DifferentiableAt ℝ f x) ∧ ContinuousOn (fderiv ℝ f) E

/-- PMA 9.20: comparison with Mathlib's C¹ predicate on open domains. -/
theorem pma9_20 {f : V → W} {E : Set V} (hE : IsOpen E) :
    IsC1On f E ↔ ContDiffOn ℝ 1 f E := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from by simp, contDiffOn_succ_iff_fderiv_of_isOpen hE]
  simp only [IsC1On, contDiffOn_zero, WithTop.zero_ne_top, false_implies, true_and]
  apply and_congr_left
  intro _
  constructor
  · exact fun h x hx => (h x hx).differentiableWithinAt
  · exact fun h x hx => (h x hx).differentiableAt (hE.mem_nhds hx)

/-- PMA 9.20: the explicit epsilon-delta description, in operator norm. -/
theorem pma9_20_continuity {f : V → W} {E : Set V} :
    ContinuousOn (fderiv ℝ f) E ↔
      ∀ x ∈ E, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ y ∈ E,
        ‖y - x‖ < δ → ‖fderiv ℝ f y - fderiv ℝ f x‖ < ε := by
  simp only [Metric.continuousOn_iff, dist_eq_norm]

/-- PMA 9.22: Rudin's real contraction factor, including the permitted c < 0
on a space with at most one point. -/
def IsContraction {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ x y, dist (f x) (f y) ≤ c * dist x y

/-- PMA 9.22: exact equivalence to Mathlib's nonnegative contraction factors.
Replacing a negative factor by zero preserves the condition, so this is not
a strengthened definition, including on empty and singleton spaces. -/
theorem pma9_22 {X : Type*} [MetricSpace X] (f : X → X) :
    IsContraction f ↔ ∃ K : ℝ≥0, ContractingWith K f := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨⟨max c 0, le_max_right _ _⟩, ?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · change max c 0 < (1 : ℝ)
      exact max_lt hc zero_lt_one
    · exact (h x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
  · rintro ⟨K, hK⟩
    exact ⟨K, hK.1, hK.2.dist_le_mul⟩

end Rudin.PMA.Chapter09
