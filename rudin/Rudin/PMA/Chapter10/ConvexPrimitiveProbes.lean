import Rudin.PMA.Chapter10.ConvexPrimitives

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def stripProjection : Euclidean 3 →L[ℝ] ℝ :=
  EuclideanSpace.proj 1 - EuclideanSpace.proj 0

def slantedStrip : Set (Euclidean 3) := stripProjection ⁻¹' Ioo (0 : ℝ) 1

private lemma slantedStrip_open : IsOpen slantedStrip :=
  isOpen_Ioo.preimage stripProjection.continuous

private lemma slantedStrip_convex : Convex ℝ slantedStrip :=
  (convex_Ioo (0 : ℝ) 1).linear_preimage stripProjection.toLinearMap

/-- The moving strip has no common second-coordinate basepoint for all
first coordinates. The source theorem still gives a global primitive and
preserves independence of the third coordinate. -/
theorem primitive_on_moving_strip (f : Euclidean 3 → ℝ)
    (hf : ContDiffOn ℝ 1 f slantedStrip)
    (h2 : ∀ x ∈ slantedStrip, coordinatePartial f x 2 = 0) :
    (¬ ∃ b : ℝ, ∀ a : ℝ, coordEquivEuclidean 3 ![a, b, 0] ∈ slantedStrip) ∧
    ∃ F : Euclidean 3 → ℝ, ContDiffOn ℝ 1 F slantedStrip ∧
      (∀ x ∈ slantedStrip, coordinatePartial F x 1 = f x) ∧
      (∀ x ∈ slantedStrip, coordinatePartial F x 2 = 0) := by
  constructor
  · rintro ⟨b, hb⟩
    have h := hb b
    have he (x : Coord 3) (i : Fin 3) : (coordEquivEuclidean 3 x) i = x i := rfl
    norm_num [slantedStrip, stripProjection, ContinuousLinearMap.sub_apply,
      EuclideanSpace.coe_proj, he] at h
  · have hz : ∀ x ∈ slantedStrip, ∀ j : Fin 3, (1 : Fin 3) < j →
        coordinatePartial f x j = 0 := by
      intro x hx j hj
      have he : j = 2 := by fin_cases j <;> simp_all
      subst j
      exact h2 x hx
    obtain ⟨F, hF, hp, hl⟩ := pma10_38 3 slantedStrip f 1
      slantedStrip_open slantedStrip_convex hf hz
    exact ⟨F, hF, hp, fun x hx => hl x hx 2 (by decide)⟩

/-- At the first coordinate the section base has dimension zero. No later
partial premise exists in dimension one, even on an unbounded domain. -/
theorem first_coordinate_primitive_on_positive_ray (f : Euclidean 1 → ℝ)
    (hf : ContDiffOn ℝ 1 f {x | 0 < x 0}) :
    ∃ F : Euclidean 1 → ℝ, ContDiffOn ℝ 1 F {x | 0 < x 0} ∧
      ∀ x : Euclidean 1, 0 < x 0 → coordinatePartial F x 0 = f x := by
  have hE : IsOpen {x : Euclidean 1 | 0 < x 0} :=
    isOpen_lt continuous_const (EuclideanSpace.proj 0).continuous
  have hc : Convex ℝ {x : Euclidean 1 | 0 < x 0} := by
    exact (convex_Ioi (0 : ℝ)).linear_preimage
      (EuclideanSpace.proj 0 : Euclidean 1 →L[ℝ] ℝ).toLinearMap
  obtain ⟨F, hF, hp, _⟩ := pma10_38 1 {x | 0 < x 0} f 0 hE hc hf (by
    intro x hx j hj
    fin_cases j
    exact (lt_irrefl (0 : Fin 1) hj).elim)
  exact ⟨F, hF, hp⟩

end Rudin.PMA.Chapter10.FidelityProbes
