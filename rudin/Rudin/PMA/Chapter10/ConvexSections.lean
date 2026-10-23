import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

noncomputable section
set_option autoImplicit false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold

namespace Rudin.PMA.Chapter10

/-- A convex open family of nonempty fibers over an open finite-dimensional
base has a global C¹ section. This supplies the nonconstant integration endpoint
needed in source10.38; it is obtained from smooth partitions of unity. -/
lemma exists_contDiffOn_convex_section
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Opens X) {V : Set (X × Y)} (hV : IsOpen V) (hc : Convex ℝ V)
    (hne : ∀ x ∈ U, ∃ y : Y, (x, y) ∈ V) :
    ∃ g : X → Y, ContDiffOn ℝ 1 g U ∧ ∀ x ∈ U, (x, g x) ∈ V := by
  classical
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let t : U → Set Y := fun x => {y | ((x : X), y) ∈ V}
  have ht : ∀ x : U, Convex ℝ (t x) := by
    intro x y hy z hz a b ha hb hab
    have hm := hc hy hz ha hb hab
    change (a • (x : X) + b • (x : X), a • y + b • z) ∈ V at hm
    rw [← add_smul, hab, one_smul] at hm
    exact hm
  have hloc : ∀ x : U, ∃ c : Y, ∀ᶠ y in 𝓝 x, c ∈ t y := by
    intro x
    obtain ⟨c, hc⟩ := hne x x.property
    refine ⟨c, ?_⟩
    have hpre : IsOpen ((fun y : U => ((y : X), c)) ⁻¹' V) :=
      hV.preimage (continuous_subtype_val.prodMk continuous_const)
    exact hpre.mem_nhds hc
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const
    (𝓘(ℝ, X)) (n := 1) ht hloc
  let F : X → Y := fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0
  have he : (fun x : U => F x) = g := by
    funext x
    simp only [F, dif_pos x.property]
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    have hd : ContMDiffAt 𝓘(ℝ, X) 𝓘(ℝ, Y) 1 (fun y : U => F y) (⟨x, hx⟩ : U) := by
      rw [he]
      exact g.contMDiff _
    exact (contMDiffAt_subtype_iff.mp hd).contDiffAt.contDiffWithinAt
  · intro x hx
    simpa only [F, dif_pos hx, t, mem_setOf_eq] using hg (⟨x, hx⟩ : U)

end Rudin.PMA.Chapter10
