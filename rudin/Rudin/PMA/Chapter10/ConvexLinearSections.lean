import Rudin.PMA.Chapter10.ConvexSections
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
open Set Function Filter TopologicalSpace
open scoped Topology Manifold

namespace Rudin.PMA.Chapter10

/-- A linear projection with a continuous linear right inverse has a C¹ section
whose image stays in any prescribed convex open set. The section is defined on
the whole projected open domain, including unbounded and nonproduct domains. -/
lemma exists_contDiffOn_linear_section
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (P : X →L[ℝ] Y) (J : Y →L[ℝ] X) (hPJ : Function.RightInverse J P)
    {E : Set X} (hE : IsOpen E) (hc : Convex ℝ E) :
    ∃ s : Y → X, ContDiffOn ℝ 1 s (P '' E) ∧
      ∀ y ∈ P '' E, s y ∈ E ∧ P (s y) = y := by
  classical
  let U : Opens Y := ⟨P '' E, P.isOpenMap hPJ.surjective E hE⟩
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let t : U → Set X := fun y => {x | x ∈ E ∧ P x = (y : Y)}
  have ht : ∀ y : U, Convex ℝ (t y) := by
    intro y x hx z hz a b ha hb hab
    refine ⟨hc hx.1 hz.1 ha hb hab, ?_⟩
    simp only [map_add, map_smul, hx.2, hz.2, ← add_smul, hab, one_smul]
  have hloc : ∀ y : U, ∃ W ∈ 𝓝 y, ∃ g : U → X,
      ContMDiffOn 𝓘(ℝ, Y) 𝓘(ℝ, X) 1 g W ∧ ∀ z ∈ W, g z ∈ t z := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    let G : Y → X := fun z => x + J (z - y)
    have hG : ContDiff ℝ 1 G := by dsimp [G]; fun_prop
    have hGy : G y = x := by simp [G]
    let W : Set U := {z | G z ∈ E}
    have hW : W ∈ 𝓝 y :=
      (hG.continuous.comp continuous_subtype_val).continuousAt.eventually
        (hE.mem_nhds (by change G y ∈ E; rw [hGy]; exact hx))
    refine ⟨W, hW, fun z => G z, ?_, ?_⟩
    · exact (hG.contMDiff.comp contMDiff_subtype_val).contMDiffOn
    · intro z hz
      refine ⟨hz, ?_⟩
      change P (x + J ((z : Y) - y)) = (z : Y)
      rw [map_add, hPJ, hxy]
      abel
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local
    (𝓘(ℝ, Y)) (n := 1) ht hloc
  let s : Y → X := fun y => if hy : y ∈ U then g ⟨y, hy⟩ else 0
  have he : (fun y : U => s y) = g := by
    funext y
    simp only [s, dif_pos y.property]
  refine ⟨s, ?_, ?_⟩
  · intro y hy
    have hd : ContMDiffAt 𝓘(ℝ, Y) 𝓘(ℝ, X) 1 (fun z : U => s z) (⟨y, hy⟩ : U) := by
      rw [he]
      exact g.contMDiff _
    exact (contMDiffAt_subtype_iff.mp hd).contDiffAt.contDiffWithinAt
  · intro y hy
    have hyU : y ∈ U := hy
    simpa only [s, dif_pos hyU, t, mem_setOf_eq] using hg (⟨y, hyU⟩ : U)

end Rudin.PMA.Chapter10
