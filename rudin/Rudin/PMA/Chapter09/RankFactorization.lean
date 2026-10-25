import Rudin.PMA.Chapter09.FirstHalf
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

/-!
Auxiliary local factorization facts for the rank theorem (9.32). A C¹ map whose
derivative vanishes in the kernel of a linear map is constant on its convex fibers.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace Rudin.PMA.Chapter09

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem rankSupport_constant_on_fibers {V : Set X} (hV : IsOpen V) (hVc : Convex ℝ V)
    {ψ : X → Y} (hψ : ContDiffOn ℝ 1 ψ V) (A : X →L[ℝ] Z)
    (hker : ∀ x ∈ V, ∀ v, A v = 0 → fderiv ℝ ψ x v = 0)
    {x y : X} (hx : x ∈ V) (hy : y ∈ V) (hxy : A x = A y) : ψ x = ψ y := by
  let γ : ℝ → X := fun t => x + t • (y - x)
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ V :=
    hVc.add_smul_sub_mem hx hy ht
  have hd (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (ψ ∘ γ) 0 (Icc (0 : ℝ) 1) t := by
    have hl : HasDerivAt γ (y - x) t := by
      simpa [γ] using ((hasDerivAt_id t).smul_const (y - x)).const_add x
    have hp := ((hψ.contDiffAt (hV.mem_nhds (hγ t ht))).differentiableAt
      (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt.comp_hasDerivAt t hl
    rw [hker _ (hγ t ht) _ (by simp [map_sub, hxy])] at hp
    exact hp.hasDerivWithinAt
  have hn := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd (fun _ _ => le_rfl) (by simp : (0 : ℝ) ∈ Icc 0 1)
      (by simp : (1 : ℝ) ∈ Icc 0 1)
  simpa [γ, Function.comp_def, norm_le_zero_iff, sub_eq_zero, eq_comm] using hn

/-- A continuous linear right inverse makes the image of an open set open. -/
theorem rankSupport_isOpen_image (A : X →L[ℝ] Z) (S : Z →L[ℝ] X)
    (hAS : ∀ z, A (S z) = z) {V : Set X} (hV : IsOpen V) : IsOpen (A '' V) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨x, hx, rfl⟩
  let L : Z → X := fun w => x + S (w - A x)
  have hL : ContinuousAt L (A x) := by fun_prop
  have hLself : L (A x) = x := by simp [L]
  have ht : ∀ᶠ w in 𝓝 (A x), L w ∈ V :=
    hL.preimage_mem_nhds (hLself.symm ▸ hV.mem_nhds hx)
  filter_upwards [ht] with w hw
  refine ⟨L w, hw, ?_⟩
  simp [L, hAS]

/-- C¹ descent through a split linear map on an open convex domain. The
extension away from the image is chosen to be zero. -/
theorem rankSupport_factorization (A : X →L[ℝ] Z) (S : Z →L[ℝ] X)
    (hAS : ∀ z, A (S z) = z) {V : Set X} (hV : IsOpen V) (hVc : Convex ℝ V)
    {ψ : X → Y} (hψ : ContDiffOn ℝ 1 ψ V)
    (hker : ∀ x ∈ V, ∀ v, A v = 0 → fderiv ℝ ψ x v = 0) :
    ∃ φ : Z → Y, ContDiffOn ℝ 1 φ (A '' V) ∧
      (∀ x ∈ V, ψ x = φ (A x)) ∧ (∀ z ∉ A '' V, φ z = 0) := by
  classical
  let φ : Z → Y := fun z => if hz : z ∈ A '' V then ψ (Classical.choose hz) else 0
  have hfactor (x : X) (hx : x ∈ V) : ψ x = φ (A x) := by
    have hz : A x ∈ A '' V := ⟨x, hx, rfl⟩
    dsimp [φ]
    rw [dite_eq_left hz]
    exact rankSupport_constant_on_fibers hV hVc hψ A hker hx
      (Classical.choose_spec hz).1 (Classical.choose_spec hz).2.symm
  refine ⟨φ, ?_, hfactor, ?_⟩
  · rintro z ⟨x, hx, rfl⟩
    let L : Z → X := fun w => x + S (w - A x)
    have hLc : ContDiff ℝ 1 L := by fun_prop
    have hLself : L (A x) = x := by simp [L]
    have hAL (w : Z) : A (L w) = w := by simp [L, hAS]
    have ht : ∀ᶠ w in 𝓝 (A x), L w ∈ V :=
      hLc.continuous.continuousAt.preimage_mem_nhds
        (hLself.symm ▸ hV.mem_nhds hx)
    have heq : φ =ᶠ[𝓝 (A x)] ψ ∘ L := by
      filter_upwards [ht] with w hw
      rw [Function.comp_apply, hfactor (L w) hw, hAL]
    have hcomp : ContDiffAt ℝ 1 (ψ ∘ L) (A x) := by
      apply ContDiffAt.comp (A x) _ hLc.contDiffAt
      rw [hLself]
      exact hψ.contDiffAt (hV.mem_nhds hx)
    exact (hcomp.congr_of_eventuallyEq heq).contDiffWithinAt
  · intro z hz
    dsimp only [φ]
    rw [dite_eq_right hz]

end Rudin.PMA.Chapter09
