import Rudin.PMA.Chapter09.Inverse
import Rudin.PMA.Chapter09.RankSupport
import Rudin.PMA.Chapter09.RankFactorization
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic

noncomputable section
open Set Filter Topology
namespace Rudin.PMA.Chapter09

/-! ## PMA 9.32: constant rank

Real finite-dimensional normed spaces generalize the book's coordinate spaces.
The map into the null space of P is encoded as a map into the ambient codomain
with the explicit assertion that all its values are killed by P.
-/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- PMA 9.32, local graph normal form for a map of constant rank. The source
of H is V, its target is U, and A(V) is open in the range of A. -/
theorem pma9_32 {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) {a : E} (ha : a ∈ s)
    (A : E →L[ℝ] F) (hA : HasFDerivAt f A a)
    (hrank : ∀ x ∈ s, Module.finrank ℝ (fderiv ℝ f x).toLinearMap.range =
      Module.finrank ℝ A.toLinearMap.range)
    (P : F →L[ℝ] F) (hP : ∀ y, P (P y) = P y)
    (hPrange : P.toLinearMap.range = A.toLinearMap.range) :
    ∃ (H : OpenPartialHomeomorph E E) (φ : A.toLinearMap.range → F),
      a ∈ H.target ∧ H.target ⊆ s ∧ Convex ℝ H.source ∧
      ContDiffOn ℝ 1 H H.source ∧ ContDiffOn ℝ 1 H.symm H.target ∧
      IsOpen (A.rangeRestrict '' H.source) ∧
      ContDiffOn ℝ 1 φ (A.rangeRestrict '' H.source) ∧
      (∀ y, P (φ y) = 0) ∧
      (∀ x ∈ H.source, f (H x) = A x + φ (A.rangeRestrict x)) := by
  classical
  obtain ⟨S, hS⟩ := rankSupport_rightInverse A
  let Q : F →L[ℝ] A.toLinearMap.range := P.codRestrict A.toLinearMap.range
    (fun y => hPrange ▸ LinearMap.mem_range_self P.toLinearMap y)
  let T : F →L[ℝ] E := S ∘L Q
  have hAT (y : F) : A (T y) = P y := hS (Q y)
  have hPA (x : E) : P (A x) = A x := by
    have hx : A x ∈ P.toLinearMap.range := hPrange.symm ▸ LinearMap.mem_range_self A.toLinearMap x
    obtain ⟨y, hy⟩ := hx
    change P y = A x at hy
    rw [← hy, hP]
  let G : E → E := fun x => x + T (f x - A x)
  have hGc : ContDiffOn ℝ 1 G s :=
    contDiffOn_id.add (T.contDiff.comp_contDiffOn (hf.sub A.contDiff.contDiffOn))
  have hGd : HasFDerivAt G (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) a := by
    convert (hasFDerivAt_id a).add (T.hasFDerivAt.comp a (hA.sub A.hasFDerivAt)) using 1 <;>
      simp [G, Pi.add_def, Pi.sub_def, Function.comp_def]
  have hAG (x : E) : A (G x) = P (f x) := by
    simp only [G, map_add, hAT, map_sub, hPA]
    abel
  obtain ⟨e, heG, hea, hes, hec⟩ := pma9_24 hs hGc ha
    (ContinuousLinearEquiv.refl ℝ E) hGd
  have heGa : G a ∈ e.target := heG ▸ e.map_source hea
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (G a) heGa
  let H := e.symm.restrOpen (Metric.ball (G a) r) Metric.isOpen_ball
  have hHsource : H.source = Metric.ball (G a) r := by
    change e.target ∩ Metric.ball (G a) r = Metric.ball (G a) r
    exact inter_eq_right.mpr hball
  have haH : a ∈ H.target := by
    change a ∈ e.source ∩ e ⁻¹' Metric.ball (G a) r
    exact ⟨hea, by change dist (e a) (G a) < r; simpa [heG] using hr⟩
  have hHs : H.target ⊆ s := fun _ hx => hes hx.1
  have hHc : ContDiffOn ℝ 1 H H.source := hec.mono (fun _ hx => hx.1)
  have hHic : ContDiffOn ℝ 1 H.symm H.target := by
    change ContDiffOn ℝ 1 e H.target
    rw [heG]
    exact hGc.mono hHs
  have hGinv (x : E) (hx : x ∈ H.source) : G (H x) = x := by
    rw [← heG]
    exact H.left_inv hx
  have hPH (x : E) (hx : x ∈ H.source) : P (f (H x)) = A x := by
    rw [← hAG, hGinv x hx]
  let Φ : E → F := fun x => f (H x)
  have hΦc : ContDiffOn ℝ 1 Φ H.source := hf.comp hHc (fun _ hx => hHs (H.map_source hx))
  have hΦker (x : E) (hx : x ∈ H.source) (v : E) (hv : A v = 0) :
      fderiv ℝ Φ x v = 0 := by
    let D := fderiv ℝ Φ x
    have hDx : HasFDerivAt Φ D x :=
      (hΦc.contDiffAt (H.open_source.mem_nhds hx)).differentiableAt_one.hasFDerivAt
    have hPD : P ∘L D = A := by
      apply HasFDerivAt.unique (P.hasFDerivAt.comp x hDx)
      apply A.hasFDerivAt.congr_of_eventuallyEq
      filter_upwards [H.open_source.mem_nhds hx] with z hz
      exact hPH z hz
    have hfd : HasFDerivAt f (fderiv ℝ f (H x)) (H x) :=
      (hf.contDiffAt (hs.mem_nhds (hHs (H.map_source hx)))).differentiableAt_one.hasFDerivAt
    have hHd := (hHc.contDiffAt (H.open_source.mem_nhds hx)).differentiableAt_one.hasFDerivAt
    have hDeq : D = fderiv ℝ f (H x) ∘L fderiv ℝ H x := hDx.unique (hfd.comp x hHd)
    have hrD : Module.finrank ℝ D.toLinearMap.range = Module.finrank ℝ A.toLinearMap.range := by
      apply le_antisymm
      · rw [hDeq]
        exact (Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)).trans_eq
          (hrank _ (hHs (H.map_source hx)))
      · have hle := Submodule.finrank_map_le P.toLinearMap D.toLinearMap.range
        rw [← LinearMap.range_comp] at hle
        change Module.finrank ℝ (P ∘L D).toLinearMap.range ≤ _ at hle
        rwa [hPD] at hle
    have hker := rankSupport_ker_comp_eq D.toLinearMap P.toLinearMap (by
      change Module.finrank ℝ (P ∘L D).toLinearMap.range = _
      rw [hPD, hrD])
    have hm : v ∈ (P.toLinearMap.comp D.toLinearMap).ker := by
      change (P ∘L D) v = 0
      rw [hPD, hv]
    rw [hker] at hm
    exact hm
  let ψ : E → F := fun x => Φ x - A x
  have hψc : ContDiffOn ℝ 1 ψ H.source := hΦc.sub A.contDiff.contDiffOn
  have hψker (x : E) (hx : x ∈ H.source) (v : E) (hv : A.rangeRestrict v = 0) :
      fderiv ℝ ψ x v = 0 := by
    have hAv : A v = 0 := congrArg Subtype.val hv
    have hd := ((hΦc.contDiffAt (H.open_source.mem_nhds hx)).differentiableAt_one.hasFDerivAt).sub
      (A.hasFDerivAt (x := x))
    change (fderiv ℝ (Φ - ⇑A) x) v = 0
    rw [hd.fderiv]
    change fderiv ℝ Φ x v - A v = 0
    rw [hΦker x hx v hAv, hAv, sub_self]
  have hAS (y : A.toLinearMap.range) : A.rangeRestrict (S y) = y := Subtype.ext (hS y)
  obtain ⟨φ, hφc, hfactor, hφzero⟩ := rankSupport_factorization A.rangeRestrict S hAS
    H.open_source (hHsource.symm ▸ convex_ball (G a) r) hψc hψker
  refine ⟨H, φ, haH, hHs, hHsource.symm ▸ convex_ball (G a) r, hHc, hHic,
    rankSupport_isOpen_image A.rangeRestrict S hAS H.open_source, hφc, ?_, ?_⟩
  · intro y
    by_cases hy : y ∈ A.rangeRestrict '' H.source
    · obtain ⟨x, hx, rfl⟩ := hy
      rw [← hfactor x hx]
      change P (f (H x) - A x) = 0
      rw [map_sub, hPH x hx, hPA, sub_self]
    · rw [hφzero y hy, map_zero]
  · intro x hx
    have h := hfactor x hx
    change f (H x) - A x = φ (A.rangeRestrict x) at h
    rw [← h]
    abel

end Rudin.PMA.Chapter09
