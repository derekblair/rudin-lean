import Rudin.PMA.Chapter09.FirstHalf
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open Set Filter Topology
open scoped NNReal

namespace Rudin.PMA.Chapter09

/-! ## PMA 9.23–9.25: fixed points and local inverses

The analytic theorems are stated for real Banach spaces; real finite-dimensional
coordinate spaces are instances. This generalizes the ambient spaces without
restricting the printed conclusions.
-/

/-- PMA 9.23. A contraction on a nonempty complete metric space has exactly
one fixed point. Deviation: nonemptiness, implicit in the book's choice of an
initial point, is explicit; without it the printed assertion is false. -/
theorem pma9_23 {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : X → X) {K : ℝ≥0} (hf : ContractingWith K f) : ∃! x, f x = x := by
  exact ⟨hf.fixedPoint f, hf.fixedPoint_isFixedPt, fun _ h => hf.fixedPoint_unique h⟩

/-- The iterates used in PMA 9.23 converge to that fixed point. -/
theorem pma9_23_iterates {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    (f : X → X) {K : ℝ≥0} (hf : ContractingWith K f) (x : X) :
    Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 (hf.fixedPoint f)) := by
  exact hf.tendsto_iterate_fixedPoint x

section Inverse
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- PMA 9.24. The open partial homeomorphism packages the open neighborhoods,
injectivity, exact image, both inverse identities, and continuity. Its inverse
is C1 throughout its target, not just at the distinguished point. -/
theorem pma9_24 {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) {a : E} (ha : a ∈ s)
    (A : E ≃L[ℝ] F) (hA : HasFDerivAt f (A : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      (e : E → F) = f ∧ a ∈ e.source ∧ e.source ⊆ s ∧
      ContDiffOn ℝ 1 e.symm e.target := by
  have hfa : ContDiffAt ℝ 1 f a := hf.contDiffAt (hs.mem_nhds ha)
  let e := hfa.toOpenPartialHomeomorph f hA (by norm_num)
  have hea : a ∈ e.source := hfa.mem_toOpenPartialHomeomorph_source hA (by norm_num)
  have hgi : ContDiffAt ℝ 1 e.symm (f a) := hfa.to_localInverse hA (by norm_num)
  obtain ⟨t, ht, hgt⟩ := hgi.contDiffOn le_rfl (by norm_num)
  obtain ⟨v, hvt, hv, hav⟩ := mem_nhds_iff.mp ht
  let e₁ := e.restrOpen s hs
  let e₂ := (e₁.symm.restrOpen v hv).symm
  have ha₁ : a ∈ e₁.source := ⟨hea, ha⟩
  have ha₂ : a ∈ e₂.source := by
    exact ⟨ha₁, hav⟩
  refine ⟨e₂, rfl, ha₂, ?_, ?_⟩
  · intro x hx
    exact hx.1.2
  · intro y hy
    exact (hgt y (hvt hy.2)).mono (fun z hz => hvt hz.2)

/-- The derivative formula (52) for any local inverse from PMA 9.24. -/
theorem pma9_24_inverse_derivative (e : OpenPartialHomeomorph E F)
    {y : F} (hy : y ∈ e.target) (A : E ≃L[ℝ] F)
    (hA : HasFDerivAt e (A : E →L[ℝ] F) (e.symm y)) :
    HasFDerivAt e.symm (A.symm : F →L[ℝ] E) y :=
  e.hasFDerivAt_symm hy hA

/-- PMA 9.25. Every open subset of the domain has open image. -/
theorem pma9_25 {f : E → F} {s : Set E} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s)
    (hinv : ∀ x ∈ s, ∃ A : E ≃L[ℝ] F, HasFDerivAt f (A : E →L[ℝ] F) x)
    {w : Set E} (hw : IsOpen w) (hws : w ⊆ s) : IsOpen (f '' w) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨A, hA⟩ := hinv x (hws hx)
  have hfx := (hf.contDiffAt (hs.mem_nhds (hws hx))).hasStrictFDerivAt' hA
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  rw [← hfx.map_nhds_eq_of_equiv]
  exact Filter.image_mem_map (hw.mem_nhds hx)

end Inverse
end Rudin.PMA.Chapter09
