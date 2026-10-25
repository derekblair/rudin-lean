import Rudin.PMA.Chapter09.FirstHalf
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

/-!
## Chapter 9, nodes 9.26–9.29: implicit functions

Products represent the book's concatenated coordinate vectors. The general results
are stated for real Banach spaces, which includes the finite-dimensional cases.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Rudin.PMA.Chapter09

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- 9.26: restriction of a linear map to the first coordinate block. -/
def pma9_26_x (A : X × Y →L[ℝ] Z) : X →L[ℝ] Z :=
  A ∘L ContinuousLinearMap.inl ℝ X Y

/-- 9.26: restriction of a linear map to the second coordinate block. -/
def pma9_26_y (A : X × Y →L[ℝ] Z) : Y →L[ℝ] Z :=
  A ∘L ContinuousLinearMap.inr ℝ X Y

/-- 9.26, equation (54): the two block restrictions reconstruct the map. -/
theorem pma9_26 (A : X × Y →L[ℝ] Z) (h : X) (k : Y) :
    A (h, k) = pma9_26_x A h + pma9_26_y A k := by
  change A (h, k) = A (h, 0) + A (0, k)
  rw [← map_add]
  simp

/-- 9.27: the linear implicit equation has exactly one solution, given by (55). -/
theorem pma9_27 (A : X × Y →L[ℝ] X) (hA : (pma9_26_x A).IsInvertible)
    (k : Y) :
    (∀ h, A (h, k) = 0 ↔ h = -(pma9_26_x A).inverse (pma9_26_y A k)) ∧
      ∃! h, A (h, k) = 0 := by
  have heq (h : X) : A (h, k) = 0 ↔
      h = -(pma9_26_x A).inverse (pma9_26_y A k) := by
    rw [pma9_26, add_eq_zero_iff_eq_neg]
    constructor
    · intro hh
      have := congrArg (pma9_26_x A).inverse hh
      simpa only [hA.inverse_apply_self, map_neg] using this
    · intro hh
      rw [hh, map_neg, hA.self_apply_inverse]
  exact ⟨heq, ⟨_, (heq _).mpr rfl, fun h hh => (heq h).mp hh⟩⟩

variable [CompleteSpace X] [CompleteSpace Y]

/-- 9.28: a local, unique C¹ implicit graph and its derivative.

The product-space/Banach-space formulation generalizes the book's coordinate
notation. `A` is the derivative at the base point, and invertibility is expressed
by `ContinuousLinearMap.IsInvertible`, without any extra regularity assumption.
-/
theorem pma9_28 {f : X × Y → X} {s : Set (X × Y)} {a : X} {b : Y}
    (hs : IsOpen s) (hab : (a, b) ∈ s) (hf : ContDiffOn ℝ 1 f s)
    (hzero : f (a, b) = 0) (A : X × Y →L[ℝ] X)
    (hderiv : HasFDerivAt f A (a, b)) (hA : (pma9_26_x A).IsInvertible) :
    ∃ (U : Set (X × Y)) (W : Set Y) (g : Y → X),
      IsOpen U ∧ IsOpen W ∧ (a, b) ∈ U ∧ b ∈ W ∧ U ⊆ s ∧
      ContDiffOn ℝ 1 g W ∧ g b = a ∧
      (∀ y ∈ W, (g y, y) ∈ U ∧ f (g y, y) = 0) ∧
      (∀ y ∈ W, ∃! x, (x, y) ∈ U ∧ f (x, y) = 0) ∧
      HasFDerivAt g (-(pma9_26_x A).inverse ∘L pma9_26_y A) b := by
  let F : Y × X → X := fun p => f (p.2, p.1)
  have hc : ContDiffAt ℝ 1 F (b, a) :=
    (hf.contDiffAt (hs.mem_nhds hab)).comp (b, a)
      (contDiffAt_snd.prodMk contDiffAt_fst)
  have hdF : fderiv ℝ F (b, a) = A ∘L (ContinuousLinearEquiv.prodComm ℝ Y X).toContinuousLinearMap :=
    (hderiv.comp (b, a) ((ContinuousLinearEquiv.prodComm ℝ Y X).toContinuousLinearMap).hasFDerivAt).fderiv
  have hxF : fderiv ℝ F (b, a) ∘L ContinuousLinearMap.inr ℝ Y X = pma9_26_x A := by
    rw [hdF]
    ext x
    rfl
  have hyF : fderiv ℝ F (b, a) ∘L ContinuousLinearMap.inl ℝ Y X = pma9_26_y A := by
    rw [hdF]
    ext y
    rfl
  have hInv : (fderiv ℝ F (b, a) ∘L ContinuousLinearMap.inr ℝ Y X).IsInvertible :=
    hxF.symm ▸ hA
  let g : Y → X := hc.implicitFunction (by norm_num) hInv
  have hgb : g b = a := hc.implicitFunction_apply_self (by norm_num) hInv
  have hgC : ContDiffAt ℝ 1 g b := hc.contDiffAt_implicitFunction (by norm_num) hInv
  have hgD : HasFDerivAt g (-(pma9_26_x A).inverse ∘L pma9_26_y A) b := by
    simpa only [hxF, hyF] using
      (hc.hasStrictFDerivAt_implicitFunction (by norm_num) hInv).hasFDerivAt
  have huniq : ∀ᶠ p : X × Y in 𝓝 (a, b), f p = 0 ↔ g p.2 = p.1 := by
    have ht := (continuous_swap.tendsto (a, b)).eventually
      (hc.eventually_apply_eq_iff_implicitFunction (by norm_num) hInv)
    simpa [F, hzero] using ht
  obtain ⟨U, hUsub, hUopen, habU⟩ := mem_nhds_iff.mp
    (inter_mem (hs.mem_nhds hab) huniq)
  have hgraph : ContinuousAt (fun y => (g y, y)) b :=
    hgC.continuousAt.prodMk continuousAt_id
  have hgraphU : ∀ᶠ y in 𝓝 b, (g y, y) ∈ U := by
    have := hgraph.preimage_mem_nhds (show U ∈ 𝓝 (g b, b) by
      rw [hgb]
      exact hUopen.mem_nhds habU)
    exact this
  obtain ⟨W, hWsub, hWopen, hbW⟩ := mem_nhds_iff.mp
    (hgraphU.and (hgC.eventually (by norm_num)))
  have hgzero (y : Y) (hy : y ∈ W) : f (g y, y) = 0 :=
    (hUsub (hWsub hy).1).2.mpr rfl
  refine ⟨U, W, g, hUopen, hWopen, habU, hbW,
    fun p hp => (hUsub hp).1,
    fun y hy => (hWsub hy).2.contDiffWithinAt, hgb,
    fun y hy => ⟨(hWsub hy).1, hgzero y hy⟩, ?_, hgD⟩
  intro y hy
  refine ⟨g y, ⟨(hWsub hy).1, hgzero y hy⟩, ?_⟩
  intro x hx
  exact ((hUsub hx.1).2.mp hx.2).symm

/-! ### 9.29: the explicit two-equation example -/

/-- 9.29: coordinates are `((x₁,x₂),(y₁,(y₂,y₃)))`. -/
def pma9_29_f (p : (ℝ × ℝ) × (ℝ × ℝ × ℝ)) : ℝ × ℝ :=
  (2 * Real.exp p.1.1 + p.1.2 * p.2.1 - 4 * p.2.2.1 + 3,
   p.1.2 * Real.cos p.1.1 - 6 * p.1.1 + 2 * p.2.1 - p.2.2.2)

/-- 9.29: the displayed two-by-five derivative matrix, as a linear map. -/
def pma9_29_A : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) →L[ℝ] ℝ × ℝ where
  toFun p := (2 * p.1.1 + 3 * p.1.2 + p.2.1 - 4 * p.2.2.1,
    -6 * p.1.1 + p.1.2 + 2 * p.2.1 - p.2.2.2)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  cont := by fun_prop

/-- 9.29: the inverse of the first two-column block. -/
def pma9_29_B : (ℝ × ℝ) →L[ℝ] ℝ × ℝ where
  toFun p := ((p.1 - 3 * p.2) / 20, (6 * p.1 + 2 * p.2) / 20)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  cont := by fun_prop

/-- 9.29: the six entries of the derivative of the implicit function. -/
def pma9_29_D : (ℝ × ℝ × ℝ) →L[ℝ] ℝ × ℝ where
  toFun p := (p.1 / 4 + p.2.1 / 5 - 3 * p.2.2 / 20,
    -p.1 / 2 + 6 * p.2.1 / 5 + p.2.2 / 10)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' c p := by ext <;> simp <;> ring
  cont := by fun_prop

theorem pma9_29_zero : pma9_29_f ((0, 1), (3, 2, 7)) = 0 := by
  norm_num [pma9_29_f]

theorem pma9_29_contDiff : ContDiff ℝ 1 pma9_29_f := by
  unfold pma9_29_f
  fun_prop

theorem pma9_29_hasFDerivAt :
    HasFDerivAt pma9_29_f pma9_29_A ((0, 1), (3, 2, 7)) := by
  let p : (ℝ × ℝ) × (ℝ × ℝ × ℝ) := ((0, 1), (3, 2, 7))
  let L₁ : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L ContinuousLinearMap.fst ℝ _ _
  let L₂ : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ) ∘L ContinuousLinearMap.fst ℝ _ _
  let L₃ : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ _) ∘L ContinuousLinearMap.snd ℝ _ _
  let L₄ : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ) ∘L (ContinuousLinearMap.snd ℝ ℝ _) ∘L
      ContinuousLinearMap.snd ℝ _ _
  let L₅ : ((ℝ × ℝ) × (ℝ × ℝ × ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ) ∘L (ContinuousLinearMap.snd ℝ ℝ _) ∘L
      ContinuousLinearMap.snd ℝ _ _
  have hd := (((L₁.hasFDerivAt (x := p)).exp.const_mul 2).add
    ((L₂.hasFDerivAt (x := p)).mul (L₃.hasFDerivAt (x := p)))).sub
      ((L₄.hasFDerivAt (x := p)).const_mul 4)
  have hd' := ((((L₂.hasFDerivAt (x := p)).mul (L₁.hasFDerivAt (x := p)).cos).sub
    ((L₁.hasFDerivAt (x := p)).const_mul 6)).add
      ((L₃.hasFDerivAt (x := p)).const_mul 2)).sub (L₅.hasFDerivAt (x := p))
  convert! (hd.add_const 3).prodMk hd' using 1
  apply ContinuousLinearMap.ext
  intro q
  apply Prod.ext <;> simp [L₁, L₂, L₃, L₄, L₅, p, pma9_29_A] <;> ring

theorem pma9_29_invertible : (pma9_26_x pma9_29_A).IsInvertible := by
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := pma9_29_B)
  · ext <;> simp [pma9_26_x, pma9_29_A, pma9_29_B] <;> ring
  · ext <;> simp [pma9_26_x, pma9_29_A, pma9_29_B] <;> ring

theorem pma9_29_derivative_formula :
    -(pma9_26_x pma9_29_A).inverse ∘L pma9_26_y pma9_29_A = pma9_29_D := by
  apply ContinuousLinearMap.ext
  intro p
  have h := pma9_29_invertible.inverse_apply_eq
    (x := -pma9_29_D p) (y := pma9_26_y pma9_29_A p)
  have hcalc : pma9_26_y pma9_29_A p = pma9_26_x pma9_29_A (-pma9_29_D p) := by
    ext <;> simp [pma9_26_y, pma9_26_x, pma9_29_A, pma9_29_D] <;> ring
  have hh := h.mpr hcalc
  simpa using congrArg Neg.neg hh

/-- 9.29: the example has the asserted local C¹ solution, with all six
displayed derivative coefficients encoded in `pma9_29_D`. -/
theorem pma9_29 :
    ∃ (U : Set ((ℝ × ℝ) × (ℝ × ℝ × ℝ))) (W : Set (ℝ × ℝ × ℝ))
      (g : (ℝ × ℝ × ℝ) → ℝ × ℝ),
      IsOpen U ∧ IsOpen W ∧ ((0, 1), (3, 2, 7)) ∈ U ∧ (3, 2, 7) ∈ W ∧
      ContDiffOn ℝ 1 g W ∧ g (3, 2, 7) = (0, 1) ∧
      (∀ y ∈ W, (g y, y) ∈ U ∧ pma9_29_f (g y, y) = 0) ∧
      (∀ y ∈ W, ∃! x, (x, y) ∈ U ∧ pma9_29_f (x, y) = 0) ∧
      HasFDerivAt g pma9_29_D (3, 2, 7) := by
  obtain ⟨U, W, g, hU, hW, ha, hb, _, hc, hg, hz, hu, hd⟩ :=
    pma9_28 isOpen_univ (mem_univ _) pma9_29_contDiff.contDiffOn pma9_29_zero
      pma9_29_A pma9_29_hasFDerivAt pma9_29_invertible
  exact ⟨U, W, g, hU, hW, ha, hb, hc, hg, hz, hu, pma9_29_derivative_formula ▸ hd⟩

end Rudin.PMA.Chapter09
