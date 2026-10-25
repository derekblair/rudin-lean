import Rudin.PMA.Chapter09.PartialContinuity
import Rudin.PMA.Chapter09.Differentiation

/-! # PMA 9.21: the continuous-partial-derivative criterion

The auxiliary finite-product proof is transported through a continuous linear
coordinate equivalence. The main statement uses the Euclidean norms and exactly
the partial derivatives defined at 9.16; it does not assume total differentiability
on the right-hand side.
-/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace Rudin.PMA.Chapter09

/-- A shifted line parameter and a replaced coordinate define the same partial derivative. -/
lemma partial_hasDerivAt_update {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {i : Fin m} {j : Fin n} {d : ℝ}
    (h : pma9_16_hasPartial f x i j d) :
    HasDerivAt (fun t => f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) j t)) i)
      d (x j) := by
  change HasDerivAt (fun t : ℝ => f (x + t • pma9_coordinate n j) i) d 0 at h
  have h' : HasDerivAt (fun t : ℝ => f (x + t • pma9_coordinate n j) i) d
      (x j - x j) := by simpa using h
  have hh := h'.comp (h := fun t : ℝ => t - x j) (x j) ((hasDerivAt_id (x j)).sub_const (x j))
  have heq : (fun t : ℝ => f (x + (t - x j) • pma9_coordinate n j) i) =
      (fun t => f (WithLp.toLp 2 (Function.update (WithLp.ofLp x) j t)) i) := by
    funext t
    apply congrArg (fun z : EuclideanSpace ℝ (Fin n) => f z i)
    ext k
    by_cases hk : k = j
    · subst k
      simp [pma9_coordinate, EuclideanSpace.basisFun_apply]
    · simp [pma9_coordinate, EuclideanSpace.basisFun_apply, hk]
  simpa only [Function.comp_def, heq, mul_one] using hh

/-- PMA 9.21: C¹ is equivalent to existence and continuity of every partial derivative. -/
theorem pma9_21 {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : IsOpen E) :
    IsC1On f E ↔
      (∀ x ∈ E, ∀ i j, ∃ d, pma9_16_hasPartial f x i j d) ∧
      (∀ i j, ContinuousOn (fun x => pma9_16_partial f x i j) E) := by
  constructor
  · rintro ⟨hf, hc⟩
    refine ⟨fun x hx i j => ⟨_, pma9_17 (hf x hx).hasFDerivAt i j⟩, ?_⟩
    intro i j
    have heval : ContinuousOn (fun x => (fderiv ℝ f x) (pma9_coordinate n j) i) E := by
      exact (PiLp.proj 2 (fun _ : Fin m => ℝ) i : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ).continuous.comp_continuousOn
        (hc.clm_apply continuousOn_const)
    exact heval.congr (fun x hx => pma9_17_entries (hf x hx).hasFDerivAt i j)
  · rintro ⟨hd, hc⟩
    apply (pma9_20 hE).2
    apply (contDiffOn_piLp 2).2
    intro i
    let e := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm
    let s : Set (Fin n → ℝ) := e ⁻¹' E
    have hs : IsOpen s := hE.preimage e.continuous
    let g : (Fin n → ℝ) → ℝ := fun v => f (e v) i
    let p : Fin n → (Fin n → ℝ) → ℝ := fun j v => pma9_16_partial f (e v) i j
    have hp : ∀ j, ContinuousOn (p j) s := fun j =>
      (hc i j).comp e.continuous.continuousOn (fun _ hv => hv)
    have hdp : ∀ x ∈ s, ∀ j,
        HasDerivAt (fun t => g (Function.update x j t)) (p j x) (x j) := by
      intro x hx j
      obtain ⟨d, hd'⟩ := hd (e x) hx i j
      have heqd : pma9_16_partial f (e x) i j = d := hd'.lineDeriv
      rw [← heqd] at hd'
      exact partial_hasDerivAt_update hd'
    have hg : ContDiffOn ℝ 1 g s := (pma9_20 hs).1
      (isC1On_of_continuous_partials n g s hs p hp hdp)
    have hh := hg.comp e.symm.contDiff.contDiffOn
      (show MapsTo e.symm E s by intro x hx; simpa [s] using hx)
    simpa [g, Function.comp_def] using hh

end Rudin.PMA.Chapter09
