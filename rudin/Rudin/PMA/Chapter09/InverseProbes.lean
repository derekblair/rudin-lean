import Rudin.PMA.Chapter09.Inverse

set_option autoImplicit false
noncomputable section
open Set Filter Topology

namespace Rudin.PMA.Chapter09.FidelityProbes

/-- The weak inverse theorem produces the inverse derivative at the actual
image point using only continuity of the original derivative at the base. -/
theorem weak_inverse_at_image {n : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → Euclidean n} {a : Euclidean n}
    (hE : IsOpen E) (ha : a ∈ E)
    (hd : ∀ x ∈ E, DifferentiableAt ℝ f x)
    (hc : ContinuousAt (fderiv ℝ f) a)
    (hi : (fderiv ℝ f a).IsInvertible) :
    ∃ g : Euclidean n → Euclidean n,
      g (f a) = a ∧ HasFDerivAt g (fderiv ℝ f a).inverse (f a) := by
  obtain ⟨e, he, hg⟩ := pma9_24.2 n E f a hE ha hd hc hi
  have hefun := he.1
  have haS := he.2.1
  have hfa : f a ∈ e.target := by
    simpa only [← hefun] using e.map_source haS
  have hea : e.symm (f a) = a := by
    simpa only [← hefun] using e.left_inv haS
  refine ⟨e.symm, hea, ?_⟩
  simpa only [hea] using hg (f a) hfa

/-- Local regularity and open images must coexist with failure of global
injectivity; openness cannot accidentally be conflated with a global inverse. -/
theorem open_map_need_not_be_injective :
    ∃ f : Euclidean 2 → Euclidean 2,
      C1On f univ ∧ IsOpenMap f ∧ ¬ Function.Injective f := by
  obtain ⟨f, hf, hi, hn⟩ := pma9_25.2
  refine ⟨f, hf, ?_, hn⟩
  intro U hU
  exact (pma9_25.1 2 univ f isOpen_univ hf (fun x _ => hi x)).1 U hU (subset_univ _)

/-- A local inverse of an arbitrary invertible linear map has the specified
inverse linear derivative. This includes orientation-reversing maps. -/
theorem linear_inverse_derivative {n : ℕ}
    (A : Euclidean n ≃L[ℝ] Euclidean n) (a : Euclidean n) :
    ∃ g : Euclidean n → Euclidean n,
      g (A a) = a ∧ HasFDerivAt g (A.symm : Euclidean n →L[ℝ] Euclidean n) (A a) := by
  have hd : ∀ x ∈ (univ : Set (Euclidean n)), DifferentiableAt ℝ A x :=
    fun _ _ => A.differentiableAt
  have he (x : Euclidean n) : fderiv ℝ A x = A.toContinuousLinearMap :=
    A.hasFDerivAt.fderiv
  have hc : ContinuousAt (fderiv ℝ A) a := by
    convert (continuousAt_const : ContinuousAt
      (fun _ : Euclidean n => A.toContinuousLinearMap) a) using 1
    funext x
    exact he x
  have hi : (fderiv ℝ A a).IsInvertible := by
    rw [he]
    exact ⟨A, rfl⟩
  obtain ⟨g, hg, hdg⟩ := weak_inverse_at_image isOpen_univ (mem_univ a) hd hc hi
  refine ⟨g, hg, ?_⟩
  simpa only [he, ContinuousLinearMap.inverse_equiv] using hdg

end Rudin.PMA.Chapter09.FidelityProbes
