import Rudin.PMA.Chapter10.CoordinateDifferentiation
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- A scalar potential gains one derivative because all of its first partials,
not merely their antisymmetric combinations, are prescribed C¹ functions. -/
lemma contDiffOn_two_of_coordinatePartials {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) {u : Euclidean n → ℝ} (hu : ContDiffOn ℝ 1 u E)
    (hp : ∀ i : Fin n, ContDiffOn ℝ 1 (fun x => coordinatePartial u x i) E) :
    ContDiffOn ℝ 2 u E := by
  apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := 1) hE).mpr
  refine ⟨hu.differentiableOn_one, by simp, contDiffOn_clm_apply.mpr ?_⟩
  intro v
  have hs : ContDiffOn ℝ 1
      (fun x => ∑ i : Fin n, coordinatePartial u x i * v i) E :=
    ContDiffOn.sum (fun i _ => (hp i).mul contDiffOn_const)
  apply hs.congr
  intro x hx
  rw [linear_apply_eq_sum_coordinates]
  have hd := hu.differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  simp_rw [← coordinatePartial_eq_fderiv hd]

lemma contDiffOn_two_of_coordinatePartials_eq {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) {u : Euclidean n → ℝ} (hu : ContDiffOn ℝ 1 u E)
    {F : Euclidean n → Euclidean n} (hF : ContDiffOn ℝ 1 F E)
    (he : ∀ x ∈ E, ∀ i : Fin n, coordinatePartial u x i = F x i) :
    ContDiffOn ℝ 2 u E := by
  apply contDiffOn_two_of_coordinatePartials hE hu
  intro i
  exact ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).contDiff.comp_contDiffOn hF).congr
    (fun x hx => he x hx i)

end Rudin.PMA.Chapter10
