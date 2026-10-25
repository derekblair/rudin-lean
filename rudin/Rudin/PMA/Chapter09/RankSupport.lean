import Rudin.PMA.Chapter09.FirstHalf
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

noncomputable section
open Set
namespace Rudin.PMA.Chapter09

/-- Linear algebra used in PMA 9.32: a projection preserving rank does not
lose any additional information on the range. -/
theorem rankSupport_ker_comp_eq {K E F G : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [AddCommGroup G] [Module K G]
    (A : E →ₗ[K] F) (P : F →ₗ[K] G)
    (h : Module.finrank K (LinearMap.range (P.comp A)) =
      Module.finrank K (LinearMap.range A)) :
    LinearMap.ker (P.comp A) = LinearMap.ker A := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (A.ker_le_ker_comp P)
  have h₁ := A.finrank_range_add_finrank_ker
  have h₂ := (P.comp A).finrank_range_add_finrank_ker
  omega

/-- A linear right inverse on the range, continuous in finite dimension. -/
theorem rankSupport_rightInverse {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) :
    ∃ S : LinearMap.range A.toLinearMap →L[ℝ] E,
      ∀ y, A (S y) = y := by
  obtain ⟨S, hS⟩ := A.toLinearMap.rangeRestrict.exists_rightInverse_of_surjective
    A.toLinearMap.range_rangeRestrict
  refine ⟨S.toContinuousLinearMap, ?_⟩
  intro y
  have h := LinearMap.congr_fun hS y
  exact congrArg Subtype.val h

end Rudin.PMA.Chapter09
