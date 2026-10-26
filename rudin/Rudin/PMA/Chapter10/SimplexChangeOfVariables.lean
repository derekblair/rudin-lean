import Rudin.PMA.Chapter10.Simplex
import Mathlib.MeasureTheory.Function.Jacobian

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory

namespace Rudin.PMA.Chapter10

/-- Native simplex integrals are invariant under a differentiable self-change
of coordinates of absolute Jacobian one. Native existence is established before
the measure-integral change-of-variables bridge is used. -/
lemma simplexRIntegral_comp_of_abs_det_one {k : ℕ} {A : Coord k → Coord k}
    {A' : Coord k → Coord k →L[ℝ] Coord k}
    (hA : ContinuousOn A (standardSimplex k))
    (hd : ∀ x ∈ standardSimplex k, HasFDerivWithinAt A (A' x) (standardSimplex k) x)
    (hinj : InjOn A (standardSimplex k))
    (himage : A '' standardSimplex k = standardSimplex k)
    (hdet : ∀ x ∈ standardSimplex k, |(A' x).det| = 1)
    {f : Coord k → ℝ} (hf : ContinuousOn f (standardSimplex k)) :
    IteratedRIntegrable (Cell.unit k) (simplexExtension (f ∘ A)) ∧
      simplexRIntegral (f ∘ A) = simplexRIntegral f := by
  have hAS : MapsTo A (standardSimplex k) (standardSimplex k) := by
    intro x hx
    rw [← himage]
    exact mem_image_of_mem A hx
  have hc := hf.comp hA hAS
  refine ⟨simplex_iteratedRIntegrable hc, ?_⟩
  rw [simplexRIntegral_eq_integral hc, simplexRIntegral_eq_integral hf]
  have he := integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_standardSimplex k).measurableSet hd hinj f
  rw [himage] at he
  rw [he]
  apply setIntegral_congr_fun (isClosed_standardSimplex k).measurableSet
  intro x hx
  simp only [hdet x hx, one_smul, Function.comp_apply]

end Rudin.PMA.Chapter10
