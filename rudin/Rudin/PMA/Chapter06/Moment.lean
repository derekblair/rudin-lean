import Rudin.PMA.Chapter06.Jump
import Rudin.PMA.Chapter06.Calculus

open Set

noncomputable section

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.18: Native quadratic moments, including the derivative-density formula. -/

theorem quadraticMoment_density {m ρ : ℝ → ℝ}
    (hm : MonotoneOn m (Icc (0 : ℝ) 1))
    (hder : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt m (ρ x) (Icc (0 : ℝ) 1) x)
    (hρ : RIntegrable ρ 0 1) :
    RIntegrable (fun x => x ^ 2 * ρ x) 0 1 ∧
    RSIntegral QuadraticPosition m 0 1 = RIntegral (fun x => x ^ 2 * ρ x) 0 1 := by
  have hbound : BoundedOn QuadraticPosition 0 1 := by
    refine ⟨1, ?_⟩
    intro x hx
    dsimp only [QuadraticPosition]
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [hx.1, hx.2]
  have hi := quadraticMoment_integrable hm
  have hd := pma6_17 QuadraticPosition m ρ 0 1 (by norm_num) hm hder hρ hbound
  exact ⟨hd.1.mp hi, hd.2 hi⟩

theorem pma6_18 : pma6_18_contract := by
  refine ⟨fun m hm => quadraticMoment_integrable hm, ?_, ?_, ?_⟩
  · intro m ρ hm hder hρ
    exact quadraticMoment_density hm hder hρ
  · intro s c hs _ hnonneg hc
    exact atomicQuadraticMoment hs hc hnonneg
  · intro n s c hs _ hnonneg
    exact finiteAtomicQuadraticMoment hs hnonneg

#print axioms quadraticMoment_density
#print axioms pma6_18

end Rudin.PMA.Chapter06
