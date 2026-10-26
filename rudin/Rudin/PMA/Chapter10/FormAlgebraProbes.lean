import Rudin.PMA.Chapter10.WedgeProducts
import Rudin.PMA.Chapter10.FormSeparation

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- Two nonsorted two-forms produce a negative top-degree form: the three
inversions include one internal inversion in each factor. -/
theorem nonsorted_two_form_product :
    ∃ S : StandardIndex 4 4,
      range (Set.powersetCard.ofFinEmbEquiv.symm S) = univ ∧
      coordinateWedge (![2, 0] : Fin 2 → Fin 4) *
        coordinateWedge (![3, 1] : Fin 2 → Fin 4) = -standardWedge S := by
  let I : Fin 4 → Fin 4 := ![2, 0, 3, 1]
  have hI : Injective I := by decide
  obtain ⟨S, hS, hw⟩ := pma10_14.2.2.1 4 4 I hI
  have hsign : tupleSign (fun j => ((I j).val : ℤ)) = -1 := by decide
  have hr : range I = univ := by
    ext i
    fin_cases i <;> simp [I, Set.mem_range, Fin.exists_fin_succ]
  refine ⟨S, hS.trans hr, ?_⟩
  rw [pma10_16.1]
  have ha : Fin.append (![2, 0] : Fin 2 → Fin 4) ![3, 1] = I := by
    ext i
    fin_cases i <;> rfl
  rw [ha, hw, hsign]
  simp

/-- A nonzero standard coefficient is detected by an actual admissible
surface, and the detecting integral has native iterated existence. -/
theorem nonzero_coefficient_detected_by_native_integral {n k : ℕ}
    {E : Set (Euclidean n)} {ω : FormField n} (hE : IsOpen E)
    (hω : IsFormOn E k ω) (S : StandardIndex n k) {x : Euclidean n}
    (hx : x ∈ E) (hne : formCoefficient ω S.val x ≠ 0) :
    ∃ Φ : Surface k n E, Φ.domain.Integrable (surfaceIntegrand Φ ω) ∧
      surfaceIntegral Φ ω ≠ 0 := by
  have hz : ¬ FormEqOn E k ω 0 := by
    intro hzero
    exact hne (((pma10_15 k n E ω hE hω).1.mp hzero) S x hx)
  simp only [FormEqOn, surfaceIntegral_zero] at hz
  push_neg at hz
  obtain ⟨Φ, hΦ⟩ := hz
  exact ⟨Φ, (pma10_11.1 k n E Φ ω hω).2, hΦ⟩

/-- In the displayed raw form both standard coefficients can cancel,
even though all four unreduced terms are present. -/
theorem raw_two_form_cancellation (x : Euclidean 3)
    (h₀ : x 0 = 1) (h₁₂ : x 1 = -x 2) : rawTwoForm x = 0 := by
  rw [rawTwoForm_standard]
  simp [standardTwoForm, h₀, h₁₂]

end Rudin.PMA.Chapter10.FidelityProbes
