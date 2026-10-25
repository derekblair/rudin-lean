import Rudin.PMA.Chapter10.PullbackRegularity

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

theorem pma10_21 : pma10_21_contract := by
  refine ⟨?_, ?_, fun _ _ => pullbackForm_scalar⟩
  · intro n m k E V T ω hE _ hT hTV hω
    exact pullbackForm_isFormOn hE hT hTV hω
  · intro n m k E T a hE hT x hx
    have hd := (hT.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds hx)
    simp only [pullbackForm, formFromCoefficients, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro I _
    rw [pullbackForm_coordinateWedge]
    congr 2
    apply List.ofFn_inj.mpr
    funext j
    simpa only [dx, ExteriorAlgebra.map_apply_ι] using pullback_dx_eq_scalarDifferential hd (I j)

end Rudin.PMA.Chapter10
