import Rudin.PMA.Chapter10.Pullbacks
import Rudin.PMA.Chapter10.PullbackEvaluation

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

theorem pma10_23 : pma10_23_contract := by
  intro n m p k E V W T S ω hE hV _ hT hS hTV _ _ x hx
  exact pullbackForm_comp_at
    ((hT.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds hx))
    ((hS.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds (hTV hx))) ω

theorem pma10_24 : pma10_24_contract := by
  intro n k E Φ ω _ hω
  have hc := Φ.continuousOn_integrand hω
  have he := surfaceIntegrand_identity_pullback Φ ω
  have hp : ContinuousOn
      (surfaceIntegrand (identityParameterSurface Φ.domain) (pullbackForm Φ.euclideanMap ω))
      Φ.domain.carrier := hc.congr he
  refine ⟨ParameterDomain.integrable_of_continuousOn hc,
    ParameterDomain.integrable_of_continuousOn hp, ?_⟩
  exact ParameterDomain.integral_congr hc hp he.symm

theorem pma10_25 : pma10_25_contract := by
  intro n m k E V T Φ ω hE _ hT hTV hω
  have hc := (Φ.mapBy T hE hT hTV).continuousOn_integrand hω
  have he := surfaceIntegrand_mapBy Φ T hE hT hTV ω
  have hp : ContinuousOn (surfaceIntegrand Φ (pullbackForm T ω)) Φ.domain.carrier :=
    hc.congr he.symm
  refine ⟨rfl, rfl, ParameterDomain.integrable_of_continuousOn hc,
    ParameterDomain.integrable_of_continuousOn hp, ?_⟩
  exact ParameterDomain.integral_congr hc hp he

end Rudin.PMA.Chapter10
