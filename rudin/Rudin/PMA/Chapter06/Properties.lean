import Rudin.PMA.Chapter06.Integrability
import Rudin.PMA.Chapter06.Split

noncomputable section
open Set
namespace Rudin.PMA.Chapter06

/-! ### PMA-6.12: Full algebra, order, restriction, and integral bounds. -/

theorem pma6_12 : pma6_12_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f g α a b c hf hg
    exact ⟨(rsIntegrable_add hf hg).1, (rsIntegrable_add hf hg).2,
      (rsIntegrable_const_mul hf c).1, (rsIntegrable_const_mul hf c).2⟩
  · intro f g α a b hf hg hfg
    exact rsIntegral_mono hf hg hfg
  · intro f α a b c hac hcb hf
    exact pma6_12_split hac hcb hf
  · intro f α a b M hf hM
    exact rsIntegral_abs_le_bound hf hM
  · intro f α β a b c hα hβ hc
    exact ⟨(rsIntegrable_integrator_add hα hβ).1, (rsIntegrable_integrator_add hα hβ).2,
      (rsIntegrable_integrator_const_mul hα hc).1,
      (rsIntegrable_integrator_const_mul hα hc).2⟩

end Rudin.PMA.Chapter06
