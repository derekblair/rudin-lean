import Rudin.PMA.Chapter09.Integrals

noncomputable section
open Set
open Rudin.PMA.Chapter06 Rudin.PMA.Chapter09

namespace Rudin.PMA.Chapter09.IntegralProbes

/-- Arbitrary native integrability suffices: no continuity in x is required. -/
theorem arbitrary_integrable_multiplier (q α : ℝ → ℝ) (a b s : ℝ)
    (hq : RSIntegrable q α a b) :
    HasDerivAt (fun t => RSIntegral (fun x => t * q x) α a b)
      (RSIntegral q α a b) s := by
  have h := pma9_42 (fun x t => t * q x) (fun x _ => q x) α a b (s-1) (s+1) s
    hq.1 hq.2.2.1 (by linarith) (by linarith)
    (fun t _ => (rsIntegrable_const_mul hq t).1)
    (by
      refine ⟨1, by norm_num, ?_⟩
      intro x hx t ht
      simpa using (hasDerivAt_id t).mul_const (q x))
    (by
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro x hx t ht
      simpa using hε)
  exact h.2

/-- A parameter cusp elsewhere in the integration parameter interval is allowed.
The derivative at s=1 uses only the positive neighborhood of that point. -/
theorem parameter_cusp_away_from_basepoint (q α : ℝ → ℝ) (a b : ℝ)
    (hq : RSIntegrable q α a b) :
    HasDerivAt (fun t => RSIntegral (fun x => |t| * q x) α a b)
      (RSIntegral q α a b) 1 := by
  have h := pma9_42 (fun x t => |t| * q x) (fun x _ => q x) α a b (-1) 2 1
    hq.1 hq.2.2.1 (by norm_num) (by norm_num)
    (fun t _ => (rsIntegrable_const_mul hq |t|).1)
    (by
      refine ⟨1/2, by norm_num, ?_⟩
      intro x hx t ht
      have htpos : 0 < t := by have := (abs_lt.mp ht).1; linarith
      simpa using (hasDerivAt_abs_pos htpos).mul_const (q x))
    (by
      intro ε hε
      refine ⟨1, by norm_num, ?_⟩
      intro x hx t ht
      simpa using hε)
  exact h.2

end Rudin.PMA.Chapter09.IntegralProbes

#print axioms Rudin.PMA.Chapter09.IntegralProbes.arbitrary_integrable_multiplier
#print axioms Rudin.PMA.Chapter09.IntegralProbes.parameter_cusp_away_from_basepoint
