module

public import Mathlib.Analysis.Calculus.MeanValue
import all Mathlib.Analysis.Calculus.FDeriv.Partial

/-!
Expose the pinned Mathlib parameterized mean-value remainder to the project's
ordinary imports. Mathlib's source proves this lemma internally in its module.
The wrapper changes neither its hypotheses nor its conclusion.
-/

public section
set_option autoImplicit false
open Asymptotics Filter
open scoped Convex Topology

namespace Rudin.PMA.Chapter09

theorem parameterized_meanValue_remainder
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α}
    (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ)
    (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l]
      (fun χ => v χ - w χ) :=
  isLittleO_sub_sub_fderiv hv hw s seg df' cf'

end Rudin.PMA.Chapter09
