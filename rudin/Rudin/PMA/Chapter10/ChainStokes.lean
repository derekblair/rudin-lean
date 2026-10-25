import Rudin.PMA.Chapter10.SimplexStokes
import Rudin.PMA.Chapter10.StokesTransport

noncomputable section
set_option autoImplicit false

namespace Rudin.PMA.Chapter10

/-- Stokes' theorem for actual C² simplex chains and C¹ forms. -/
theorem pma10_33 : pma10_33_contract := by
  intro d n E ω Γ hE hω
  exact chain_stokes_of_simplex
    (simplex_stokes_of_standard (fun U η hSU hU hη => standard_simplex_stokes hU hSU hη) hE hω) Γ

end Rudin.PMA.Chapter10
