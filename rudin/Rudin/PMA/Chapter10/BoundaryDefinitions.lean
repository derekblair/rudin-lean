import Rudin.PMA.Chapter10.PositiveBoundaries
import Rudin.PMA.Chapter10.SquareBoundaries

set_option autoImplicit false

namespace Rudin.PMA.Chapter10

def pma10_31_contract : Prop := positiveBoundary_contract ∧ squareBoundary_contract

theorem pma10_31 : pma10_31_contract := ⟨positiveBoundary, squareBoundary⟩

end Rudin.PMA.Chapter10
