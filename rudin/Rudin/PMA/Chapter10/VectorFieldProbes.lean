import Rudin.PMA.Chapter10.VectorFields

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- The cyclic middle two-form dz∧dx corresponds to the positive y vector,
although its increasing-basis coefficient at {x,z} is negative. -/
theorem cyclic_middle_form_positive_vector (x : Euclidean 3) :
    twoFormVector (fun _ : Euclidean 3 => dx (2 : Fin 3) * dx 0) x =
      coordinateVector 3 1 := by
  let F : VectorField := fun _ => coordinateVector 3 1
  have he : vectorTwoForm F = fun _ : Euclidean 3 => dx (2 : Fin 3) * dx 0 := by
    funext y
    simp [vectorTwoForm, F, coordinateVector, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, Fin.sum_univ_three, radialBasis]
  rw [← he]
  exact congrFun (twoFormVector_vectorTwoForm F) x

end Rudin.PMA.Chapter10.FidelityProbes
