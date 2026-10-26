import Rudin.PMA.Chapter10.VectorPotentials

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- The proved scalar converse supplies an actual C² potential, whose Hessian
entries recover the prescribed field's first coordinate partials. -/
theorem scalar_potential_C2_hessian {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E)
    (hc : Convex ℝ U) (F : VectorField) (hF : ContDiffOn ℝ 1 F E)
    (hz : EqOn (curl F) 0 E) :
    ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) F E ∧
      ∀ x ∈ E, ∀ i j : Fin 3,
        coordinatePartial (fun y => coordinatePartial u y i) x j =
          coordinatePartial (fun y => F y i) x j := by
  obtain ⟨u, hu, he⟩ := pma10_43_scalar_converse U E e F hU hE hc hF hz
  refine ⟨u, hu, he, ?_⟩
  intro x hx i j
  apply coordinatePartial_congr_of_eqOn hE ?_ hx j
  intro y hy
  simpa only [gradient, coordEquivEuclidean_apply_coordinate] using
    congrArg (fun z : Euclidean 3 => z i) (he hy)

end Rudin.PMA.Chapter10.FidelityProbes
