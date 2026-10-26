import Rudin.PMA.Chapter10.SphereExamples

noncomputable section
set_option autoImplicit false
open Set

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- The spherical parametrization really identifies boundary points; the
source's injectivity assertion applies only to the parameter interior. -/
theorem sphere_boundary_identification :
    ¬ InjOn sphericalMap sphericalCell.carrier ∧
      InjOn sphericalMap (interior sphericalCell.carrier) := by
  refine ⟨?_, sphericalMap_injOn⟩
  intro hi
  let v : Coord 3 := ![0, Real.pi, 0]
  have h0 : (0 : Coord 3) ∈ sphericalCell.carrier := by
    rw [Cell.mem_carrier]
    intro i
    fin_cases i <;> simp [sphericalCell] <;> positivity
  have hv : v ∈ sphericalCell.carrier := by
    rw [Cell.mem_carrier]
    intro i
    fin_cases i <;> simp [sphericalCell, v] <;> positivity
  have he : sphericalMap 0 = sphericalMap v := by
    ext i
    fin_cases i <;> simp [sphericalMap, v]
  have hp : (0 : ℝ) = Real.pi := by
    simpa [v] using congrArg (fun u : Coord 3 => u 1) (hi h0 hv he)
  exact Real.pi_ne_zero hp.symm

/-- The volume example has an existing positive native integral even though
its derivative determinant vanishes at a parameter boundary point. -/
theorem sphere_volume_with_degenerate_boundary :
    ∃ Φ : Surface 3 3 univ,
      Φ.domain = .cell sphericalCell ∧ Φ.map = sphericalMap ∧
      IteratedRIntegrable sphericalCell (surfaceIntegrand Φ volumeForm) ∧
      0 < surfaceIntegral Φ volumeForm ∧ sphericalJacobian 0 = 0 := by
  obtain ⟨Φ, hD, hmap, hJ, hi, hv, _, _⟩ := pma10_12.2.2
  refine ⟨Φ, hD, hmap, hi, ?_, ?_⟩
  · rw [hv]
    positivity
  · simpa using hJ 0

end Rudin.PMA.Chapter10.FidelityProbes
