import Rudin.PMA.Chapter10.TorusVolume
import Rudin.PMA.Chapter10.TorusBoundary

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The literal solid torus and its oriented surface, with native volume/area,
ordinary image volume, all-continuous-form boundary equality, and outward normal. -/
theorem pma10_47 : pma10_47_contract := by
  intro a b ha hab
  have hv : IsFormOn univ 3 volumeForm := by
    rw [← densityForm_one_three]
    exact isFormOn_densityForm continuousOn_const
  refine ⟨torusSolidSurface_isC2 a b ha, torusOuterSurface_isC2 a b,
    torusMap_injOn ha hab, torusMap_image ha hab, torusJacobian_eq b,
    fun u hu => torusJacobian_sign ha hab hu,
    ParameterDomain.integrable_of_continuousOn ((torusSolidSurface a b ha).continuousOn_integrand hv),
    torusSolidSurface_integrand a b ha, torusSolidSurface_volume a b ha,
    torus_volume ha hab, torus_boundary_representation a b ha, ?_,
    ParameterDomain.integrable_of_continuousOn (surfaceNormal_continuousOn (torusOuterSurface a b)).norm,
    torusOuterSurface_area ha hab, fun x hx => solidTorus_z_le ha hab hx,
    torusOuterMap_top a b, torusOuterSurface_normal_top a b⟩
  intro u hu
  exact ⟨torusOuterSurface_normal a b u, torusUnitNormal_norm u,
    mul_pos ha (torus_revolution_radius_pos hab ⟨ha.le, le_rfl⟩ _),
    torusOuterSurface_normal_norm ha hab u,
    fun s hs => torusOuterMap_outward ha hab u hs⟩

end Rudin.PMA.Chapter10
