import Rudin.PMA.Chapter10.TorusCalculus
import Rudin.PMA.Chapter10.CellImageVolume

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma densityForm_one_three : densityForm (fun _ : Euclidean 3 => 1) = volumeForm := by
  funext x
  simp [densityForm, standardVolume, volumeForm]

lemma torusSolidSurface_coordinateJacobian (a b : ℝ) (ha : 0 < a)
    {u : Coord 3} (hu : u ∈ (torusCell a ha).carrier) :
    coordinateJacobian (torusSolidSurface a b ha).coordinateMap u = torusJacobian b u := by
  have h := surfaceIntegrand_densityForm (torusSolidSurface a b ha)
    (f := fun _ => 1) continuousOn_const hu
  rw [densityForm_one_three, one_mul, torusSolidSurface_integrand] at h
  exact h.symm

lemma torus_volume {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (volume (solidTorus a b)).toReal = 2 * Real.pi ^ 2 * a ^ 2 * b := by
  have h := surfaceIntegral_density_eq_image_of_interior_inj
    (torusSolidSurface a b ha) (torusCell a ha) rfl (torusMap_injOn ha hab)
    (fun u hu => by
      rw [torusSolidSurface_coordinateJacobian a b ha hu]
      exact (torusJacobian_sign ha hab hu).1)
    (f := fun _ => 1) continuousOn_const
  rw [densityForm_one_three, torusSolidSurface_volume] at h
  have himage : (torusSolidSurface a b ha).image = solidTorus a b := torusMap_image ha hab
  rw [himage] at h
  simpa only [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] using h.symm

end Rudin.PMA.Chapter10
