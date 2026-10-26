import Rudin.PMA.Chapter10.TorusGeometry

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma torusSolidSurface_isC2 (a b : ℝ) (ha : 0 < a) : (torusSolidSurface a b ha).IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _, (torusMap_contDiff b 2).contDiffOn⟩

lemma torusOuterSurface_isC2 (a b : ℝ) : (torusOuterSurface a b).IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _, (torusOuterMap_contDiff a b 2).contDiffOn⟩

def torusDerivative (b : ℝ) (u : Coord 3) : Coord 3 →L[ℝ] Euclidean 3 :=
  (coordEquivEuclidean 3 : Coord 3 →L[ℝ] Euclidean 3).comp
    (ContinuousLinearMap.pi ![
      Real.cos (u 1) • ContinuousLinearMap.proj 0 -
        (u 0 * Real.sin (u 1)) • ContinuousLinearMap.proj 1,
      (Real.sin (u 1) * Real.cos (u 2)) • ContinuousLinearMap.proj 0 +
        (u 0 * Real.cos (u 1) * Real.cos (u 2)) • ContinuousLinearMap.proj 1 -
        ((b + u 0 * Real.sin (u 1)) * Real.sin (u 2)) • ContinuousLinearMap.proj 2,
      (Real.sin (u 1) * Real.sin (u 2)) • ContinuousLinearMap.proj 0 +
        (u 0 * Real.cos (u 1) * Real.sin (u 2)) • ContinuousLinearMap.proj 1 +
        ((b + u 0 * Real.sin (u 1)) * Real.cos (u 2)) • ContinuousLinearMap.proj 2])

lemma torusMap_hasFDerivAt (b : ℝ) (u : Coord 3) :
    HasFDerivAt (torusMap b) (torusDerivative b u) u := by
  have h0 := (ContinuousLinearMap.proj 0 : Coord 3 →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h1 := (ContinuousLinearMap.proj 1 : Coord 3 →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h2 := (ContinuousLinearMap.proj 2 : Coord 3 →L[ℝ] ℝ).hasFDerivAt (x := u)
  apply (coordEquivEuclidean 3).hasFDerivAt.comp u
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert h0.mul h1.cos using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring
  · convert ((h0.mul h1.sin).const_add b).mul h2.cos using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring
  · convert ((h0.mul h1.sin).const_add b).mul h2.sin using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring

lemma torusJacobian_eq (b : ℝ) (u : Coord 3) :
    torusJacobian b u = u 0 * (b + u 0 * Real.sin (u 1)) := by
  rw [torusJacobian, (torusMap_hasFDerivAt b u).fderiv]
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => torusDerivative b u (Pi.single j 1) i
  change M.det = _
  rw [Matrix.det_fin_three]
  simp [M, torusDerivative, Pi.single_apply, smul_eq_mul]
  calc
    _ = u 0 * (b + u 0 * Real.sin (u 1)) *
      (Real.sin (u 1) ^ 2 + Real.cos (u 1) ^ 2) *
      (Real.sin (u 2) ^ 2 + Real.cos (u 2) ^ 2) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

lemma torusJacobian_sign {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {u : Coord 3} (hu : u ∈ (torusCell a ha).carrier) :
    0 ≤ torusJacobian b u ∧ (0 < torusJacobian b u ↔ 0 < u 0) := by
  have ht : u 0 ∈ Icc 0 a := (Cell.mem_carrier.mp hu) 0
  have hρ := torus_revolution_radius_pos hab ht (u 1)
  rw [torusJacobian_eq]
  exact ⟨mul_nonneg ht.1 hρ.le, mul_pos_iff_of_pos_right hρ⟩

def torusOuterDerivative (a b : ℝ) (u : Coord 2) : Coord 2 →L[ℝ] Euclidean 3 :=
  (coordEquivEuclidean 3 : Coord 3 →L[ℝ] Euclidean 3).comp
    (ContinuousLinearMap.pi ![
      (-a * Real.sin (u 0)) • ContinuousLinearMap.proj 0,
      (a * Real.cos (u 0) * Real.cos (u 1)) • ContinuousLinearMap.proj 0 -
        ((b + a * Real.sin (u 0)) * Real.sin (u 1)) • ContinuousLinearMap.proj 1,
      (a * Real.cos (u 0) * Real.sin (u 1)) • ContinuousLinearMap.proj 0 +
        ((b + a * Real.sin (u 0)) * Real.cos (u 1)) • ContinuousLinearMap.proj 1])

lemma torusOuterMap_hasFDerivAt (a b : ℝ) (u : Coord 2) :
    HasFDerivAt (torusOuterMap a b) (torusOuterDerivative a b u) u := by
  have h0 := (ContinuousLinearMap.proj 0 : Coord 2 →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h1 := (ContinuousLinearMap.proj 1 : Coord 2 →L[ℝ] ℝ).hasFDerivAt (x := u)
  apply (coordEquivEuclidean 3).hasFDerivAt.comp u
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert h0.cos.const_mul a using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, smul_eq_mul] <;> ring
  · convert ((h0.sin.const_mul a).const_add b).mul h1.cos using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring
  · convert ((h0.sin.const_mul a).const_add b).mul h1.sin using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring

lemma torusOuterSurface_normal (a b : ℝ) (u : Coord 2) :
    surfaceNormal (torusOuterSurface a b) u =
      (a * (b + a * Real.sin (u 0))) • torusUnitNormal u := by
  change cross3 (fderiv ℝ (torusOuterMap a b) u (Pi.single 0 1))
    (fderiv ℝ (torusOuterMap a b) u (Pi.single 1 1)) = _
  rw [(torusOuterMap_hasFDerivAt a b u).fderiv]
  ext i
  fin_cases i <;> simp [cross3, torusOuterDerivative, torusUnitNormal,
    Pi.single_apply, PiLp.smul_apply, smul_eq_mul]
  · calc
      _ = a * (b + a * Real.sin (u 0)) * Real.cos (u 0) *
        (Real.sin (u 1) ^ 2 + Real.cos (u 1) ^ 2) := by ring
      _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring
  · ring
  · ring

lemma torusOuterSurface_normal_norm {a b : ℝ} (ha : 0 < a) (hab : a < b) (u : Coord 2) :
    ‖surfaceNormal (torusOuterSurface a b) u‖ = a * (b + a * Real.sin (u 0)) := by
  rw [torusOuterSurface_normal, norm_smul, torusUnitNormal_norm, mul_one,
    Real.norm_eq_abs, abs_of_pos (mul_pos ha (torus_revolution_radius_pos hab ⟨ha.le, le_rfl⟩ _))]

lemma torusOuterSurface_normal_top (a b : ℝ) :
    surfaceNormal (torusOuterSurface a b) ![Real.pi / 2, Real.pi / 2] =
      (a * (b + a)) • coordinateVector 3 2 := by
  rw [torusOuterSurface_normal]
  ext i
  fin_cases i <;> simp [torusUnitNormal, coordinateVector, EuclideanSpace.basisFun_apply,
    PiLp.smul_apply, PiLp.single_apply, smul_eq_mul]

lemma torusSolidSurface_integrand (a b : ℝ) (ha : 0 < a) (u : Coord 3) :
    surfaceIntegrand (torusSolidSurface a b ha) volumeForm u = torusJacobian b u := by
  change evaluateForm 3 _ (coordinateWedge id) = _
  rw [evaluateForm_coordinateWedge]
  rfl

lemma torus_angular_integral (t b : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), (2 * Real.pi) * (t * (b + t * Real.sin θ))) =
      4 * Real.pi ^ 2 * t * b := by
  have he : (fun θ : ℝ => (2 * Real.pi) * (t * (b + t * Real.sin θ))) =
      (fun θ => (2 * Real.pi * t * b) + (2 * Real.pi * t ^ 2) * Real.sin θ) := by
    funext θ
    ring
  have hc : IntervalIntegrable (fun _ : ℝ => 2 * Real.pi * t * b) volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  have hs : IntervalIntegrable (fun θ : ℝ => (2 * Real.pi * t ^ 2) * Real.sin θ) volume 0 (2 * Real.pi) :=
    (show Continuous (fun θ : ℝ => (2 * Real.pi * t ^ 2) * Real.sin θ) by fun_prop).intervalIntegrable _ _
  rw [he, intervalIntegral.integral_add hc hs]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul, integral_sin]
  simp only [Real.cos_two_pi, Real.cos_zero, sub_self, mul_zero, add_zero]
  ring

lemma torusVolume_nativeSlice (a b : ℝ) (ha : 0 < a) (w : Coord 2) :
    nativeSliceIntegral (torusCell a ha) (fun u => u 0 * (b + u 0 * Real.sin (u 1))) w =
      (2 * Real.pi) * (w 0 * (b + w 0 * Real.sin (w 1))) := by
  have he : (fun t : ℝ => (Fin.snoc (α := fun _ : Fin 3 => ℝ) w t) 0 * (b + (Fin.snoc (α := fun _ : Fin 3 => ℝ) w t) 0 * Real.sin ((Fin.snoc (α := fun _ : Fin 3 => ℝ) w t) 1))) =
      (fun _ : ℝ => w 0 * (b + w 0 * Real.sin (w 1))) := by
    funext t
    simp [Fin.snoc]
  unfold nativeSliceIntegral
  rw [he, rIntegral_eq_intervalIntegral_of_continuousOn
    ((torusCell a ha).lower_le_upper _) continuousOn_const]
  simp [torusCell, smul_eq_mul]
  ring

lemma torusSolidSurface_volume (a b : ℝ) (ha : 0 < a) :
    surfaceIntegral (torusSolidSurface a b ha) volumeForm = 2 * Real.pi ^ 2 * a ^ 2 * b := by
  have he : surfaceIntegrand (torusSolidSurface a b ha) volumeForm =
      (fun u => u 0 * (b + u 0 * Real.sin (u 1))) := by
    funext u
    rw [torusSolidSurface_integrand, torusJacobian_eq]
  change iteratedRIntegral (torusCell a ha) _ = _
  rw [he]
  change iteratedRIntegral (torusCell a ha).init (nativeSliceIntegral (torusCell a ha)
    (fun u => u 0 * (b + u 0 * Real.sin (u 1)))) = _
  rw [funext (torusVolume_nativeSlice a b ha)]
  have hc : Continuous (fun w : Coord 2 => (2 * Real.pi) * (w 0 * (b + w 0 * Real.sin (w 1)))) := by
    fun_prop
  rw [cellRIntegral_two_eq_doubleIntegral _ hc]
  change (∫ t in (0 : ℝ)..a, ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (2 * Real.pi) * (t * (b + t * Real.sin θ))) = _
  simp_rw [torus_angular_integral]
  have hg : (fun t : ℝ => 4 * Real.pi ^ 2 * t * b) = (fun t => (4 * Real.pi ^ 2 * b) * t) := by
    funext t
    ring
  rw [hg, intervalIntegral.integral_const_mul, integral_id]
  ring

lemma torusOuterSurface_area {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    surfaceArea (torusOuterSurface a b) = 4 * Real.pi ^ 2 * a * b := by
  rw [surfaceArea_eq_integral]
  have he : (fun u => ‖surfaceNormal (torusOuterSurface a b) u‖) =
      (fun u => a * (b + a * Real.sin (u 0))) := funext (torusOuterSurface_normal_norm ha hab)
  rw [he]
  change iteratedRIntegral torusOuterCell _ = _
  have hc : Continuous (fun u : Coord 2 => a * (b + a * Real.sin (u 0))) := by fun_prop
  rw [cellRIntegral_two_eq_doubleIntegral torusOuterCell hc]
  change (∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ φ in (0 : ℝ)..(2 * Real.pi),
    a * (b + a * Real.sin θ)) = _
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  exact torus_angular_integral a b

end Rudin.PMA.Chapter10
