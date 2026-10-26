import Rudin.PMA.Chapter10.FormExamples
import Mathlib.Analysis.SpecialFunctions.PolarCoord

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

theorem contDiff_sphericalMap : ContDiff ℝ 1 sphericalMap := by
  apply (coordEquivEuclidean 3).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

def sphericalSurface : Surface 3 3 univ where
  domain := .cell sphericalCell
  map := sphericalMap
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := contDiff_sphericalMap.contDiffOn
  mapsTo := mapsTo_univ _ _

theorem sphericalMap_norm_sq (u : Coord 3) : ‖sphericalMap u‖ ^ 2 = (u 0)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    sphericalMap, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, add_zero]
  calc
    _ = (u 0)^2 * ((Real.sin (u 1))^2 *
      ((Real.cos (u 2))^2 + (Real.sin (u 2))^2) + (Real.cos (u 1))^2) := by ring
    _ = (u 0)^2 := by rw [Real.cos_sq_add_sin_sq, mul_one, Real.sin_sq_add_cos_sq, mul_one]

theorem sphericalMap_norm {u : Coord 3} (hr : 0 ≤ u 0) : ‖sphericalMap u‖ = u 0 :=
  (sq_eq_sq₀ (norm_nonneg _) hr).mp (sphericalMap_norm_sq u)

theorem exists_nonnegative_polar (x y : ℝ) :
    ∃ ρ φ : ℝ, 0 ≤ ρ ∧ φ ∈ Icc 0 (2 * Real.pi) ∧
      ρ * Real.cos φ = x ∧ ρ * Real.sin φ = y ∧ ρ^2 = x^2 + y^2 := by
  let z : ℂ := ⟨x, y⟩
  have hs : ‖z‖^2 = x^2 + y^2 := by simpa [z, Complex.normSq_apply, pow_two] using Complex.sq_norm z
  by_cases h : 0 ≤ Complex.arg z
  · exact ⟨‖z‖, Complex.arg z, norm_nonneg _, ⟨h, by linarith [Complex.arg_le_pi z, Real.pi_pos]⟩,
      Complex.norm_mul_cos_arg z, Complex.norm_mul_sin_arg z, hs⟩
  · refine ⟨‖z‖, Complex.arg z + 2 * Real.pi, norm_nonneg _,
      ⟨by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos], by linarith⟩, ?_, ?_, hs⟩
    · simpa only [Real.cos_add_two_pi] using Complex.norm_mul_cos_arg z
    · simpa only [Real.sin_add_two_pi] using Complex.norm_mul_sin_arg z

theorem sphericalMap_image : sphericalMap '' sphericalCell.carrier = Metric.closedBall 0 1 := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hr := (Cell.mem_carrier.mp hu) 0
    rw [Metric.mem_closedBall, dist_zero_right, sphericalMap_norm hr.1]
    exact hr.2
  · intro hx
    have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
    by_cases hx0 : x = 0
    · subst x
      refine ⟨0, ?_, ?_⟩
      · rw [Cell.mem_carrier]
        intro i
        fin_cases i <;> simp [sphericalCell] <;> positivity
      · ext i
        fin_cases i <;> simp [sphericalMap]
    have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hs : ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
      simpa [Fin.sum_univ_succ, add_assoc] using EuclideanSpace.real_norm_sq_eq x
    have hbound : -(1 : ℝ) ≤ x 2 / ‖x‖ ∧ x 2 / ‖x‖ ≤ 1 := by
      have hcoord : |x 2| ≤ ‖x‖ := by
        apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
        rw [sq_abs]
        nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
      constructor
      · rw [le_div_iff₀ hr]
        linarith [(abs_le.mp hcoord).1]
      · rw [div_le_iff₀ hr]
        linarith [(abs_le.mp hcoord).2]
    let θ := Real.arccos (x 2 / ‖x‖)
    have hθ : θ ∈ Icc 0 Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
    have hcos : ‖x‖ * Real.cos θ = x 2 := by
      rw [show Real.cos θ = x 2 / ‖x‖ from Real.cos_arccos hbound.1 hbound.2]
      field_simp
    obtain ⟨ρ, φ, hρ, hφ, hφx, hφy, hρsq⟩ := exists_nonnegative_polar (x 0) (x 1)
    have hsin : ‖x‖ * Real.sin θ = ρ := by
      apply (sq_eq_sq₀ (mul_nonneg hr.le (Real.sin_nonneg_of_mem_Icc hθ)) hρ).mp
      have htrig : (‖x‖ * Real.sin θ)^2 + (‖x‖ * Real.cos θ)^2 = ‖x‖^2 := by
        calc
          _ = ‖x‖^2 * (Real.sin θ^2 + Real.cos θ^2) := by ring
          _ = ‖x‖^2 := by rw [Real.sin_sq_add_cos_sq, mul_one]
      rw [hcos] at htrig
      nlinarith
    refine ⟨![‖x‖, θ, φ], ?_, ?_⟩
    · rw [Cell.mem_carrier]
      intro i
      fin_cases i
      · exact ⟨hr.le, hxnorm⟩
      · exact hθ
      · exact hφ
    · ext i
      fin_cases i
      · simpa [sphericalMap, hsin] using hφx
      · simpa [sphericalMap, hsin] using hφy
      · simpa [sphericalMap] using hcos

theorem sphericalCell_mem_interior {u : Coord 3} :
    u ∈ interior sphericalCell.carrier ↔
      u 0 ∈ Ioo 0 1 ∧ u 1 ∈ Ioo 0 Real.pi ∧ u 2 ∈ Ioo 0 (2 * Real.pi) := by
  rw [Cell.carrier, ← pi_univ_Icc, interior_pi_set finite_univ]
  simp [sphericalCell, Set.mem_pi, Fin.forall_fin_succ]

theorem sphericalMap_injOn : InjOn sphericalMap (interior sphericalCell.carrier) := by
  intro u hu v hv huv
  rcases sphericalCell_mem_interior.mp hu with ⟨hu₀, hu₁, hu₂⟩
  rcases sphericalCell_mem_interior.mp hv with ⟨hv₀, hv₁, hv₂⟩
  have hr : u 0 = v 0 := by
    simpa only [sphericalMap_norm hu₀.1.le, sphericalMap_norm hv₀.1.le] using congrArg norm huv
  have hz := congrArg (fun x : Euclidean 3 => x 2) huv
  simp only [sphericalMap, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_two] at hz
  have hθ : u 1 = v 1 := Real.injOn_cos ⟨hu₁.1.le, hu₁.2.le⟩ ⟨hv₁.1.le, hv₁.2.le⟩
    (by rw [← hr] at hz; exact mul_left_cancel₀ hu₀.1.ne' hz)
  have hρ : 0 < u 0 * Real.sin (u 1) := mul_pos hu₀.1
    (Real.sin_pos_of_pos_of_lt_pi hu₁.1 hu₁.2)
  have hx := congrArg (fun x : Euclidean 3 => x 0) huv
  have hy := congrArg (fun x : Euclidean 3 => x 1) huv
  simp only [sphericalMap, coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero,
    Matrix.cons_val_one, ← hr, ← hθ] at hx hy
  have hc := mul_left_cancel₀ hρ.ne' hx
  have hs := mul_left_cancel₀ hρ.ne' hy
  have hp : (1, u 2 - Real.pi) ∈ polarCoord.target :=
    ⟨by norm_num, ⟨by linarith [hu₂.1], by linarith [hu₂.2]⟩⟩
  have hq : (1, v 2 - Real.pi) ∈ polarCoord.target :=
    ⟨by norm_num, ⟨by linarith [hv₂.1], by linarith [hv₂.2]⟩⟩
  have hang := polarCoord.symm.injOn hp hq (by
    ext <;> simp [polarCoord, Real.cos_sub, Real.sin_sub, hc, hs])
  have hφ : u 2 = v 2 := by have := congrArg Prod.snd hang; dsimp at this; linarith
  ext i
  fin_cases i
  · exact hr
  · exact hθ
  · exact hφ

def sphericalDerivative (u : Coord 3) : Coord 3 →L[ℝ] Euclidean 3 :=
  (coordEquivEuclidean 3 : Coord 3 →L[ℝ] Euclidean 3).comp
    (ContinuousLinearMap.pi ![
      (Real.sin (u 1) * Real.cos (u 2)) • ContinuousLinearMap.proj 0 +
        (u 0 * Real.cos (u 1) * Real.cos (u 2)) • ContinuousLinearMap.proj 1 -
        (u 0 * Real.sin (u 1) * Real.sin (u 2)) • ContinuousLinearMap.proj 2,
      (Real.sin (u 1) * Real.sin (u 2)) • ContinuousLinearMap.proj 0 +
        (u 0 * Real.cos (u 1) * Real.sin (u 2)) • ContinuousLinearMap.proj 1 +
        (u 0 * Real.sin (u 1) * Real.cos (u 2)) • ContinuousLinearMap.proj 2,
      Real.cos (u 1) • ContinuousLinearMap.proj 0 -
        (u 0 * Real.sin (u 1)) • ContinuousLinearMap.proj 1])

theorem hasFDerivAt_sphericalMap (u : Coord 3) :
    HasFDerivAt sphericalMap (sphericalDerivative u) u := by
  have h₀ := (ContinuousLinearMap.proj 0 : Coord 3 →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h₁ := (ContinuousLinearMap.proj 1 : Coord 3 →L[ℝ] ℝ).hasFDerivAt (x := u)
  have h₂ := (ContinuousLinearMap.proj 2 : Coord 3 →L[ℝ] ℝ).hasFDerivAt (x := u)
  apply (coordEquivEuclidean 3).hasFDerivAt.comp u
  apply hasFDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert (h₀.mul h₁.sin).mul h₂.cos using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring
  · convert (h₀.mul h₁.sin).mul h₂.sin using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring
  · convert h₀.mul h₁.cos using 1 <;> ext v <;>
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul] <;> ring

theorem sphericalJacobian_eq (u : Coord 3) : sphericalJacobian u = (u 0)^2 * Real.sin (u 1) := by
  rw [sphericalJacobian, (hasFDerivAt_sphericalMap u).fderiv]
  let M : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => sphericalDerivative u (Pi.single j 1) i
  change Matrix.det M = _
  rw [Matrix.det_fin_three]
  simp only [M, sphericalDerivative, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    coordEquivEuclidean_apply_coordinate, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, smul_eq_mul]
  norm_num
  calc
    _ = (u 0)^2 * Real.sin (u 1) *
      (Real.sin (u 1)^2 + Real.cos (u 1)^2) *
      (Real.sin (u 2)^2 + Real.cos (u 2)^2) := by ring
    _ = (u 0)^2 * Real.sin (u 1) := by rw [Real.sin_sq_add_cos_sq, Real.sin_sq_add_cos_sq]; ring

theorem spherical_surfaceIntegrand : surfaceIntegrand sphericalSurface volumeForm =
    fun u => (u 0)^2 * Real.sin (u 1) := by
  funext u
  change evaluateForm 3 _ (coordinateWedge id) = _
  rw [evaluateForm_coordinateWedge]
  exact sphericalJacobian_eq u

theorem sphericalDensity_integral :
    iteratedRIntegral sphericalCell (fun u => (u 0)^2 * Real.sin (u 1)) = 4 * Real.pi / 3 := by
  have hφ : nativeSliceIntegral sphericalCell (fun u => (u 0)^2 * Real.sin (u 1)) =
      fun u : Coord 2 => (2 * Real.pi) * (u 0)^2 * Real.sin (u 1) := by
    funext u
    change Chapter06.RIntegral (fun _ : ℝ => (u 0)^2 * Real.sin (u 1)) 0 (2 * Real.pi) = _
    rw [rIntegral_eq_intervalIntegral_of_continuousOn (by positivity) continuousOn_const]
    simp [intervalIntegral.integral_const]
    ring
  have hθ : nativeSliceIntegral sphericalCell.init
      (fun u : Coord 2 => (2 * Real.pi) * (u 0)^2 * Real.sin (u 1)) =
      fun u : Coord 1 => (4 * Real.pi) * (u 0)^2 := by
    funext u
    change Chapter06.RIntegral (fun t : ℝ => (2 * Real.pi) * (u 0)^2 * Real.sin t) 0 Real.pi = _
    rw [rIntegral_eq_intervalIntegral_of_continuousOn Real.pi_pos.le (by fun_prop)]
    rw [intervalIntegral.integral_const_mul, integral_sin]
    simp
    ring
  rw [iteratedRIntegral, hφ, iteratedRIntegral, hθ, iteratedRIntegral_one]
  change Chapter06.RIntegral (fun t => 4 * Real.pi * t^2) 0 1 = _
  rw [rIntegral_eq_intervalIntegral_of_continuousOn zero_le_one (by fun_prop),
    intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

theorem spherical_integral :
    IteratedRIntegrable sphericalCell (surfaceIntegrand sphericalSurface volumeForm) ∧
    surfaceIntegral sphericalSurface volumeForm = 4 * Real.pi / 3 := by
  constructor
  · rw [spherical_surfaceIntegrand]
    apply iteratedRIntegrable_of_continuousOn
    fun_prop
  · change iteratedRIntegral sphericalCell _ = _
    rw [spherical_surfaceIntegrand]
    exact sphericalDensity_integral

theorem pma10_12 : pma10_12_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ hD
    obtain ⟨hi, hv⟩ := xyDifferential_endpoint Φ hD
    refine ⟨hi, hv, ?_⟩
    intro hclosed
    rw [hv, hclosed, sub_self]
  · intro a b _ _
    exact ⟨ellipseSurface a b, rfl, rfl, ellipseSurface_closed a b, ellipse_integrals a b⟩
  · exact ⟨sphericalSurface, rfl, rfl, sphericalJacobian_eq,
      spherical_integral.1, spherical_integral.2, sphericalMap_image, sphericalMap_injOn⟩

end Rudin.PMA.Chapter10
