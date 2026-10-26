import Rudin.PMA.Chapter10.SphereExamples
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The geometric interpretations in Example 10.12

The original example identifies two numerical form integrals with area and volume.
This supplement proves these identifications, including that the ellipse curve is
the frontier of the stated bounded region. Area and volume are represented by
Lebesgue measure, converted to a real number by `ENNReal.toReal`; the regions have
finite measure. The ellipse region is explicitly the diagonal image of the closed
unit disk, and its usual normalized-coordinate inequality is proved below.
-/

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Scaling the two coordinate axes by the semiaxes of the ellipse. -/
def ellipseScaling (a b : ℝ) : Euclidean 2 →L[ℝ] Euclidean 2 :=
  (Matrix.toLin (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (Matrix.diagonal ![a, b])).toContinuousLinearMap

@[simp] theorem ellipseScaling_apply_zero (a b : ℝ) (x : Euclidean 2) :
    ellipseScaling a b x 0 = a * x 0 := by
  simp [ellipseScaling, Matrix.toLin_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Matrix.mulVec]

@[simp] theorem ellipseScaling_apply_one (a b : ℝ) (x : Euclidean 2) :
    ellipseScaling a b x 1 = b * x 1 := by
  simp [ellipseScaling, Matrix.toLin_apply, EuclideanSpace.basisFun_repr,
    EuclideanSpace.basisFun_apply, Matrix.mulVec]

theorem ellipseScaling_det (a b : ℝ) :
    LinearMap.det (ellipseScaling a b).toLinearMap = a * b := by
  change LinearMap.det (Matrix.toLin _ _ (Matrix.diagonal ![a, b])) = _
  rw [LinearMap.det_toLin]
  simp

/-- The closed region enclosed by the ellipse of semiaxes a and b. -/
def ellipseRegion (a b : ℝ) : Set (Euclidean 2) :=
  ellipseScaling a b '' Metric.closedBall 0 1

theorem ellipseRegion_eq_inequality {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ellipseRegion a b = {x | (x 0 / a)^2 + (x 1 / b)^2 ≤ 1} := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [mem_ofPred_eq, ellipseScaling_apply_zero, ellipseScaling_apply_one,
      mul_div_cancel_left₀ _ ha.ne', mul_div_cancel_left₀ _ hb.ne']
    have hu' : ‖u‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hu
    have hs := EuclideanSpace.real_norm_sq_eq u
    simp only [Fin.sum_univ_two] at hs
    nlinarith [norm_nonneg u]
  · intro hx
    change (x 0 / a)^2 + (x 1 / b)^2 ≤ 1 at hx
    let u : Euclidean 2 := coordEquivEuclidean 2 ![x 0 / a, x 1 / b]
    refine ⟨u, ?_, ?_⟩
    · have hs : ‖u‖^2 = (x 0 / a)^2 + (x 1 / b)^2 := by
        simpa [u, Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq u
      rw [Metric.mem_closedBall, dist_zero_right]
      apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
      simpa only [one_pow, hs] using hx
    · ext i
      fin_cases i
      · simp [u, mul_div_cancel₀ _ ha.ne']
      · simp [u, mul_div_cancel₀ _ hb.ne']

theorem ellipseRegion_volume {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (ellipseRegion a b) = ENNReal.ofReal (Real.pi * a * b) := by
  rw [ellipseRegion, Measure.addHaar_image_continuousLinearMap, ellipseScaling_det]
  simp only [EuclideanSpace.volume_closedBall_fin_two, ENNReal.ofReal_one, one_pow, one_mul,
    abs_of_pos (mul_pos ha hb)]
  rw [← ENNReal.ofReal_mul (mul_pos ha hb).le]
  congr 1
  ring

/-- The unit-circle parameterization covers precisely the unit sphere. -/
theorem ellipseMap_unit_image :
    ellipseMap 1 1 '' ellipseCell.carrier = Metric.sphere 0 1 := by
  ext x
  constructor
  · rintro ⟨u, _, rfl⟩
    rw [Metric.mem_sphere, dist_zero_right]
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, ellipseMap, coordEquivEuclidean_apply_coordinate,
      Matrix.cons_val_zero, Matrix.cons_val_one, one_mul, one_pow]
    exact Real.cos_sq_add_sin_sq _
  · intro hx
    have hn : ‖x‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hx
    have hs : (x 0)^2 + (x 1)^2 = 1 := by
      simpa only [Fin.sum_univ_two, hn, one_pow] using
        (EuclideanSpace.real_norm_sq_eq x).symm
    obtain ⟨ρ, φ, hρ, hφ, hφx, hφy, hρsq⟩ := exists_nonnegative_polar (x 0) (x 1)
    have hρ1 : ρ = 1 := by nlinarith
    refine ⟨fun _ => φ, ?_, ?_⟩
    · rw [Cell.mem_carrier]
      intro i
      exact hφ
    · ext i
      fin_cases i
      · simpa [ellipseMap, hρ1] using hφx
      · simpa [ellipseMap, hρ1] using hφy

theorem ellipseMap_scaling (a b : ℝ) :
    ellipseMap a b = ellipseScaling a b ∘ ellipseMap 1 1 := by
  funext u
  ext i
  fin_cases i <;> simp [ellipseMap]

/-- The ellipse curve in Example 10.12(b) is exactly the frontier of the
closed bounded region whose area is computed here. -/
theorem ellipseMap_image_eq_frontier {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ellipseMap a b '' ellipseCell.carrier = frontier (ellipseRegion a b) := by
  let e : Euclidean 2 ≃L[ℝ] Euclidean 2 :=
    ((ellipseScaling a b).toLinearMap.equivOfDetNeZero
      (by rw [ellipseScaling_det]; exact mul_ne_zero ha.ne' hb.ne')).toContinuousLinearEquiv
  have he : (e : Euclidean 2 → Euclidean 2) = ellipseScaling a b := rfl
  rw [ellipseMap_scaling, Set.image_comp, ellipseMap_unit_image]
  have hf := e.toHomeomorph.image_frontier (Metric.closedBall (0 : Euclidean 2) 1)
  simpa only [frontier_closedBall _ one_ne_zero, ContinuousLinearEquiv.coe_toHomeomorph,
    he, ellipseRegion] using hf

theorem ellipseRegion_isCompact (a b : ℝ) : IsCompact (ellipseRegion a b) :=
  (isCompact_closedBall (0 : Euclidean 2) 1).image (ellipseScaling a b).continuous

theorem ellipseRegion_volume_ne_top {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    volume (ellipseRegion a b) ≠ ⊤ := by
  rw [ellipseRegion_volume ha hb]
  exact ENNReal.ofReal_ne_top

/-- The positive numerical integral in 10.12(b) is the enclosed ellipse's area. -/
theorem ellipse_integral_eq_area {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    surfaceIntegral (ellipseSurface a b) (coordinateOneForm 0 1) =
      (volume (ellipseRegion a b)).toReal := by
  rw [(ellipse_integrals a b).2.2.1, ellipseRegion_volume ha hb, ENNReal.toReal_ofReal]
  positivity

/-- The numerical integral in 10.12(c) is the volume of the image of its actual
parameterization, despite boundary points being identified. -/
theorem spherical_integral_eq_image_volume :
    surfaceIntegral sphericalSurface volumeForm =
      (volume (sphericalMap '' sphericalCell.carrier)).toReal := by
  rw [spherical_integral.2, sphericalMap_image,
    EuclideanSpace.volume_closedBall_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

/-- The boundary identifications mentioned in 10.12(c) occur at explicit points. -/
theorem sphericalMap_identifies_boundary_points :
    ∃ u v : Coord 3, u ∈ frontier sphericalCell.carrier ∧
      v ∈ frontier sphericalCell.carrier ∧ u ≠ v ∧ sphericalMap u = sphericalMap v := by
  refine ⟨0, ![0, Real.pi, 0], ?_, ?_, ?_, ?_⟩
  · rw [frontier, sphericalCell.isClosed_carrier.closure_eq]
    constructor
    · rw [Cell.mem_carrier]
      intro i
      fin_cases i <;> simp [sphericalCell] <;> positivity
    · simp [sphericalCell_mem_interior]
  · rw [frontier, sphericalCell.isClosed_carrier.closure_eq]
    constructor
    · rw [Cell.mem_carrier]
      intro i
      fin_cases i <;> simp [sphericalCell, Real.pi_pos.le]
    · simp [sphericalCell_mem_interior]
  · intro h
    have he := congrFun h (1 : Fin 3)
    exact Real.pi_ne_zero (by simpa using he.symm)
  · ext i
    fin_cases i <;> simp [sphericalMap]

/-- The geometric conclusions of 10.12, supplementary to its numerical contract. -/
theorem pma10_12_geometry :
    (∀ a b : ℝ, 0 < a → 0 < b →
      ellipseRegion a b = {x | (x 0 / a)^2 + (x 1 / b)^2 ≤ 1} ∧
      ellipseMap a b '' ellipseCell.carrier = frontier (ellipseRegion a b) ∧
      IsCompact (ellipseRegion a b) ∧ volume (ellipseRegion a b) ≠ ⊤ ∧
      surfaceIntegral (ellipseSurface a b) (coordinateOneForm 0 1) =
        (volume (ellipseRegion a b)).toReal) ∧
    surfaceIntegral sphericalSurface volumeForm =
      (volume (sphericalMap '' sphericalCell.carrier)).toReal ∧
    (∃ u v : Coord 3, u ∈ frontier sphericalCell.carrier ∧
      v ∈ frontier sphericalCell.carrier ∧ u ≠ v ∧ sphericalMap u = sphericalMap v) := by
  refine ⟨?_, spherical_integral_eq_image_volume, sphericalMap_identifies_boundary_points⟩
  intro a b ha hb
  exact ⟨ellipseRegion_eq_inequality ha hb, ellipseMap_image_eq_frontier ha hb,
    ellipseRegion_isCompact a b, ellipseRegion_volume_ne_top ha hb, ellipse_integral_eq_area ha hb⟩

end Rudin.PMA.Chapter10
