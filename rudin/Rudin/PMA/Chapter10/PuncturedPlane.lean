import Rudin.PMA.Chapter10.AngularForm
import Rudin.PMA.Chapter10.CellNormalization

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma puncturedCircleMap_contDiff (r : ℝ) (m : WithTop ENat) :
    ContDiff ℝ m (puncturedCircleMap r) := by
  apply (coordEquivEuclidean 2).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  have hc : ContDiff ℝ m (fun u : Coord 1 => u 0) := contDiff_apply ℝ ℝ 0
  fin_cases i
  · exact contDiff_const.mul hc.cos
  · exact contDiff_const.mul hc.sin

lemma puncturedCircleMap_radiusSq (r : ℝ) (u : Coord 1) :
    planeRadiusSq (puncturedCircleMap r u) = r ^ 2 := by
  simp only [planeRadiusSq, puncturedCircleMap, coordEquivEuclidean_apply_coordinate,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = r ^ 2 * (Real.cos (u 0) ^ 2 + Real.sin (u 0) ^ 2) := by ring
    _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]

def puncturedCircleSurface (r : ℝ) (hr : 0 < r) : Surface 1 2 (puncturedSpace 2) where
  domain := .cell ellipseCell
  map := puncturedCircleMap r
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (puncturedCircleMap_contDiff r 1).contDiffOn
  mapsTo := by
    intro u hu hz
    have he := puncturedCircleMap_radiusSq r u
    rw [hz] at he
    simp only [planeRadiusSq, PiLp.zero_apply, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at he
    nlinarith

lemma puncturedCircleSurface_isC2 (r : ℝ) (hr : 0 < r) : (puncturedCircleSurface r hr).IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _, (puncturedCircleMap_contDiff r 2).contDiffOn⟩

lemma puncturedCircleSurface_closed (r : ℝ) (hr : 0 < r) :
    (puncturedCircleSurface r hr).map 0 =
      (puncturedCircleSurface r hr).map (fun _ => 2 * Real.pi) := by
  exact ellipseSurface_closed r r

lemma surfaceIntegrand_angularForm {E : Set (Euclidean 2)} (Φ : Surface 1 2 E) (u : Coord 1) :
    surfaceIntegrand Φ angularForm u = (planeRadiusSq (Φ.map u))⁻¹ *
      (surfaceIntegrand Φ (coordinateOneForm 0 1) u -
        surfaceIntegrand Φ (coordinateOneForm 1 0) u) := by
  simp only [surfaceIntegrand, angularForm, coordinateOneForm, planeRadiusSq,
    map_smul, map_sub, smul_eq_mul]

lemma puncturedCircle_angular_integrand (r : ℝ) (hr : 0 < r) {u : Coord 1}
    (hu : u ∈ ellipseCell.carrier) : surfaceIntegrand (puncturedCircleSurface r hr) angularForm u = 1 := by
  have hv : (fun _ : Fin 1 => u 0) = u := by funext i; fin_cases i; rfl
  have he := ellipse_integrands r r ((Cell.mem_carrier.mp hu) 0)
  rw [hv] at he
  rw [surfaceIntegrand_angularForm]
  have h0 : surfaceIntegrand (puncturedCircleSurface r hr) (coordinateOneForm 0 1) u =
      (r * r) * Real.cos (u 0) ^ 2 := he.1
  have h1 : surfaceIntegrand (puncturedCircleSurface r hr) (coordinateOneForm 1 0) u =
      -(r * r) * Real.sin (u 0) ^ 2 := he.2
  rw [h0, h1]
  change (planeRadiusSq (puncturedCircleMap r u))⁻¹ * _ = 1
  rw [puncturedCircleMap_radiusSq]
  have ht : (r * r) * Real.cos (u 0) ^ 2 - (-(r * r) * Real.sin (u 0) ^ 2) = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos (u 0) ^ 2 + Real.sin (u 0) ^ 2) := by ring
      _ = _ := by rw [Real.cos_sq_add_sin_sq, mul_one]
  rw [ht, inv_mul_cancel₀ (pow_ne_zero _ hr.ne')]

lemma puncturedCircle_angular_integral (r : ℝ) (hr : 0 < r) :
    surfaceIntegral (puncturedCircleSurface r hr) angularForm = 2 * Real.pi := by
  have hc := (puncturedCircleSurface r hr).continuousOn_integrand angularForm_closed.1.isFormOn
  change iteratedRIntegral ellipseCell _ = _
  rw [iteratedRIntegral_one_eq_intervalIntegral hc]
  calc
    _ = ∫ t in (0 : ℝ)..(2 * Real.pi), (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      apply puncturedCircle_angular_integrand r hr
      have h : t ∈ Icc (0 : ℝ) (2 * Real.pi) := by
        simpa [ellipseCell, uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] using ht
      exact ⟨fun _ => h.1, fun _ => h.2⟩
    _ = _ := by simp

def puncturedCircleSimplex (r : ℝ) (hr : 0 < r) : C2Simplex 1 2 (puncturedSpace 2) :=
  (puncturedCircleSurface r hr).intervalSimplex ellipseCell rfl (puncturedCircleSurface_isC2 r hr)

lemma puncturedCircleSimplex_formula (r : ℝ) (hr : 0 < r) :
    (puncturedCircleSimplex r hr).map =
      (fun u => puncturedCircleMap r (fun _ => 2 * Real.pi * u 0)) := by
  funext u
  change puncturedCircleMap r (cellNormalize ellipseCell u) = _
  congr 1
  funext i
  fin_cases i
  simp [cellNormalize, ellipseCell]

lemma puncturedCircleSimplex_integral (r : ℝ) (hr : 0 < r) {ω : FormField 2}
    (hω : IsFormOn (puncturedSpace 2) 1 ω) :
    chainIntegral ω (Finsupp.single (puncturedCircleSimplex r hr) 1) =
      surfaceIntegral (puncturedCircleSurface r hr) ω := by
  rw [chainIntegral_single, Int.cast_one, one_mul]
  exact surfaceIntegral_intervalSimplex _ _ rfl _ hω

lemma puncturedCircleSimplex_cycle (r : ℝ) (hr : 0 < r) :
    ChainEq (chainBoundary (Finsupp.single (puncturedCircleSimplex r hr) 1)) 0 := by
  have hf : (puncturedCircleSimplex r hr).face 0 = (puncturedCircleSimplex r hr).face 1 := by
    apply C2Simplex.ext
    funext u
    change (puncturedCircleSimplex r hr).map (standardFaceMap 0 u) =
      (puncturedCircleSimplex r hr).map (standardFaceMap 1 u)
    rw [puncturedCircleSimplex_formula]
    have h0 : (standardFaceMap (0 : Fin 2) u) 0 = 1 := by
      rw [standardFaceMap_zero]
      simp
    have h1 : (standardFaceMap (1 : Fin 2) u) 0 = 0 := by
      rw [show (1 : Fin 2) = (0 : Fin 1).succ by rfl, standardFaceMap_succ]
      simp
    change puncturedCircleMap r (fun _ => 2 * Real.pi * (standardFaceMap 0 u) 0) =
      puncturedCircleMap r (fun _ => 2 * Real.pi * (standardFaceMap 1 u) 0)
    rw [h0, h1, mul_one, mul_zero]
    exact (puncturedCircleSurface_closed r hr).symm
  have hz : chainBoundary (Finsupp.single (puncturedCircleSimplex r hr) 1) = 0 := by
    simp [chainBoundary_single, simplexBoundary, Fin.sum_univ_two, hf]
  rw [hz]
  intro ω hω
  rfl

theorem pma10_36 : pma10_36_contract := by
  have hne (r : ℝ) (hr : 0 < r) :
      chainIntegral angularForm (Finsupp.single (puncturedCircleSimplex r hr) 1) ≠ 0 := by
    rw [puncturedCircleSimplex_integral r hr angularForm_closed.1.isFormOn,
      puncturedCircle_angular_integral]
    positivity
  refine ⟨angularForm_closed, ?_, ?_⟩
  · exact not_exact_of_nonzero_cycle_integral (puncturedSpace_isOpen 2) angularForm_closed.1.isFormOn
      (Finsupp.single (puncturedCircleSimplex 1 zero_lt_one) 1)
      (puncturedCircleSimplex_cycle 1 zero_lt_one) (hne 1 zero_lt_one)
  · intro r hr
    refine ⟨puncturedCircleSurface r hr, rfl, rfl, puncturedCircleSurface_closed r hr,
      ParameterDomain.integrable_of_continuousOn
        ((puncturedCircleSurface r hr).continuousOn_integrand angularForm_closed.1.isFormOn),
      puncturedCircle_angular_integral r hr, ?_, puncturedCircleSimplex r hr,
      puncturedCircleSimplex_formula r hr, fun _ hω => puncturedCircleSimplex_integral r hr hω,
      puncturedCircleSimplex_cycle r hr, ?_⟩
    · rw [puncturedCircle_angular_integral]
      positivity
    · exact not_boundary_of_closed_integral_ne_zero (puncturedSpace_isOpen 2) angularForm_closed
        (Finsupp.single (puncturedCircleSimplex r hr) 1) (hne r hr)

end Rudin.PMA.Chapter10
