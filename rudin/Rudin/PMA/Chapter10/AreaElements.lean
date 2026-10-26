import Rudin.PMA.Chapter10.VectorFields
import Rudin.PMA.Chapter10.RectangleChains
import Mathlib.LinearAlgebra.CrossProduct

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The ordered real cross product, transported to the Euclidean norm model. -/
def cross3 (a b : Euclidean 3) : Euclidean 3 :=
  coordEquivEuclidean 3
    ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

def surfaceTangent {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (u : Coord 2) :
    Coord 2 →L[ℝ] Euclidean 3 := fderiv ℝ Φ.map u

def surfaceNormal {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (u : Coord 2) : Euclidean 3 :=
  cross3 (surfaceTangent Φ u (Pi.single 0 1)) (surfaceTangent Φ u (Pi.single 1 1))

def surfaceCoordinateJacobian {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    (u : Coord 2) (i j : Fin 3) : ℝ :=
  Matrix.det (fun a b : Fin 2 => surfaceTangent Φ u (Pi.single b 1) (![i, j] a))

/-- The affine tangent image belongs to the parameter point, with no injectivity assumption. -/
def surfaceTangentPlane {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (u : Coord 2) :
    AffineSubspace ℝ (Euclidean 3) :=
  AffineSubspace.mk' (Φ.map u) (surfaceTangent Φ u).toLinearMap.range

def areaIntegrand {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    (f : Euclidean 3 → ℝ) (u : Coord 2) : ℝ := f (Φ.map u) * ‖surfaceNormal Φ u‖

def areaIntegral {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    (f : Euclidean 3 → ℝ) : ℝ := Φ.domain.integral (areaIntegrand Φ f)

def surfaceArea {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) : ℝ := areaIntegral Φ (fun _ => 1)

def affineRectangleSurface (C : Cell 2) (p : Euclidean 3) (A : Coord 2 →L[ℝ] Euclidean 3) :
    Surface 2 3 univ where
  domain := .cell C
  map := fun u => p + A u
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (contDiff_const.add A.contDiff).contDiffOn
  mapsTo := mapsTo_univ _ _

/-- Source 10.46. Area is the actual native parameter integral. Its density
needs continuity only on the image, and all ranks and degenerate cells remain admitted. -/
def pma10_46_contract : Prop :=
  (∀ (E : Set (Euclidean 3)) (Φ : Surface 2 3 E),
    (∀ u : Coord 2, surfaceNormal Φ u = coordEquivEuclidean 3
      ![surfaceCoordinateJacobian Φ u 1 2, surfaceCoordinateJacobian Φ u 2 0,
        surfaceCoordinateJacobian Φ u 0 1]) ∧
    (∀ f : Euclidean 3 → ℝ, ContinuousOn f (Φ.map '' Φ.domain.carrier) →
      Φ.domain.Integrable (areaIntegrand Φ f) ∧
      areaIntegral Φ f = Φ.domain.integral (fun u => f (Φ.map u) * ‖surfaceNormal Φ u‖)) ∧
    Φ.domain.Integrable (fun u => ‖surfaceNormal Φ u‖) ∧
    surfaceArea Φ = Φ.domain.integral (fun u => ‖surfaceNormal Φ u‖) ∧
    (∀ u ∈ Φ.domain.carrier,
      let A := surfaceTangent Φ u
      let a := A (Pi.single 0 1)
      let b := A (Pi.single 1 1)
      let N := surfaceNormal Φ u
      inner ℝ N a = 0 ∧ inner ℝ N b = 0 ∧
      (∀ v : Coord 2, inner ℝ N (A v) = 0) ∧
      Matrix.det (fun i j : Fin 3 => (![a, b, N] j) i) = ‖N‖ ^ 2 ∧
      Module.finrank ℝ A.toLinearMap.range ≤ 2 ∧
      (Module.finrank ℝ A.toLinearMap.range = 2 ↔ N ≠ 0) ∧
      (Module.finrank ℝ A.toLinearMap.range < 2 ↔ N = 0) ∧
      (surfaceTangentPlane Φ u : Set (Euclidean 3)) = range (fun v => Φ.map u + A v) ∧
      Module.finrank ℝ (surfaceTangentPlane Φ u).direction = Module.finrank ℝ A.toLinearMap.range ∧
      (Module.finrank ℝ A.toLinearMap.range = 2 →
        0 < Matrix.det (fun i j : Fin 3 => (![a, b, N] j) i)))) ∧
  (∀ (C : Cell 2) (p : Euclidean 3) (A : Coord 2 →L[ℝ] Euclidean 3),
    let N := cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1))
    (∀ u, surfaceNormal (affineRectangleSurface C p A) u = N) ∧
    surfaceArea (affineRectangleSurface C p A) = ‖N‖ * (volume C.carrier).toReal ∧
    surfaceArea (affineRectangleSurface C p A) =
      ‖N‖ * ((C.upper 0 - C.lower 0) * (C.upper 1 - C.lower 1)) ∧
    surfaceArea (affineRectangleSurface (Cell.unit 2) p A) = ‖N‖)

lemma continuous_cross3 : Continuous (fun p : Euclidean 3 × Euclidean 3 => cross3 p.1 p.2) := by
  apply (coordEquivEuclidean 3).continuous.comp
  apply continuous_pi
  intro i
  have ha (j : Fin 3) : Continuous (fun p : Euclidean 3 × Euclidean 3 => p.1 j) :=
    (EuclideanSpace.proj j : Euclidean 3 →L[ℝ] ℝ).continuous.comp continuous_fst
  have hb (j : Fin 3) : Continuous (fun p : Euclidean 3 × Euclidean 3 => p.2 j) :=
    (EuclideanSpace.proj j : Euclidean 3 →L[ℝ] ℝ).continuous.comp continuous_snd
  fin_cases i
  · exact ((ha 1).mul (hb 2)).sub ((ha 2).mul (hb 1))
  · exact ((ha 2).mul (hb 0)).sub ((ha 0).mul (hb 2))
  · exact ((ha 0).mul (hb 1)).sub ((ha 1).mul (hb 0))

lemma surfaceNormal_continuousOn {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) :
    ContinuousOn (surfaceNormal Φ) Φ.domain.carrier := by
  have hc (i : Fin 2) : ContinuousOn (fun u => surfaceTangent Φ u (Pi.single i 1)) Φ.domain.carrier :=
    ((Φ.regularity.continuousOn_fderiv_of_isOpen Φ.open_neighborhood le_rfl).clm_apply
      continuousOn_const).mono Φ.domain_subset
  have h := continuous_cross3.comp_continuousOn ((hc 0).prodMk (hc 1))
  change ContinuousOn (fun u => cross3 (surfaceTangent Φ u (Pi.single 0 1))
    (surfaceTangent Φ u (Pi.single 1 1))) Φ.domain.carrier at h
  exact h

lemma areaIntegrand_continuousOn {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    {f : Euclidean 3 → ℝ} (hf : ContinuousOn f (Φ.map '' Φ.domain.carrier)) :
    ContinuousOn (areaIntegrand Φ f) Φ.domain.carrier :=
  (hf.comp (Φ.regularity.continuousOn.mono Φ.domain_subset) (mapsTo_image _ _)).mul
    (surfaceNormal_continuousOn Φ).norm

lemma areaIntegrand_integrable {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    {f : Euclidean 3 → ℝ} (hf : ContinuousOn f (Φ.map '' Φ.domain.carrier)) :
    Φ.domain.Integrable (areaIntegrand Φ f) :=
  ParameterDomain.integrable_of_continuousOn (areaIntegrand_continuousOn Φ hf)

lemma surfaceArea_eq_integral {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) :
    surfaceArea Φ = Φ.domain.integral (fun u => ‖surfaceNormal Φ u‖) := by
  change Φ.domain.integral (areaIntegrand Φ (fun _ => 1)) = _
  congr 1
  funext u
  exact one_mul _

lemma cross3_inner_left (a b : Euclidean 3) : inner ℝ (cross3 a b) a = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, cross3]
  ring

lemma cross3_inner_right (a b : Euclidean 3) : inner ℝ (cross3 a b) b = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, cross3]
  ring

lemma coord_two_eq_sum (v : Coord 2) :
    v = v 0 • Pi.single 0 1 + v 1 • Pi.single 1 1 := by
  ext i
  fin_cases i <;> simp

lemma cross3_inner_range (A : Coord 2 →L[ℝ] Euclidean 3) (v : Coord 2) :
    inner ℝ (cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1))) (A v) = 0 := by
  have hv : A v = v 0 • A (Pi.single 0 1) + v 1 • A (Pi.single 1 1) := by
    conv_lhs => rw [coord_two_eq_sum v]
    rw [map_add, map_smul, map_smul]
  rw [hv, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, cross3_inner_left, cross3_inner_right]
  ring

lemma cross3_det (a b : Euclidean 3) :
    Matrix.det (fun i j : Fin 3 => (![a, b, cross3 a b] j) i) = ‖cross3 a b‖ ^ 2 := by
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (![a, b, cross3 a b] j) i
  change M.det = _
  rw [Matrix.det_fin_three, EuclideanSpace.real_norm_sq_eq]
  simp [M, cross3, Fin.sum_univ_three]
  ring

lemma cross3_ne_zero_iff_linearIndependent (a b : Euclidean 3) :
    cross3 a b ≠ 0 ↔ LinearIndependent ℝ ![a, b] := by
  let e := coordEquivEuclidean 3
  have hz : cross3 a b = 0 ↔ crossProduct (fun i => a i) (fun i => b i) = 0 := by
    change e (crossProduct (fun i => a i) (fun i => b i)) = 0 ↔ _
    exact e.map_eq_zero_iff
  change (¬ cross3 a b = 0) ↔ _
  rw [not_congr hz]
  change crossProduct (fun i => a i) (fun i => b i) ≠ 0 ↔ _
  rw [crossProduct_ne_zero_iff_linearIndependent]
  have hi := e.symm.toLinearMap.linearIndependent_iff
    (LinearMap.ker_eq_bot.mpr e.symm.injective) (v := ![a, b])
  have he : (e.symm.toLinearMap ∘ ![a, b]) = ![(fun i => a i), (fun i => b i)] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at hi
  exact hi

lemma cross3_ne_zero_iff_injective (A : Coord 2 →L[ℝ] Euclidean 3) :
    cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1)) ≠ 0 ↔ Injective A := by
  rw [cross3_ne_zero_iff_linearIndependent]
  have hp : ![A (Pi.single 0 1), A (Pi.single 1 1)] =
      (fun i : Fin 2 => A (Pi.single i 1)) := by
    funext i
    fin_cases i <;> rfl
  rw [hp, linearIndependent_iff_injective_fintypeLinearCombination]
  have he : Fintype.linearCombination ℝ (fun i : Fin 2 => A (Pi.single i 1)) = A.toLinearMap := by
    apply LinearMap.ext
    intro v
    rw [Fintype.linearCombination_apply, Fin.sum_univ_two]
    change v 0 • A (Pi.single 0 1) + v 1 • A (Pi.single 1 1) = A v
    rw [← map_smul, ← map_smul, ← map_add, ← coord_two_eq_sum v]
  rw [he]
  rfl

lemma surface_rank_eq_two_iff (A : Coord 2 →L[ℝ] Euclidean 3) :
    Module.finrank ℝ A.toLinearMap.range = 2 ↔
      cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1)) ≠ 0 := by
  rw [cross3_ne_zero_iff_injective]
  have hn := A.toLinearMap.finrank_range_add_finrank_ker
  have hd : Module.finrank ℝ (Coord 2) = 2 := by
    simp [Coord, Module.finrank_fintype_fun_eq_card]
  rw [hd] at hn
  constructor
  · intro h
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    omega
  · intro h
    simpa only [hd] using LinearMap.finrank_range_of_inj (f := A.toLinearMap) h

lemma surface_rank_le_two (A : Coord 2 →L[ℝ] Euclidean 3) :
    Module.finrank ℝ A.toLinearMap.range ≤ 2 := by
  simpa [Coord, Module.finrank_fintype_fun_eq_card] using A.toLinearMap.finrank_range_le

lemma surface_rank_lt_two_iff (A : Coord 2 →L[ℝ] Euclidean 3) :
    Module.finrank ℝ A.toLinearMap.range < 2 ↔
      cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1)) = 0 := by
  have hr := surface_rank_le_two A
  have he := surface_rank_eq_two_iff A
  constructor
  · intro h
    by_contra hn
    have := he.mpr hn
    omega
  · intro h
    by_contra hn
    have heq : Module.finrank ℝ A.toLinearMap.range = 2 := by omega
    exact he.mp heq h

lemma surfaceNormal_eq_minors {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (u : Coord 2) :
    surfaceNormal Φ u = coordEquivEuclidean 3
      ![surfaceCoordinateJacobian Φ u 1 2, surfaceCoordinateJacobian Φ u 2 0,
        surfaceCoordinateJacobian Φ u 0 1] := by
  have hj (i j : Fin 3) : surfaceCoordinateJacobian Φ u i j =
      surfaceTangent Φ u (Pi.single 0 1) i * surfaceTangent Φ u (Pi.single 1 1) j -
      surfaceTangent Φ u (Pi.single 1 1) i * surfaceTangent Φ u (Pi.single 0 1) j := by
    let M : Matrix (Fin 2) (Fin 2) ℝ :=
      fun a b => surfaceTangent Φ u (Pi.single b 1) (![i, j] a)
    change M.det = _
    rw [Matrix.det_fin_two]
    rfl
  ext i
  fin_cases i <;> simp [surfaceNormal, cross3, hj] <;> ring

lemma surfaceTangentPlane_eq_range {E : Set (Euclidean 3)} (Φ : Surface 2 3 E) (u : Coord 2) :
    (surfaceTangentPlane Φ u : Set (Euclidean 3)) =
      range (fun v => Φ.map u + surfaceTangent Φ u v) := by
  ext x
  change x ∈ AffineSubspace.mk' (Φ.map u) (surfaceTangent Φ u).toLinearMap.range ↔ _
  rw [AffineSubspace.mem_mk']
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    change surfaceTangent Φ u v = x - Φ.map u at hv
    change Φ.map u + surfaceTangent Φ u v = x
    rw [hv]
    abel
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    change surfaceTangent Φ u v = Φ.map u + surfaceTangent Φ u v - Φ.map u
    abel

lemma surfaceNormal_affineRectangle (C : Cell 2) (p : Euclidean 3)
    (A : Coord 2 →L[ℝ] Euclidean 3) (u : Coord 2) :
    surfaceNormal (affineRectangleSurface C p A) u =
      cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1)) := by
  have hd : HasFDerivAt (fun v => p + A v) A u := A.hasFDerivAt.const_add p
  change cross3 (fderiv ℝ (fun v => p + A v) u (Pi.single 0 1))
    (fderiv ℝ (fun v => p + A v) u (Pi.single 1 1)) = _
  rw [hd.fderiv]

lemma surfaceArea_affineRectangle (C : Cell 2) (p : Euclidean 3)
    (A : Coord 2 →L[ℝ] Euclidean 3) :
    surfaceArea (affineRectangleSurface C p A) =
      ‖cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1))‖ * (volume C.carrier).toReal := by
  rw [surfaceArea_eq_integral]
  simp only [surfaceNormal_affineRectangle]
  change iteratedRIntegral C (fun _ => ‖cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1))‖) = _
  rw [iteratedRIntegral_eq_setIntegral continuousOn_const, setIntegral_const,
    measureReal_def, smul_eq_mul, mul_comm]

lemma surfaceArea_affineRectangle_product (C : Cell 2) (p : Euclidean 3)
    (A : Coord 2 →L[ℝ] Euclidean 3) :
    surfaceArea (affineRectangleSurface C p A) =
      ‖cross3 (A (Pi.single 0 1)) (A (Pi.single 1 1))‖ *
        ((C.upper 0 - C.lower 0) * (C.upper 1 - C.lower 1)) := by
  rw [surfaceArea_affineRectangle]
  change _ * (volume (Icc C.lower C.upper)).toReal = _
  rw [Real.volume_Icc_pi_toReal C.lower_le_upper, Fin.prod_univ_two]

lemma surfaceIntegrand_vectorTwoForm {E : Set (Euclidean 3)} (Φ : Surface 2 3 E)
    (F : VectorField) (u : Coord 2) :
    surfaceIntegrand Φ (vectorTwoForm F) u = inner ℝ (F (Φ.map u)) (surfaceNormal Φ u) := by
  simp [surfaceIntegrand, vectorTwoForm, radialBasis, map_sum, map_smul,
    evaluateForm_two_dx_mul_dx, PiLp.inner_apply, Fin.sum_univ_three, surfaceNormal,
    cross3, surfaceTangent, smul_eq_mul]
  ring

theorem pma10_46 : pma10_46_contract := by
  refine ⟨?_, ?_⟩
  · intro E Φ
    refine ⟨surfaceNormal_eq_minors Φ, fun f hf => ⟨areaIntegrand_integrable Φ hf, rfl⟩,
      ParameterDomain.integrable_of_continuousOn (surfaceNormal_continuousOn Φ).norm,
      surfaceArea_eq_integral Φ, ?_⟩
    intro u hu
    refine ⟨cross3_inner_left _ _, cross3_inner_right _ _, cross3_inner_range _,
      cross3_det _ _, surface_rank_le_two _, surface_rank_eq_two_iff _,
      surface_rank_lt_two_iff _, surfaceTangentPlane_eq_range Φ u, ?_, ?_⟩
    · rw [surfaceTangentPlane, AffineSubspace.direction_mk']
    · intro hr
      exact lt_of_lt_of_eq
        (sq_pos_of_pos (norm_pos_iff.mpr ((surface_rank_eq_two_iff _).mp hr)))
        (cross3_det _ _).symm
  · intro C p A
    refine ⟨surfaceNormal_affineRectangle C p A, surfaceArea_affineRectangle C p A,
      surfaceArea_affineRectangle_product C p A, ?_⟩
    simpa [Cell.unit] using surfaceArea_affineRectangle_product (Cell.unit 2) p A

end Rudin.PMA.Chapter10
