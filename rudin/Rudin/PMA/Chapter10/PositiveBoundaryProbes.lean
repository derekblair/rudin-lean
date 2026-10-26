import Rudin.PMA.Chapter10.BoundaryDefinitions

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private lemma simplex_one_eq_preimage : standardSimplex 1 =
    (fun u : Coord 1 => u 0) ⁻¹' Icc (0 : ℝ) 1 := by
  ext u
  simp [standardSimplex, Fin.sum_univ_one]

private def cubeCoordinates (u : Coord 1) : Coord 1 := fun i => (u i)^3

private lemma cubeCoordinates_contDiff : ContDiff ℝ 2 cubeCoordinates := by
  apply contDiff_pi.mpr
  intro i
  exact (contDiff_apply ℝ ℝ i).pow 3

private lemma cubeCoordinates_jacobian (u : Coord 1) :
    coordinateJacobian cubeCoordinates u = 3 * (u 0)^2 := by
  have hd : HasFDerivAt cubeCoordinates
      (ContinuousLinearMap.pi (fun i : Fin 1 =>
        (3 * (u i)^2) • (ContinuousLinearMap.proj i : Coord 1 →L[ℝ] ℝ))) u := by
    apply hasFDerivAt_pi.mpr
    intro i
    have hp : HasFDerivAt (fun v : Coord 1 => v i)
        (ContinuousLinearMap.proj i : Coord 1 →L[ℝ] ℝ) u := hasFDerivAt_apply i u
    simpa only [cubeCoordinates, Nat.reduceSub, nsmul_eq_mul, Nat.cast_ofNat] using! hp.pow 3
  rw [coordinateJacobian_eq_matrix, hd.fderiv, Matrix.det_fin_one]
  simp [LinearMap.toMatrix'_apply, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.proj_apply, Pi.single_apply]

private def cubeSimplex : C2Simplex 1 1 univ where
  map := coordEquivEuclidean 1 ∘ cubeCoordinates
  regularity := ⟨univ, isOpen_univ, subset_univ _,
    ((coordEquivEuclidean 1).contDiff.comp cubeCoordinates_contDiff).contDiffOn⟩
  mapsTo := mapsTo_univ _ _

private lemma cubeSimplex_coordinateMap : cubeSimplex.coordinateMap = cubeCoordinates := by
  funext u
  exact (coordEquivEuclidean 1).symm_apply_apply _

private def cubePositive : PositiveSimplex 1 univ where
  simplex := cubeSimplex
  injective := by
    intro u hu v hv he
    have hc := (coordEquivEuclidean 1).injective he
    ext i
    exact (Odd.strictMono_pow (by decide : Odd 3)).injective (congrFun hc i)
  positive := by
    intro u hu
    rw [cubeSimplex_coordinateMap, cubeCoordinates_jacobian]
    rw [simplex_one_eq_preimage] at hu
    have hi : u 0 ∈ interior (Icc (0 : ℝ) 1) :=
      (isOpenMap_eval (0 : Fin 1)).interior_preimage_subset_preimage_interior hu
    rw [interior_Icc] at hi
    exact mul_pos (by norm_num) (pow_pos hi.1 2)

private def identitySimplex : C2Simplex 1 1 univ where
  map := coordEquivEuclidean 1
  regularity := ⟨univ, isOpen_univ, subset_univ _, (coordEquivEuclidean 1).contDiff.contDiffOn⟩
  mapsTo := mapsTo_univ _ _

private lemma identitySimplex_coordinateMap : identitySimplex.coordinateMap = id := by
  funext u
  exact (coordEquivEuclidean 1).symm_apply_apply u

private def identityPositive : PositiveSimplex 1 univ where
  simplex := identitySimplex
  injective := (coordEquivEuclidean 1).injective.injOn
  positive := by
    intro u hu
    rw [identitySimplex_coordinateMap]
    simp [coordinateJacobian, fderiv_id]

private lemma cubeCoordinates_image : cubeCoordinates '' standardSimplex 1 = standardSimplex 1 := by
  have hmono : StrictMono (fun t : ℝ => t^3) := Odd.strictMono_pow (by decide : Odd 3)
  have himage : (fun t : ℝ => t^3) '' Icc (0 : ℝ) 1 = Icc 0 1 := by
    simpa using (continuous_id.pow 3).image_Icc_of_strictMono hmono (a := 0) (b := 1)
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [simplex_one_eq_preimage] at hv ⊢
    change (v 0)^3 ∈ Icc (0 : ℝ) 1
    rw [← himage]
    exact mem_image_of_mem _ hv
  · intro hu
    rw [simplex_one_eq_preimage] at hu
    obtain ⟨t, ht, he⟩ := show u 0 ∈ (fun t : ℝ => t^3) '' Icc (0 : ℝ) 1 by
      rwa [himage]
    refine ⟨fun _ => t, ?_, ?_⟩
    · rwa [simplex_one_eq_preimage]
    · ext i
      fin_cases i
      exact he

private lemma cubePositive_carrier : cubePositive.carrier = identityPositive.carrier := by
  change (coordEquivEuclidean 1 ∘ cubeCoordinates) '' standardSimplex 1 =
    coordEquivEuclidean 1 '' standardSimplex 1
  rw [image_comp, cubeCoordinates_image]

/-- The positive-parametrization theorem permits a singular derivative at
the boundary. The cubic and linear parametrizations induce the same boundary
functional for every continuous zero-form. -/
theorem cubic_positive_boundary_with_singular_endpoint :
    coordinateJacobian cubePositive.simplex.coordinateMap 0 = 0 ∧
    ChainEq cubePositive.boundary identityPositive.boundary := by
  constructor
  · change coordinateJacobian cubeSimplex.coordinateMap 0 = 0
    rw [cubeSimplex_coordinateMap, cubeCoordinates_jacobian]
    norm_num
  · exact pma10_31.1.2.2.1 0 univ cubePositive identityPositive isOpen_univ cubePositive_carrier

end Rudin.PMA.Chapter10.FidelityProbes
