import Rudin.PMA.Chapter10.CubicalStokes
import Rudin.PMA.Chapter10.TorusCalculus

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma cellFaceMap_three_zero (t : ℝ) (u : Coord 2) :
    cellFaceMap (0 : Fin 3) t u = ![t, u 0, u 1] := by
  ext j
  refine Fin.succAboveCases (0 : Fin 3) ?_ (fun l => ?_) j
  · simp only [cellFaceMap, Fin.insertNth_apply_same, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · simp only [cellFaceMap, Fin.insertNth_apply_succAbove]
    fin_cases l <;> rfl

lemma cellFaceMap_three_one (t : ℝ) (u : Coord 2) :
    cellFaceMap (1 : Fin 3) t u = ![u 0, t, u 1] := by
  ext j
  refine Fin.succAboveCases (1 : Fin 3) ?_ (fun l => ?_) j
  · simp only [cellFaceMap, Fin.insertNth_apply_same, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · simp only [cellFaceMap, Fin.insertNth_apply_succAbove]
    fin_cases l <;> rfl

lemma cellFaceMap_three_two (t : ℝ) (u : Coord 2) :
    cellFaceMap (2 : Fin 3) t u = ![u 0, u 1, t] := by
  ext j
  refine Fin.succAboveCases (2 : Fin 3) ?_ (fun l => ?_) j
  · simp only [cellFaceMap, Fin.insertNth_apply_same, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  · simp only [cellFaceMap, Fin.insertNth_apply_succAbove]
    fin_cases l <;> rfl

lemma torusCell_delete_zero (a : ℝ) (ha : 0 < a) :
    (torusCell a ha).delete 0 = torusOuterCell := by
  have hu : (fun j : Fin 2 => (torusCell a ha).upper ((0 : Fin 3).succAbove j)) =
      torusOuterCell.upper := by
    funext j
    fin_cases j <;> rfl
  unfold Cell.delete torusOuterCell
  congr 1

lemma torusFace_periodic_one (a b : ℝ) (ha : 0 < a) (ω : FormField 3) :
    surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 1 (2 * Real.pi)) ω =
    surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 1 0) ω := by
  have hm : torusMap b ∘ cellFaceMap (1 : Fin 3) (2 * Real.pi) =
      torusMap b ∘ cellFaceMap (1 : Fin 3) 0 := by
    funext u
    change torusMap b (cellFaceMap 1 (2 * Real.pi) u) = torusMap b (cellFaceMap 1 0 u)
    rw [cellFaceMap_three_one, cellFaceMap_three_one]
    simp [torusMap]
  have hD : (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 1 (2 * Real.pi)).domain =
      (cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 1 0).domain := by
    change (ParameterDomain.cell ((torusCell a ha).delete 1) : ParameterDomain 2) =
      ParameterDomain.cell ((torusCell a ha).delete 1)
    rfl
  exact surfaceIntegral_congr_map
    (Φ := cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1)
      1 (2 * Real.pi))
    (Ψ := cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 1 0)
    hD hm ω

lemma torusFace_periodic_two (a b : ℝ) (ha : 0 < a) (ω : FormField 3) :
    surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 2 (2 * Real.pi)) ω =
    surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 2 0) ω := by
  have hm : torusMap b ∘ cellFaceMap (2 : Fin 3) (2 * Real.pi) =
      torusMap b ∘ cellFaceMap (2 : Fin 3) 0 := by
    funext u
    change torusMap b (cellFaceMap 2 (2 * Real.pi) u) = torusMap b (cellFaceMap 2 0 u)
    rw [cellFaceMap_three_two, cellFaceMap_three_two]
    simp [torusMap]
  have hD : (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 2 (2 * Real.pi)).domain =
      (cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 2 0).domain := by
    change (ParameterDomain.cell ((torusCell a ha).delete 2) : ParameterDomain 2) =
      ParameterDomain.cell ((torusCell a ha).delete 2)
    rfl
  exact surfaceIntegral_congr_map
    (Φ := cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1)
      2 (2 * Real.pi))
    (Ψ := cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 2 0)
    hD hm ω

lemma torusFace_outer (a b : ℝ) (ha : 0 < a) (ω : FormField 3) :
    surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 0 a) ω = surfaceIntegral (torusOuterSurface a b) ω := by
  apply surfaceIntegral_congr_map
  · change ParameterDomain.cell ((torusCell a ha).delete 0) = .cell torusOuterCell
    rw [torusCell_delete_zero]
  · funext u
    change torusMap b (cellFaceMap 0 a u) = torusMap b ![a, u 0, u 1]
    rw [cellFaceMap_three_zero]

lemma evaluateForm_two_first_zero {n : ℕ} {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^2 (Coord n))) {v : Fin 2 → Euclidean n} (hv : v 0 = 0) :
    evaluateForm 2 v a = 0 := by
  rw [standard_expansion a ha]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro S hS
  suffices hz : evaluateForm 2 v (standardWedge S) = 0 by rw [hz, mul_zero]
  rw [standardWedge_eq_coordinateWedge, evaluateForm_coordinateWedge]
  let M : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
    v j ((powersetCard.ofFinEmbEquiv.symm S) i)
  change M.det = 0
  rw [Matrix.det_fin_two]
  simp [M, hv]

/-- The radius-zero face is a circle with a redundant parameter, so every
continuous two-form has zero native integral on it. -/
lemma torusFace_inner_zero (a b : ℝ) (ha : 0 < a)
    {ω : FormField 3} (hω : IsFormOn univ 2 ω) :
    surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 1) 0 0) ω = 0 := by
  let Φ := cellFaceSurface (torusCell a ha) (torusMap b) (torusMap_contDiff b 1) 0 0
  have hz (u : Coord 2) : fderiv ℝ Φ.map u (Pi.single 0 1) = 0 := by
    have hd := (torusMap_hasFDerivAt b (cellFaceMap 0 0 u)).comp u
      (cellFaceMap_hasFDerivAt (0 : Fin 3) 0 u)
    change fderiv ℝ (torusMap b ∘ cellFaceMap (0 : Fin 3) 0) u (Pi.single 0 1) = 0
    rw [hd.fderiv]
    simp only [ContinuousLinearMap.comp_apply, cellFaceLinear_single]
    rw [cellFaceMap_three_zero]
    ext j
    fin_cases j <;> simp [torusDerivative, Pi.single_apply, smul_eq_mul]
  have he : EqOn (surfaceIntegrand Φ ω) (fun _ => 0) Φ.domain.carrier := by
    intro u hu
    apply evaluateForm_two_first_zero (hω.1 _ (mem_univ _))
    exact hz u
  change surfaceIntegral Φ ω = 0
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral (Φ.continuousOn_integrand hω),
    setIntegral_congr_fun Φ.domain.isClosed.measurableSet he]
  simp

/-- All six actual cell faces reduce, as integration functionals on continuous
two-forms, to the outer torus surface. -/
lemma torus_boundary_representation (a b : ℝ) (ha : 0 < a) :
    ∃ Γ : SimplexChain 3 3 univ,
      (∀ ω : FormField 3, IsFormOn univ 3 ω →
        chainIntegral ω Γ = surfaceIntegral (torusSolidSurface a b ha) ω) ∧
      (∀ ω : FormField 3, IsFormOn univ 2 ω →
        chainIntegral ω (chainBoundary Γ) = surfaceIntegral (torusOuterSurface a b) ω) := by
  let Φ := cellMapSurface (torusCell a ha) (torusMap b)
    ((torusMap_contDiff b 2).of_le (by norm_num))
  let hΦ : Φ.IsC2 := cellMapSurface_isC2 (torusCell a ha) (torusMap b) (torusMap_contDiff b 2)
  refine ⟨Φ.integralChain hΦ, ?_, ?_⟩
  · intro ω hω
    rw [Surface.integralChain_integral Φ hΦ hω]
    exact surfaceIntegral_congr_map rfl rfl ω
  · intro ω hω
    change chainIntegral ω (Φ.boundaryChain hΦ) = _
    rw [cellMapSurface_boundary_integral (torusCell a ha) (torusMap b)
      (torusMap_contDiff b 2) hω]
    change (∑ i : Fin 3, (-1 : ℝ)^i.val *
      (surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
        (torusMap_contDiff b 1) i ((torusCell a ha).upper i)) ω -
       surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
        (torusMap_contDiff b 1) i ((torusCell a ha).lower i)) ω)) = _
    have he (i : Fin 3) : (-1 : ℝ)^i.val *
        (surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
          (torusMap_contDiff b 1) i ((torusCell a ha).upper i)) ω -
         surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
          (torusMap_contDiff b 1) i ((torusCell a ha).lower i)) ω) =
        if i = 0 then surfaceIntegral (torusOuterSurface a b) ω else 0 := by
      fin_cases i
      · change (-1 : ℝ)^0 *
          (surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
            (torusMap_contDiff b 1) 0 a) ω -
           surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
            (torusMap_contDiff b 1) 0 0) ω) = _
        rw [torusFace_outer a b ha ω, torusFace_inner_zero a b ha hω]
        simp
      · change (-1 : ℝ)^1 *
          (surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
            (torusMap_contDiff b 1) 1 (2 * Real.pi)) ω -
           surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
            (torusMap_contDiff b 1) 1 0) ω) = _
        rw [torusFace_periodic_one a b ha ω]
        simp
      · change (-1 : ℝ)^2 *
          (surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
            (torusMap_contDiff b 1) 2 (2 * Real.pi)) ω -
           surfaceIntegral (cellFaceSurface (torusCell a ha) (torusMap b)
            (torusMap_contDiff b 1) 2 0) ω) = _
        rw [torusFace_periodic_two a b ha ω]
        simp
    simp_rw [he]
    simp


end Rudin.PMA.Chapter10
