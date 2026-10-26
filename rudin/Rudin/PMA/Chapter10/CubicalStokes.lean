import Rudin.PMA.Chapter10.CellFaces
import Rudin.PMA.Chapter10.FormIntegralContinuity

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

lemma cellRIntegral_congr {k : ℕ} {C : Cell k} {f g : Coord k → ℝ}
    (hf : ContinuousOn f C.carrier) (hg : ContinuousOn g C.carrier) (he : EqOn f g C.carrier) :
    iteratedRIntegral C f = iteratedRIntegral C g := by
  rw [iteratedRIntegral_eq_setIntegral hf, iteratedRIntegral_eq_setIntegral hg]
  exact setIntegral_congr_fun C.isClosed_carrier.measurableSet he

lemma cellRIntegral_sum {k : ℕ} {C : Cell k} {ι : Type*} [Fintype ι] {f : ι → Coord k → ℝ}
    (hf : ∀ a, ContinuousOn (f a) C.carrier) :
    iteratedRIntegral C (fun u => ∑ a, f a u) = ∑ a, iteratedRIntegral C (f a) := by
  rw [iteratedRIntegral_eq_setIntegral (continuousOn_finsetSum _ (fun a _ => hf a))]
  simp_rw [iteratedRIntegral_eq_setIntegral (hf _)]
  exact integral_finsetSum _ (fun a _ => Cell.integrable_measure (hf a))

lemma cellRIntegral_const_mul {k : ℕ} {C : Cell k} {f : Coord k → ℝ}
    (hf : ContinuousOn f C.carrier) (c : ℝ) :
    iteratedRIntegral C (fun u => c * f u) = c * iteratedRIntegral C f := by
  have hc : ContinuousOn (fun u => c * f u) C.carrier := continuousOn_const.mul hf
  rw [iteratedRIntegral_eq_setIntegral hc,
    iteratedRIntegral_eq_setIntegral hf, integral_const_mul]

lemma standard_cell_stokes {d : ℕ} (C : Cell (d + 1)) {ω : FormField (d + 1)}
    (hω : IsCFormOn 1 univ d ω) :
    surfaceIntegral (identityParameterSurface (.cell C)) (exteriorDerivative ω) =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        (surfaceIntegral (standardCellFace C i (C.upper i)) ω -
          surfaceIntegral (standardCellFace C i (C.lower i)) ω) := by
  classical
  let a (i : Fin (d + 1)) : Coord (d + 1) → ℝ :=
    omittedCoefficient ω i ∘ coordEquivEuclidean (d + 1)
  have ha (i : Fin (d + 1)) : ContDiff ℝ 1 (a i) :=
    (contDiffOn_univ.mp (contDiffOn_omittedCoefficient hω i)).comp
      (coordEquivEuclidean (d + 1)).contDiff
  have hd (i : Fin (d + 1)) : ContinuousOn (simplexCoordinateDerivative (a i) i) C.carrier :=
    (continuousOn_simplexCoordinateDerivative isOpen_univ (ha i).contDiffOn i).mono (subset_univ _)
  have hc : ContinuousOn
      (surfaceIntegrand (identityParameterSurface (.cell C)) (exteriorDerivative ω)) C.carrier :=
    (identityParameterSurface (.cell C)).continuousOn_integrand
      (isCFormOn_exteriorDerivative (r := 0) isOpen_univ hω).isFormOn
  have hg : ContinuousOn (fun u => ∑ i : Fin (d + 1),
      (-1 : ℝ)^i.val * simplexCoordinateDerivative (a i) i u) C.carrier :=
    continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hd i))
  have he : EqOn (surfaceIntegrand (identityParameterSurface (.cell C)) (exteriorDerivative ω))
      (fun u => ∑ i : Fin (d + 1), (-1 : ℝ)^i.val * simplexCoordinateDerivative (a i) i u)
      C.carrier := by
    intro u hu
    change evaluateForm (d + 1)
      (fun j => fderiv ℝ (coordEquivEuclidean (d + 1)) u (Pi.single j 1))
      (exteriorDerivative ω (coordEquivEuclidean (d + 1) u)) = _
    rw [(coordEquivEuclidean (d + 1)).fderiv]
    simp only [ContinuousLinearEquiv.coe_coe, coordEquivEuclidean_single,
      exteriorDerivative_eq_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [evaluateForm_dx_standard i
      (coefficientDerivative_mem isOpen_univ hω.isFormOn (mem_univ _) i)]
    rw [simplexCoordinateDerivative_comp_coordEquiv
      ((contDiffOn_univ.mp (contDiffOn_omittedCoefficient hω i)).differentiable
        (by norm_num)).differentiableAt]
    unfold omittedCoefficient
    rw [coordinatePartial_linear_formEvaluation
      (hω.coefficientsDifferentiableAt isOpen_univ (mem_univ _))]
  change iteratedRIntegral C _ = _
  rw [cellRIntegral_congr hc hg he, cellRIntegral_sum
    (f := fun i u => (-1 : ℝ)^i.val * simplexCoordinateDerivative (a i) i u)
      (fun i => continuousOn_const.mul (hd i))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [cellRIntegral_const_mul (hd i),
    cell_coordinate_ftc C isOpen_univ (subset_univ _) (ha i).contDiffOn i]
  congr 1
  congr 1 <;> change iteratedRIntegral (C.delete i) _ = iteratedRIntegral (C.delete i) _ <;>
    congr 1 <;> funext u <;> exact (standardCellFace_integrand C i _ ω u).symm

lemma cellMapSurface_stokes {d n : ℕ} (C : Cell (d + 1)) (F : Coord (d + 1) → Euclidean n)
    (hF : ContDiff ℝ 2 F) {ω : FormField n} (hω : IsCFormOn 1 univ d ω) :
    surfaceIntegral (cellMapSurface C F (hF.of_le (by norm_num))) (exteriorDerivative ω) =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        (surfaceIntegral (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.upper i)) ω -
          surfaceIntegral (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.lower i)) ω) := by
  let T := F ∘ (coordEquivEuclidean (d + 1)).symm
  let Φ := cellMapSurface C F (hF.of_le (by norm_num))
  have hT : ContDiffOn ℝ 2 T univ :=
    (hF.comp (coordEquivEuclidean (d + 1)).symm.contDiff).contDiffOn
  have hp := pullbackForm_isCFormOn isOpen_univ hT (mapsTo_univ _ _) hω
  have he : exteriorDerivative (pullbackForm T ω) = pullbackForm T (exteriorDerivative ω) :=
    funext (fun x => exteriorDerivative_pullback isOpen_univ isOpen_univ hT
      (mapsTo_univ _ _) hω (mem_univ x))
  have hd : IsFormOn univ (d + 1) (exteriorDerivative ω) :=
    (isCFormOn_exteriorDerivative (r := 0) isOpen_univ hω).isFormOn
  calc
    surfaceIntegral Φ (exteriorDerivative ω) =
        surfaceIntegral (identityParameterSurface (.cell C)) (pullbackForm T (exteriorDerivative ω)) :=
      (pma10_24 n (d + 1) univ Φ (exteriorDerivative ω) isOpen_univ hd).2.2
    _ = surfaceIntegral (identityParameterSurface (.cell C))
        (exteriorDerivative (pullbackForm T ω)) := by rw [he]
    _ = _ := by
      rw [standard_cell_stokes C hp]
      apply Finset.sum_congr rfl
      intro i hi
      rw [cellFaceSurface_pullback_integral C F _ i (C.upper i) hω.isFormOn,
        cellFaceSurface_pullback_integral C F _ i (C.lower i) hω.isFormOn]

/-- The signed actual faces, each represented by its finite affine simplex chain. -/
def cellBoundaryChain {d n : ℕ} (C : Cell (d + 1)) (F : Coord (d + 1) → Euclidean n)
    (hF : ContDiff ℝ 2 F) : SimplexChain d n univ :=
  ∑ i : Fin (d + 1), (-1 : ℤ)^i.val •
    ((cellFaceSurface C F (hF.of_le (by norm_num)) i (C.upper i)).integralChain
        (cellFaceSurface_isC2 C F hF i (C.upper i)) -
      (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.lower i)).integralChain
        (cellFaceSurface_isC2 C F hF i (C.lower i)))

lemma cellBoundaryChain_integral {d n : ℕ} (C : Cell (d + 1)) (F : Coord (d + 1) → Euclidean n)
    (hF : ContDiff ℝ 2 F) {ω : FormField n} (hω : IsFormOn univ d ω) :
    chainIntegral ω (cellBoundaryChain C F hF) =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        (surfaceIntegral (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.upper i)) ω -
          surfaceIntegral (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.lower i)) ω) := by
  simp only [cellBoundaryChain, map_sum, map_smul, map_sub, zsmul_eq_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Surface.integralChain_integral _ _ hω]

lemma cellMapSurface_boundary_eq {d n : ℕ} (C : Cell (d + 1))
    (F : Coord (d + 1) → Euclidean n) (hF : ContDiff ℝ 2 F) :
    ChainEq ((cellMapSurface C F (hF.of_le (by norm_num))).boundaryChain (cellMapSurface_isC2 C F hF))
      (cellBoundaryChain C F hF) := by
  apply chainEq_of_c1
  intro ω hω
  rw [cellBoundaryChain_integral C F hF hω.isFormOn,
    ← Surface.stokes isOpen_univ _ _ hω]
  exact cellMapSurface_stokes C F hF hω

lemma cellMapSurface_boundary_integral {d n : ℕ} (C : Cell (d + 1))
    (F : Coord (d + 1) → Euclidean n) (hF : ContDiff ℝ 2 F)
    {ω : FormField n} (hω : IsFormOn univ d ω) :
    chainIntegral ω ((cellMapSurface C F (hF.of_le (by norm_num))).boundaryChain
      (cellMapSurface_isC2 C F hF)) =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        (surfaceIntegral (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.upper i)) ω -
          surfaceIntegral (cellFaceSurface C F (hF.of_le (by norm_num)) i (C.lower i)) ω) := by
  rw [cellMapSurface_boundary_eq C F hF ω hω, cellBoundaryChain_integral C F hF hω]

end Rudin.PMA.Chapter10
