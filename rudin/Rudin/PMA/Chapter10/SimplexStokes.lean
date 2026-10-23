import Rudin.PMA.Chapter10.StandardSimplexSurface
import Rudin.PMA.Chapter10.SimplexBoundaries
import Rudin.PMA.Chapter10.SimplexOrientation
import Rudin.PMA.Chapter10.PullbackDifferentiation
import Rudin.PMA.Chapter10.SimplexFTC
import Rudin.PMA.Chapter10.StokesCoefficients
import Rudin.PMA.Chapter10.SimplexFormFaces

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The standard parameter-simplex case of Stokes. General C² simplices and
finite integer chains are transported from this scalar-coefficient calculation. -/
def standardSimplexStokes_contract : Prop :=
  ∀ (d : ℕ) (U : Set (Euclidean (d + 1))) (ω : FormField (d + 1))
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U),
    IsOpen U → IsCFormOn 1 U d ω →
      surfaceIntegral (standardC2Simplex U hSU).toSurface (exteriorDerivative ω) =
        chainIntegral ω (simplexBoundary (standardC2Simplex U hSU))

lemma simplexRIntegral_sum {k : ℕ} {ι : Type*} [Fintype ι] {f : ι → Coord k → ℝ}
    (hf : ∀ a, ContinuousOn (f a) (standardSimplex k)) :
    simplexRIntegral (fun u => ∑ a, f a u) = ∑ a, simplexRIntegral (f a) := by
  rw [simplexRIntegral_eq_integral (continuousOn_finsetSum _ (fun a _ => hf a))]
  simp_rw [simplexRIntegral_eq_integral (hf _)]
  exact integral_finsetSum _ (fun a _ => (hf a).integrableOn_compact (isCompact_standardSimplex k))

lemma simplexRIntegral_sub {k : ℕ} {f g : Coord k → ℝ}
    (hf : ContinuousOn f (standardSimplex k)) (hg : ContinuousOn g (standardSimplex k)) :
    simplexRIntegral (fun u => f u - g u) = simplexRIntegral f - simplexRIntegral g := by
  change simplexRIntegral (f - g) = simplexRIntegral f - simplexRIntegral g
  rw [simplexRIntegral_eq_integral (hf.sub hg), simplexRIntegral_eq_integral hf,
    simplexRIntegral_eq_integral hg]
  exact integral_sub (hf.integrableOn_compact (isCompact_standardSimplex k))
    (hg.integrableOn_compact (isCompact_standardSimplex k))

lemma simplexRIntegral_congr {k : ℕ} {f g : Coord k → ℝ}
    (hf : ContinuousOn f (standardSimplex k)) (hg : ContinuousOn g (standardSimplex k))
    (he : EqOn f g (standardSimplex k)) : simplexRIntegral f = simplexRIntegral g := by
  rw [simplexRIntegral_eq_integral hf, simplexRIntegral_eq_integral hg]
  exact setIntegral_congr_fun (isClosed_standardSimplex k).measurableSet he

/-- Reordering the upper face to the single ordered face opposite zero. -/
lemma upperFace_eq_standardFace_comp {d : ℕ} (i : Fin (d + 1)) (u : Coord d) :
    i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u =
      standardFaceMap (0 : Fin (d + 2)) (simplexVertexPermutation i.cycleRange.symm u) := by
  let p : Fin (d + 1) → Coord (d + 1) := fun j => Pi.single (i.cycleRange.symm j) 1
  have ha : affineMapFromVertices p =
      (standardFaceAffine (0 : Fin (d + 2))).comp (simplexVertexPermutation i.cycleRange.symm) := by
    apply affineMap_ext_standardVertex
    intro j
    change affineMapFromVertices p (standardVertex d j) =
      standardFaceMap 0 (simplexVertexPermutation i.cycleRange.symm (standardVertex d j))
    rw [affineMapFromVertices_standardVertex, simplexVertexPermutation_vertex, standardFaceMap_vertex]
    simp only [p, standardVertex, Fin.succAbove_zero, Fin.cons_succ]
  have hp : affineMapFromVertices p u =
      i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u := by
    rw [affineMapFromVertices_barycentric, Fin.sum_univ_succ]
    simp only [p, Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ, barycentricWeights,
      Fin.cons_zero, Fin.cons_succ]
    ext l
    refine Fin.succAboveCases i ?_ (fun j => ?_) l
    · simp [Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]
    · simp [Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove, eq_comm]
  rw [← hp, ha]
  rfl

lemma simplexRIntegral_upper_face {d : ℕ} {f : Coord (d + 1) → ℝ}
    (hf : ContinuousOn f (standardSimplex (d + 1))) (i : Fin (d + 1)) :
    simplexRIntegral (fun u => f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u)) =
      simplexRIntegral (fun u => f (standardFaceMap (0 : Fin (d + 2)) u)) := by
  have hc : ContinuousOn (fun u => f (standardFaceMap (0 : Fin (d + 2)) u)) (standardSimplex d) :=
    hf.comp (standardFaceMap_contDiff 0 1).continuous.continuousOn (standardFaceMap_mapsTo 0)
  have he : (fun u => f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u)) =
      (fun u => f (standardFaceMap (0 : Fin (d + 2)) u)) ∘ simplexVertexPermutation i.cycleRange.symm := by
    funext u
    rw [upperFace_eq_standardFace_comp i u]
    rfl
  rw [he]
  exact (simplexRIntegral_vertexPermutation i.cycleRange.symm hc).2

lemma standardFaceMap_hasFDerivAt {d : ℕ} (i : Fin (d + 2)) (u : Coord d) :
    HasFDerivAt (standardFaceMap i) (vertexLinear (standardVertex (d + 1) ∘ i.succAbove)) u :=
  (vertexLinear (standardVertex (d + 1) ∘ i.succAbove)).hasFDerivAt.const_add
    ((standardVertex (d + 1) ∘ i.succAbove) 0)

lemma standardFace_tangent_difference {d : ℕ} (i : Fin (d + 2)) (j : Fin d) :
    vertexLinear (standardVertex (d + 1) ∘ i.succAbove) (Pi.single j 1) =
      standardFaceMap i (Pi.single j 1) - standardFaceMap i 0 := by
  simp [standardFaceMap, standardFaceAffine, affineMapFromVertices]

lemma standardFace_tangent_succ {d : ℕ} (i : Fin (d + 1)) (j : Fin d) :
    coordEquivEuclidean (d + 1)
      (vertexLinear (standardVertex (d + 1) ∘ i.succ.succAbove) (Pi.single j 1)) =
      coordinateVector (d + 1) (i.succAbove j) := by
  rw [standardFace_tangent_difference, standardFaceMap_succ, standardFaceMap_succ]
  have he : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 (Pi.single j 1) -
      i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 0 = Pi.single (i.succAbove j) 1 := by
    ext l
    refine Fin.succAboveCases i ?_ (fun h => ?_) l
    · simp [Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]
    · simp [Pi.single_apply, eq_comm]
  rw [he, coordEquivEuclidean_single]

lemma standardFace_tangent_zero {d : ℕ} (j : Fin d) :
    coordEquivEuclidean (d + 1)
      (vertexLinear (standardVertex (d + 1) ∘ (0 : Fin (d + 2)).succAbove) (Pi.single j 1)) =
      coordinateVector (d + 1) j.succ - coordinateVector (d + 1) 0 := by
  rw [standardFace_tangent_difference, standardFaceMap_zero, standardFaceMap_zero]
  have he : Fin.cons (1 - ∑ l, (Pi.single j (1 : ℝ)) l) (Pi.single j 1) -
      Fin.cons (1 - ∑ _ : Fin d, (0 : ℝ)) (0 : Coord d) =
      (Pi.single j.succ 1 : Coord (d + 1)) - Pi.single 0 1 := by
    ext l
    refine Fin.cases ?_ (fun h => ?_) l <;> simp [Pi.single_apply]
  simp only [Pi.zero_apply]
  rw [he, map_sub, coordEquivEuclidean_single, coordEquivEuclidean_single]

lemma standardSimplex_full_integrand {d : ℕ} {U : Set (Euclidean (d + 1))}
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U)
    (ω : FormField (d + 1)) (u : Coord (d + 1)) :
    surfaceIntegrand (standardC2Simplex U hSU).toSurface ω u =
      evaluateForm (d + 1) (fun j => coordinateVector (d + 1) j) (ω (coordEquivEuclidean (d + 1) u)) := by
  change evaluateForm (d + 1)
    (fun j => fderiv ℝ (coordEquivEuclidean (d + 1)) u (Pi.single j 1))
      (ω (coordEquivEuclidean (d + 1) u)) = _
  rw [(coordEquivEuclidean (d + 1)).fderiv]
  simp only [ContinuousLinearEquiv.coe_coe, coordEquivEuclidean_single]

lemma standardSimplex_face_integrand {d : ℕ} {U : Set (Euclidean (d + 1))}
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U)
    (ω : FormField (d + 1)) (i : Fin (d + 2)) (u : Coord d) :
    surfaceIntegrand ((standardC2Simplex U hSU).face i).toSurface ω u =
      evaluateForm d (fun j => coordEquivEuclidean (d + 1)
        (vertexLinear (standardVertex (d + 1) ∘ i.succAbove) (Pi.single j 1)))
        (ω (coordEquivEuclidean (d + 1) (standardFaceMap i u))) := by
  have hd := (coordEquivEuclidean (d + 1)).hasFDerivAt.comp u (standardFaceMap_hasFDerivAt i u)
  change evaluateForm d (fun j => fderiv ℝ
    (coordEquivEuclidean (d + 1) ∘ standardFaceMap i) u (Pi.single j 1)) (ω _) = _
  rw [hd.fderiv]
  rfl

lemma standardSimplex_face_integrand_succ {d : ℕ} {U : Set (Euclidean (d + 1))}
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U)
    (ω : FormField (d + 1)) (i : Fin (d + 1)) (u : Coord d) :
    surfaceIntegrand ((standardC2Simplex U hSU).face i.succ).toSurface ω u =
      omittedCoefficient ω i (coordEquivEuclidean (d + 1)
        (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u)) := by
  rw [standardSimplex_face_integrand]
  simp only [standardFace_tangent_succ, standardFaceMap_succ, omittedCoefficient]

lemma standardSimplex_face_integrand_zero {d : ℕ} {U : Set (Euclidean (d + 1))}
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U)
    {ω : FormField (d + 1)} (hω : IsFormOn U d ω) {u : Coord d} (hu : u ∈ standardSimplex d) :
    surfaceIntegrand ((standardC2Simplex U hSU).face 0).toSurface ω u =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        omittedCoefficient ω i (coordEquivEuclidean (d + 1) (standardFaceMap 0 u)) := by
  rw [standardSimplex_face_integrand]
  simp only [standardFace_tangent_zero]
  exact evaluateForm_upper_standard (hω.1 _ (hSU (standardFaceMap_mapsTo 0 hu)))

lemma standardSimplex_derivative_integrand {d : ℕ} {U : Set (Euclidean (d + 1))}
    (hU : IsOpen U)
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U)
    {ω : FormField (d + 1)} (hω : IsCFormOn 1 U d ω)
    {u : Coord (d + 1)} (hu : u ∈ standardSimplex (d + 1)) :
    surfaceIntegrand (standardC2Simplex U hSU).toSurface (exteriorDerivative ω) u =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        coordinatePartial (omittedCoefficient ω i) (coordEquivEuclidean (d + 1) u) i := by
  rw [standardSimplex_full_integrand, exteriorDerivative_eq_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [evaluateForm_dx_standard i (coefficientDerivative_mem hU hω.isFormOn (hSU hu) i)]
  unfold omittedCoefficient
  rw [coordinatePartial_linear_formEvaluation (hω.coefficientsDifferentiableAt hU (hSU hu))]

/-- Stokes on the standard simplex, from scalar FTC and the actual signed face
integrands. This includes a one-simplex with its two zero-dimensional faces. -/
theorem standard_simplex_stokes {d : ℕ} {U : Set (Euclidean (d + 1))}
    (hU : IsOpen U)
    (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U)
    {ω : FormField (d + 1)} (hω : IsCFormOn 1 U d ω) :
    surfaceIntegral (standardC2Simplex U hSU).toSurface (exteriorDerivative ω) =
      chainIntegral ω (simplexBoundary (standardC2Simplex U hSU)) := by
  classical
  let σ := standardC2Simplex U hSU
  let V := (coordEquivEuclidean (d + 1)) ⁻¹' U
  let a (i : Fin (d + 1)) : Coord (d + 1) → ℝ :=
    omittedCoefficient ω i ∘ coordEquivEuclidean (d + 1)
  let upper (i : Fin (d + 1)) : Coord d → ℝ := fun u =>
    a i (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u)
  let lower (i : Fin (d + 1)) : Coord d → ℝ := fun u =>
    a i (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u)
  let top (i : Fin (d + 1)) : Coord d → ℝ := fun u => a i (standardFaceMap 0 u)
  have hV : IsOpen V := hU.preimage (coordEquivEuclidean (d + 1)).continuous
  have hSV : standardSimplex (d + 1) ⊆ V := hSU
  have haV (i : Fin (d + 1)) : ContDiffOn ℝ 1 (a i) V :=
    (contDiffOn_omittedCoefficient hω i).comp
      (coordEquivEuclidean (d + 1)).contDiff.contDiffOn (mapsTo_preimage _ _)
  have ha (i : Fin (d + 1)) : ContinuousOn (a i) (standardSimplex (d + 1)) :=
    (haV i).continuousOn.mono hSV
  have hd (i : Fin (d + 1)) :
      ContinuousOn (simplexCoordinateDerivative (a i) i) (standardSimplex (d + 1)) :=
    (continuousOn_simplexCoordinateDerivative hV (haV i) i).mono hSV
  have hup (i : Fin (d + 1)) : ContinuousOn (upper i) (standardSimplex d) :=
    (ha i).comp (continuous_simplex_upper_face i).continuousOn (fun _ hu => simplex_upper_face_mem i hu)
  have hlo (i : Fin (d + 1)) : ContinuousOn (lower i) (standardSimplex d) :=
    (ha i).comp (continuous_simplex_lower_face i).continuousOn (fun _ hu => simplex_lower_face_mem i hu)
  have htop (i : Fin (d + 1)) : ContinuousOn (top i) (standardSimplex d) :=
    (ha i).comp (standardFaceMap_contDiff 0 1).continuous.continuousOn (standardFaceMap_mapsTo 0)
  have hupper (i : Fin (d + 1)) : simplexRIntegral (upper i) = simplexRIntegral (top i) :=
    simplexRIntegral_upper_face (ha i) i
  have hftc (i : Fin (d + 1)) :
      simplexRIntegral (simplexCoordinateDerivative (a i) i) =
        simplexRIntegral (top i) - simplexRIntegral (lower i) := by
    rw [(simplex_coordinate_ftc hV hSV (haV i) i).2.2]
    change simplexRIntegral (fun u => upper i u - lower i u) = _
    rw [simplexRIntegral_sub (hup i) (hlo i), hupper i]
  have hvolume : surfaceIntegral σ.toSurface (exteriorDerivative ω) =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val *
        (simplexRIntegral (top i) - simplexRIntegral (lower i)) := by
    have hc : ContinuousOn (surfaceIntegrand σ.toSurface (exteriorDerivative ω))
        (standardSimplex (d + 1)) :=
      σ.toSurface.continuousOn_integrand (isCFormOn_exteriorDerivative (r := 0) hU hω).isFormOn
    have hg : ContinuousOn (fun u => ∑ i : Fin (d + 1),
        (-1 : ℝ)^i.val * simplexCoordinateDerivative (a i) i u) (standardSimplex (d + 1)) :=
      continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (hd i))
    have he : EqOn (surfaceIntegrand σ.toSurface (exteriorDerivative ω))
        (fun u => ∑ i : Fin (d + 1), (-1 : ℝ)^i.val * simplexCoordinateDerivative (a i) i u)
        (standardSimplex (d + 1)) := by
      intro u hu
      rw [standardSimplex_derivative_integrand hU hSU hω hu]
      apply Finset.sum_congr rfl
      intro i hi
      rw [simplexCoordinateDerivative_comp_coordEquiv
        ((contDiffOn_omittedCoefficient hω i).differentiableOn_one.differentiableAt
          (hU.mem_nhds (hSU hu)))]
    change simplexRIntegral (surfaceIntegrand σ.toSurface (exteriorDerivative ω)) = _
    rw [simplexRIntegral_congr hc hg he,
      simplexRIntegral_sum (f := fun i u => (-1 : ℝ)^i.val * simplexCoordinateDerivative (a i) i u)
        (fun i => continuousOn_const.mul (hd i))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [simplexRIntegral_const_mul (hd i), hftc i]
  have hface0 : surfaceIntegral (σ.face 0).toSurface ω =
      ∑ i : Fin (d + 1), (-1 : ℝ)^i.val * simplexRIntegral (top i) := by
    have hc : ContinuousOn (surfaceIntegrand (σ.face 0).toSurface ω) (standardSimplex d) :=
      (σ.face 0).toSurface.continuousOn_integrand hω.isFormOn
    have hg : ContinuousOn (fun u => ∑ i : Fin (d + 1), (-1 : ℝ)^i.val * top i u)
        (standardSimplex d) :=
      continuousOn_finsetSum _ (fun i _ => continuousOn_const.mul (htop i))
    have he : EqOn (surfaceIntegrand (σ.face 0).toSurface ω)
        (fun u => ∑ i : Fin (d + 1), (-1 : ℝ)^i.val * top i u) (standardSimplex d) := by
      intro u hu
      exact standardSimplex_face_integrand_zero hSU hω.isFormOn hu
    change simplexRIntegral (surfaceIntegrand (σ.face 0).toSurface ω) = _
    rw [simplexRIntegral_congr hc hg he,
      simplexRIntegral_sum (f := fun i u => (-1 : ℝ)^i.val * top i u)
        (fun i => continuousOn_const.mul (htop i))]
    apply Finset.sum_congr rfl
    intro i hi
    exact simplexRIntegral_const_mul (htop i) _
  have hface (i : Fin (d + 1)) : surfaceIntegral (σ.face i.succ).toSurface ω =
      simplexRIntegral (lower i) := by
    change simplexRIntegral (surfaceIntegrand (σ.face i.succ).toSurface ω) = _
    congr 1
    funext u
    exact standardSimplex_face_integrand_succ hSU ω i u
  have hboundary : chainIntegral ω (simplexBoundary σ) =
      (∑ i : Fin (d + 1), (-1 : ℝ)^i.val * simplexRIntegral (top i)) -
        ∑ i : Fin (d + 1), (-1 : ℝ)^i.val * simplexRIntegral (lower i) := by
    simp only [simplexBoundary, map_sum, map_smul, chainIntegral_single,
      Int.cast_one, mul_one, zsmul_eq_mul, Int.cast_pow, Int.cast_neg]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, hface0, hface]
    have hs (i : Fin (d + 1)) : (-1 : ℝ)^i.succ.val * simplexRIntegral (lower i) =
        -((-1 : ℝ)^i.val * simplexRIntegral (lower i)) := by
      rw [Fin.val_succ, pow_succ]
      ring
    simp only [hs, Finset.sum_neg_distrib, sub_eq_add_neg]
  rw [hvolume, hboundary]
  simp only [mul_sub, Finset.sum_sub_distrib]

theorem standardSimplexStokes : standardSimplexStokes_contract := by
  intro d U ω hSU hU hω
  exact standard_simplex_stokes hU hSU hω

end Rudin.PMA.Chapter10
