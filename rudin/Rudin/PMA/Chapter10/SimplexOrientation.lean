import Rudin.PMA.Chapter10.AffineFaces
import Rudin.PMA.Chapter10.SimplexChangeOfVariables
import Rudin.PMA.Chapter10.StandardForms

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Reparametrize the standard simplex by permuting all its vertices, including zero. -/
def simplexVertexPermutation {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) : Coord k →ᵃ[ℝ] Coord k :=
  affineMapFromVertices (standardVertex k ∘ σ)

/-- The augmented vertex matrix records the leading barycentric coordinate.
Its determinant is the edge determinant, also for degenerate vertex families. -/
def augmentedVertexMatrix {k : ℕ} (p : Fin (k + 1) → Coord k) :
    Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ := fun i => Fin.cons 1 (p i)

/-- Rudin 10.27: permutation of the actual parametrization changes every native
form integral by its sign. Native integrability is included for both orders;
no positive-dimension or affine-independence assumption is imposed. -/
def pma10_27_contract : Prop :=
  ∀ (k n : ℕ) (E : Set (Euclidean n)) (p : Fin (k + 1) → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex k) E)
    (σ : Equiv.Perm (Fin (k + 1))) (ω : FormField n),
    IsOpen E → IsFormOn E k ω →
    ∃ hq : MapsTo (affineSimplexMap (p ∘ σ)) (standardSimplex k) E,
      ParameterDomain.Integrable .simplex (surfaceIntegrand (affineSimplexSurface p hp) ω) ∧
      ParameterDomain.Integrable .simplex (surfaceIntegrand (affineSimplexSurface (p ∘ σ) hq) ω) ∧
      surfaceIntegral (affineSimplexSurface (p ∘ σ) hq) ω =
        (σ.sign : ℤ) * surfaceIntegral (affineSimplexSurface p hp) ω

@[simp] lemma simplexVertexPermutation_vertex {k : ℕ} (σ : Equiv.Perm (Fin (k + 1)))
    (i : Fin (k + 1)) :
    simplexVertexPermutation σ (standardVertex k i) = standardVertex k (σ i) :=
  affineMapFromVertices_standardVertex _ i

lemma simplexVertexPermutation_mapsTo {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) :
    MapsTo (simplexVertexPermutation σ) (standardSimplex k) (standardSimplex k) := by
  intro u hu
  exact affineMapFromVertices_mem_convex (convex_standardSimplex k)
    (standardVertex k ∘ σ) (fun i => standardVertex_mem _ _) hu

lemma simplexVertexPermutation_comp {k : ℕ} (σ τ : Equiv.Perm (Fin (k + 1))) :
    (simplexVertexPermutation σ).comp (simplexVertexPermutation τ) =
      simplexVertexPermutation (σ * τ) := by
  apply affineMap_ext_standardVertex
  intro i
  change simplexVertexPermutation σ (simplexVertexPermutation τ (standardVertex k i)) = _
  simp

@[simp] lemma simplexVertexPermutation_refl {k : ℕ} :
    simplexVertexPermutation (Equiv.refl (Fin (k + 1))) = AffineMap.id ℝ (Coord k) := by
  apply affineMap_ext_standardVertex
  intro i
  simp

lemma simplexVertexPermutation_leftInverse {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) :
    LeftInverse (simplexVertexPermutation σ.symm) (simplexVertexPermutation σ) := by
  intro u
  have h := congrArg (fun A : Coord k →ᵃ[ℝ] Coord k => A u)
    (simplexVertexPermutation_comp σ.symm σ)
  have he : σ.symm * σ = Equiv.refl (Fin (k + 1)) := by
    ext i
    simp
  rw [he, simplexVertexPermutation_refl] at h
  exact h

lemma simplexVertexPermutation_image {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) :
    simplexVertexPermutation σ '' standardSimplex k = standardSimplex k := by
  apply Subset.antisymm
  · exact (simplexVertexPermutation_mapsTo σ).image_subset
  · intro u hu
    refine ⟨simplexVertexPermutation σ.symm u, simplexVertexPermutation_mapsTo σ.symm hu, ?_⟩
    simpa using simplexVertexPermutation_leftInverse σ.symm u

lemma affineSimplexMap_comp_permutation {k n : ℕ} (p : Fin (k + 1) → Euclidean n)
    (σ : Equiv.Perm (Fin (k + 1))) :
    affineSimplexMap p ∘ simplexVertexPermutation σ = affineSimplexMap (p ∘ σ) := by
  have h : (affineMapFromVertices p).comp (simplexVertexPermutation σ) =
      affineMapFromVertices (p ∘ σ) := by
    apply affineMap_ext_standardVertex
    intro i
    change affineMapFromVertices p (simplexVertexPermutation σ (standardVertex k i)) = _
    simp
  exact congrArg DFunLike.coe h

lemma vertexLinear_det_eq_augmented {k : ℕ} (p : Fin (k + 1) → Coord k) :
    LinearMap.det (vertexLinear p).toLinearMap = (augmentedVertexMatrix p).det := by
  let B : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    Fin.cons (Fin.cons 1 (p 0)) (fun i => Fin.cons 0 (fun j => p i.succ j - p 0 j))
  have hB : B.det = (augmentedVertexMatrix p).det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const (Fin.cons 0 (fun _ => -1)) 0
    · rfl
    · intro i j
      refine Fin.cases ?_ (fun l => ?_) i
      · simp [B, augmentedVertexMatrix]
      · refine Fin.cases ?_ (fun m => ?_) j <;>
          simp [B, augmentedVertexMatrix, sub_eq_add_neg]
  let M : Matrix (Fin k) (Fin k) ℝ := fun i j => p i.succ j - p 0 j
  have he : B.det = M.det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [B, M, Matrix.submatrix]
    congr 1
  have hm : LinearMap.toMatrix' (vertexLinear p).toLinearMap = M.transpose := by
    ext i j
    rw [LinearMap.toMatrix'_apply]
    exact congrArg (fun v : Coord k => v i) (vertexLinear_single p j)
  rw [← LinearMap.det_toMatrix', hm, Matrix.det_transpose, ← he, hB]

lemma vertexLinear_standard {k : ℕ} :
    vertexLinear (standardVertex k) = ContinuousLinearMap.id ℝ (Coord k) := by
  ext u j
  simp [vertexLinear_apply, standardVertex, Pi.single_apply]

lemma simplexVertexPermutation_det {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) :
    LinearMap.det (vertexLinear (standardVertex k ∘ σ)).toLinearMap = (σ.sign : ℤ) := by
  rw [vertexLinear_det_eq_augmented]
  have hm : augmentedVertexMatrix (standardVertex k ∘ σ) =
      (augmentedVertexMatrix (standardVertex k)).submatrix σ id := rfl
  rw [hm, Matrix.det_permute, ← vertexLinear_det_eq_augmented, vertexLinear_standard]
  simp

lemma simplexRIntegral_vertexPermutation {k : ℕ} (σ : Equiv.Perm (Fin (k + 1)))
    {f : Coord k → ℝ} (hf : ContinuousOn f (standardSimplex k)) :
    IteratedRIntegrable (Cell.unit k) (simplexExtension (f ∘ simplexVertexPermutation σ)) ∧
      simplexRIntegral (f ∘ simplexVertexPermutation σ) = simplexRIntegral f := by
  apply simplexRIntegral_comp_of_abs_det_one
    (A' := fun _ => vertexLinear (standardVertex k ∘ σ))
    (contDiff_affineMapFromVertices _ 1).continuous.continuousOn
  · intro u hu
    exact ((vertexLinear (standardVertex k ∘ σ)).hasFDerivAt.const_add
      ((standardVertex k ∘ σ) 0)).hasFDerivWithinAt
  · exact (simplexVertexPermutation_leftInverse σ).injective.injOn
  · exact simplexVertexPermutation_image σ
  · intro u hu
    change |LinearMap.det (vertexLinear (standardVertex k ∘ σ)).toLinearMap| = 1
    rw [simplexVertexPermutation_det]
    exact abs_unit_intCast σ.sign
  · exact hf

lemma evaluateForm_coordinate_precompose {k n : ℕ} (A : Coord k →L[ℝ] Euclidean n)
    (B : Coord k →L[ℝ] Coord k) (I : Fin k → Fin n) :
    evaluateForm k (fun j => A (B (Pi.single j 1))) (coordinateWedge I) =
      LinearMap.det B.toLinearMap *
        evaluateForm k (fun j => A (Pi.single j 1)) (coordinateWedge I) := by
  rw [evaluateForm_coordinateWedge, evaluateForm_coordinateWedge]
  let C : Coord k →L[ℝ] Coord k :=
    ContinuousLinearMap.pi (fun i => (EuclideanSpace.proj (𝕜 := ℝ) (I i)).comp A)
  have h1 : (fun i j => A (B (Pi.single j 1)) (I i)) =
      LinearMap.toMatrix' (C.comp B).toLinearMap := by
    ext i j
    rfl
  have h0 : (fun i j => A (Pi.single j 1) (I i)) =
      LinearMap.toMatrix' C.toLinearMap := by
    ext i j
    rfl
  rw [h1, h0, LinearMap.det_toMatrix', LinearMap.det_toMatrix']
  change LinearMap.det (C.toLinearMap.comp B.toLinearMap) = _
  rw [LinearMap.det_comp, mul_comm]

lemma evaluateForm_precompose {k n : ℕ} (A : Coord k →L[ℝ] Euclidean n)
    (B : Coord k →L[ℝ] Coord k) {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) :
    evaluateForm k (fun j => A (B (Pi.single j 1))) a =
      LinearMap.det B.toLinearMap * evaluateForm k (fun j => A (Pi.single j 1)) a := by
  rw [standard_expansion a ha]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [standardWedge_eq_coordinateWedge, evaluateForm_coordinate_precompose]
  ring

lemma simplexVertexPermutation_hasFDerivAt {k : ℕ} (σ : Equiv.Perm (Fin (k + 1))) (u : Coord k) :
    HasFDerivAt (simplexVertexPermutation σ) (vertexLinear (standardVertex k ∘ σ)) u :=
  (vertexLinear (standardVertex k ∘ σ)).hasFDerivAt.const_add ((standardVertex k ∘ σ) 0)

lemma affineSimplex_permuted_mapsTo {k n : ℕ} {E : Set (Euclidean n)}
    (p : Fin (k + 1) → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex k) E)
    (σ : Equiv.Perm (Fin (k + 1))) :
    MapsTo (affineSimplexMap (p ∘ σ)) (standardSimplex k) E := by
  rw [← affineSimplexMap_comp_permutation]
  exact hp.comp (simplexVertexPermutation_mapsTo σ)

lemma affineSimplex_surfaceIntegrand_permutation {k n : ℕ} {E : Set (Euclidean n)}
    (p : Fin (k + 1) → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex k) E)
    (σ : Equiv.Perm (Fin (k + 1))) {ω : FormField n} (hω : IsFormOn E k ω) :
    EqOn (surfaceIntegrand (affineSimplexSurface (p ∘ σ) (affineSimplex_permuted_mapsTo p hp σ)) ω)
      (fun u => (σ.sign : ℤ) * surfaceIntegrand (affineSimplexSurface p hp) ω
        (simplexVertexPermutation σ u)) (standardSimplex k) := by
  intro u hu
  have hd : HasFDerivAt (affineSimplexMap (p ∘ σ))
      ((affineSimplexLinear p).comp (vertexLinear (standardVertex k ∘ σ))) u := by
    rw [← affineSimplexMap_comp_permutation]
    exact (hasFDerivAt_affineSimplexMap p (simplexVertexPermutation σ u)).comp u
      (simplexVertexPermutation_hasFDerivAt σ u)
  change evaluateForm k (fun j => fderiv ℝ (affineSimplexMap (p ∘ σ)) u (Pi.single j 1))
      (ω (affineSimplexMap (p ∘ σ) u)) =
    (σ.sign : ℤ) * evaluateForm k
      (fun j => fderiv ℝ (affineSimplexMap p) (simplexVertexPermutation σ u) (Pi.single j 1))
      (ω (affineSimplexMap p (simplexVertexPermutation σ u)))
  rw [hd.fderiv, (hasFDerivAt_affineSimplexMap p (simplexVertexPermutation σ u)).fderiv,
    ← congrFun (affineSimplexMap_comp_permutation p σ) u]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  rw [evaluateForm_precompose _ _ (hω.1 _ (hp (simplexVertexPermutation_mapsTo σ hu))),
    simplexVertexPermutation_det]

lemma simplexRIntegral_const_mul {k : ℕ} {f : Coord k → ℝ}
    (hf : ContinuousOn f (standardSimplex k)) (c : ℝ) :
    simplexRIntegral (fun u => c * f u) = c * simplexRIntegral f := by
  have hc : ContinuousOn (fun u => c * f u) (standardSimplex k) := continuousOn_const.mul hf
  rw [simplexRIntegral_eq_integral hc, simplexRIntegral_eq_integral hf, integral_const_mul]

lemma affineSimplex_surfaceIntegral_permutation {k n : ℕ} {E : Set (Euclidean n)}
    (p : Fin (k + 1) → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex k) E)
    (σ : Equiv.Perm (Fin (k + 1))) {ω : FormField n} (hω : IsFormOn E k ω) :
    surfaceIntegral (affineSimplexSurface (p ∘ σ) (affineSimplex_permuted_mapsTo p hp σ)) ω =
      (σ.sign : ℤ) * surfaceIntegral (affineSimplexSurface p hp) ω := by
  let f := surfaceIntegrand (affineSimplexSurface p hp) ω
  have hf : ContinuousOn f (standardSimplex k) :=
    (affineSimplexSurface p hp).continuousOn_integrand hω
  have hq := (affineSimplexSurface (p ∘ σ) (affineSimplex_permuted_mapsTo p hp σ)).continuousOn_integrand hω
  have hcomp : ContinuousOn (f ∘ simplexVertexPermutation σ) (standardSimplex k) :=
    hf.comp (contDiff_affineMapFromVertices _ 1).continuous.continuousOn
      (simplexVertexPermutation_mapsTo σ)
  change simplexRIntegral _ = (σ.sign : ℤ) * simplexRIntegral f
  calc
    _ = simplexRIntegral (fun u => (σ.sign : ℤ) * f (simplexVertexPermutation σ u)) := by
      have hc : ContinuousOn (fun u => (σ.sign : ℤ) * f (simplexVertexPermutation σ u))
          (standardSimplex k) := continuousOn_const.mul hcomp
      rw [simplexRIntegral_eq_integral hq, simplexRIntegral_eq_integral hc]
      apply setIntegral_congr_fun (isClosed_standardSimplex k).measurableSet
      exact affineSimplex_surfaceIntegrand_permutation p hp σ hω
    _ = (σ.sign : ℤ) * simplexRIntegral (f ∘ simplexVertexPermutation σ) :=
      simplexRIntegral_const_mul hcomp _
    _ = (σ.sign : ℤ) * simplexRIntegral f := by
      rw [(simplexRIntegral_vertexPermutation σ hf).2]

theorem pma10_27 : pma10_27_contract := by
  intro k n E p hp σ ω _ hω
  refine ⟨affineSimplex_permuted_mapsTo p hp σ, ?_, ?_,
    affineSimplex_surfaceIntegral_permutation p hp σ hω⟩
  · exact ParameterDomain.integrable_of_continuousOn
      ((affineSimplexSurface p hp).continuousOn_integrand hω)
  · exact ParameterDomain.integrable_of_continuousOn
      ((affineSimplexSurface (p ∘ σ) (affineSimplex_permuted_mapsTo p hp σ)).continuousOn_integrand hω)

end Rudin.PMA.Chapter10
