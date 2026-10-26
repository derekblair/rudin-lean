import Rudin.PMA.Chapter10.FormOperations
import Rudin.PMA.Chapter10.Prerequisites

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The linear part of the affine map with the prescribed vertices. -/
def vertexLinear {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Fin (k + 1) → V) : Coord k →L[ℝ] V :=
  ∑ i : Fin k, (ContinuousLinearMap.proj i).smulRight (p i.succ - p 0)

/-- Arbitrary vertices are allowed, including repeated and affinely dependent ones. -/
def affineMapFromVertices {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Fin (k + 1) → V) : Coord k →ᵃ[ℝ] V :=
  AffineMap.const ℝ (Coord k) (p 0) + (vertexLinear p).toLinearMap.toAffineMap

def affineSimplexMap {k n : ℕ} (p : Fin (k + 1) → Euclidean n) : Coord k → Euclidean n :=
  affineMapFromVertices p

abbrev affineSimplexLinear {k n : ℕ} (p : Fin (k + 1) → Euclidean n) :
    Coord k →L[ℝ] Euclidean n := vertexLinear p

/-- Vertices of the standard simplex in the native parameter coordinates. -/
def standardVertex (k : ℕ) : Fin (k + 1) → Coord k :=
  Fin.cons 0 (fun i => Pi.single i 1)

lemma vertexLinear_apply {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (p : Fin (k + 1) → V) (u : Coord k) :
    vertexLinear p u = ∑ i : Fin k, u i • (p i.succ - p 0) := by
  simp [vertexLinear, ContinuousLinearMap.sum_apply]

lemma affineMapFromVertices_apply {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 1) → V) (u : Coord k) :
    affineMapFromVertices p u = p 0 + ∑ i : Fin k, u i • (p i.succ - p 0) := by
  simp [affineMapFromVertices, vertexLinear_apply]

lemma contDiff_affineMapFromVertices {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 1) → V) (r : WithTop ENat) :
    ContDiff ℝ r (affineMapFromVertices p) :=
  contDiff_const.add (vertexLinear p).contDiff

lemma contDiff_affineSimplexMap {k n : ℕ} (p : Fin (k + 1) → Euclidean n) (r : WithTop ENat) :
    ContDiff ℝ r (affineSimplexMap p) := contDiff_affineMapFromVertices p r

/-- The source's affine simplex as an actual surface with the native simplex integral. -/
def affineSimplexSurface {k n : ℕ} {E : Set (Euclidean n)}
    (p : Fin (k + 1) → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex k) E) : Surface k n E where
  domain := .simplex
  map := affineSimplexMap p
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (contDiff_affineSimplexMap p 1).contDiffOn
  mapsTo := hp

/-- Orientation of a full-dimensional nondegenerate affine simplex. -/
def AffinePositiveOrientation {n : ℕ} (p : Fin (n + 1) → Euclidean n) : Prop :=
  0 < columnDet (fun i : Fin n => p i.succ - p 0)

def AffineNegativeOrientation {n : ℕ} (p : Fin (n + 1) → Euclidean n) : Prop :=
  columnDet (fun i : Fin n => p i.succ - p 0) < 0

/-- A sign attached to a simplex multiplies its integration functional; it does
not multiply the parametrization. This also supplies both signed zero-simplices. -/
def signedAffineIntegral {k n : ℕ} {E : Set (Euclidean n)} (ε : ℤˣ)
    (p : Fin (k + 1) → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex k) E) (ω : FormField n) : ℝ :=
  (ε : ℤ) * surfaceIntegral (affineSimplexSurface p hp) ω

/-- Rudin 10.26, including affine uniqueness, degenerate simplices, the actual
Jacobian convention, full-dimensional orientation and signed point integration. -/
def pma10_26_contract : Prop :=
  (∀ (X Y : Type*) [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
      (f : X → Y),
    (∃ F : X →ᵃ[ℝ] Y, (F : X → Y) = f) ↔
      ∃ A : X →ₗ[ℝ] Y, ∀ x, f x = f 0 + A x) ∧
  (∀ (k n : ℕ) (F : Coord k →ᵃ[ℝ] Euclidean n) (u : Coord k),
    F u = F 0 + F.linear u ∧
    F u = affineSimplexMap (Fin.cons (F 0) (fun i => F (Pi.single i 1))) u) ∧
  (∀ (k n : ℕ) (F G : Coord k →ᵃ[ℝ] Euclidean n), F 0 = G 0 →
    (∀ i : Fin k, F (Pi.single i 1) = G (Pi.single i 1)) → F = G) ∧
  (∀ (k n : ℕ) (p : Fin (k + 1) → Euclidean n),
    affineSimplexMap p 0 = p 0 ∧
    (∀ i : Fin k, affineSimplexMap p (Pi.single i 1) = p i.succ) ∧
    (∀ u : Coord k, affineSimplexMap p u = p 0 + ∑ i, u i • (p i.succ - p 0)) ∧
    ContDiff ℝ ⊤ (affineSimplexMap p) ∧
    (∀ u : Coord k, HasFDerivAt (affineSimplexMap p) (affineSimplexLinear p) u)) ∧
  (∀ (n : ℕ) (p : Fin (n + 1) → Euclidean n) (x : Euclidean n),
    jacobian (affineSimplexMap p ∘ (coordEquivEuclidean n).symm) x =
      columnDet (fun i : Fin n => p i.succ - p 0)) ∧
  (∀ (n : ℕ) (p : Fin (n + 1) → Euclidean n),
    LinearIndependent ℝ (fun i : Fin n => p i.succ - p 0) →
      columnDet (fun i : Fin n => p i.succ - p 0) ≠ 0 ∧
      (AffinePositiveOrientation p ∨ AffineNegativeOrientation p) ∧
      ∀ x : Euclidean n,
        (fderiv ℝ (affineSimplexMap p ∘ (coordEquivEuclidean n).symm) x).IsInvertible) ∧
  (∀ n : ℕ,
    affineSimplexMap (fun i => coordEquivEuclidean n (standardVertex n i)) = coordEquivEuclidean n ∧
    AffinePositiveOrientation (fun i => coordEquivEuclidean n (standardVertex n i))) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (p : Fin 1 → Euclidean n)
    (hp : MapsTo (affineSimplexMap p) (standardSimplex 0) E) (ε : ℤˣ) (f : Euclidean n → ℝ),
    signedAffineIntegral ε p hp (scalarForm f) = (ε : ℤ) * f (p 0))

lemma affineMap_apply_eq_zero_add {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (F : X →ᵃ[ℝ] Y) (x : X) :
    F x = F 0 + F.linear x := by
  simpa only [vadd_eq_add, add_zero, add_comm] using F.map_vadd (0 : X) x

lemma affineMap_characterization {X Y : Type*} [AddCommGroup X] [Module ℝ X]
    [AddCommGroup Y] [Module ℝ Y] (f : X → Y) :
    (∃ F : X →ᵃ[ℝ] Y, (F : X → Y) = f) ↔
      ∃ A : X →ₗ[ℝ] Y, ∀ x, f x = f 0 + A x := by
  constructor
  · rintro ⟨F, rfl⟩
    exact ⟨F.linear, affineMap_apply_eq_zero_add F⟩
  · rintro ⟨A, hA⟩
    exact ⟨AffineMap.const ℝ X (f 0) + A.toAffineMap, funext (fun x => (hA x).symm)⟩

@[simp] lemma vertexLinear_single {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 1) → V) (i : Fin k) :
    vertexLinear p (Pi.single i 1) = p i.succ - p 0 := by
  simp [vertexLinear_apply, Pi.single_apply]

@[simp] lemma affineMapFromVertices_zero {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 1) → V) : affineMapFromVertices p 0 = p 0 := by
  simp [affineMapFromVertices]

@[simp] lemma affineMapFromVertices_single {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 1) → V) (i : Fin k) :
    affineMapFromVertices p (Pi.single i 1) = p i.succ := by
  simp [affineMapFromVertices]

@[simp] lemma affineMapFromVertices_standardVertex {k : ℕ} {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Fin (k + 1) → V) (i : Fin (k + 1)) :
    affineMapFromVertices p (standardVertex k i) = p i := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [standardVertex]

lemma affineMap_ext_vertices {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    {F G : Coord k →ᵃ[ℝ] V} (h0 : F 0 = G 0)
    (h : ∀ i : Fin k, F (Pi.single i 1) = G (Pi.single i 1)) : F = G := by
  apply AffineMap.ext_linear ?_ h0
  apply (Pi.basisFun ℝ (Fin k)).ext
  intro i
  have hF : F.linear (Pi.single i 1) = F (Pi.single i 1) - F 0 := by
    simpa only [vsub_eq_sub, sub_zero] using F.linearMap_vsub (Pi.single i 1) 0
  have hG : G.linear (Pi.single i 1) = G (Pi.single i 1) - G 0 := by
    simpa only [vsub_eq_sub, sub_zero] using G.linearMap_vsub (Pi.single i 1) 0
  simpa only [Pi.basisFun_apply] using hF.trans ((by rw [h i, h0] :
    F (Pi.single i 1) - F 0 = G (Pi.single i 1) - G 0).trans hG.symm)

lemma affineMap_ext_standardVertex {k : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    {F G : Coord k →ᵃ[ℝ] V} (h : ∀ i : Fin (k + 1), F (standardVertex k i) = G (standardVertex k i)) :
    F = G := by
  exact affineMap_ext_vertices (by simpa [standardVertex] using h 0)
    (fun i => by simpa [standardVertex] using h i.succ)

lemma affineMap_eq_fromVertices {k : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : Coord k →ᵃ[ℝ] V) :
    F = affineMapFromVertices (fun i => F (standardVertex k i)) := by
  apply affineMap_ext_standardVertex
  intro i
  simp

lemma hasFDerivAt_affineSimplexMap {k n : ℕ} (p : Fin (k + 1) → Euclidean n) (u : Coord k) :
    HasFDerivAt (affineSimplexMap p) (affineSimplexLinear p) u := by
  exact (vertexLinear p).hasFDerivAt.const_add (p 0)

lemma affineSimplex_jacobian {n : ℕ} (p : Fin (n + 1) → Euclidean n) (x : Euclidean n) :
    jacobian (affineSimplexMap p ∘ (coordEquivEuclidean n).symm) x =
      columnDet (fun i : Fin n => p i.succ - p 0) := by
  have hd := (hasFDerivAt_affineSimplexMap p ((coordEquivEuclidean n).symm x)).comp x
    (coordEquivEuclidean n).symm.hasFDerivAt
  rw [jacobian, hd.fderiv]
  congr 1
  ext i j
  rw [operatorMatrix_apply, ContinuousLinearMap.comp_apply]
  have he : (coordEquivEuclidean n).symm (standardBasis n j) = Pi.single j 1 := by
    ext l
    simp [coordEquivEuclidean, coordinateVector, standardBasis, EuclideanSpace.basisFun_apply,
      Pi.single_apply, eq_comm]
  simp only [ContinuousLinearEquiv.coe_coe]
  rw [he, vertexLinear_single]

lemma columnDet_ne_zero_of_linearIndependent {n : ℕ} {v : Fin n → Euclidean n}
    (hv : LinearIndependent ℝ v) : columnDet v ≠ 0 := by
  have hc : Fintype.card (Fin n) = Module.finrank ℝ (Euclidean n) := by simp [Euclidean]
  have hu : IsUnit ((standardBasis n).det v) :=
    (standardBasis n).is_basis_iff_det.mp ⟨hv, hv.span_eq_top_of_card_eq_finrank' hc⟩
  have hm : (standardBasis n).toMatrix v = (fun i j => v j i) := by
    ext i j
    rfl
  rw [Basis.det_apply, hm] at hu
  exact hu.ne_zero

lemma affineSimplexMap_standard (n : ℕ) :
    affineSimplexMap (fun i => coordEquivEuclidean n (standardVertex n i)) = coordEquivEuclidean n := by
  have h := affineMap_eq_fromVertices (coordEquivEuclidean n).toLinearMap.toAffineMap
  exact congrArg DFunLike.coe h.symm

lemma affineSimplex_standard_positive (n : ℕ) :
    AffinePositiveOrientation (fun i => coordEquivEuclidean n (standardVertex n i)) := by
  change 0 < columnDet (fun i : Fin n =>
    coordEquivEuclidean n (standardVertex n i.succ) - coordEquivEuclidean n (standardVertex n 0))
  have he : (fun i : Fin n =>
    coordEquivEuclidean n (standardVertex n i.succ) - coordEquivEuclidean n (standardVertex n 0)) =
      standardBasis n := by
    ext i j
    simp [standardVertex, coordEquivEuclidean, Pi.single_apply, standardBasis_apply, eq_comm]
  rw [he]
  have hd : columnDet (standardBasis n) = 1 := by
    have hm : (standardBasis n).toMatrix (standardBasis n) =
        (fun i j => standardBasis n j i) := by
      ext i j
      rfl
    have hs := (standardBasis n).det_self
    rw [Basis.det_apply, hm] at hs
    exact hs
  rw [hd]
  norm_num

theorem pma10_26 : pma10_26_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Y _ _ _ _ f
    exact affineMap_characterization f
  · intro k n F u
    refine ⟨affineMap_apply_eq_zero_add F u, ?_⟩
    have h := congrArg (fun G : Coord k →ᵃ[ℝ] Euclidean n => G u) (affineMap_eq_fromVertices F)
    have he : (fun i => F (standardVertex k i)) = Fin.cons (F 0) (fun i => F (Pi.single i 1)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [standardVertex]
    rw [he] at h
    exact h
  · intro k n F G h0 h
    exact affineMap_ext_vertices h0 h
  · intro k n p
    exact ⟨affineMapFromVertices_zero p, affineMapFromVertices_single p,
      affineMapFromVertices_apply p, contDiff_affineSimplexMap p ⊤, hasFDerivAt_affineSimplexMap p⟩
  · intro n
    exact affineSimplex_jacobian
  · intro n p hp
    have hn := columnDet_ne_zero_of_linearIndependent hp
    refine ⟨hn, ?_, ?_⟩
    · rcases lt_or_gt_of_ne hn with h | h
      · exact Or.inr h
      · exact Or.inl h
    · intro x
      have hd := (hasFDerivAt_affineSimplexMap p ((coordEquivEuclidean n).symm x)).comp x
        (coordEquivEuclidean n).symm.hasFDerivAt
      apply ((pma9_38.1 n _ x hd.differentiableAt).2).mpr
      rwa [affineSimplex_jacobian]
  · intro n
    exact ⟨affineSimplexMap_standard n, affineSimplex_standard_positive n⟩
  · intro n E p hp ε f
    rw [signedAffineIntegral, surfaceIntegral_scalar_zero_dimension]
    simp only [affineSimplexSurface, affineSimplexMap, affineMapFromVertices_zero]

end Rudin.PMA.Chapter10
