import Rudin.PMA.Chapter10.AffineSimplices
import Mathlib.Analysis.Convex.Combination

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The affine face deleting the indicated vertex of the standard simplex. -/
def standardFaceAffine {k : ℕ} (i : Fin (k + 2)) : Coord k →ᵃ[ℝ] Coord (k + 1) :=
  affineMapFromVertices (standardVertex (k + 1) ∘ i.succAbove)

def standardFaceMap {k : ℕ} (i : Fin (k + 2)) : Coord k → Coord (k + 1) :=
  standardFaceAffine i

/-- Barycentric weights, including the vertex at zero. -/
def barycentricWeights {k : ℕ} (u : Coord k) : Fin (k + 1) → ℝ :=
  Fin.cons (1 - ∑ i, u i) u

lemma barycentricWeights_sum {k : ℕ} (u : Coord k) : ∑ i, barycentricWeights u i = 1 := by
  simp [barycentricWeights, Fin.sum_univ_succ]

lemma barycentricWeights_nonneg {k : ℕ} {u : Coord k} (hu : u ∈ standardSimplex k)
    (i : Fin (k + 1)) : 0 ≤ barycentricWeights u i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact sub_nonneg.mpr hu.2
  · exact hu.1 j

lemma affineMapFromVertices_barycentric {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 1) → V) (u : Coord k) :
    affineMapFromVertices p u = ∑ i, barycentricWeights u i • p i := by
  rw [affineMapFromVertices_apply, Fin.sum_univ_succ]
  simp only [barycentricWeights, Fin.cons_zero, Fin.cons_succ, smul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_smul]
  module

lemma affineMapFromVertices_mem_convex {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {S : Set V} (hS : Convex ℝ S) (p : Fin (k + 1) → V)
    (hp : ∀ i, p i ∈ S) {u : Coord k} (hu : u ∈ standardSimplex k) :
    affineMapFromVertices p u ∈ S := by
  rw [affineMapFromVertices_barycentric]
  exact hS.sum_mem (fun i _ => barycentricWeights_nonneg hu i)
    (barycentricWeights_sum u) (fun i _ => hp i)

lemma convex_standardSimplex (k : ℕ) : Convex ℝ (standardSimplex k) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i)), ?_⟩
  change (∑ i, (a * x i + b * y i)) ≤ 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  nlinarith [hx.2, hy.2]

lemma standardVertex_mem (k : ℕ) (i : Fin (k + 1)) : standardVertex k i ∈ standardSimplex k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [standardVertex, standardSimplex]
  · change (∀ l : Fin k, 0 ≤ (Pi.single j 1 : Coord k) l) ∧
      (∑ l : Fin k, (Pi.single j 1 : Coord k) l) ≤ 1
    constructor
    · intro l
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    · simp

lemma standardFaceMap_contDiff {k : ℕ} (i : Fin (k + 2)) (r : WithTop ENat) :
    ContDiff ℝ r (standardFaceMap i) := contDiff_affineMapFromVertices _ r

lemma standardFaceMap_mapsTo {k : ℕ} (i : Fin (k + 2)) :
    MapsTo (standardFaceMap i) (standardSimplex k) (standardSimplex (k + 1)) := by
  intro u hu
  exact affineMapFromVertices_mem_convex (convex_standardSimplex (k + 1))
    (standardVertex (k + 1) ∘ i.succAbove) (fun j => standardVertex_mem _ _) hu

@[simp] lemma standardFaceMap_vertex {k : ℕ} (i : Fin (k + 2)) (j : Fin (k + 1)) :
    standardFaceMap i (standardVertex k j) = standardVertex (k + 1) (i.succAbove j) :=
  affineMapFromVertices_standardVertex _ j

lemma affineMapFromVertices_comp_face {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (p : Fin (k + 2) → V) (i : Fin (k + 2)) :
    (affineMapFromVertices p).comp (standardFaceAffine i) =
      affineMapFromVertices (p ∘ i.succAbove) := by
  apply affineMap_ext_standardVertex
  intro j
  change affineMapFromVertices p (standardFaceMap i (standardVertex k j)) = _
  simp

lemma affineSimplexMap_comp_face {k n : ℕ} (p : Fin (k + 2) → Euclidean n) (i : Fin (k + 2)) :
    affineSimplexMap p ∘ standardFaceMap i = affineSimplexMap (p ∘ i.succAbove) :=
  congrArg DFunLike.coe (affineMapFromVertices_comp_face p i)

/-- The two orders of deleting the same two vertices give exactly the same map.
This is the combinatorial identity needed for cancellation in the second boundary. -/
lemma standardFaceMap_comp_face {k : ℕ} (i : Fin (k + 3)) (j : Fin (k + 2)) :
    standardFaceMap i ∘ standardFaceMap j =
      standardFaceMap (i.succAbove j) ∘ standardFaceMap (j.predAbove i) := by
  have h : (standardFaceAffine i).comp (standardFaceAffine j) =
      (standardFaceAffine (i.succAbove j)).comp (standardFaceAffine (j.predAbove i)) := by
    apply affineMap_ext_standardVertex
    intro l
    change standardFaceMap i (standardFaceMap j (standardVertex k l)) =
      standardFaceMap (i.succAbove j) (standardFaceMap (j.predAbove i) (standardVertex k l))
    simp only [standardFaceMap_vertex, Fin.succAbove_succAbove_succAbove_predAbove]
  exact congrArg DFunLike.coe h

/-- The face opposite zero has the different base vertex required in Rudin 10.29. -/
lemma standardFaceMap_zero {k : ℕ} (u : Coord k) :
    standardFaceMap (0 : Fin (k + 2)) u = Fin.cons (1 - ∑ i, u i) u := by
  ext j
  refine Fin.cases ?_ (fun l => ?_) j
  · simp [standardFaceMap, standardFaceAffine, affineMapFromVertices_apply, standardVertex,
      Function.comp_def, Pi.single_apply, Finset.sum_sub_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [standardFaceMap, standardFaceAffine, affineMapFromVertices_apply, standardVertex,
      Function.comp_def, Pi.single_apply, eq_comm]

/-- Every other standard face inserts a zero in one ordinary coordinate. -/
lemma standardFaceMap_succ {k : ℕ} (i : Fin (k + 1)) (u : Coord k) :
    standardFaceMap i.succ u = Fin.insertNth i 0 u := by
  ext j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simp [standardFaceMap, standardFaceAffine, affineMapFromVertices_apply, standardVertex,
      Function.comp_def, Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]
  · simp [standardFaceMap, standardFaceAffine, affineMapFromVertices_apply, standardVertex,
      Function.comp_def, Pi.single_apply, eq_comm]

end Rudin.PMA.Chapter10
