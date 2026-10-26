import Rudin.PMA.Chapter10.AffineChains
import Rudin.PMA.Chapter10.AffineFaces

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def C2Simplex.face {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex (k + 1) n E) (i : Fin (k + 2)) : C2Simplex k n E :=
  σ.precompose (standardFaceMap i) (standardFaceMap_contDiff i 2) (standardFaceMap_mapsTo i)

def simplexBoundary {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex (k + 1) n E) : SimplexChain k n E :=
  ∑ i : Fin (k + 2), ((-1 : ℤ)^i.val) • Finsupp.single (σ.face i) 1

def chainBoundary {k n : ℕ} {E : Set (Euclidean n)} :
    SimplexChain (k + 1) n E →ₗ[ℤ] SimplexChain k n E :=
  Finsupp.linearCombination ℤ simplexBoundary

def AffineSimplexIn.face {k n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn (k + 1) n E) (i : Fin (k + 2)) : AffineSimplexIn k n E where
  vertices := σ.vertices ∘ i.succAbove
  mapsTo := by
    intro u hu
    have he := congrFun (affineSimplexMap_comp_face σ.vertices i) u
    rw [← he]
    exact σ.mapsTo (standardFaceMap_mapsTo i hu)

def affineSimplexBoundary {k n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn (k + 1) n E) : AffineChain k n E :=
  ∑ i : Fin (k + 2), ((-1 : ℤ)^i.val) • Finsupp.single (σ.face i) 1

def affineChainBoundary {k n : ℕ} {E : Set (Euclidean n)} :
    AffineChain (k + 1) n E →ₗ[ℤ] AffineChain k n E :=
  Finsupp.linearCombination ℤ affineSimplexBoundary

def pma10_29_contract : Prop :=
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (σ : AffineSimplexIn (k + 1) n E),
    affineChainBoundary (Finsupp.single σ 1) =
      ∑ i : Fin (k + 2), ((-1 : ℤ)^i.val) • Finsupp.single (σ.face i) 1) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (σ : AffineSimplexIn (k + 1) n E)
    (i : Fin (k + 2)),
    (σ.face i).vertices = σ.vertices ∘ i.succAbove ∧
    (σ.face i).toC2 = σ.toC2.face i) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (σ : AffineSimplexIn (k + 1) n E)
    (u : Coord k),
    affineSimplexMap (σ.face 0).vertices u =
      σ.vertices 1 + ∑ j : Fin k, u j • (σ.vertices j.succ.succ - σ.vertices 1)) ∧
  (∀ (k : ℕ) (i : Fin (k + 1)) (u : Coord k),
    standardFaceMap i.succ u = Fin.insertNth i 0 u) ∧
  (∀ (n : ℕ) (E : Set (Euclidean n)) (σ : AffineSimplexIn 2 n E),
    affineSimplexBoundary σ = Finsupp.single (σ.face 0) 1 -
      Finsupp.single (σ.face 1) 1 + Finsupp.single (σ.face 2) 1) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Γ : AffineChain (k + 1) n E),
    affineChainToSimplex (affineChainBoundary Γ) = chainBoundary (affineChainToSimplex Γ))

@[simp] lemma chainBoundary_single {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex (k + 1) n E) (z : ℤ) :
    chainBoundary (Finsupp.single σ z) = z • simplexBoundary σ := by
  simp [chainBoundary, Finsupp.linearCombination_single]

@[simp] lemma affineChainBoundary_single {k n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn (k + 1) n E) (z : ℤ) :
    affineChainBoundary (Finsupp.single σ z) = z • affineSimplexBoundary σ := by
  simp [affineChainBoundary, Finsupp.linearCombination_single]

lemma AffineSimplexIn.face_toC2 {k n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn (k + 1) n E) (i : Fin (k + 2)) :
    (σ.face i).toC2 = σ.toC2.face i := by
  apply C2Simplex.ext
  exact (affineSimplexMap_comp_face σ.vertices i).symm

lemma affineSimplexBoundary_toC2 {k n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn (k + 1) n E) :
    affineChainToSimplex (affineSimplexBoundary σ) = simplexBoundary σ.toC2 := by
  simp only [affineSimplexBoundary, simplexBoundary, map_sum, map_smul,
    affineChainToSimplex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    AffineSimplexIn.face_toC2]

lemma affineChainBoundary_toC2 {k n : ℕ} {E : Set (Euclidean n)}
    (Γ : AffineChain (k + 1) n E) :
    affineChainToSimplex (affineChainBoundary Γ) = chainBoundary (affineChainToSimplex Γ) := by
  have he : (affineChainToSimplex (k := k) (n := n) (E := E)).comp affineChainBoundary =
      chainBoundary.comp (affineChainToSimplex (k := k + 1) (n := n) (E := E)) := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [LinearMap.comp_apply, affineChainBoundary_single, map_smul,
      affineSimplexBoundary_toC2]
    simp only [affineChainToSimplex, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      chainBoundary_single]
  exact LinearMap.congr_fun he Γ

lemma C2Simplex.face_mapBy {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (σ : C2Simplex (k + 1) n E) (i : Fin (k + 2))
    (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) :
    (σ.mapBy T hE hT hTV).face i = (σ.face i).mapBy T hE hT hTV := by
  apply C2Simplex.ext
  rfl

lemma simplexBoundary_mapBy {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (σ : C2Simplex (k + 1) n E)
    (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) :
    simplexBoundary (σ.mapBy T hE hT hTV) = chainMap T hE hT hTV (simplexBoundary σ) := by
  simp only [simplexBoundary, map_sum, map_smul, chainMap_single, C2Simplex.face_mapBy]

lemma chainBoundary_map {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (Γ : SimplexChain (k + 1) n E)
    (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) :
    chainBoundary (chainMap T hE hT hTV Γ) = chainMap T hE hT hTV (chainBoundary Γ) := by
  have he : (chainBoundary (k := k) (n := m) (E := V)).comp (chainMap T hE hT hTV) =
      (chainMap T hE hT hTV).comp (chainBoundary (k := k) (n := n) (E := E)) := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [LinearMap.comp_apply, chainMap_single, chainBoundary_single, map_smul,
      simplexBoundary_mapBy]
  exact LinearMap.congr_fun he Γ

theorem pma10_29 : pma10_29_contract := by
  refine ⟨?_, ?_, ?_, fun _ => standardFaceMap_succ, ?_, fun _ _ _ => affineChainBoundary_toC2⟩
  · intro k n E σ
    simp [affineChainBoundary_single, affineSimplexBoundary]
  · intro k n E σ i
    exact ⟨rfl, σ.face_toC2 i⟩
  · intro k n E σ u
    simp [AffineSimplexIn.face, affineSimplexMap, affineMapFromVertices_apply, Function.comp_def]
  · intro n E σ
    simp [affineSimplexBoundary, Fin.sum_univ_succ, sub_eq_add_neg, add_assoc]

end Rudin.PMA.Chapter10
