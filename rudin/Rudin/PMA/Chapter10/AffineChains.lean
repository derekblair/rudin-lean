import Rudin.PMA.Chapter10.AffineSimplices
import Rudin.PMA.Chapter10.SimplexChains

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Affine simplices inside a target set retain all ordered vertices. -/
structure AffineSimplexIn (k n : ℕ) (E : Set (Euclidean n)) where
  vertices : Fin (k + 1) → Euclidean n
  mapsTo : MapsTo (affineSimplexMap vertices) (standardSimplex k) E

def AffineSimplexIn.toC2 {k n : ℕ} {E : Set (Euclidean n)}
    (σ : AffineSimplexIn k n E) : C2Simplex k n E where
  map := affineSimplexMap σ.vertices
  regularity := ⟨univ, isOpen_univ, subset_univ _,
    (contDiff_affineSimplexMap σ.vertices 2).contDiffOn⟩
  mapsTo := σ.mapsTo

abbrev AffineChain (k n : ℕ) (E : Set (Euclidean n)) := AffineSimplexIn k n E →₀ ℤ

def affineChainIntegral {k n : ℕ} {E : Set (Euclidean n)} (ω : FormField n) :
    AffineChain k n E →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ
    (fun σ => surfaceIntegral (affineSimplexSurface σ.vertices σ.mapsTo) ω)

def affineChainToSimplex {k n : ℕ} {E : Set (Euclidean n)} :
    AffineChain k n E →ₗ[ℤ] SimplexChain k n E :=
  Finsupp.lmapDomain ℤ ℤ AffineSimplexIn.toC2

def AffineChainEq {k n : ℕ} {E : Set (Euclidean n)} (Γ Δ : AffineChain k n E) : Prop :=
  ∀ ω : FormField n, IsFormOn E k ω → affineChainIntegral ω Γ = affineChainIntegral ω Δ

def pma10_28_contract : Prop :=
  (∀ (k n N : ℕ) (E : Set (Euclidean n)) (σ : Fin N → AffineSimplexIn k n E)
    (z : Fin N → ℤ) (ω : FormField n),
    affineChainIntegral ω (∑ i, Finsupp.single (σ i) (z i)) =
      ∑ i, (z i : ℝ) * surfaceIntegral (affineSimplexSurface (σ i).vertices (σ i).mapsTo) ω) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Γ Δ : AffineChain k n E) (z : ℤ) (ω : FormField n),
    affineChainIntegral ω (Γ + Δ) = affineChainIntegral ω Γ + affineChainIntegral ω Δ ∧
    affineChainIntegral ω (z • Γ) = (z : ℝ) * affineChainIntegral ω Γ ∧
    affineChainIntegral ω (Γ - Γ) = 0) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Γ Δ : AffineChain k n E),
    AffineChainEq Γ Δ ↔ ∀ ω : FormField n, IsFormOn E k ω →
      affineChainIntegral ω Γ = affineChainIntegral ω Δ) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Γ : AffineChain k n E) (ω : FormField n),
    chainIntegral ω (affineChainToSimplex Γ) = affineChainIntegral ω Γ)

@[simp] lemma affineChainIntegral_single {k n : ℕ} {E : Set (Euclidean n)}
    (ω : FormField n) (σ : AffineSimplexIn k n E) (z : ℤ) :
    affineChainIntegral ω (Finsupp.single σ z) =
      (z : ℝ) * surfaceIntegral (affineSimplexSurface σ.vertices σ.mapsTo) ω := by
  simp [affineChainIntegral, Finsupp.linearCombination_single, zsmul_eq_mul]

lemma affineChainToSimplex_integral {k n : ℕ} {E : Set (Euclidean n)}
    (Γ : AffineChain k n E) (ω : FormField n) :
    chainIntegral ω (affineChainToSimplex Γ) = affineChainIntegral ω Γ := by
  have he : (chainIntegral ω).comp affineChainToSimplex = affineChainIntegral (k := k) (E := E) ω := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [LinearMap.comp_apply, affineChainToSimplex, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, chainIntegral_single, affineChainIntegral_single]
    rfl
  exact LinearMap.congr_fun he Γ

theorem pma10_28 : pma10_28_contract := by
  refine ⟨?_, ?_, fun _ _ _ _ _ => Iff.rfl, fun _ _ _ => affineChainToSimplex_integral⟩
  · intro k n N E σ z ω
    simp only [map_sum, affineChainIntegral_single]
  · intro k n E Γ Δ z ω
    exact ⟨map_add _ _ _, by simp only [map_smul, zsmul_eq_mul], by simp⟩

end Rudin.PMA.Chapter10
