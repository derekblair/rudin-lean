import Rudin.PMA.Chapter10.SimplexBoundaries
import Rudin.PMA.Chapter10.SurfacePullbacks

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma affineMap_euclidean_contDiff {n m : ℕ} (F : Euclidean n →ᵃ[ℝ] Euclidean m)
    (r : WithTop ENat) : ContDiff ℝ r F := by
  have he : (F : Euclidean n → Euclidean m) = fun x => F 0 + F.linear.toContinuousLinearMap x :=
    funext (affineMap_apply_eq_zero_add F)
  rw [he]
  exact contDiff_const.add F.linear.toContinuousLinearMap.contDiff

lemma affineSimplexMap_postcompose {k n m : ℕ}
    (F : Euclidean n →ᵃ[ℝ] Euclidean m) (p : Fin (k + 1) → Euclidean n) :
    F ∘ affineSimplexMap p = affineSimplexMap (F ∘ p) := by
  have he : F.comp (affineMapFromVertices p) = affineMapFromVertices (F ∘ p) := by
    apply affineMap_ext_standardVertex
    intro j
    simp only [AffineMap.comp_apply, affineMapFromVertices_standardVertex, Function.comp_apply]
  exact congrArg DFunLike.coe he

def AffineSimplexIn.mapAffine {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (σ : AffineSimplexIn k n E)
    (F : Euclidean n →ᵃ[ℝ] Euclidean m) (hFV : MapsTo F E V) : AffineSimplexIn k m V where
  vertices := F ∘ σ.vertices
  mapsTo := by
    intro u hu
    rw [← congrFun (affineSimplexMap_postcompose F σ.vertices) u]
    exact hFV (σ.mapsTo hu)

lemma AffineSimplexIn.mapAffine_toC2 {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (σ : AffineSimplexIn k n E)
    (F : Euclidean n →ᵃ[ℝ] Euclidean m) (hE : IsOpen E) (hFV : MapsTo F E V) :
    (σ.mapAffine F hFV).toC2 = σ.toC2.mapBy F hE
      (affineMap_euclidean_contDiff F 2).contDiffOn hFV := by
  apply C2Simplex.ext
  exact (affineSimplexMap_postcompose F σ.vertices).symm

def pma10_30_contract : Prop :=
  (∀ (k n m : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (σ : C2Simplex k n E) (T : Euclidean n → Euclidean m)
    (hE : IsOpen E) (hV : IsOpen V) (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V),
    (σ.mapBy T hE hT hTV).map = T ∘ σ.map ∧
    (σ.mapBy T hE hT hTV).toSurface.IsC2 ∧
    ∀ (ω : FormField m), IsFormOn V k ω →
      (ParameterDomain.simplex : ParameterDomain k).Integrable
        (surfaceIntegrand (σ.mapBy T hE hT hTV).toSurface ω) ∧
      (ParameterDomain.simplex : ParameterDomain k).Integrable
        (surfaceIntegrand σ.toSurface (pullbackForm T ω)) ∧
      surfaceIntegral (σ.mapBy T hE hT hTV).toSurface ω =
        surfaceIntegral σ.toSurface (pullbackForm T ω)) ∧
  (∀ (k n m : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (Γ Δ : SimplexChain k n E) (z : ℤ) (T : Euclidean n → Euclidean m)
    (hE : IsOpen E) (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V),
    chainMap T hE hT hTV (Γ + Δ) = chainMap T hE hT hTV Γ + chainMap T hE hT hTV Δ ∧
    chainMap T hE hT hTV (z • Γ) = z • chainMap T hE hT hTV Γ) ∧
  (∀ (k n m : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (Γ : SimplexChain (k + 1) n E) (T : Euclidean n → Euclidean m)
    (hE : IsOpen E) (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V),
    chainBoundary (chainMap T hE hT hTV Γ) = chainMap T hE hT hTV (chainBoundary Γ)) ∧
  (∀ (k n m : ℕ) (E : Set (Euclidean n)) (V : Set (Euclidean m))
    (σ : AffineSimplexIn (k + 1) n E) (F : Euclidean n →ᵃ[ℝ] Euclidean m)
    (hE : IsOpen E) (hFV : MapsTo F E V),
    (σ.mapAffine F hFV).toC2 = σ.toC2.mapBy F hE
      (affineMap_euclidean_contDiff F 2).contDiffOn hFV ∧
    simplexBoundary (σ.toC2.mapBy F hE (affineMap_euclidean_contDiff F 2).contDiffOn hFV) =
      affineChainToSimplex (affineSimplexBoundary (σ.mapAffine F hFV)))

theorem pma10_30 : pma10_30_contract := by
  refine ⟨?_, ?_, fun _ _ _ _ _ Γ T hE hT hTV => chainBoundary_map Γ T hE hT hTV, ?_⟩
  · intro k n m E V σ T hE hV hT hTV
    refine ⟨rfl, (σ.mapBy T hE hT hTV).toSurface_isC2, ?_⟩
    intro ω hω
    exact (pma10_25 n m k E V T σ.toSurface ω hE hV (hT.of_le (by norm_num)) hTV hω).2.2
  · intro k n m E V Γ Δ z T hE hT hTV
    exact ⟨map_add _ _ _, map_smul _ _ _⟩
  · intro k n m E V σ F hE hFV
    have he := σ.mapAffine_toC2 F hE hFV
    refine ⟨he, ?_⟩
    rw [← he]
    exact (affineSimplexBoundary_toC2 _).symm

lemma chainIntegral_map {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (Γ : SimplexChain k n E) (T : Euclidean n → Euclidean m)
    (hE : IsOpen E) (hV : IsOpen V) (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V)
    {ω : FormField m} (hω : IsFormOn V k ω) :
    chainIntegral ω (chainMap T hE hT hTV Γ) = chainIntegral (pullbackForm T ω) Γ := by
  have he : (chainIntegral ω).comp (chainMap T hE hT hTV) =
      chainIntegral (k := k) (E := E) (pullbackForm T ω) := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [LinearMap.comp_apply, chainMap_single, chainIntegral_single]
    rw [((pma10_30.1 k n m E V σ T hE hV hT hTV).2.2 ω hω).2.2]
  exact LinearMap.congr_fun he Γ

end Rudin.PMA.Chapter10
