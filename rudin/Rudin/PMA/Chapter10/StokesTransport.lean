import Rudin.PMA.Chapter10.ChainMaps
import Rudin.PMA.Chapter10.StandardSimplexSurface
import Rudin.PMA.Chapter10.PullbackDifferentiation

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The parameter neighborhood is restricted to where the ambient map lands
in the form's open domain, then transferred to the Euclidean coordinate model. -/
def C2Simplex.euclideanNeighborhood {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : Set (Euclidean k) :=
  (coordEquivEuclidean k).symm ⁻¹' σ.toSurface.targetNeighborhood

def C2Simplex.euclideanMap {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : Euclidean k → Euclidean n :=
  σ.map ∘ (coordEquivEuclidean k).symm

lemma C2Simplex.euclideanNeighborhood_isOpen {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) (hE : IsOpen E) : IsOpen σ.euclideanNeighborhood :=
  (σ.toSurface.targetNeighborhood_isOpen hE).preimage (coordEquivEuclidean k).symm.continuous

lemma C2Simplex.parameter_mapsTo {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : MapsTo (coordEquivEuclidean k) (standardSimplex k)
      σ.euclideanNeighborhood := by
  intro u hu
  change (coordEquivEuclidean k).symm (coordEquivEuclidean k u) ∈ σ.toSurface.targetNeighborhood
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact σ.toSurface.domain_subset_targetNeighborhood hu

lemma C2Simplex.euclideanMap_mapsTo {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : MapsTo σ.euclideanMap σ.euclideanNeighborhood E :=
  fun _ hx => hx.2

lemma C2Simplex.euclideanMap_contDiffOn {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : ContDiffOn ℝ 2 σ.euclideanMap σ.euclideanNeighborhood := by
  apply (σ.regularity.choose_spec.2.2.mono inter_subset_left).comp
    (coordEquivEuclidean k).symm.contDiff.contDiffOn
  exact mapsTo_preimage _ _

lemma C2Simplex.standard_mapBy {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) (hE : IsOpen E) :
    (standardC2Simplex σ.euclideanNeighborhood σ.parameter_mapsTo).mapBy σ.euclideanMap
      (σ.euclideanNeighborhood_isOpen hE) σ.euclideanMap_contDiffOn σ.euclideanMap_mapsTo = σ := by
  apply C2Simplex.ext
  funext u
  change σ.map ((coordEquivEuclidean k).symm (coordEquivEuclidean k u)) = σ.map u
  rw [ContinuousLinearEquiv.symm_apply_apply]

def pma10_33_contract : Prop :=
  ∀ (d n : ℕ) (E : Set (Euclidean n)) (ω : FormField n) (Γ : SimplexChain (d + 1) n E),
    IsOpen E → IsCFormOn 1 E d ω →
      chainIntegral (exteriorDerivative ω) Γ = chainIntegral ω (chainBoundary Γ)

lemma simplex_stokes_of_standard {d n : ℕ} {E : Set (Euclidean n)}
    (hstandard : ∀ (U : Set (Euclidean (d + 1))) (η : FormField (d + 1))
      (hSU : MapsTo (coordEquivEuclidean (d + 1)) (standardSimplex (d + 1)) U),
      IsOpen U → IsCFormOn 1 U d η →
        surfaceIntegral (standardC2Simplex U hSU).toSurface (exteriorDerivative η) =
          chainIntegral η (simplexBoundary (standardC2Simplex U hSU)))
    (hE : IsOpen E) {ω : FormField n} (hω : IsCFormOn 1 E d ω)
    (σ : C2Simplex (d + 1) n E) :
    surfaceIntegral σ.toSurface (exteriorDerivative ω) = chainIntegral ω (simplexBoundary σ) := by
  let U := σ.euclideanNeighborhood
  let T := σ.euclideanMap
  let τ := standardC2Simplex U σ.parameter_mapsTo
  have hU : IsOpen U := σ.euclideanNeighborhood_isOpen hE
  have hT : ContDiffOn ℝ 2 T U := σ.euclideanMap_contDiffOn
  have hTV : MapsTo T U E := σ.euclideanMap_mapsTo
  have hτ : τ.mapBy T hU hT hTV = σ := σ.standard_mapBy hE
  have hp : IsCFormOn 1 U d (pullbackForm T ω) := pullbackForm_isCFormOn hU hT hTV hω
  have hd : IsFormOn E (d + 1) (exteriorDerivative ω) := (pma10_18.1 n d E ω hE hω).1
  have hnatural := ((pma10_30.1 (d + 1) (d + 1) n U E τ T hU hE hT hTV).2.2
    (exteriorDerivative ω) hd).2.2
  rw [hτ] at hnatural
  have heq : FormEqOn U (d + 1) (pullbackForm T (exteriorDerivative ω))
      (exteriorDerivative (pullbackForm T ω)) :=
    FormEqOn.of_eqOn (pullbackForm_isFormOn hU (hT.of_le (by norm_num)) hTV hd)
      (pma10_18.1 (d + 1) d U _ hU hp).1
      (exteriorDerivative_pullback hU hE hT hTV hω).symm
  calc
    _ = surfaceIntegral τ.toSurface (pullbackForm T (exteriorDerivative ω)) := hnatural
    _ = surfaceIntegral τ.toSurface (exteriorDerivative (pullbackForm T ω)) := heq τ.toSurface
    _ = chainIntegral (pullbackForm T ω) (simplexBoundary τ) :=
      hstandard U _ σ.parameter_mapsTo hU hp
    _ = chainIntegral ω (chainMap T hU hT hTV (simplexBoundary τ)) :=
      (chainIntegral_map (simplexBoundary τ) T hU hE hT hTV hω.isFormOn).symm
    _ = chainIntegral ω (simplexBoundary σ) := by
      rw [← simplexBoundary_mapBy, hτ]

lemma chain_stokes_of_simplex {d n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (h : ∀ σ : C2Simplex (d + 1) n E,
      surfaceIntegral σ.toSurface (exteriorDerivative ω) = chainIntegral ω (simplexBoundary σ))
    (Γ : SimplexChain (d + 1) n E) :
    chainIntegral (exteriorDerivative ω) Γ = chainIntegral ω (chainBoundary Γ) := by
  have he : chainIntegral (k := d + 1) (E := E) (exteriorDerivative ω) =
      (chainIntegral ω).comp chainBoundary := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [LinearMap.comp_apply, chainIntegral_single, chainBoundary_single, map_smul,
      zsmul_eq_mul, h σ]
  exact LinearMap.congr_fun he Γ

end Rudin.PMA.Chapter10
