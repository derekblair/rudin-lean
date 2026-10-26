import Rudin.PMA.Chapter10.CellIntegralNormalization
import Rudin.PMA.Chapter10.ChainStokes

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma cellStaircase_affine {k : ℕ} (C : Cell k) (σ : Equiv.Perm (Fin k)) :
    ∃ A : Coord k →ᵃ[ℝ] Coord k, (A : Coord k → Coord k) = cellStaircase C σ := by
  refine ⟨AffineMap.const ℝ (Coord k) C.lower +
    ((cellNormalizeLinear C).comp (staircaseLinear σ)).toLinearMap.toAffineMap, ?_⟩
  funext u
  ext i
  rfl

lemma cellStaircase_det {k : ℕ} (C : Cell k) (σ : Equiv.Perm (Fin k)) (u : Coord k) :
    LinearMap.det (fderiv ℝ (cellStaircase C σ) u).toLinearMap =
      ∏ i, (C.upper i - C.lower i) := by
  have hd := (cellNormalize_hasFDerivAt C (staircaseLinear σ u)).comp u
    (staircaseLinear σ).hasFDerivAt
  rw [cellStaircase, hd.fderiv]
  change LinearMap.det ((cellNormalizeLinear C).toLinearMap.comp (staircaseLinear σ).toLinearMap) = _
  rw [LinearMap.det_comp, staircaseLinear_det, mul_one]
  simpa only [(cellNormalize_hasFDerivAt C u).fderiv] using cellNormalize_det C u

def Surface.staircaseSurface {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (C : Cell k) (hD : Φ.domain = .cell C) (σ : Equiv.Perm (Fin k)) : Surface k n E :=
  Φ.precompose .simplex (cellStaircase C σ) (cellStaircase_contDiff C σ 1)
    (by rw [hD]; exact cellStaircase_mapsTo C σ)

lemma surfaceIntegral_staircase {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (C : Cell k) (hD : Φ.domain = .cell C)
    {ω : FormField n} (hω : IsFormOn E k ω) :
    surfaceIntegral Φ ω = ∑ σ : Equiv.Perm (Fin k), surfaceIntegral (Φ.staircaseSurface C hD σ) ω := by
  have hc := Φ.continuousOn_integrand hω
  rw [hD] at hc
  have he : surfaceIntegral Φ ω = iteratedRIntegral C (surfaceIntegrand Φ ω) := by
    unfold surfaceIntegral
    rw [hD]
    rfl
  rw [he]
  rw [cell_integral_staircase C hc]
  apply Finset.sum_congr rfl
  intro σ hσ
  change simplexRIntegral _ = simplexRIntegral _
  refine simplexRIntegral_congr
    (continuousOn_const.mul (hc.comp (cellStaircase_contDiff C σ 1).continuous.continuousOn
      (cellStaircase_mapsTo C σ)))
    ((Φ.staircaseSurface C hD σ).continuousOn_integrand hω) ?_
  intro u hu
  have h := surfaceIntegrand_precompose Φ .simplex (cellStaircase C σ)
    (cellStaircase_contDiff C σ 1) (by rw [hD]; exact cellStaircase_mapsTo C σ) hω hu
  simpa only [cellStaircase_det, Surface.staircaseSurface] using h.symm

/-- The same affine subdivision yields actual C² simplices for a C² cell surface. -/
def Surface.staircaseSimplex {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (C : Cell k) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    (σ : Equiv.Perm (Fin k)) : C2Simplex k n E where
  map := Φ.map ∘ cellStaircase C σ
  regularity := by
    obtain ⟨U, hU, hDU, hΦ⟩ := h₂
    refine ⟨cellStaircase C σ ⁻¹' U, hU.preimage (cellStaircase_contDiff C σ 2).continuous,
      ?_, hΦ.comp (cellStaircase_contDiff C σ 2).contDiffOn (fun _ hu => hu)⟩
    intro u hu
    apply hDU
    rw [hD]
    exact cellStaircase_mapsTo C σ hu
  mapsTo := by
    intro u hu
    apply Φ.mapsTo
    rw [hD]
    exact cellStaircase_mapsTo C σ hu

def Surface.staircaseChain {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (C : Cell k) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) : SimplexChain k n E :=
  ∑ σ : Equiv.Perm (Fin k), Finsupp.single (Φ.staircaseSimplex C hD h₂ σ) 1

lemma staircaseChain_integral {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (C : Cell k) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    {ω : FormField n} (hω : IsFormOn E k ω) :
    chainIntegral ω (Φ.staircaseChain C hD h₂) = surfaceIntegral Φ ω := by
  simp only [Surface.staircaseChain, map_sum, chainIntegral_single, Int.cast_one, one_mul]
  rw [surfaceIntegral_staircase Φ C hD hω]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact surfaceIntegral_congr_map rfl rfl ω

lemma staircaseChain_boundary {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface (k+1) n E) (C : Cell (k+1)) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) :
    chainBoundary (Φ.staircaseChain C hD h₂) =
      ∑ σ : Equiv.Perm (Fin (k+1)), simplexBoundary (Φ.staircaseSimplex C hD h₂ σ) := by
  simp only [Surface.staircaseChain, map_sum, chainBoundary_single, one_smul]

lemma staircaseChain_stokes {k n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (Φ : Surface (k+1) n E) (C : Cell (k+1))
    (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) {ω : FormField n} (hω : IsCFormOn 1 E k ω) :
    surfaceIntegral Φ (exteriorDerivative ω) =
      chainIntegral ω (chainBoundary (Φ.staircaseChain C hD h₂)) := by
  rw [← staircaseChain_integral Φ C hD h₂ (pma10_18.1 n k E ω hE hω).1]
  exact pma10_33 k n E ω (Φ.staircaseChain C hD h₂) hE hω

/-- The finite affine triangulation is exhibited, covers the original cell,
preserves native integrals, and carries the actual induced chain boundary. -/
def pma10_41_contract : Prop :=
  (∀ (k : ℕ) (C : Cell k),
    (⋃ σ : Equiv.Perm (Fin k), cellStaircase C σ '' standardSimplex k) = C.carrier ∧
    ∀ σ : Equiv.Perm (Fin k),
      (∃ A : Coord k →ᵃ[ℝ] Coord k, (A : Coord k → Coord k) = cellStaircase C σ) ∧
      ContDiff ℝ ⊤ (cellStaircase C σ) ∧
      ∀ u : Coord k, LinearMap.det (fderiv ℝ (cellStaircase C σ) u).toLinearMap =
        ∏ i, (C.upper i - C.lower i)) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Φ : Surface k n E)
      (C : Cell k) (hD : Φ.domain = .cell C) (ω : FormField n), IsFormOn E k ω →
    Φ.domain.Integrable (surfaceIntegrand Φ ω) ∧
    (∀ σ : Equiv.Perm (Fin k), (ParameterDomain.simplex : ParameterDomain k).Integrable
      (surfaceIntegrand (Φ.staircaseSurface C hD σ) ω)) ∧
    surfaceIntegral Φ ω = ∑ σ : Equiv.Perm (Fin k), surfaceIntegral (Φ.staircaseSurface C hD σ) ω) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Φ : Surface k n E)
      (C : Cell k) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
      (ω : FormField n), IsFormOn E k ω →
    chainIntegral ω (Φ.staircaseChain C hD h₂) = surfaceIntegral Φ ω) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Φ : Surface (k+1) n E)
      (C : Cell (k+1)) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2),
    chainBoundary (Φ.staircaseChain C hD h₂) =
      ∑ σ : Equiv.Perm (Fin (k+1)), simplexBoundary (Φ.staircaseSimplex C hD h₂ σ)) ∧
  (∀ (k n : ℕ) (E : Set (Euclidean n)) (Φ : Surface (k+1) n E)
      (C : Cell (k+1)) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
      (ω : FormField n), IsOpen E → IsCFormOn 1 E k ω →
    surfaceIntegral Φ (exteriorDerivative ω) =
      chainIntegral ω (chainBoundary (Φ.staircaseChain C hD h₂)))

theorem pma10_41 : pma10_41_contract := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k C
    exact ⟨cellStaircases_cover C, fun σ =>
      ⟨cellStaircase_affine C σ, cellStaircase_contDiff C σ ⊤, cellStaircase_det C σ⟩⟩
  · intro k n E Φ C hD ω hω
    exact ⟨ParameterDomain.integrable_of_continuousOn (Φ.continuousOn_integrand hω),
      fun σ => ParameterDomain.integrable_of_continuousOn ((Φ.staircaseSurface C hD σ).continuousOn_integrand hω),
      surfaceIntegral_staircase Φ C hD hω⟩
  · intro k n E Φ C hD h₂ ω hω
    exact staircaseChain_integral Φ C hD h₂ hω
  · exact fun k n E Φ C hD h₂ => staircaseChain_boundary Φ C hD h₂
  · exact fun k n E Φ C hD h₂ ω hE hω => staircaseChain_stokes hE Φ C hD h₂ hω

end Rudin.PMA.Chapter10
