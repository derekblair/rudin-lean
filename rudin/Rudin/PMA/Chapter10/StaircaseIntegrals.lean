import Rudin.PMA.Chapter10.StaircaseGeometry

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory Filter
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma staircaseChamber_isCompact {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    IsCompact (staircaseChamber σ) := by
  rw [← staircaseLinear_image]
  exact (isCompact_standardSimplex n).image (staircaseLinear σ).continuous

lemma staircaseChamber_convex {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Convex ℝ (staircaseChamber σ) := by
  rw [← staircaseLinear_image]
  exact (convex_standardSimplex n).linear_image (staircaseLinear σ).toLinearMap

lemma staircaseChamber_frontier_null {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    volume (frontier (staircaseChamber σ)) = 0 :=
  (staircaseChamber_convex σ).addHaar_frontier volume

lemma staircase_integral_image {n : ℕ} (σ : Equiv.Perm (Fin n))
    {f : Coord n → ℝ} (hf : ContinuousOn f (Cell.unit n).carrier) :
    simplexRIntegral (fun u => f (staircaseLinear σ u)) =
      ∫ y in staircaseChamber σ, f y := by
  have hm : MapsTo (staircaseLinear σ) (standardSimplex n) (Cell.unit n).carrier := by
    intro u hu
    exact (show staircaseLinear σ u ∈ staircaseChamber σ by
      rw [← staircaseLinear_image]; exact mem_image_of_mem _ hu).1
  have hc : ContinuousOn (fun u => f (staircaseLinear σ u)) (standardSimplex n) :=
    hf.comp (staircaseLinear σ).continuous.continuousOn hm
  rw [simplexRIntegral_eq_integral hc, ← staircaseLinear_image]
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume
    (isClosed_standardSimplex n).measurableSet
    (fun u hu => (staircaseLinear σ).hasFDerivAt.hasFDerivWithinAt)
    (staircaseLinear_injective σ).injOn]
  simp only [staircaseLinear_det, abs_one, one_smul]

/-- Native integration on the unit cell is the sum over all positively
oriented staircase simplices. Every original parameter fiber is integrable. -/
lemma unitCell_integral_staircase {n : ℕ} {f : Coord n → ℝ}
    (hf : ContinuousOn f (Cell.unit n).carrier) :
    IteratedRIntegrable (Cell.unit n) f ∧
    (∀ σ : Equiv.Perm (Fin n), IteratedRIntegrable (Cell.unit n)
      (simplexExtension (fun u => f (staircaseLinear σ u)))) ∧
    iteratedRIntegral (Cell.unit n) f =
      ∑ σ : Equiv.Perm (Fin n), simplexRIntegral (fun u => f (staircaseLinear σ u)) := by
  classical
  have hc (σ : Equiv.Perm (Fin n)) :
      ContinuousOn (fun u => f (staircaseLinear σ u)) (standardSimplex n) := by
    apply hf.comp (staircaseLinear σ).continuous.continuousOn
    intro u hu
    exact (show staircaseLinear σ u ∈ staircaseChamber σ by
      rw [← staircaseLinear_image]; exact mem_image_of_mem _ hu).1
  refine ⟨iteratedRIntegrable_of_continuousOn hf,
    fun σ => simplex_iteratedRIntegrable (hc σ), ?_⟩
  rw [iteratedRIntegral_eq_setIntegral hf]
  have ha (σ : Equiv.Perm (Fin n)) :
      interior (staircaseChamber σ) =ᵐ[volume] staircaseChamber σ :=
    interior_ae_eq_of_null_frontier (staircaseChamber_frontier_null σ)
  have hu : (⋃ σ, interior (staircaseChamber σ)) =ᵐ[volume] (Cell.unit n).carrier := by
    simpa only [staircaseChambers_cover] using EventuallyEqSet.iUnion ha
  have hi (σ : Equiv.Perm (Fin n)) : IntegrableOn f (staircaseChamber σ) :=
    (hf.mono (fun _ h => h.1)).integrableOn_compact (staircaseChamber_isCompact σ)
  have hs := integral_biUnion_finset (Finset.univ : Finset (Equiv.Perm (Fin n)))
    (fun σ _ => isOpen_interior.measurableSet)
    (fun σ _ τ _ hστ => staircaseChambers_interiors_disjoint hστ)
    (fun σ _ => (hi σ).mono_set interior_subset)
  have hs' : (∫ y in ⋃ σ, interior (staircaseChamber σ), f y) =
      ∑ σ : Equiv.Perm (Fin n), ∫ y in interior (staircaseChamber σ), f y := by
    simpa only [Finset.mem_univ, iUnion_true] using hs
  rw [← setIntegral_congr_set hu, hs']
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [setIntegral_congr_set (ha σ), staircase_integral_image σ hf]

end Rudin.PMA.Chapter10
