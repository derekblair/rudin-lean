import Rudin.PMA.Chapter10.Surfaces

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Increasing coordinate subsets index the standard forms. -/
abbrev StandardIndex (n k : ℕ) := Set.powersetCard (Fin n) k

def standardWedge {n k : ℕ} (S : StandardIndex n k) : CotangentExterior n :=
  exteriorBasis n S.val

lemma standardWedge_eq_coordinateWedge {n k : ℕ} (S : StandardIndex n k) :
    standardWedge S = coordinateWedge (Set.powersetCard.ofFinEmbEquiv.symm S) := by
  exact ExteriorAlgebra.basis_apply_powersetCard (covectorBasis n) S

lemma coordinateWedge_mem {n k : ℕ} (I : Fin k → Fin n) :
    coordinateWedge I ∈ (⋀[ℝ]^k (Coord n)) :=
  ExteriorAlgebra.ιMulti_range ℝ k (mem_range_self _)

lemma standardWedge_mem {n k : ℕ} (S : StandardIndex n k) :
    standardWedge S ∈ (⋀[ℝ]^k (Coord n)) := by
  rw [standardWedge_eq_coordinateWedge]
  exact coordinateWedge_mem _

lemma coordinateWedge_perm {n k : ℕ} (I : Fin k → Fin n) (σ : Equiv.Perm (Fin k)) :
    coordinateWedge (I ∘ σ) = σ.sign • coordinateWedge I :=
  (ExteriorAlgebra.ιMulti ℝ k).map_perm (fun i => covectorBasis n (I i)) σ

lemma coordinateWedge_swap {n k : ℕ} (I : Fin k → Fin n) {i j : Fin k} (hij : i ≠ j) :
    coordinateWedge (I ∘ Equiv.swap i j) = -coordinateWedge I :=
  (ExteriorAlgebra.ιMulti ℝ k).map_swap (fun i => covectorBasis n (I i)) hij

lemma coordinateWedge_of_lt {n k : ℕ} (h : n < k) (I : Fin k → Fin n) :
    coordinateWedge I = 0 := by
  apply (ExteriorAlgebra.ιMulti ℝ k).map_eq_zero_of_not_injective
  intro hi
  have hI : Injective I := by
    intro a b hab
    apply hi
    simp only [hab]
  have := Fintype.card_le_of_injective I hI
  simp only [Fintype.card_fin] at this
  omega

lemma coordinateWedge_mul {n k m : ℕ} (I : Fin k → Fin n) (J : Fin m → Fin n) :
    coordinateWedge I * coordinateWedge J = coordinateWedge (Fin.append I J) := by
  unfold coordinateWedge
  rw [ExteriorAlgebra.ιMulti_mul_ιMulti]
  congr 1
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;> simp

lemma formField_expansion {n : ℕ} (ω : FormField n) (x : Euclidean n) :
    ω x = ∑ S, formCoefficient ω S x • exteriorBasis n S :=
  ((exteriorBasis n).sum_repr (ω x)).symm

lemma formFromCoefficients_grade {n k : ℕ}
    (a : (Fin k → Fin n) → Euclidean n → ℝ) (x : Euclidean n) :
    formFromCoefficients a x ∈ (⋀[ℝ]^k (Coord n)) := by
  exact Submodule.sum_mem _ (fun I _ => Submodule.smul_mem _ _ (coordinateWedge_mem I))

lemma formFromCoefficients_of_lt {n k : ℕ} (h : n < k)
    (a : (Fin k → Fin n) → Euclidean n → ℝ) : formFromCoefficients a = 0 := by
  funext x
  simp [formFromCoefficients, coordinateWedge_of_lt h]

/-- All ordered coordinate coefficients give exactly the source's sum of minors. -/
lemma surfaceIntegrand_fromCoefficients {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (a : (Fin k → Fin n) → Euclidean n → ℝ) (u : Coord k) :
    surfaceIntegrand Φ (formFromCoefficients a) u =
      ∑ I, a I (Φ.map u) *
        Matrix.det (fun i j => (fderiv ℝ Φ.map u (Pi.single j 1)) (I i)) := by
  simp only [surfaceIntegrand, formFromCoefficients, map_sum, map_smul,
    evaluateForm_coordinateWedge, smul_eq_mul]

lemma surfaceIntegral_fromCoefficients {n k : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (a : (Fin k → Fin n) → Euclidean n → ℝ) :
    surfaceIntegral Φ (formFromCoefficients a) = Φ.domain.integral
      (fun u => ∑ I, a I (Φ.map u) *
        Matrix.det (fun i j => (fderiv ℝ Φ.map u (Pi.single j 1)) (I i))) := by
  unfold surfaceIntegral
  congr 1
  funext u
  exact surfaceIntegrand_fromCoefficients Φ a u

lemma FormEqOn.of_eq {n k : ℕ} {E : Set (Euclidean n)} {ω η : FormField n}
    (h : ω = η) : FormEqOn E k ω η := by
  subst η
  intro Φ
  rfl

end Rudin.PMA.Chapter10
