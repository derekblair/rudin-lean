import Rudin.PMA.Chapter10.SimplexBoundaries
import Mathlib.Data.Fin.Parity

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The two deletion orders are equal as actual parameterized simplices. -/
lemma C2Simplex.face_face {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex (k + 2) n E) (i : Fin (k + 3)) (j : Fin (k + 2)) :
    (σ.face i).face j = (σ.face (i.succAbove j)).face (j.predAbove i) := by
  apply C2Simplex.ext
  funext u
  change σ.map (standardFaceMap i (standardFaceMap j u)) =
    σ.map (standardFaceMap (i.succAbove j) (standardFaceMap (j.predAbove i) u))
  exact congrArg σ.map (congrFun (standardFaceMap_comp_face i j) u)

/-- Each codimension-two face occurs twice with opposite integer signs.
This is literal cancellation in the free chain module. -/
lemma chainBoundary_simplexBoundary {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex (k + 2) n E) : chainBoundary (simplexBoundary σ) = 0 := by
  classical
  simp only [simplexBoundary, map_sum, map_smul, chainBoundary_single,
    Finset.smul_sum, smul_smul, one_mul, ← pow_add]
  rw [← Finset.sum_product', Finset.univ_product_univ]
  apply Finset.sum_ninvolution
    (fun p : Fin (k + 3) × Fin (k + 2) => (p.1.succAbove p.2, p.2.predAbove p.1))
  · rintro ⟨i, j⟩
    dsimp only
    rw [Fin.neg_one_pow_succAbove_add_predAbove, ← σ.face_face i j, neg_smul]
    exact add_neg_cancel _
  · rintro ⟨i, j⟩ _ he
    exact Fin.succAbove_ne i j (congrArg Prod.fst he)
  · intro p
    exact Finset.mem_univ _
  · rintro ⟨i, j⟩
    simp only [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

/-- The boundary operator squares to zero on every finite integer chain. -/
lemma chainBoundary_twice {k n : ℕ} {E : Set (Euclidean n)}
    (Γ : SimplexChain (k + 2) n E) : chainBoundary (chainBoundary Γ) = 0 := by
  have he : (chainBoundary (k := k) (n := n) (E := E)).comp chainBoundary = 0 := by
    apply Finsupp.lhom_ext
    intro σ z
    simp only [LinearMap.comp_apply, chainBoundary_single, map_smul,
      chainBoundary_simplexBoundary, smul_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun he Γ

end Rudin.PMA.Chapter10
