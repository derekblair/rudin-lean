import Rudin.PMA.Chapter10.AffineSimplices
import Rudin.PMA.Chapter10.StandardForms

/-!
# PMA 10.26: relative orientation of affine simplices

The discussion on printed page 267 defines relative orientation by a permutation
of the ordered vertices. This supplements `pma10_26_contract`; the integration
identity which justifies the convention is the subsequent Theorem 10.27.

Relative orientation below is a relation on vertex families, not equality of
their parametrizations. Repeated vertices are permitted. In that degenerate
case different permutations can witness different signs, so no uniqueness of
the sign is asserted.
-/

noncomputable section
set_option autoImplicit false
open Function

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The relative-orientation convention in 10.26: `q` is obtained from `p`
by a permutation of sign `ε`. -/
def HasAffineRelativeOrientation {k n : ℕ} (ε : ℤˣ)
    (p q : Fin (k + 1) → Euclidean n) : Prop :=
  ∃ σ : Equiv.Perm (Fin (k + 1)), q = p ∘ σ ∧ σ.sign = ε

/-- The same-orientation relation of 10.26. -/
def SameAffineOrientation {k n : ℕ} (p q : Fin (k + 1) → Euclidean n) : Prop :=
  HasAffineRelativeOrientation 1 p q

/-- The opposite-orientation relation of 10.26. -/
def OppositeAffineOrientation {k n : ℕ} (p q : Fin (k + 1) → Euclidean n) : Prop :=
  HasAffineRelativeOrientation (-1) p q

/-- The affine change of parameter corresponding to an ordered vertex
permutation. Its name is separate from the construction used in 10.27. -/
def affineVertexReparametrization10_26 {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) : Coord k →ᵃ[ℝ] Coord k :=
  affineMapFromVertices (standardVertex k ∘ σ)

theorem affineRelativeOrientation_permutation {k n : ℕ}
    (p : Fin (k + 1) → Euclidean n) (σ : Equiv.Perm (Fin (k + 1))) :
    HasAffineRelativeOrientation σ.sign p (p ∘ σ) :=
  ⟨σ, rfl, rfl⟩

theorem sameAffineOrientation_refl {k n : ℕ} (p : Fin (k + 1) → Euclidean n) :
    SameAffineOrientation p p := by
  exact ⟨1, by ext i; rfl, by simp⟩

theorem affineRelativeOrientation_symm {k n : ℕ} {ε : ℤˣ}
    {p q : Fin (k + 1) → Euclidean n} (h : HasAffineRelativeOrientation ε p q) :
    HasAffineRelativeOrientation ε q p := by
  obtain ⟨σ, rfl, hσ⟩ := h
  refine ⟨σ.symm, ?_, ?_⟩
  · ext i
    simp
  · simpa only [Equiv.Perm.sign_symm] using hσ

theorem affineRelativeOrientation_trans {k n : ℕ} {ε δ : ℤˣ}
    {p q r : Fin (k + 1) → Euclidean n}
    (hpq : HasAffineRelativeOrientation ε p q)
    (hqr : HasAffineRelativeOrientation δ q r) :
    HasAffineRelativeOrientation (ε * δ) p r := by
  obtain ⟨σ, rfl, hσ⟩ := hpq
  obtain ⟨τ, rfl, hτ⟩ := hqr
  exact ⟨σ * τ, rfl, by rw [Equiv.Perm.sign_mul, hσ, hτ]⟩

theorem affineRelativeOrientation_sign_cases {k n : ℕ} {ε : ℤˣ}
    {p q : Fin (k + 1) → Euclidean n} (h : HasAffineRelativeOrientation ε p q) :
    SameAffineOrientation p q ∨ OppositeAffineOrientation p q := by
  obtain rfl | rfl := Int.units_eq_one_or ε
  · exact Or.inl h
  · exact Or.inr h

/-- Repeated vertices explain why the relative sign is not asserted to be
unique: a constant one-simplex admits both orientation witnesses. -/
theorem constantAffineSimplex_both_orientations {n : ℕ} (x : Euclidean n) :
    SameAffineOrientation (fun _ : Fin 2 => x) (fun _ => x) ∧
      OppositeAffineOrientation (fun _ : Fin 2 => x) (fun _ => x) := by
  refine ⟨sameAffineOrientation_refl _, ?_⟩
  exact ⟨Equiv.swap 0 1, rfl, Equiv.Perm.sign_swap (by decide)⟩

@[simp] theorem affineVertexReparametrization10_26_vertex {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) (i : Fin (k + 1)) :
    affineVertexReparametrization10_26 σ (standardVertex k i) = standardVertex k (σ i) :=
  affineMapFromVertices_standardVertex _ i

/-- The two orderings have parametrizations related by composition, rather
than literal equality or pointwise multiplication by their relative sign. -/
theorem affineSimplexMap_relative_reparametrization {k n : ℕ}
    (p : Fin (k + 1) → Euclidean n) (σ : Equiv.Perm (Fin (k + 1))) :
    affineSimplexMap (p ∘ σ) = affineSimplexMap p ∘ affineVertexReparametrization10_26 σ := by
  have h : affineMapFromVertices (p ∘ σ) =
      (affineMapFromVertices p).comp (affineVertexReparametrization10_26 σ) := by
    apply affineMap_ext_standardVertex
    intro i
    simp
  exact congrArg DFunLike.coe h

/-- The sign convention agrees with Rudin's integer tuple sign from 9.33,
using the zero-based vertex indices of 10.26. -/
theorem affinePermutationSign_tupleSign {k : ℕ}
    (σ : Equiv.Perm (Fin (k + 1))) :
    tupleSign (fun i => ((σ i).val : ℤ)) = (σ.sign : ℤ) := by
  exact tupleSign_increasing_perm (I := id) (fun _ _ h => h) σ

/-- Supplementary coverage for the relative-orientation paragraph of 10.26.
The preceding `pma10_26` supplies its affine, derivative, determinant, and
signed zero-simplex clauses. -/
def pma10_26_relativeOrientation_contract : Prop :=
  ∀ (k n : ℕ) (p : Fin (k + 1) → Euclidean n)
    (σ : Equiv.Perm (Fin (k + 1))),
    HasAffineRelativeOrientation σ.sign p (p ∘ σ) ∧
    tupleSign (fun i => ((σ i).val : ℤ)) = (σ.sign : ℤ) ∧
    affineSimplexMap (p ∘ σ) = affineSimplexMap p ∘ affineVertexReparametrization10_26 σ ∧
    (σ.sign = 1 → SameAffineOrientation p (p ∘ σ)) ∧
    (σ.sign = -1 → OppositeAffineOrientation p (p ∘ σ))

theorem pma10_26_relativeOrientation : pma10_26_relativeOrientation_contract := by
  intro k n p σ
  refine ⟨affineRelativeOrientation_permutation p σ, affinePermutationSign_tupleSign σ,
    affineSimplexMap_relative_reparametrization p σ, ?_, ?_⟩
  · intro h
    exact ⟨σ, rfl, h⟩
  · intro h
    exact ⟨σ, rfl, h⟩

end Rudin.PMA.Chapter10
