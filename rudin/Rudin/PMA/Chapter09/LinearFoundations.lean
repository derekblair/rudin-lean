import Mathlib

/-!
# PMA 9.1–9.5: vector spaces and linear transformations

The algebraic assertions are stated for abstract real vector spaces, rather than
only subspaces of Euclidean space. This is the generalization explicitly allowed
in the chapter's opening paragraph. Finite families are indexed by `Fin n` (indices
start at zero). The set formulation of 9.1(a) and the Euclidean examples are also
included. `pma9_1_dimension_iff` identifies the book's definition of dimension with
Mathlib's `finrank`; thus later use of `finrank` does not replace that definition
by an unproved convention.
-/

noncomputable section

open scoped BigOperators
open Module

namespace Rudin.PMA.Chapter09

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- 9.1(a): a nonempty subset closed under addition and real scalar multiplication. -/
def pma9_1_vectorSpace (X : Set V) : Prop :=
  X.Nonempty ∧ (∀ x ∈ X, ∀ y ∈ X, x + y ∈ X) ∧
    ∀ c : ℝ, ∀ x ∈ X, c • x ∈ X

/-- The set definition is exactly the carrier of a real submodule. -/
theorem pma9_1_vectorSpace_iff (X : Set V) :
    pma9_1_vectorSpace X ↔ ∃ S : Submodule ℝ V, (S : Set V) = X := by
  constructor
  · rintro ⟨⟨x, hx⟩, ha, hs⟩
    refine ⟨{ carrier := X
              zero_mem' := by simpa using hs 0 x hx
              add_mem' := fun hx hy => ha _ hx _ hy
              smul_mem' := fun c _ hx => hs c _ hx }, rfl⟩
  · rintro ⟨S, rfl⟩
    exact ⟨⟨0, S.zero_mem⟩, fun _ hx _ hy => S.add_mem hx hy,
      fun c _ hx => S.smul_mem c hx⟩

/-- 9.1(b): a finite linear combination. -/
def pma9_1_linearCombination {r : ℕ} (x : Fin r → V) (c : Fin r → ℝ) : V :=
  ∑ i, c i • x i

/-- 9.1(b): the span of an arbitrary set. -/
abbrev pma9_1_span (S : Set V) : Submodule ℝ V := Submodule.span ℝ S

/-- 9.1(b): `S` spans `E` when `E` is its span. -/
def pma9_1_spans (S E : Set V) : Prop := (pma9_1_span S : Set V) = E

/-- Span membership means being a finite linear combination of elements of the set. -/
theorem pma9_1_span_iff (S : Set V) (x : V) :
    x ∈ pma9_1_span S ↔
      ∃ (c : V → ℝ) (t : Finset V), (↑t : Set V) ⊆ S ∧
        Function.support c ⊆ (↑t : Set V) ∧ ∑ y ∈ t, c y • y = x :=
  Submodule.mem_span_iff_exists_finset_subset

/-- The observation attached to 9.1(b): every span is a vector space. -/
theorem pma9_1_span_vectorSpace (S : Set V) :
    pma9_1_vectorSpace (pma9_1_span S : Set V) :=
  (pma9_1_vectorSpace_iff _).2 ⟨pma9_1_span S, rfl⟩

/-- 9.1(c): independence, with the book's coefficient criterion below. -/
abbrev pma9_1_independent {r : ℕ} (x : Fin r → V) : Prop := LinearIndependent ℝ x

/-- 9.1(c): dependence is the negation of independence. -/
def pma9_1_dependent {r : ℕ} (x : Fin r → V) : Prop := ¬pma9_1_independent x

theorem pma9_1_independent_iff {r : ℕ} (x : Fin r → V) :
    pma9_1_independent x ↔
      ∀ c : Fin r → ℝ, pma9_1_linearCombination x c = 0 → ∀ i, c i = 0 :=
  Fintype.linearIndependent_iff

theorem pma9_1_dependent_iff {r : ℕ} (x : Fin r → V) :
    pma9_1_dependent x ↔
      ∃ c : Fin r → ℝ, pma9_1_linearCombination x c = 0 ∧ ∃ i, c i ≠ 0 :=
  Fintype.not_linearIndependent_iff

/-- The observation attached to 9.1(c): an independent family contains no zero. -/
theorem pma9_1_independent_ne_zero {r : ℕ} {x : Fin r → V}
    (hx : pma9_1_independent x) (i : Fin r) : x i ≠ 0 := hx.ne_zero i

/-- 9.1(d): there are `r` independent vectors, but not `r + 1` independent vectors. -/
def pma9_1_dimension (V : Type*) [AddCommGroup V] [Module ℝ V] (r : ℕ) : Prop :=
  (∃ x : Fin r → V, LinearIndependent ℝ x) ∧
    ¬∃ x : Fin (r + 1) → V, LinearIndependent ℝ x

theorem pma9_1_dimension_iff [FiniteDimensional ℝ V] (r : ℕ) :
    pma9_1_dimension V r ↔ Module.finrank ℝ V = r := by
  constructor
  · rintro ⟨⟨x, hx⟩, hnext⟩
    have hlo : r ≤ Module.finrank ℝ V := by simpa using hx.fintype_card_le_finrank
    have hhi : Module.finrank ℝ V ≤ r := by
      by_contra h
      exact hnext (exists_linearIndependent_of_le_finrank (by omega))
    omega
  · intro h
    refine ⟨exists_linearIndependent_of_le_finrank h.ge, ?_⟩
    rintro ⟨x, hx⟩
    have := hx.fintype_card_le_finrank
    simp [h] at this

/-- The zero space in 9.1(d) has dimension zero. -/
theorem pma9_1_zero_dimension : pma9_1_dimension (⊥ : Submodule ℝ V) 0 := by
  apply (pma9_1_dimension_iff 0).2
  simp

/-- The set consisting of zero is a vector space, as stated in 9.1(d). -/
theorem pma9_1_zero_vectorSpace : pma9_1_vectorSpace ({0} : Set V) := by
  exact (pma9_1_vectorSpace_iff _).2 ⟨⊥, by simp⟩

/-- 9.1(e): an independent spanning family is a basis. -/
def pma9_1_isBasis {r : ℕ} (x : Fin r → V) : Prop :=
  pma9_1_independent x ∧ pma9_1_span (Set.range x) = ⊤

/-- The book's basis criterion produces Mathlib's bundled basis. -/
def pma9_1_basis {r : ℕ} {x : Fin r → V} (hx : pma9_1_isBasis x) :
    Basis (Fin r) ℝ V := Basis.mk hx.1 hx.2.ge

theorem pma9_1_basis_apply {r : ℕ} {x : Fin r → V} (hx : pma9_1_isBasis x)
    (i : Fin r) : pma9_1_basis hx i = x i := Basis.mk_apply _ _ _

/-- 9.1(e): coordinates with respect to a basis. -/
def pma9_1_coordinates {r : ℕ} (b : Basis (Fin r) ℝ V) (x : V) : Fin r → ℝ :=
  fun i => b.repr x i

/-- The existence and uniqueness assertion attached to 9.1(e). -/
theorem pma9_1_unique_coordinates {r : ℕ} (b : Basis (Fin r) ℝ V) (x : V) :
    ∃! c : Fin r → ℝ, pma9_1_linearCombination b c = x := by
  refine ⟨pma9_1_coordinates b x, b.sum_repr x, ?_⟩
  intro c hc
  change c = fun i => b.repr x i
  rw [← hc]
  exact (b.repr_sum_self c).symm

/-- 9.1(e): the standard basis of Euclidean space. -/
def pma9_1_standardBasis (n : ℕ) : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

theorem pma9_1_standardBasis_apply (n : ℕ) (i j : Fin n) :
    pma9_1_standardBasis n i j = if j = i then 1 else 0 := by
  simp [pma9_1_standardBasis, EuclideanSpace.basisFun_apply, eq_comm]

theorem pma9_1_standard_coordinates (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑ i, x i • pma9_1_standardBasis n i) = x := by
  simpa [pma9_1_standardBasis] using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr x

/-- 9.2: a space spanned by `r` vectors has dimension at most `r`.
The harmless generalization `r = 0` is included. -/
theorem pma9_2 {r : ℕ} {x : Fin r → V}
    (hx : Submodule.span ℝ (Set.range x) = ⊤) : Module.finrank ℝ V ≤ r := by
  simpa using finrank_le_of_span_eq_top hx

/-- 9.2 in the book's dimension predicate, including existence of the dimension. -/
theorem pma9_2_dimension {r : ℕ} {x : Fin r → V}
    (hx : Submodule.span ℝ (Set.range x) = ⊤) :
    ∃ d ≤ r, pma9_1_dimension V d := by
  classical
  let : Module.Finite ℝ V := Module.Finite.of_fg_top
    ⟨Finset.univ.image x, by simpa using hx⟩
  exact ⟨Module.finrank ℝ V, pma9_2 hx, (pma9_1_dimension_iff _).2 rfl⟩

/-- The corollary to 9.2: Euclidean `n`-space has dimension `n`. -/
theorem pma9_2_corollary (n : ℕ) :
    pma9_1_dimension (EuclideanSpace ℝ (Fin n)) n := by
  apply (pma9_1_dimension_iff n).2
  simp

/-- 9.3(a): `n` vectors in a space of dimension `n` span iff they are independent. -/
theorem pma9_3_a [FiniteDimensional ℝ V] {n : ℕ}
    (hdim : pma9_1_dimension V n) (x : Fin n → V) :
    Submodule.span ℝ (Set.range x) = ⊤ ↔ LinearIndependent ℝ x := by
  have hn : Fintype.card (Fin n) = Module.finrank ℝ V := by
    simpa using ((pma9_1_dimension_iff n).1 hdim).symm
  exact ⟨fun hx => linearIndependent_of_top_le_span_of_card_eq_finrank hx.ge hn,
    fun hx => hx.span_eq_top_of_card_eq_finrank' hn⟩

/-- 9.3(b): a basis with `n` members exists. -/
theorem pma9_3_b [FiniteDimensional ℝ V] {n : ℕ}
    (hdim : pma9_1_dimension V n) : Nonempty (Basis (Fin n) ℝ V) :=
  ⟨Module.finBasisOfFinrankEq ℝ V ((pma9_1_dimension_iff n).1 hdim)⟩

/-- The other assertion in 9.3(b): every basis is finite and has `n` members. -/
theorem pma9_3_b_card [FiniteDimensional ℝ V] {n : ℕ}
    (hdim : pma9_1_dimension V n) {ι : Type*} (b : Basis ι ℝ V) :
    Finite ι ∧ Nat.card ι = n := by
  exact ⟨b.linearIndependent.finite,
    (Module.finrank_eq_nat_card_basis b).symm.trans ((pma9_1_dimension_iff n).1 hdim)⟩

/-- 9.3(c): any independent family extends to a basis with `n` members.
The empty independent family is included, as well as the printed `1 ≤ r ≤ n` case. -/
theorem pma9_3_c [FiniteDimensional ℝ V] {n r : ℕ}
    (hdim : pma9_1_dimension V n) {x : Fin r → V} (hx : LinearIndependent ℝ x) :
    ∃ b : Basis (Fin n) ℝ V, Set.range x ⊆ Set.range b := by
  let b := Basis.extend hx.linearIndepOn_id
  let := Fintype.ofFinite (hx.linearIndepOn_id.extend (Set.subset_univ _))
  have hc : Fintype.card (hx.linearIndepOn_id.extend (Set.subset_univ _)) = n := by
    rw [← Module.finrank_eq_card_basis b]
    exact (pma9_1_dimension_iff n).1 hdim
  refine ⟨b.reindex (Fintype.equivFinOfCardEq hc), ?_⟩
  rw [Basis.range_reindex, Basis.range_extend]
  exact hx.linearIndepOn_id.subset_extend _

/-- 9.4: linearity of an ordinary function. -/
def pma9_4_isLinear (A : V → W) : Prop :=
  (∀ x y, A (x + y) = A x + A y) ∧ ∀ (c : ℝ) x, A (c • x) = c • A x

/-- 9.4's two identities are exactly the data of a linear transformation. -/
def pma9_4_linearMap {A : V → W} (hA : pma9_4_isLinear A) : V →ₗ[ℝ] W where
  toFun := A
  map_add' := hA.1
  map_smul' := hA.2

theorem pma9_4_linearMap_isLinear (A : V →ₗ[ℝ] W) : pma9_4_isLinear A :=
  ⟨A.map_add, A.map_smul⟩

theorem pma9_4_zero (A : V →ₗ[ℝ] W) : A 0 = 0 := A.map_zero

/-- The image formula in 9.4. -/
theorem pma9_4_basis_image {r : ℕ} (A : V →ₗ[ℝ] W) (b : Basis (Fin r) ℝ V) (x : V) :
    A x = ∑ i, b.repr x i • A (b i) := by
  calc
    A x = A (∑ i, b.repr x i • b i) := congrArg A (b.sum_repr x).symm
    _ = ∑ i, b.repr x i • A (b i) := by simp only [map_sum, map_smul]

/-- A linear transformation is determined by its values on a basis. -/
theorem pma9_4_determined_by_basis {ι : Type*} (b : Basis ι ℝ V)
    (A B : V →ₗ[ℝ] W) (h : ∀ i, A (b i) = B (b i)) : A = B := b.ext h

/-- 9.4: a linear operator is a linear transformation from a space to itself. -/
abbrev pma9_4_operator (V : Type*) [AddCommGroup V] [Module ℝ V] := V →ₗ[ℝ] V

/-- 9.4: invertibility means both injectivity and surjectivity. -/
def pma9_4_invertible (A : V →ₗ[ℝ] V) : Prop :=
  Function.Injective A ∧ Function.Surjective A

/-- The inverse in 9.4 is itself a linear operator. -/
def pma9_4_inverse (A : V →ₗ[ℝ] V) (hA : pma9_4_invertible A) : V →ₗ[ℝ] V :=
  (LinearEquiv.ofBijective A hA).symm.toLinearMap

theorem pma9_4_inverse_left (A : V →ₗ[ℝ] V) (hA : pma9_4_invertible A) (x : V) :
    pma9_4_inverse A hA (A x) = x := (LinearEquiv.ofBijective A hA).symm_apply_apply x

theorem pma9_4_inverse_right (A : V →ₗ[ℝ] V) (hA : pma9_4_invertible A) (x : V) :
    A (pma9_4_inverse A hA x) = x := (LinearEquiv.ofBijective A hA).apply_symm_apply x

/-- 9.5: in finite dimension, an endomorphism is injective iff it is onto. -/
theorem pma9_5 [FiniteDimensional ℝ V] (A : V →ₗ[ℝ] V) :
    Function.Injective A ↔ Function.Surjective A := LinearMap.injective_iff_surjective

/-- The equivalent formulation using the range, exactly as in 9.5. -/
theorem pma9_5_range [FiniteDimensional ℝ V] (A : V →ₗ[ℝ] V) :
    Function.Injective A ↔ LinearMap.range A = ⊤ := by
  rw [LinearMap.range_eq_top]
  exact pma9_5 A

end Rudin.PMA.Chapter09
