import Rudin.PMA.Chapter10.CumulativeCoordinates

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Relabel coordinates by a permutation. -/
def coordinatePermutation {n : ℕ} (σ : Equiv.Perm (Fin n)) : Coord n ≃ₗ[ℝ] Coord n where
  toFun u := u ∘ σ.symm
  invFun u := u ∘ σ
  left_inv u := by ext i; simp
  right_inv u := by ext i; simp
  map_add' u v := rfl
  map_smul' c u := rfl

lemma coordinatePermutation_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Coord n) (i : Fin n) :
    coordinatePermutation σ u i = u (σ.symm i) := rfl

lemma coordinatePermutation_symm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Coord n) (i : Fin n) :
    (coordinatePermutation σ).symm u i = u (σ i) := rfl

lemma coordinatePermutation_simplex {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MapsTo (coordinatePermutation σ) (standardSimplex n) (standardSimplex n) := by
  intro u hu
  refine ⟨fun i => hu.1 _, ?_⟩
  change (∑ i, u (σ.symm i)) ≤ 1
  rw [Equiv.sum_comp]
  exact hu.2

lemma coordinatePermutation_unit {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    MapsTo (coordinatePermutation σ) (Cell.unit n).carrier (Cell.unit n).carrier := by
  intro u hu
  rw [Cell.mem_carrier] at hu ⊢
  exact fun i => hu (σ.symm i)

/-- Simultaneous relabeling in source and target keeps every staircase chart
positively oriented, without a parity-dependent choice of vertices. -/
def staircaseLinear {n : ℕ} (σ : Equiv.Perm (Fin n)) : Coord n →L[ℝ] Coord n :=
  ((coordinatePermutation σ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (cumulativeCoordinates n)).comp
    (coordinatePermutation σ).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma staircaseLinear_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : Coord n) :
    staircaseLinear σ u = coordinatePermutation σ
      (cumulativeCoordinates n ((coordinatePermutation σ).symm u)) := rfl

lemma staircaseLinear_det {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    LinearMap.det (staircaseLinear σ).toLinearMap = 1 := by
  change LinearMap.det ((coordinatePermutation σ).toLinearMap.comp
    ((cumulativeCoordinates n).toLinearMap.comp (coordinatePermutation σ).symm.toLinearMap)) = 1
  rw [LinearMap.det_conj, cumulativeCoordinates_det]

lemma staircaseLinear_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Injective (staircaseLinear σ) :=
  (coordinatePermutation σ).injective.comp
    ((cumulativeCoordinates_injective n).comp (coordinatePermutation σ).symm.injective)

def staircaseChamber {n : ℕ} (σ : Equiv.Perm (Fin n)) : Set (Coord n) :=
  {y | y ∈ (Cell.unit n).carrier ∧ Monotone (y ∘ σ)}

lemma staircaseLinear_image {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    staircaseLinear σ '' standardSimplex n = staircaseChamber σ := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hp : (coordinatePermutation σ).symm u ∈ standardSimplex n :=
      coordinatePermutation_simplex σ.symm hu
    refine ⟨coordinatePermutation_unit σ (cumulativeCoordinates_unit hp), ?_⟩
    have he : (staircaseLinear σ u) ∘ σ =
        cumulativeCoordinates n ((coordinatePermutation σ).symm u) := by
      ext i
      simp [staircaseLinear_apply, coordinatePermutation_apply]
    rw [he]
    exact cumulativeCoordinates_monotone hp.1
  · rintro ⟨hy, hm⟩
    have hp : (coordinatePermutation σ).symm y ∈ (Cell.unit n).carrier :=
      coordinatePermutation_unit σ.symm hy
    let u := coordinatePermutation σ (coordinateIncrements ((coordinatePermutation σ).symm y))
    refine ⟨u, coordinatePermutation_simplex σ (coordinateIncrements_simplex hp hm), ?_⟩
    simp [u, staircaseLinear_apply, cumulativeCoordinates_increments]

lemma staircaseChambers_cover (n : ℕ) :
    (⋃ σ : Equiv.Perm (Fin n), staircaseChamber σ) = (Cell.unit n).carrier := by
  ext y
  constructor
  · intro hy
    obtain ⟨σ, hy⟩ := mem_iUnion.mp hy
    exact hy.1
  · intro hy
    exact mem_iUnion.mpr ⟨Tuple.sort y, hy, Tuple.monotone_sort y⟩

lemma interior_coordinate_le_strict {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    interior {y : Coord n | y i ≤ y j} ⊆ {y | y i < y j} := by
  let L : Coord n →L[ℝ] ℝ := (ContinuousLinearMap.proj i : Coord n →L[ℝ] ℝ) -
    (ContinuousLinearMap.proj j : Coord n →L[ℝ] ℝ)
  have hs : Surjective L := by
    intro t
    refine ⟨Pi.single i t, ?_⟩
    simp [L, Pi.single_apply, hij, Ne.symm hij]
  have he : {y : Coord n | y i ≤ y j} = L ⁻¹' Iic 0 := by
    ext y
    simp [L, sub_nonpos]
  rw [he, L.interior_preimage hs, interior_Iic]
  intro y hy
  change y i - y j < 0 at hy
  exact sub_neg.mp hy

lemma staircaseChamber_interior_strict {n : ℕ} {σ : Equiv.Perm (Fin n)}
    {y : Coord n} (hy : y ∈ interior (staircaseChamber σ)) : StrictMono (y ∘ σ) := by
  intro i j hij
  have hsub : staircaseChamber σ ⊆ {y : Coord n | y (σ i) ≤ y (σ j)} :=
    fun y h => h.2 hij.le
  exact interior_coordinate_le_strict (σ i) (σ j) (σ.injective.ne hij.ne)
    (interior_mono hsub hy)

lemma staircaseChambers_interiors_disjoint {n : ℕ} :
    Pairwise (fun σ τ : Equiv.Perm (Fin n) =>
      Disjoint (interior (staircaseChamber σ)) (interior (staircaseChamber τ))) := by
  intro σ τ hne
  apply disjoint_left.mpr
  intro y hyσ hyτ
  have hs := staircaseChamber_interior_strict hyσ
  have ht := staircaseChamber_interior_strict hyτ
  have hσ : σ = Tuple.sort y := Tuple.eq_sort_iff.mpr
    ⟨hs.monotone, fun i j hij he => False.elim ((hs hij).ne he)⟩
  have hτ : τ = Tuple.sort y := Tuple.eq_sort_iff.mpr
    ⟨ht.monotone, fun i j hij he => False.elim ((ht hij).ne he)⟩
  exact hne (hσ.trans hτ.symm)

end Rudin.PMA.Chapter10
