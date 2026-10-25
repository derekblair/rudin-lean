import Rudin.PMA.Chapter09.Linear
import Mathlib.Topology.PartitionOfUnity

set_option autoImplicit false
noncomputable section
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- A finite continuous partition subordinate to an arbitrary open cover,
with the global decomposition of a function supported on the compact set. -/
def pma10_8_contract : Prop :=
  ∀ (n : ℕ) (ι : Type) (K : Set (Euclidean n)) (V : ι → Set (Euclidean n)),
    IsCompact K → (∀ i, IsOpen (V i)) → K ⊆ ⋃ i, V i →
    ∃ (s : Finset ι) (ψ : s → C(Euclidean n, ℝ)),
      (∀ i x, ψ i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, tsupport (ψ i) ⊆ V i) ∧
      (∀ x ∈ K, ∑ i, ψ i x = 1) ∧
      (∀ f : C(Euclidean n, ℝ), tsupport f ⊆ K →
        (∀ x, f x = ∑ i, ψ i x * f x) ∧
        ∀ i, Continuous (fun x => ψ i x * f x) ∧
          tsupport (fun x => ψ i x * f x) ⊆ V i)

theorem pma10_8 : pma10_8_contract := by
  classical
  intro n ι K V hK hV hcover
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover V hV hcover
  have hcover' : K ⊆ ⋃ i : s, V i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hx)
    obtain ⟨his, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨⟨i, his⟩, hxi⟩
  obtain ⟨ψ, hψ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
    (fun i : s => V i) (fun i => hV i) hcover'
  have hsum : ∀ x ∈ K, ∑ i : s, ψ i x = 1 := by
    intro x hx
    simpa only [finsum_eq_sum_of_fintype] using ψ.sum_eq_one hx
  refine ⟨s, fun i => ψ i, fun i x => ⟨ψ.nonneg i x, ψ.le_one i x⟩,
    hψ, hsum, ?_⟩
  intro f hf
  constructor
  · intro x
    by_cases hx : x ∈ K
    · rw [← Finset.sum_mul, hsum x hx, one_mul]
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
      simp only [hz, mul_zero, Finset.sum_const_zero]
  · intro i
    exact ⟨(ψ i).continuous.mul f.continuous,
      tsupport_mul_subset_left.trans (hψ i)⟩

end Rudin.PMA.Chapter10
