import Rudin.PMA.Chapter10.Partition

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- An empty compact set permits an actually empty index type: no hidden
inhabited-cover premise may enter the partition theorem. -/
theorem empty_cover_partition (n : ℕ) :
    ∃ (s : Finset Empty) (ψ : s → C(Euclidean n, ℝ)),
      s = ∅ ∧ ∀ x, ∑ i, ψ i x = 0 := by
  classical
  obtain ⟨s, ψ, _, _, _, _⟩ :=
    pma10_8 n Empty ∅ (fun _ => ∅) isCompact_empty
      (fun _ => isOpen_empty) (by simp)
  refine ⟨s, ψ, ?_, ?_⟩
  · ext i
    exact Empty.elim i
  · intro x
    exact Finset.sum_eq_zero (fun i _ => Empty.elim i.val)

/-- The partition must detect every covered point by a strictly positive
coefficient, and its closed-support condition forces each coefficient to vanish
at every point outside the assigned open set. -/
theorem partition_detects_points_and_vanishes_outside (n : ℕ) (ι : Type)
    (K : Set (Euclidean n)) (V : ι → Set (Euclidean n))
    (hK : IsCompact K) (hV : ∀ i, IsOpen (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ (s : Finset ι) (ψ : s → C(Euclidean n, ℝ)),
      (∀ x ∈ K, ∃ i : s, 0 < ψ i x ∧ x ∈ V i) ∧
      (∀ i : s, ∀ x, x ∉ V i → ψ i x = 0) := by
  classical
  obtain ⟨s, ψ, hbounds, hsupp, hsum, _⟩ := pma10_8 n ι K V hK hV hcover
  refine ⟨s, ψ, ?_, ?_⟩
  · intro x hx
    have hpos : ∃ i : s, 0 < ψ i x := by
      by_contra! hnone
      have hz : ∀ i : s, ψ i x = 0 :=
        fun i => le_antisymm (hnone i) (hbounds i x).1
      have h := hsum x hx
      simp only [hz, Finset.sum_const_zero] at h
      norm_num at h
    obtain ⟨i, hi⟩ := hpos
    refine ⟨i, hi, hsupp i ?_⟩
    exact subset_tsupport (ψ i) (ne_of_gt hi)
  · intro i x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp i h))

end Rudin.PMA.Chapter10.FidelityProbes
