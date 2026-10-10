import Mathlib

/-! Native closed-cell Darboux definitions for PMA Chapter 6.
This file deliberately imposes no continuity convention on the integrator. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter06

/-- Source partitions allow repeated points and zero-width cells. -/
structure Partition (a b : ℝ) where
  n : ℕ
  point : Fin (n + 1) → ℝ
  mono : Monotone point
  left : point 0 = a
  right : point (Fin.last n) = b

def BoundedOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M

def Partition.cell {a b : ℝ} (P : Partition a b) (i : Fin P.n) : Set ℝ :=
  Icc (P.point i.castSucc) (P.point i.succ)

def Partition.weight {a b : ℝ} (P : Partition a b) (α : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  α (P.point i.succ) - α (P.point i.castSucc)

def cellLower {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b) (i : Fin P.n) : ℝ :=
  sInf (f '' P.cell i)

def cellUpper {a b : ℝ} (f : ℝ → ℝ) (P : Partition a b) (i : Fin P.n) : ℝ :=
  sSup (f '' P.cell i)

def lowerSum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ i : Fin P.n, cellLower f P i * P.weight α i

def upperSum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b) : ℝ :=
  ∑ i : Fin P.n, cellUpper f P i * P.weight α i

def lowerIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup (Set.range (lowerSum f α : Partition a b → ℝ))

def upperIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf (Set.range (upperSum f α : Partition a b → ℝ))

def RSIntegrable (f α : ℝ → ℝ) (a b : ℝ) : Prop :=
  a ≤ b ∧ BoundedOn f a b ∧ MonotoneOn α (Icc a b) ∧
    lowerIntegral f α a b = upperIntegral f α a b

/-- This totalized value is an integral only under `RSIntegrable`. -/
def RSIntegral (f α : ℝ → ℝ) (a b : ℝ) : ℝ := lowerIntegral f α a b

abbrev RIntegrable (f : ℝ → ℝ) (a b : ℝ) : Prop := RSIntegrable f id a b
abbrev RIntegral (f : ℝ → ℝ) (a b : ℝ) : ℝ := RSIntegral f id a b

def TaggedBy {a b : ℝ} (P : Partition a b) (tag : Fin P.n → ℝ) : Prop :=
  ∀ i, tag i ∈ P.cell i

def taggedSum {a b : ℝ} (f α : ℝ → ℝ) (P : Partition a b)
    (tag : Fin P.n → ℝ) : ℝ :=
  ∑ i : Fin P.n, f (tag i) * P.weight α i


theorem Partition.point_mem {a b : ℝ} (P : Partition a b) (i : Fin (P.n+1)) :
    P.point i ∈ Icc a b := by
  constructor
  · simpa only [P.left] using P.mono (Fin.zero_le i)
  · simpa only [P.right] using P.mono (Fin.le_last i)

theorem Partition.cell_order {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    P.point i.castSucc ≤ P.point i.succ := P.mono (by exact_mod_cast Nat.le_succ i.val)

theorem Partition.cell_subset {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    P.cell i ⊆ Icc a b := by
  intro x hx
  exact ⟨(P.point_mem i.castSucc).1.trans hx.1, hx.2.trans (P.point_mem i.succ).2⟩

theorem Partition.cell_nonempty {a b : ℝ} (P : Partition a b) (i : Fin P.n) :
    (P.cell i).Nonempty := ⟨P.point i.castSucc, le_rfl, P.cell_order i⟩

theorem Partition.weight_nonneg {a b : ℝ} (P : Partition a b) (α : ℝ → ℝ)
    (hα : MonotoneOn α (Icc a b)) (i : Fin P.n) : 0 ≤ P.weight α i := by
  exact sub_nonneg.mpr (hα (P.point_mem _) (P.point_mem _) (P.cell_order i))

theorem Partition.sum_weights {a b : ℝ} (P : Partition a b) (α : ℝ → ℝ) :
    ∑ i : Fin P.n, P.weight α i = α b - α a := by
  simp only [Partition.weight, Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_castSucc (fun i : Fin (P.n + 1) => α (P.point i))
  have h₂ := Fin.sum_univ_succ (fun i : Fin (P.n + 1) => α (P.point i))
  rw [P.left] at h₂
  rw [P.right] at h₁
  linarith

def Partition.single {a b : ℝ} (hab : a ≤ b) : Partition a b where
  n := 1
  point := ![a,b]
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  left := rfl
  right := rfl

theorem Partition.nonempty {a b : ℝ} (hab : a ≤ b) : Nonempty (Partition a b) :=
  ⟨Partition.single hab⟩

theorem BoundedOn.bddAbove_image {a b : ℝ} {f : ℝ → ℝ} (hf : BoundedOn f a b)
    {s : Set ℝ} (hs : s ⊆ Icc a b) : BddAbove (f '' s) := by
  rcases hf with ⟨M,hM⟩
  exact ⟨M, by rintro y ⟨x,hx,rfl⟩; exact (le_abs_self _).trans (hM x (hs hx))⟩

theorem BoundedOn.bddBelow_image {a b : ℝ} {f : ℝ → ℝ} (hf : BoundedOn f a b)
    {s : Set ℝ} (hs : s ⊆ Icc a b) : BddBelow (f '' s) := by
  rcases hf with ⟨M,hM⟩
  refine ⟨-M, ?_⟩
  rintro y ⟨x,hx,rfl⟩
  exact (abs_le.mp (hM x (hs hx))).1

theorem cellLower_le_value {a b : ℝ} {f : ℝ → ℝ} (hf : BoundedOn f a b)
    (P : Partition a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ P.cell i) :
    cellLower f P i ≤ f x :=
  csInf_le (hf.bddBelow_image (P.cell_subset i)) ⟨x,hx,rfl⟩

theorem value_le_cellUpper {a b : ℝ} {f : ℝ → ℝ} (hf : BoundedOn f a b)
    (P : Partition a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ P.cell i) :
    f x ≤ cellUpper f P i :=
  le_csSup (hf.bddAbove_image (P.cell_subset i)) ⟨x,hx,rfl⟩

theorem cellLower_le_cellUpper {a b : ℝ} {f : ℝ → ℝ} (hf : BoundedOn f a b)
    (P : Partition a b) (i : Fin P.n) : cellLower f P i ≤ cellUpper f P i := by
  obtain ⟨x,hx⟩ := P.cell_nonempty i
  exact (cellLower_le_value hf P i hx).trans (value_le_cellUpper hf P i hx)

theorem lowerSum_le_upperSum {a b : ℝ} {f α : ℝ → ℝ} (hf : BoundedOn f a b)
    (hα : MonotoneOn α (Icc a b)) (P : Partition a b) :
    lowerSum f α P ≤ upperSum f α P := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
    (cellLower_le_cellUpper hf P i) (P.weight_nonneg α hα i))



theorem lowerSum_lower_bound {a b m : ℝ} {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (hm : ∀ x ∈ Icc a b, m ≤ f x)
    (P : Partition a b) : m * (α b - α a) ≤ lowerSum f α P := by
  rw [← P.sum_weights α, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (P.weight_nonneg α hα i)
  exact le_csInf ((P.cell_nonempty i).image f) (by
    rintro y ⟨x,hx,rfl⟩
    exact hm x (P.cell_subset i hx))

theorem upperSum_upper_bound {a b M : ℝ} {f α : ℝ → ℝ}
    (hα : MonotoneOn α (Icc a b)) (hM : ∀ x ∈ Icc a b, f x ≤ M)
    (P : Partition a b) : upperSum f α P ≤ M * (α b - α a) := by
  rw [← P.sum_weights α, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (P.weight_nonneg α hα i)
  exact csSup_le ((P.cell_nonempty i).image f) (by
    rintro y ⟨x,hx,rfl⟩
    exact hM x (P.cell_subset i hx))

theorem darbouxsums_bounds {a b m M : ℝ} {f α : ℝ → ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hm : ∀ x ∈ Icc a b, m ≤ f x) (hM : ∀ x ∈ Icc a b, f x ≤ M)
    (P : Partition a b) :
    m * (α b - α a) ≤ lowerSum f α P ∧ lowerSum f α P ≤ upperSum f α P ∧
      upperSum f α P ≤ M * (α b - α a) :=
  ⟨lowerSum_lower_bound hα hm P, lowerSum_le_upperSum hf hα P,
    upperSum_upper_bound hα hM P⟩

theorem sums_bounded {a b : ℝ} {f α : ℝ → ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    BddAbove (range (lowerSum f α : Partition a b → ℝ)) ∧
    BddBelow (range (lowerSum f α : Partition a b → ℝ)) ∧
    BddAbove (range (upperSum f α : Partition a b → ℝ)) ∧
    BddBelow (range (upperSum f α : Partition a b → ℝ)) := by
  obtain ⟨M,hM⟩ := hf
  have hh (P : Partition a b) := darbouxsums_bounds ⟨M,hM⟩ hα
    (fun x hx => (abs_le.mp (hM x hx)).1) (fun x hx => (abs_le.mp (hM x hx)).2) P
  refine ⟨⟨M*(α b-α a), ?_⟩, ⟨-M*(α b-α a), ?_⟩,
    ⟨M*(α b-α a), ?_⟩, ⟨-M*(α b-α a), ?_⟩⟩
  · rintro y ⟨P,rfl⟩; exact (hh P).2.1.trans (hh P).2.2
  · rintro y ⟨P,rfl⟩; exact (hh P).1
  · rintro y ⟨P,rfl⟩; exact (hh P).2.2
  · rintro y ⟨P,rfl⟩; exact (hh P).1.trans (hh P).2.1

theorem lowerSum_le_lowerIntegral {a b : ℝ} {f α : ℝ → ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) (P : Partition a b) :
    lowerSum f α P ≤ lowerIntegral f α a b :=
  le_csSup (sums_bounded hf hα).1 ⟨P,rfl⟩

theorem upperIntegral_le_upperSum {a b : ℝ} {f α : ℝ → ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) (P : Partition a b) :
    upperIntegral f α a b ≤ upperSum f α P :=
  csInf_le (sums_bounded hf hα).2.2.2 ⟨P,rfl⟩

theorem darboux_integrals_bounds {a b m M : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hm : ∀ x ∈ Icc a b, m ≤ f x) (hM : ∀ x ∈ Icc a b, f x ≤ M) :
    m * (α b - α a) ≤ lowerIntegral f α a b ∧ lowerIntegral f α a b ≤ M * (α b - α a) ∧
    m * (α b - α a) ≤ upperIntegral f α a b ∧ upperIntegral f α a b ≤ M * (α b - α a) := by
  let P := Partition.single hab
  have hlo := lowerSum_lower_bound hα hm P
  have hup := upperSum_upper_bound hα hM P
  refine ⟨hlo.trans (lowerSum_le_lowerIntegral hf hα P), ?_, ?_,
    (upperIntegral_le_upperSum hf hα P).trans hup⟩
  · exact csSup_le ⟨lowerSum f α P, P, rfl⟩ (by
      rintro y ⟨Q,rfl⟩
      exact (lowerSum_le_upperSum hf hα Q).trans (upperSum_upper_bound hα hM Q))
  · exact le_csInf ⟨upperSum f α P, P, rfl⟩ (by
      rintro y ⟨Q,rfl⟩
      exact (lowerSum_lower_bound hα hm Q).trans (lowerSum_le_upperSum hf hα Q))

end Rudin.PMA.Chapter06
