import Rudin.PMA.Chapter06.Basic
import Rudin.PMA.Chapter06.Refinement

noncomputable section
open Set
open scoped BigOperators

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.5: Comparison of the lower and upper integrals -/

theorem lowerSum_le_upperSum_other {a b : ℝ} {f α : ℝ → ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) (P Q : Partition a b) :
    lowerSum f α P ≤ upperSum f α Q := by
  obtain ⟨R, _, hRP, hRQ⟩ := pma6_3_common_refinement P Q
  exact (pma6_4_lower P R hRP hf hα).trans
    ((lowerSum_le_upperSum hf hα R).trans (pma6_4_upper Q R hRQ hf hα))

theorem pma6_5 {a b : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    lowerIntegral f α a b ≤ upperIntegral f α a b := by
  change sSup (range (lowerSum f α : Partition a b → ℝ)) ≤
    sInf (range (upperSum f α : Partition a b → ℝ))
  have hU : (range (upperSum f α : Partition a b → ℝ)).Nonempty :=
    ⟨upperSum f α (Partition.single hab), Partition.single hab, rfl⟩
  have hL : (range (lowerSum f α : Partition a b → ℝ)).Nonempty :=
    ⟨lowerSum f α (Partition.single hab), Partition.single hab, rfl⟩
  apply le_csInf hU
  rintro _ ⟨Q, rfl⟩
  apply csSup_le hL
  rintro _ ⟨P, rfl⟩
  exact lowerSum_le_upperSum_other hf hα P Q

/-! ### PMA-6.6: The Darboux integrability criterion -/

theorem rsIntegrable_iff_gap {a b : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    RSIntegrable f α a b ↔
      ∀ ε : ℝ, 0 < ε → ∃ P : Partition a b, upperSum f α P - lowerSum f α P < ε := by
  constructor
  · intro h ε hε
    have hL : (range (lowerSum f α : Partition a b → ℝ)).Nonempty :=
      ⟨lowerSum f α (Partition.single hab), Partition.single hab, rfl⟩
    have hU : (range (upperSum f α : Partition a b → ℝ)).Nonempty :=
      ⟨upperSum f α (Partition.single hab), Partition.single hab, rfl⟩
    obtain ⟨_, ⟨P, rfl⟩, hP⟩ := exists_lt_of_lt_csSup hL
      (show lowerIntegral f α a b - ε / 2 < lowerIntegral f α a b by linarith)
    obtain ⟨_, ⟨Q, rfl⟩, hQ⟩ := exists_lt_of_csInf_lt hU
      (show upperIntegral f α a b < upperIntegral f α a b + ε / 2 by linarith)
    obtain ⟨R, _, hRP, hRQ⟩ := pma6_3_common_refinement P Q
    refine ⟨R, ?_⟩
    have h₁ := pma6_4_lower P R hRP hf hα
    have h₂ := pma6_4_upper Q R hRQ hf hα
    have heq := h.2.2.2
    linarith
  · intro h
    refine ⟨hab, hf, hα, le_antisymm (pma6_5 hab hf hα) ?_⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨P, hP⟩ := h ε hε
    have hL := lowerSum_le_lowerIntegral hf hα P
    have hU := upperIntegral_le_upperSum hf hα P
    linarith

theorem pma6_6 {a b : ℝ} {f α : ℝ → ℝ}
    (hab : a ≤ b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) :
    RSIntegrable f α a b ↔
      ∀ ε : ℝ, 0 < ε → ∃ P : Partition a b, upperSum f α P - lowerSum f α P < ε :=
  rsIntegrable_iff_gap hab hf hα

/-! ### PMA-6.7: Refinement and tagged-sum estimates -/

theorem taggedSum_bounds {a b : ℝ} {f α : ℝ → ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (P : Partition a b) {tag : Fin P.n → ℝ} (htag : TaggedBy P tag) :
    lowerSum f α P ≤ taggedSum f α P tag ∧
      taggedSum f α P tag ≤ upperSum f α P := by
  constructor
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (cellLower_le_value hf P i (htag i)) (P.weight_nonneg α hα i))
  · exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
      (value_le_cellUpper hf P i (htag i)) (P.weight_nonneg α hα i))

theorem rsIntegral_bounds {a b : ℝ} {f α : ℝ → ℝ}
    (h : RSIntegrable f α a b) (P : Partition a b) :
    lowerSum f α P ≤ RSIntegral f α a b ∧ RSIntegral f α a b ≤ upperSum f α P := by
  refine ⟨lowerSum_le_lowerIntegral h.2.1 h.2.2.1 P, ?_⟩
  change lowerIntegral f α a b ≤ upperSum f α P
  rw [h.2.2.2]
  exact upperIntegral_le_upperSum h.2.1 h.2.2.1 P

theorem pma6_7_refinement_gap {a b ε : ℝ} {f α : ℝ → ℝ}
    (P Q : Partition a b) (hQP : Q.Refines P)
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hgap : upperSum f α P - lowerSum f α P < ε) :
    upperSum f α Q - lowerSum f α Q < ε := by
  have h := pma6_4 P Q hQP hf hα
  linarith [h.1, h.2]

theorem two_tags_le_gap {a b : ℝ} {f α : ℝ → ℝ}
    (P : Partition a b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    {s t : Fin P.n → ℝ} (hs : TaggedBy P s) (ht : TaggedBy P t) :
    (∑ i : Fin P.n, |f (s i) - f (t i)| * P.weight α i) ≤
      upperSum f α P - lowerSum f α P := by
  rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hsL := cellLower_le_value hf P i (hs i)
  have htL := cellLower_le_value hf P i (ht i)
  have hsU := value_le_cellUpper hf P i (hs i)
  have htU := value_le_cellUpper hf P i (ht i)
  have hdiff : |f (s i) - f (t i)| ≤ cellUpper f P i - cellLower f P i :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  simpa only [sub_mul] using mul_le_mul_of_nonneg_right hdiff (P.weight_nonneg α hα i)

theorem taggedSum_sub_integral_le_gap {a b : ℝ} {f α : ℝ → ℝ}
    (h : RSIntegrable f α a b) (P : Partition a b)
    {tag : Fin P.n → ℝ} (htag : TaggedBy P tag) :
    |taggedSum f α P tag - RSIntegral f α a b| ≤
      upperSum f α P - lowerSum f α P := by
  have htagbounds := taggedSum_bounds h.2.1 h.2.2.1 P htag
  have hIbounds := rsIntegral_bounds h P
  apply abs_le.mpr
  constructor <;> linarith [htagbounds.1, htagbounds.2, hIbounds.1, hIbounds.2]

theorem pma6_7 {a b ε : ℝ} {f α : ℝ → ℝ}
    (P : Partition a b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hgap : upperSum f α P - lowerSum f α P < ε) :
    (∀ Q : Partition a b, Q.Refines P → upperSum f α Q - lowerSum f α Q < ε) ∧
    (∀ s t : Fin P.n → ℝ, TaggedBy P s → TaggedBy P t →
      (∑ i : Fin P.n, |f (s i) - f (t i)| * P.weight α i) < ε) ∧
    (RSIntegrable f α a b → ∀ tag : Fin P.n → ℝ, TaggedBy P tag →
      |taggedSum f α P tag - RSIntegral f α a b| < ε) := by
  refine ⟨fun Q hQP => pma6_7_refinement_gap P Q hQP hf hα hgap, ?_, ?_⟩
  · intro s t hs ht
    exact (two_tags_le_gap P hf hα hs ht).trans_lt hgap
  · intro h tag htag
    exact (taggedSum_sub_integral_le_gap h P htag).trans_lt hgap

end Rudin.PMA.Chapter06
