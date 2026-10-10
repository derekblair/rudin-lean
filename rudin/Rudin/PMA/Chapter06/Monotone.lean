import Rudin.PMA.Chapter06.Integrability

noncomputable section
open Set
open scoped BigOperators
namespace Rudin.PMA.Chapter06

theorem monotoneOn_boundedOn {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) : BoundedOn f a b := by
  refine ⟨max |f a| |f b|, ?_⟩
  intro x hx
  apply abs_le.mpr
  constructor
  · exact (neg_le_neg (le_max_left _ _)).trans
      ((neg_abs_le _).trans (hf ⟨le_rfl,hab⟩ hx hx.1))
  · exact (hf hx ⟨hab,le_rfl⟩ hx.2).trans
      ((le_abs_self _).trans (le_max_right _ _))

theorem cellLower_of_monotone {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (Icc a b)) (P : Partition a b) (i : Fin P.n) :
    cellLower f P i = f (P.point i.castSucc) := by
  have hab := (P.point_mem 0).1.trans (P.point_mem 0).2
  have hbounded := monotoneOn_boundedOn hab hf
  apply le_antisymm
  · exact cellLower_le_value hbounded P i ⟨le_rfl,P.cell_order i⟩
  · exact le_csInf ((P.cell_nonempty i).image f) (by
      rintro y ⟨x,hx,rfl⟩
      exact hf (P.point_mem _) (P.cell_subset i hx) hx.1)

theorem cellUpper_of_monotone {f : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (Icc a b)) (P : Partition a b) (i : Fin P.n) :
    cellUpper f P i = f (P.point i.succ) := by
  have hab := (P.point_mem 0).1.trans (P.point_mem 0).2
  have hbounded := monotoneOn_boundedOn hab hf
  apply le_antisymm
  · exact csSup_le ((P.cell_nonempty i).image f) (by
      rintro y ⟨x,hx,rfl⟩
      exact hf (P.cell_subset i hx) (P.point_mem _) hx.2)
  · exact value_le_cellUpper hbounded P i ⟨P.cell_order i,le_rfl⟩

theorem gap_swap_monotone {f α : ℝ → ℝ} {a b : ℝ}
    (hf : MonotoneOn f (Icc a b)) (hα : MonotoneOn α (Icc a b)) (P : Partition a b) :
    upperSum f α P - lowerSum f α P = upperSum α f P - lowerSum α f P := by
  simp only [upperSum,lowerSum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [cellLower_of_monotone hf,cellUpper_of_monotone hf,
    cellLower_of_monotone hα,cellUpper_of_monotone hα]
  dsimp only [Partition.weight]
  ring

theorem rsIntegrable_monotone {f α : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MonotoneOn f (Icc a b)) (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousOn α (Icc a b)) : RSIntegrable f α a b := by
  have hs := rsIntegrable_of_continuousOn hab hc hf
  apply (rsIntegrable_iff_gap hab (monotoneOn_boundedOn hab hf) hα).mpr
  intro ε hε
  obtain ⟨P,hP⟩ := (rsIntegrable_iff_gap hab hs.2.1 hf).mp hs ε hε
  exact ⟨P, by rwa [gap_swap_monotone hf hα]⟩

theorem rsIntegrable_antitone {f α : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : AntitoneOn f (Icc a b)) (hα : MonotoneOn α (Icc a b))
    (hc : ContinuousOn α (Icc a b)) : RSIntegrable f α a b := by
  have hg : MonotoneOn (fun x => -f x) (Icc a b) :=
    fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  have h := rsIntegrable_monotone hab hg hα hc
  have hn := (rsIntegrable_const_mul h (-1)).1
  simpa using hn

theorem pma6_9 : pma6_9_contract := by
  intro f α a b hab hf hα hc
  rcases hf with hf | hf
  · exact rsIntegrable_monotone hab hf hα hc
  · exact rsIntegrable_antitone hab hf hα hc

end Rudin.PMA.Chapter06
