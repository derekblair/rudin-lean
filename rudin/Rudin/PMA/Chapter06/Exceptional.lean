import Rudin.PMA.Chapter06.Integrability
import Rudin.PMA.Chapter06.Split
import Rudin.PMA.Chapter06.Definitions
import Rudin.PMA.Chapter06.Jump
import Rudin.PMA.Chapter06.Endpoint

noncomputable section
open Set
open scoped Topology
namespace Rudin.PMA.Chapter06

/-- A finite-exception induction. Its base is supplied by the separately proved
trimmed-interval theorem, never assumed by the completed source theorem. -/
theorem finite_exceptional_open_of_base {f α : ℝ → ℝ}
    (base : ∀ (a b : ℝ), a < b → BoundedOn f a b → MonotoneOn α (Icc a b) →
      ContinuousOn f (Ioo a b) →
      (ContinuousWithinAt f (Icc a b) a ∨ ContinuousWithinAt α (Icc a b) a) →
      (ContinuousWithinAt f (Icc a b) b ∨ ContinuousWithinAt α (Icc a b) b) →
      RSIntegrable f α a b)
    (E : Finset ℝ) :
    ∀ (a b : ℝ), a < b → BoundedOn f a b → MonotoneOn α (Icc a b) →
      (∀ x ∈ Ioo a b, x ∉ E → ContinuousAt f x) →
      (∀ x ∈ Ioo a b, x ∈ E → ContinuousAt α x) →
      (ContinuousWithinAt f (Icc a b) a ∨ ContinuousWithinAt α (Icc a b) a) →
      (ContinuousWithinAt f (Icc a b) b ∨ ContinuousWithinAt α (Icc a b) b) →
      RSIntegrable f α a b := by
  classical
  induction E using Finset.induction_on with
  | empty =>
      intro a b hab hf hα hc hE ha hb
      exact base a b hab hf hα (fun x hx => (hc x hx (by simp)).continuousWithinAt) ha hb
  | @insert p E hp ih =>
      intro a b hab hf hα hc hE ha hb
      by_cases hpi : p ∈ Ioo a b
      · have hαp : ContinuousAt α p := hE p hpi (by simp)
        have hleft : RSIntegrable f α a p := by
          apply ih a p hpi.1 (split_bounded_left hf hpi.2.le)
            (hα.mono (Icc_subset_Icc_right hpi.2.le))
          · intro x hx hxE
            apply hc x ⟨hx.1,hx.2.trans hpi.2⟩
            simp only [Finset.mem_insert, not_or]
            exact ⟨ne_of_lt hx.2,hxE⟩
          · intro x hx hxE
            exact hE x ⟨hx.1,hx.2.trans hpi.2⟩ (by simp [hxE])
          · exact ha.imp
              (fun h => h.mono (Icc_subset_Icc_right hpi.2.le))
              (fun h => h.mono (Icc_subset_Icc_right hpi.2.le))
          · exact Or.inr hαp.continuousWithinAt
        have hright : RSIntegrable f α p b := by
          apply ih p b hpi.2 (split_bounded_right hf hpi.1.le)
            (hα.mono (Icc_subset_Icc_left hpi.1.le))
          · intro x hx hxE
            apply hc x ⟨hpi.1.trans hx.1,hx.2⟩
            simp only [Finset.mem_insert, not_or]
            exact ⟨ne_of_gt hx.1,hxE⟩
          · intro x hx hxE
            exact hE x ⟨hpi.1.trans hx.1,hx.2⟩ (by simp [hxE])
          · exact Or.inr hαp.continuousWithinAt
          · exact hb.imp
              (fun h => h.mono (Icc_subset_Icc_left hpi.1.le))
              (fun h => h.mono (Icc_subset_Icc_left hpi.1.le))
        exact split_rsIntegrable_append hleft hright
      · apply ih a b hab hf hα
        · intro x hx hxE
          apply hc x hx
          simp only [Finset.mem_insert, not_or]
          exact ⟨fun hxp => hpi (hxp ▸ hx),hxE⟩
        · intro x hx hxE
          exact hE x hx (by simp [hxE])
        · exact ha
        · exact hb

/-- Source continuity hypotheses reduce to the finite-exception induction. -/
theorem rsIntegrable_finite_discontinuities_of_base {f α : ℝ → ℝ}
    (base : ∀ (a b : ℝ), a < b → BoundedOn f a b → MonotoneOn α (Icc a b) →
      ContinuousOn f (Ioo a b) →
      (ContinuousWithinAt f (Icc a b) a ∨ ContinuousWithinAt α (Icc a b) a) →
      (ContinuousWithinAt f (Icc a b) b ∨ ContinuousWithinAt α (Icc a b) b) →
      RSIntegrable f α a b)
    {a b : ℝ} (hab : a ≤ b) (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b))
    (hfinite : {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x}.Finite)
    (hαc : ∀ x ∈ Icc a b, ¬ ContinuousWithinAt f (Icc a b) x →
      ContinuousWithinAt α (Icc a b) x) : RSIntegrable f α a b := by
  classical
  rcases hab.eq_or_lt with rfl | hab
  · exact (rsIntegral_same_endpoint f α a).1
  · let E := hfinite.toFinset
    apply finite_exceptional_open_of_base base E a b hab hf hα
    · intro x hx hxE
      have hnot : ¬ (x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x) := by
        simpa [E] using hxE
      have hc : ContinuousWithinAt f (Icc a b) x := by
        by_contra hn
        exact hnot ⟨⟨hx.1.le,hx.2.le⟩,hn⟩
      exact hc.continuousAt (Icc_mem_nhds hx.1 hx.2)
    · intro x hx hxE
      have hbad : x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x := by
        simpa [E] using hxE
      exact (hαc x hbad.1 hbad.2).continuousAt (Icc_mem_nhds hx.1 hx.2)
    · by_cases h : ContinuousWithinAt f (Icc a b) a
      · exact Or.inl h
      · exact Or.inr (hαc a ⟨le_rfl,hab.le⟩ h)
    · by_cases h : ContinuousWithinAt f (Icc a b) b
      · exact Or.inl h
      · exact Or.inr (hαc b ⟨hab.le,le_rfl⟩ h)


/-! ### PMA-6.10: Finitely many discontinuities, with the shared-jump caution. -/

theorem pma6_10 : pma6_10_contract := by
  constructor
  · intro f α a b hab hf hα hfinite hαc
    exact rsIntegrable_finite_discontinuities_of_base
      (fun a b hab hf hα hc ha hb =>
        rsIntegrable_of_continuousOn_Ioo hab hf hα hc ha hb)
      hab hf hα hfinite hαc
  · exact unitStep_source_caution.2

end Rudin.PMA.Chapter06
