import Rudin.PMA.Chapter06.Basic

noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Rudin.PMA.Chapter06


/-! ### PMA-6.1: Ordinary closed-cell Darboux definitions and finite bounds. -/

def pma6_1_contract : Prop :=
  ∀ (f : ℝ → ℝ) (a b m M : ℝ), a ≤ b → BoundedOn f a b →
    (∀ x ∈ Icc a b, m ≤ f x) → (∀ x ∈ Icc a b, f x ≤ M) →
    (∀ P : Partition a b,
      m*(b-a) ≤ lowerSum f id P ∧ lowerSum f id P ≤ upperSum f id P ∧
        upperSum f id P ≤ M*(b-a)) ∧
    (m*(b-a) ≤ lowerIntegral f id a b ∧ lowerIntegral f id a b ≤ M*(b-a) ∧
      m*(b-a) ≤ upperIntegral f id a b ∧ upperIntegral f id a b ≤ M*(b-a)) ∧
    (RIntegrable f a b ↔ lowerIntegral f id a b = upperIntegral f id a b) ∧
    (RIntegrable f a b → RIntegral f a b = lowerIntegral f id a b ∧
      RIntegral f a b = upperIntegral f id a b)

/-! ### PMA-6.2: Weighted Darboux definitions and ordinary specialization. -/

def pma6_2_contract : Prop :=
  ∀ (f α : ℝ → ℝ) (a b m M : ℝ), a ≤ b → BoundedOn f a b →
    MonotoneOn α (Icc a b) →
    (∀ x ∈ Icc a b, m ≤ f x) → (∀ x ∈ Icc a b, f x ≤ M) →
    (∀ P : Partition a b, (∀ i, 0 ≤ P.weight α i) ∧
      m*(α b-α a) ≤ lowerSum f α P ∧ lowerSum f α P ≤ upperSum f α P ∧
        upperSum f α P ≤ M*(α b-α a)) ∧
    (m*(α b-α a) ≤ lowerIntegral f α a b ∧ lowerIntegral f α a b ≤ M*(α b-α a) ∧
      m*(α b-α a) ≤ upperIntegral f α a b ∧ upperIntegral f α a b ≤ M*(α b-α a)) ∧
    (RSIntegrable f α a b ↔ lowerIntegral f α a b = upperIntegral f α a b) ∧
    (RSIntegrable f α a b → RSIntegral f α a b = lowerIntegral f α a b ∧
      RSIntegral f α a b = upperIntegral f α a b) ∧
    (RSIntegrable f id a b ↔ RIntegrable f a b) ∧
    RSIntegral f id a b = RIntegral f a b


theorem pma6_1 : pma6_1_contract := by
  intro f a b m M hab hf hm hM
  have hi : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
  refine ⟨fun P => darbouxsums_bounds hf hi hm hM P,
    darboux_integrals_bounds hab hf hi hm hM, ?_, ?_⟩
  · exact ⟨fun h => h.2.2.2, fun h => ⟨hab,hf,hi,h⟩⟩
  · intro h
    exact ⟨rfl,h.2.2.2⟩

theorem pma6_2 : pma6_2_contract := by
  intro f α a b m M hab hf hα hm hM
  refine ⟨fun P => ⟨P.weight_nonneg α hα, darbouxsums_bounds hf hα hm hM P⟩,
    darboux_integrals_bounds hab hf hα hm hM, ?_, ?_, Iff.rfl, rfl⟩
  · exact ⟨fun h => h.2.2.2, fun h => ⟨hab,hf,hα,h⟩⟩
  · intro h
    exact ⟨rfl,h.2.2.2⟩

theorem rsIntegral_const {a b c : ℝ} {α : ℝ → ℝ} (hab : a ≤ b)
    (hα : MonotoneOn α (Icc a b)) :
    RSIntegrable (fun _ => c) α a b ∧ RSIntegral (fun _ => c) α a b = c*(α b-α a) := by
  have hf : BoundedOn (fun _ => c) a b := ⟨|c|, fun _ _ => le_rfl⟩
  have h := darboux_integrals_bounds hab hf hα (m:=c) (M:=c)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have hl := le_antisymm h.2.1 h.1
  have hu := le_antisymm h.2.2.2 h.2.2.1
  exact ⟨⟨hab,hf,hα,hl.trans hu.symm⟩,hl⟩

theorem rsIntegral_const_integrator {a b c : ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hf : BoundedOn f a b) :
    RSIntegrable f (fun _ => c) a b ∧ RSIntegral f (fun _ => c) a b = 0 := by
  obtain ⟨M,hM⟩ := hf
  have hα : MonotoneOn (fun _ : ℝ => c) (Icc a b) := fun _ _ _ _ _ => le_rfl
  have h := darboux_integrals_bounds hab ⟨M,hM⟩ hα
    (fun x hx => (abs_le.mp (hM x hx)).1) (fun x hx => (abs_le.mp (hM x hx)).2)
  simp only [sub_self,mul_zero] at h
  have hl := le_antisymm h.2.1 h.1
  have hu := le_antisymm h.2.2.2 h.2.2.1
  exact ⟨⟨hab,⟨M,hM⟩,hα,hl.trans hu.symm⟩,hl⟩

theorem rsIntegral_same_endpoint (f α : ℝ → ℝ) (a : ℝ) :
    RSIntegrable f α a a ∧ RSIntegral f α a a = 0 := by
  have hf : BoundedOn f a a := by
    refine ⟨|f a|, ?_⟩
    intro x hx
    have hx' : x = a := le_antisymm hx.2 hx.1
    simp [hx']
  have hα : MonotoneOn α (Icc a a) := by
    intro x hx y hy hxy
    have hx' : x = a := le_antisymm hx.2 hx.1
    have hy' : y = a := le_antisymm hy.2 hy.1
    simp [hx',hy']
  obtain ⟨M,hM⟩ := hf
  have h := darboux_integrals_bounds le_rfl ⟨M,hM⟩ hα
    (fun x hx => (abs_le.mp (hM x hx)).1) (fun x hx => (abs_le.mp (hM x hx)).2)
  simp only [sub_self,mul_zero] at h
  have hl := le_antisymm h.2.1 h.1
  have hu := le_antisymm h.2.2.2 h.2.2.1
  exact ⟨⟨le_rfl,⟨M,hM⟩,hα,hl.trans hu.symm⟩,hl⟩

end Rudin.PMA.Chapter06
