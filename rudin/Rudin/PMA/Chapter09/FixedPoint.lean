import Rudin.PMA.Chapter01

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped NNReal

namespace Rudin.PMA.Chapter09

/-- Rudin's contraction inequality, retaining the source's real constant.
A negative constant is harmless on a singleton; normalization is proved below. -/
def IsContraction {X : Type*} [MetricSpace X] (f : X → X) : Prop :=
  ∃ c : ℝ, c < 1 ∧ ∀ x y : X, dist (f x) (f y) ≤ c * dist x y

def pma9_22_contract : Prop :=
  ∀ (X : Type*) [MetricSpace X] (f : X → X),
    (IsContraction f ↔ ∃ c : ℝ≥0, ContractingWith c f) ∧
    (IsContraction f → Continuous f)

/-- The nonempty hypothesis is explicit: an empty complete metric space has no
fixed point. This is the necessary nonempty reading of the source statement. -/
def pma9_23_contract : Prop :=
  ∀ (X : Type*) [MetricSpace X] [CompleteSpace X] [Nonempty X] (f : X → X),
    IsContraction f → ∃ p : X, f p = p ∧ (∀ q : X, f q = q → q = p) ∧
      ∀ x : X, Tendsto (fun n : ℕ => f^[n] x) atTop (𝓝 p)

theorem isContraction_iff {X : Type*} [MetricSpace X] (f : X → X) :
    IsContraction f ↔ ∃ c : ℝ≥0, ContractingWith c f := by
  constructor
  · rintro ⟨c, hc, hdist⟩
    refine ⟨⟨max c 0, le_max_right c 0⟩, ?_, ?_⟩
    · exact_mod_cast max_lt hc zero_lt_one
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      exact (hdist x y).trans (mul_le_mul_of_nonneg_right (le_max_left c 0) dist_nonneg)
  · rintro ⟨c, hc⟩
    exact ⟨c, by exact_mod_cast hc.1, hc.dist_le_mul⟩

theorem pma9_22 : pma9_22_contract := by
  intro X _ f
  refine ⟨isContraction_iff f, ?_⟩
  intro hf
  obtain ⟨c, hc⟩ := (isContraction_iff f).mp hf
  exact hc.toLipschitzWith.continuous

theorem pma9_23 : pma9_23_contract := by
  intro X _ _ _ f hf
  obtain ⟨c, hc⟩ := (isContraction_iff f).mp hf
  exact ⟨hc.fixedPoint f, hc.fixedPoint_isFixedPt,
    fun _ hq => hc.fixedPoint_unique hq, hc.tendsto_iterate_fixedPoint⟩

end Rudin.PMA.Chapter09
