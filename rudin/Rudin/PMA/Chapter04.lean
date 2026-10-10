import Mathlib
import Rudin.PMA.Chapter03

noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter Topology

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 4: Continuity

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

namespace Rudin.PMA.Chapter04

/-! ### PMA-4.1: Punctured function limits -/
def FunctionLimitOn {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) (p : X) (q : Y) : Prop :=
  Chapter02.IsLimitPoint p E ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, 0 < dist x p → dist x p < δ → dist (f x) q < ε


def pma4_1_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X) (q : Y), Chapter02.IsLimitPoint p E →
    (FunctionLimitOn E f p q ↔ Tendsto f (𝓝[E \ {p}] p) (𝓝 q))

theorem functionLimitPoint_iff_neBot {X : Type*} [MetricSpace X] (E : Set X) (p : X) :
    Chapter02.IsLimitPoint p E ↔ (𝓝[E \ {p}] p).NeBot := by
  rw [Chapter02.isLimitPoint_iff_accPt, accPt_principal_iff_clusterPt]
  rfl

theorem functionLimitOn_iff_tendsto {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) (p : X) (q : Y) (hp : Chapter02.IsLimitPoint p E) :
    FunctionLimitOn E f p q ↔ Tendsto f (𝓝[E \ {p}] p) (𝓝 q) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hd⟩ := h.2 ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx hxp
    exact hd x hx.1 (dist_pos.mpr (by simpa using hx.2)) hxp
  · intro h
    refine ⟨hp, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx hpos hxp
    exact hd ⟨hx, by simpa using (dist_pos.mp hpos)⟩ hxp

theorem pma4_1 : pma4_1_contract := by
  intro X Y _ _ E f p q hp
  exact functionLimitOn_iff_tendsto E f p q hp

end Rudin.PMA.Chapter04
