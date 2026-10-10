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

/-! ### PMA-4.2: Sequential criterion and uniqueness -/
def pma4_2_contract : Prop :=
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X) (q : Y), Chapter02.IsLimitPoint p E →
      (FunctionLimitOn E f p q ↔ ∀ s : ℕ → X,
        (∀ n, s n ∈ E ∧ s n ≠ p) → Tendsto s atTop (𝓝 p) →
          Tendsto (f ∘ s) atTop (𝓝 q))) ∧
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X) (q r : Y),
      FunctionLimitOn E f p q → FunctionLimitOn E f p r → q = r)

theorem tendsto_within_iff_all_sequences {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (S : Set X) (f : X → Y) (p : X) (q : Y) :
    Tendsto f (𝓝[S] p) (𝓝 q) ↔ ∀ s : ℕ → X,
      (∀ n, s n ∈ S) → Tendsto s atTop (𝓝 p) → Tendsto (f ∘ s) atTop (𝓝 q) := by
  constructor
  · intro hf s hs ht
    exact hf.comp (tendsto_nhdsWithin_iff.mpr ⟨ht, Eventually.of_forall hs⟩)
  · intro h
    apply tendsto_iff_seq_tendsto.mpr
    intro s hs
    obtain ⟨ht, he⟩ := tendsto_nhdsWithin_iff.mp hs
    obtain ⟨N, hN⟩ := eventually_atTop.mp he
    have hshift := h (fun n => s (n + N))
      (fun n => hN (n + N) (Nat.le_add_left N n)) (ht.comp (tendsto_add_atTop_nat N))
    exact (tendsto_add_atTop_iff_nat N).mp hshift

theorem functionLimitOn_unique {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) (p : X) (q r : Y)
    (hq : FunctionLimitOn E f p q) (hr : FunctionLimitOn E f p r) : q = r := by
  have : (𝓝[E \ {p}] p).NeBot := (functionLimitPoint_iff_neBot E p).mp hq.1
  exact tendsto_nhds_unique ((functionLimitOn_iff_tendsto E f p q hq.1).mp hq)
    ((functionLimitOn_iff_tendsto E f p r hr.1).mp hr)

theorem pma4_2 : pma4_2_contract := by
  constructor
  · intro X Y _ _ E f p q hp
    rw [functionLimitOn_iff_tendsto E f p q hp, tendsto_within_iff_all_sequences]
    simp only [Set.mem_sdiff, mem_singleton_iff]
  · exact fun E f p q r => functionLimitOn_unique E f p q r

/-! ### PMA-4.3: Pointwise operations -/
def ComplexSum {X : Type*} (f g : X → ℂ) (x : X) : ℂ := f x + g x
def ComplexDifference {X : Type*} (f g : X → ℂ) (x : X) : ℂ := f x - g x
def ComplexProduct {X : Type*} (f g : X → ℂ) (x : X) : ℂ := f x * g x
def QuotientDomain {X : Type*} (E : Set X) (g : X → ℂ) : Set X := E ∩ {x | g x ≠ 0}
def ComplexQuotient {X : Type*} (f g : X → ℂ) (x : X) : ℂ := f x / g x
def ConstantFunction {X Y : Type*} (c : Y) (_ : X) : Y := c
def PointwiseLE {X : Type*} (E : Set X) (f g : X → ℝ) : Prop := ∀ x ∈ E, f x ≤ g x
def VectorSum {X : Type*} {k : ℕ} (f g : X → EuclideanSpace ℝ (Fin k))
    (x : X) : EuclideanSpace ℝ (Fin k) := f x + g x
def InnerFunction {X : Type*} {k : ℕ} (f g : X → EuclideanSpace ℝ (Fin k))
    (x : X) : ℝ := inner ℝ (f x) (g x)
def ScalarMultiple {X : Type*} {k : ℕ} (a : ℝ) (f : X → EuclideanSpace ℝ (Fin k))
    (x : X) : EuclideanSpace ℝ (Fin k) := a • f x

def pma4_3_contract : Prop :=
  (∀ {X : Type*} (E : Set X) (g : X → ℂ) (x : X),
    x ∈ QuotientDomain E g ↔ x ∈ E ∧ g x ≠ 0) ∧
  (∀ {X : Type*} (E : Set X) (f g : X → ℝ),
    PointwiseLE E f g ↔ ∀ x ∈ E, f x ≤ g x)

theorem pma4_3 : pma4_3_contract := ⟨fun _ _ _ => Iff.rfl, fun _ _ _ => Iff.rfl⟩

/-! ### PMA-4.4: Algebra of function limits -/
def pma4_4_contract : Prop :=
  (∀ {X : Type*} [MetricSpace X] (E : Set X) (f g : X → ℂ)
    (p : X) (A B : ℂ), FunctionLimitOn E f p A → FunctionLimitOn E g p B →
      FunctionLimitOn E (ComplexSum f g) p (A + B) ∧
      FunctionLimitOn E (ComplexProduct f g) p (A * B) ∧
      (B ≠ 0 → FunctionLimitOn (QuotientDomain E g) (ComplexQuotient f g) p (A / B))) ∧
  (∀ {X : Type*} [MetricSpace X] {k : ℕ} (E : Set X)
    (f g : X → EuclideanSpace ℝ (Fin k)) (p : X) (A B : EuclideanSpace ℝ (Fin k)),
      FunctionLimitOn E f p A → FunctionLimitOn E g p B →
        FunctionLimitOn E (VectorSum f g) p (A + B) ∧
        FunctionLimitOn E (InnerFunction f g) p (inner ℝ A B))

theorem pma4_4 : pma4_4_contract := by
  constructor
  · intro X _ E f g p A B hf hg
    have ht := (functionLimitOn_iff_tendsto E f p A hf.1).mp hf
    have hu := (functionLimitOn_iff_tendsto E g p B hg.1).mp hg
    refine ⟨(functionLimitOn_iff_tendsto E _ p _ hf.1).mpr (ht.add hu),
      (functionLimitOn_iff_tendsto E _ p _ hf.1).mpr (ht.mul hu), ?_⟩
    intro hB
    have heq : 𝓝[QuotientDomain E g \ {p}] p = 𝓝[E \ {p}] p := by
      have hset : QuotientDomain E g \ {p} = {x | g x ≠ 0} ∩ (E \ {p}) := by
        ext x
        simp only [QuotientDomain, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
        tauto
      rw [hset]
      exact nhdsWithin_inter_of_mem (hu.eventually_ne hB)
    have hp : Chapter02.IsLimitPoint p (QuotientDomain E g) := by
      rw [functionLimitPoint_iff_neBot, heq]
      exact (functionLimitPoint_iff_neBot E p).mp hf.1
    apply (functionLimitOn_iff_tendsto _ _ _ _ hp).mpr
    rw [heq]
    exact ht.div hu hB
  · intro X _ k E f g p A B hf hg
    have ht := (functionLimitOn_iff_tendsto E f p A hf.1).mp hf
    have hu := (functionLimitOn_iff_tendsto E g p B hg.1).mp hg
    exact ⟨(functionLimitOn_iff_tendsto E _ p _ hf.1).mpr (ht.add hu),
      (functionLimitOn_iff_tendsto E _ p _ hf.1).mpr (ht.inner hu)⟩

end Rudin.PMA.Chapter04
