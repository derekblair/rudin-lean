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

/-! ### PMA-4.5: Continuity and isolated points -/
def FunctionContinuousWithinAt {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) (p : X) : Prop :=
  p ∈ E ∧ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, dist x p < δ → dist (f x) (f p) < ε

def FunctionContinuousOn {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) : Prop := ∀ p ∈ E, FunctionContinuousWithinAt E f p


def pma4_5_contract : Prop :=
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X), p ∈ E →
      (FunctionContinuousWithinAt E f p ↔ ContinuousWithinAt f E p)) ∧
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X) (f : X → Y),
    FunctionContinuousOn E f ↔ ContinuousOn f E) ∧
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X), Chapter02.IsIsolatedPoint p E → FunctionContinuousWithinAt E f p)

theorem functionContinuousWithinAt_iff {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) (p : X) (hp : p ∈ E) :
    FunctionContinuousWithinAt E f p ↔ ContinuousWithinAt f E p := by
  simp only [FunctionContinuousWithinAt, hp, true_and, Metric.continuousWithinAt_iff]

theorem functionContinuousOn_iff {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : X → Y) : FunctionContinuousOn E f ↔ ContinuousOn f E := by
  unfold FunctionContinuousOn ContinuousOn
  exact forall₂_congr fun p hp => functionContinuousWithinAt_iff E f p hp

theorem functionContinuousOn_univ_iff {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) : FunctionContinuousOn univ f ↔ Continuous f := by
  rw [functionContinuousOn_iff, continuousOn_univ]

theorem pma4_5 : pma4_5_contract := by
  refine ⟨fun E f p hp => functionContinuousWithinAt_iff E f p hp,
    fun E f => functionContinuousOn_iff E f, ?_⟩
  intro X Y _ _ E f p hp
  apply (functionContinuousWithinAt_iff E f p hp.1).mpr
  apply continuousWithinAt_of_not_accPt
  exact fun h => hp.2 ((Chapter02.isLimitPoint_iff_accPt p E).mpr h)

/-! ### PMA-4.6: Continuity as a function limit -/
def pma4_6_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : X), p ∈ E → Chapter02.IsLimitPoint p E →
      (FunctionContinuousWithinAt E f p ↔ FunctionLimitOn E f p (f p))

theorem pma4_6 : pma4_6_contract := by
  intro X Y _ _ E f p hp ha
  rw [functionContinuousWithinAt_iff E f p hp, functionLimitOn_iff_tendsto E f p (f p) ha]
  exact continuousWithinAt_sdiff_self.symm

/-! ### PMA-4.7: Composition -/
def Compose {X Y Z : Type*} (f : X → Y) (g : Y → Z) (x : X) : Z := g (f x)
def pma4_7_contract : Prop :=
  ∀ {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z]
    (E : Set X) (f : X → Y) (g : Y → Z) (p : X),
    FunctionContinuousWithinAt E f p →
      FunctionContinuousWithinAt (f '' E) g (f p) → FunctionContinuousWithinAt E (Compose f g) p

theorem pma4_7 : pma4_7_contract := by
  intro X Y Z _ _ _ E f g p hf hg
  apply (functionContinuousWithinAt_iff E _ p hf.1).mpr
  have ht := (functionContinuousWithinAt_iff E f p hf.1).mp hf
  have hu := (functionContinuousWithinAt_iff (f '' E) g (f p) hg.1).mp hg
  exact hu.comp ht (fun x hx => mem_image_of_mem f hx)

/-! ### PMA-4.8: Open and closed inverse images -/
def pma4_8_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y),
    (FunctionContinuousOn univ f ↔ ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V)) ∧
    (FunctionContinuousOn univ f ↔ ∀ C : Set Y, IsClosed C → IsClosed (f ⁻¹' C))

theorem pma4_8 : pma4_8_contract := by
  intro X Y _ _ f
  rw [functionContinuousOn_univ_iff]
  exact ⟨continuous_def, continuous_iff_isClosed⟩

/-! ### PMA-4.9: Algebra of continuous complex functions -/
def pma4_9_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] (f g : X → ℂ), Continuous f → Continuous g →
    Continuous (ComplexSum f g) ∧ Continuous (ComplexProduct f g) ∧
      ((∀ x, g x ≠ 0) → Continuous (ComplexQuotient f g))

theorem pma4_9 : pma4_9_contract := by
  intro X _ f g hf hg
  exact ⟨hf.add hg, hf.mul hg, fun h => hf.div hg h⟩

/-! ### PMA-4.10: Coordinates and Euclidean operations -/
def pma4_10_contract : Prop :=
  (∀ {X : Type*} [MetricSpace X] {k : ℕ} (f : X → EuclideanSpace ℝ (Fin k)),
    Continuous f ↔ ∀ i, Continuous (fun x => f x i)) ∧
  (∀ {X : Type*} [MetricSpace X] {k : ℕ} (f g : X → EuclideanSpace ℝ (Fin k)),
    Continuous f → Continuous g → Continuous (VectorSum f g) ∧ Continuous (InnerFunction f g))

theorem continuous_euclidean_iff_coordinates {X : Type*} [MetricSpace X] {k : ℕ}
    (f : X → EuclideanSpace ℝ (Fin k)) : Continuous f ↔ ∀ i, Continuous (fun x => f x i) := by
  constructor
  · intro h i
    exact (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).comp h
  · intro h
    exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin k => ℝ)).comp (continuous_pi h)

theorem pma4_10 : pma4_10_contract := by
  refine ⟨fun f => continuous_euclidean_iff_coordinates f, ?_⟩
  intro X _ k f g hf hg
  exact ⟨hf.add hg, hf.inner hg⟩

/-! ### PMA-4.11: Polynomial, rational and norm examples -/
def EuclideanMonomial {k : ℕ} (m : Fin k → ℕ) (x : EuclideanSpace ℝ (Fin k)) : ℂ :=
  ∏ i, (x i : ℂ) ^ m i
def EuclideanPolynomial {k : ℕ} (P : MvPolynomial (Fin k) ℂ)
    (x : EuclideanSpace ℝ (Fin k)) : ℂ := MvPolynomial.eval (fun i => (x i : ℂ)) P
def pma4_11_contract : Prop :=
  (∀ {k : ℕ} (i : Fin k),
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin k) => x i) ∧
      Continuous (fun x : EuclideanSpace ℝ (Fin k) => x i)) ∧
  (∀ {k : ℕ}, LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖) ∧
    Continuous (fun x : EuclideanSpace ℝ (Fin k) => ‖x‖)) ∧
  (∀ {k : ℕ} (m : Fin k → ℕ), Continuous (EuclideanMonomial m)) ∧
  (∀ {k : ℕ} (P : MvPolynomial (Fin k) ℂ), Continuous (EuclideanPolynomial P)) ∧
  (∀ {k : ℕ} (P Q : MvPolynomial (Fin k) ℂ),
    ContinuousOn (fun x => EuclideanPolynomial P x / EuclideanPolynomial Q x)
      {x | EuclideanPolynomial Q x ≠ 0}) ∧
  (∀ {X : Type*} [MetricSpace X] {k : ℕ} (f : X → EuclideanSpace ℝ (Fin k)),
    Continuous f → Continuous (fun x => ‖f x‖))

theorem euclidean_coordinate_lipschitz {k : ℕ} (i : Fin k) :
    LipschitzWith 1 (fun x : EuclideanSpace ℝ (Fin k) => x i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul, PiLp.sub_apply] using
    PiLp.norm_apply_le (x-y) i

theorem euclidean_monomial_continuous {k : ℕ} (m : Fin k → ℕ) :
    Continuous (EuclideanMonomial m) := by
  unfold EuclideanMonomial
  fun_prop

theorem euclidean_polynomial_continuous {k : ℕ} (P : MvPolynomial (Fin k) ℂ) :
    Continuous (EuclideanPolynomial P) := by
  exact P.continuous_eval.comp (continuous_pi fun i =>
    Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i))

theorem pma4_11 : pma4_11_contract := by
  refine ⟨fun i => ⟨euclidean_coordinate_lipschitz i, (euclidean_coordinate_lipschitz i).continuous⟩,
    ⟨lipschitzWith_one_norm, continuous_norm⟩, fun m => euclidean_monomial_continuous m,
    fun P => euclidean_polynomial_continuous P, ?_, fun _ h => h.norm⟩
  intro k P Q
  exact (euclidean_polynomial_continuous P).continuousOn.div
    (euclidean_polynomial_continuous Q).continuousOn (fun _ h => h)

/-! ### PMA-4.12: Induced domain metric -/
def pma4_12_contract : Prop :=
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X)
    (f : X → Y) (p : E), FunctionContinuousWithinAt E f p.val ↔
      ContinuousAt (fun x : E => f x.val) p) ∧
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (E : Set X) (f : X → Y),
    FunctionContinuousOn E f ↔ Continuous (fun x : E => f x.val))

theorem pma4_12 : pma4_12_contract := by
  constructor
  · intro X Y _ _ E f p
    rw [functionContinuousWithinAt_iff E f p.val p.property]
    exact continuousWithinAt_iff_continuousAt_domRestrict f p.property
  · intro X Y _ _ E f
    rw [functionContinuousOn_iff]
    exact continuousOn_iff_continuous_domRestrict
/-! ### PMA-4.13: Bounded functions -/
def BoundedFunction {X V : Type*} [NormedAddCommGroup V] (f : X → V) : Prop :=
  ∃ M : ℝ, ∀ x, ‖f x‖ < M

def pma4_13_contract : Prop :=
  ∀ {X : Type*} {k : ℕ} (f : X → EuclideanSpace ℝ (Fin k)),
    BoundedFunction f ↔ Bornology.IsBounded (range f)

theorem boundedFunction_iff_isBounded_range {X V : Type*} [NormedAddCommGroup V]
    (f : X → V) : BoundedFunction f ↔ Bornology.IsBounded (range f) := by
  constructor
  · rintro ⟨M, hM⟩
    exact isBounded_iff_forall_norm_le.mpr ⟨M, by
      rintro _ ⟨x, rfl⟩
      exact (hM x).le⟩
  · intro h
    obtain ⟨M, hM⟩ := h.exists_norm_le
    exact ⟨M + 1, fun x => lt_of_le_of_lt (hM _ ⟨x, rfl⟩) (lt_add_one M)⟩

theorem pma4_13 : pma4_13_contract := by
  intro X k f
  exact boundedFunction_iff_isBounded_range f

/-! ### PMA-4.14: Continuous compact images -/
def pma4_14_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (f : X → Y), Continuous f → IsCompact (range f)

theorem pma4_14 : pma4_14_contract := by
  intro X Y _ _ _ f hf
  exact isCompact_range hf

/-! ### PMA-4.15: Closed and bounded Euclidean images -/
def pma4_15_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] [CompactSpace X] {k : ℕ}
    (f : X → EuclideanSpace ℝ (Fin k)), Continuous f →
      IsClosed (range f) ∧ Bornology.IsBounded (range f) ∧ BoundedFunction f

theorem pma4_15 : pma4_15_contract := by
  intro X _ _ k f hf
  have hc := isCompact_range hf
  exact ⟨hc.isClosed, hc.isBounded, (boundedFunction_iff_isBounded_range f).mpr hc.isBounded⟩

/-! ### PMA-4.16: Attained supremum and infimum -/
def pma4_16_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    (f : X → ℝ), Continuous f →
      (∃ xmax, f xmax = sSup (range f) ∧ ∀ x, f x ≤ f xmax) ∧
      (∃ xmin, f xmin = sInf (range f) ∧ ∀ x, f xmin ≤ f x)

theorem pma4_16 : pma4_16_contract := by
  intro X _ _ _ f hf
  obtain ⟨xmax, _, hmax, hle⟩ := isCompact_univ.exists_sSup_image_eq_and_ge
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hf.continuousOn
  obtain ⟨xmin, _, hmin, hge⟩ := isCompact_univ.exists_sInf_image_eq_and_le
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hf.continuousOn
  refine ⟨⟨xmax, ?_, fun x => hle x (mem_univ x)⟩,
    ⟨xmin, ?_, fun x => hge x (mem_univ x)⟩⟩
  · simpa only [image_univ] using hmax.symm
  · simpa only [image_univ] using hmin.symm

/-! ### PMA-4.17: Continuous inverse from a compact domain -/
def pma4_17_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (e : X ≃ Y), Continuous e → Continuous e.symm

theorem pma4_17 : pma4_17_contract := by
  intro X Y _ _ _ e he
  exact (e.toHomeomorphOfContinuousClosed he he.isClosedMap).continuous_invFun

/-! ### PMA-4.18: Uniform continuity -/
def UniformlyContinuous {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ p q, dist p q < δ → dist (f p) (f q) < ε

def pma4_18_contract : Prop :=
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y),
    UniformlyContinuous f ↔ UniformContinuous f) ∧
  (∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y),
    UniformlyContinuous f → Continuous f)

theorem uniformlyContinuous_iff_uniformContinuous {X Y : Type*}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    UniformlyContinuous f ↔ UniformContinuous f := by
  exact Metric.uniformContinuous_iff.symm

theorem pma4_18 : pma4_18_contract := by
  constructor
  · intro X Y _ _ f
    exact uniformlyContinuous_iff_uniformContinuous f
  · intro X Y _ _ f hf
    exact ((uniformlyContinuous_iff_uniformContinuous f).mp hf).continuous

/-! ### PMA-4.19: Uniform continuity on compact domains -/
def pma4_19_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompactSpace X]
    (f : X → Y), Continuous f → UniformlyContinuous f

theorem pma4_19 : pma4_19_contract := by
  intro X Y _ _ _ f hf
  exact (uniformlyContinuous_iff_uniformContinuous f).mpr
    (CompactSpace.uniformContinuous_of_continuous hf)

/-! ### PMA-4.20: Converse counterexamples on noncompact real sets -/
def pma4_20_contract : Prop :=
  (∀ (E : Set ℝ), ¬ IsCompact E →
    (∃ f : E → ℝ, Continuous f ∧ ¬ BoundedFunction f) ∧
    (∃ g : E → ℝ, Continuous g ∧ BoundedFunction g ∧
      ¬ ∃ xmax, ∀ x, g x ≤ g xmax) ∧
    (Bornology.IsBounded E →
      ∃ h : E → ℝ, Continuous h ∧ ¬ UniformlyContinuous h)) ∧
  (∀ {Y : Type*} [MetricSpace Y] (f : ℤ → Y), UniformlyContinuous f)

theorem exists_continuous_unbounded_of_not_compact (E : Set ℝ) (hE : ¬ IsCompact E) :
    ∃ f : E → ℝ, Continuous f ∧ ¬ BoundedFunction f := by
  by_cases hb : Bornology.IsBounded E
  · have hnclosed : ¬ IsClosed E := fun hc => hE (Metric.isCompact_iff_isClosed_bounded.mpr ⟨hc, hb⟩)
    have hnsub : ¬ closure E ⊆ E := fun hs => hnclosed (isClosed_of_closure_subset hs)
    obtain ⟨p, hpcl, hpE⟩ := not_subset.mp hnsub
    let f : E → ℝ := fun x => (dist (x : ℝ) p)⁻¹
    have hdistpos (x : E) : 0 < dist (x : ℝ) p := by
      exact dist_pos.mpr (fun h => hpE (h ▸ x.property))
    refine ⟨f, (continuous_subtype_val.dist continuous_const).inv₀
      (fun x => ne_of_gt (hdistpos x)), ?_⟩
    rintro ⟨M, hM⟩
    have hR : 0 < max M 0 + 1 := by positivity
    obtain ⟨x, hxE, hxp⟩ := Metric.mem_closure_iff.mp hpcl
      (max M 0 + 1)⁻¹ (inv_pos.mpr hR)
    have hfx : max M 0 + 1 < f ⟨x, hxE⟩ := by
      change max M 0 + 1 < (dist x p)⁻¹
      have h' : dist x p < (max M 0 + 1)⁻¹ := by simpa only [dist_comm] using hxp
      simpa only [inv_inv] using
        (inv_lt_inv₀ (inv_pos.mpr hR) (hdistpos ⟨x, hxE⟩)).mpr h'
    have hm := hM ⟨x, hxE⟩
    rw [Real.norm_of_nonneg (inv_nonneg.mpr dist_nonneg)] at hm
    linarith [le_max_left M 0]
  · refine ⟨fun x => (x : ℝ), continuous_subtype_val, ?_⟩
    intro hf
    apply hb
    simpa using
      (boundedFunction_iff_isBounded_range (fun x : E => (x : ℝ))).mp hf

theorem exists_continuous_bounded_without_max_of_unbounded {X : Type*}
    [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f) (hfu : ¬ BoundedFunction f) :
    ∃ g : X → ℝ, Continuous g ∧ BoundedFunction g ∧ ¬ ∃ xmax, ∀ x, g x ≤ g xmax := by
  let g : X → ℝ := fun x => ‖f x‖ / (1 + ‖f x‖)
  have hden (x : X) : 0 < 1 + ‖f x‖ := by positivity
  refine ⟨g, hf.norm.div (continuous_const.add hf.norm)
    (fun x => ne_of_gt (hden x)), ⟨1, ?_⟩, ?_⟩
  · intro x
    change ‖(‖f x‖ / (1 + ‖f x‖) : ℝ)‖ < 1
    rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hden x).le)]
    exact (div_lt_one (hden x)).mpr (by linarith)
  · rintro ⟨xmax, hmax⟩
    have hy : ∃ y, ‖f xmax‖ < ‖f y‖ := by
      by_contra hn
      push Not at hn
      exact hfu ⟨‖f xmax‖ + 1, fun y => lt_of_le_of_lt (hn y) (lt_add_one _)⟩
    obtain ⟨y, hy⟩ := hy
    have hstrict : g xmax < g y := by
      change ‖f xmax‖ / (1 + ‖f xmax‖) < ‖f y‖ / (1 + ‖f y‖)
      rw [div_lt_div_iff₀ (hden xmax) (hden y)]
      nlinarith
    exact not_lt_of_ge (hmax y) hstrict

theorem pma4_20 : pma4_20_contract := by
  constructor
  · intro E hE
    obtain ⟨f, hf, hfu⟩ := exists_continuous_unbounded_of_not_compact E hE
    obtain ⟨g, hg, hgb, hgm⟩ := exists_continuous_bounded_without_max_of_unbounded hf hfu
    refine ⟨⟨f, hf, hfu⟩, ⟨g, hg, hgb, hgm⟩, ?_⟩
    intro hb
    refine ⟨f, hf, ?_⟩
    intro hu
    have htot : TotallyBounded E := hb.isCompact_closure.totallyBounded.subset subset_closure
    have htotSub : TotallyBounded (univ : Set E) := by
      have hp : (Subtype.val : E → ℝ) ⁻¹' E = univ := by
        ext x
        simp only [mem_preimage, x.property, mem_univ]
      simpa only [hp] using
        (totallyBounded_preimage (f := (Subtype.val : E → ℝ))
          isUniformEmbedding_subtype_val.isUniformInducing htot)
    have hrange : Bornology.IsBounded (range f) := by
      simpa only [image_univ] using
        (htotSub.image ((uniformlyContinuous_iff_uniformContinuous f).mp hu)).isBounded
    exact hfu ((boundedFunction_iff_isBounded_range f).mpr hrange)
  · intro Y _ f ε hε
    refine ⟨1, zero_lt_one, fun p q hpq => ?_⟩
    have heq : p = q := by
      by_contra hne
      exact not_lt_of_ge (Int.pairwise_one_le_dist hne) hpq
    simpa only [heq, dist_self] using hε

/-! ### PMA-4.21: Circle parametrization counterexample -/
def CircleParam (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos t, Real.sin t]

def UnitCircle : Set (EuclideanSpace ℝ (Fin 2)) := {z | ‖z‖ = 1}

def CircleParameterOrigin : Ico (0 : ℝ) (2 * Real.pi) :=
  ⟨0, le_rfl, mul_pos (by norm_num) Real.pi_pos⟩

def pma4_21_contract : Prop :=
  (∃ e : Ico (0 : ℝ) (2 * Real.pi) ≃ UnitCircle,
    (∀ t, (e t).val = CircleParam t.val) ∧ Continuous e ∧
      ¬ ContinuousAt e.symm (e CircleParameterOrigin)) ∧
  ¬ IsCompact (Ico (0 : ℝ) (2 * Real.pi)) ∧ IsCompact UnitCircle

def complexCircleEuclideanEquiv : Circle ≃ UnitCircle where
  toFun z := ⟨Complex.orthonormalBasisOneI.repr (z : ℂ), by
    change ‖Complex.orthonormalBasisOneI.repr (z : ℂ)‖ = 1
    rw [Complex.orthonormalBasisOneI.repr.norm_map]
    exact z.norm_coe⟩
  invFun z := ⟨Complex.orthonormalBasisOneI.repr.symm z.val, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
    exact z.property⟩
  left_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.symm_apply_apply (z : ℂ))
  right_inv z := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply z.val)

def circleParameterEquiv : Ico (0 : ℝ) (2 * Real.pi) ≃ UnitCircle := by
  have : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  exact (Set.equivOfEq (by simp : Ico (0 : ℝ) (2 * Real.pi) = Ico 0 (0 + 2 * Real.pi))).trans
    ((AddCircle.equivIco (2 * Real.pi) 0).symm.trans
      (AddCircle.homeomorphCircle'.toEquiv.trans complexCircleEuclideanEquiv))

theorem circleParameterEquiv_apply (t : Ico (0 : ℝ) (2 * Real.pi)) :
    (circleParameterEquiv t).val = CircleParam t.val := by
  have : Fact (0 < 2 * Real.pi) := ⟨mul_pos (by norm_num) Real.pi_pos⟩
  change Complex.orthonormalBasisOneI.repr
    ((AddCircle.homeomorphCircle' ((AddCircle.equivIco (2 * Real.pi) 0).symm
      ⟨t.val, by simpa only [zero_add] using t.property⟩)) : ℂ) = _
  change Complex.orthonormalBasisOneI.repr
    ((AddCircle.homeomorphCircle' (t.val : AddCircle (2 * Real.pi))) : ℂ) = _
  rw [AddCircle.homeomorphCircle'_apply_mk]
  ext i
  fin_cases i <;> simp [CircleParam, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem circleParam_continuous : Continuous CircleParam := by
  unfold CircleParam
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · simpa using Real.continuous_cos
  · simpa using Real.continuous_sin

theorem circleParam_two_pi_eq_zero : CircleParam (2 * Real.pi) = CircleParam 0 := by
  ext i
  fin_cases i <;> simp [CircleParam]

theorem unitCircle_isCompact : IsCompact UnitCircle := by
  have heq : UnitCircle = Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext z
    simp only [UnitCircle, mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
  rw [heq]
  exact isCompact_sphere _ _

theorem circleParam_inverse_not_continuous_origin
    (e : Ico (0 : ℝ) (2 * Real.pi) ≃ UnitCircle)
    (he : ∀ t, (e t).val = CircleParam t.val) :
    ¬ ContinuousAt e.symm (e CircleParameterOrigin) := by
  let t : ℕ → Ico (0 : ℝ) (2 * Real.pi) := fun n =>
    ⟨2 * Real.pi - Real.pi / ((n : ℝ) + 1), by
      have hd : 0 < (n : ℝ) + 1 := by positivity
      have hle : Real.pi / ((n : ℝ) + 1) ≤ Real.pi := by
        apply (div_le_iff₀ hd).mpr
        nlinarith [mul_nonneg Real.pi_pos.le (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      constructor
      · linarith [Real.pi_pos]
      · linarith [div_pos Real.pi_pos hd]⟩
  have ht : Tendsto (fun n => (t n).val) atTop (𝓝 (2 * Real.pi)) := by
    have hsmall : Tendsto (fun n : ℕ => Real.pi / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, one_div, one_mul, mul_zero] using
        Tendsto.const_mul Real.pi (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [t, sub_zero] using tendsto_const_nhds.sub hsmall
  have hmap : Tendsto (fun n => e (t n)) atTop (𝓝 (e CircleParameterOrigin)) := by
    apply tendsto_subtype_rng.mpr
    simp only [he]
    change Tendsto (fun n => CircleParam (t n).val) atTop (𝓝 (CircleParam 0))
    rw [← circleParam_two_pi_eq_zero]
    exact circleParam_continuous.continuousAt.tendsto.comp ht
  intro hcont
  have hzero : Tendsto (fun n => (t n).val) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Equiv.symm_apply_apply, CircleParameterOrigin] using
      continuous_subtype_val.continuousAt.tendsto.comp (hcont.tendsto.comp hmap)
  have heq := tendsto_nhds_unique ht hzero
  linarith [Real.pi_pos]

theorem circleParam_contract_of_equiv
    (e : Ico (0 : ℝ) (2 * Real.pi) ≃ UnitCircle)
    (he : ∀ t, (e t).val = CircleParam t.val) : pma4_21_contract := by
  have hcont : Continuous e := by
    apply continuous_induced_rng.mpr
    exact (circleParam_continuous.comp continuous_subtype_val).congr (fun t => (he t).symm)
  refine ⟨⟨e, he, hcont, circleParam_inverse_not_continuous_origin e he⟩, ?_, unitCircle_isCompact⟩
  rw [isCompact_Ico_iff]
  exact not_le.mpr (mul_pos (by norm_num) Real.pi_pos)

theorem pma4_21 : pma4_21_contract :=
  circleParam_contract_of_equiv circleParameterEquiv circleParameterEquiv_apply

/-! ### PMA-4.22: Connected images -/
def pma4_22_contract : Prop :=
  ∀ {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y)
    (E : Set X), Continuous f → Chapter02.RudinConnected E →
      Chapter02.RudinConnected (f '' E)

theorem pma4_22 : pma4_22_contract := by
  intro X Y _ _ f E hf hE
  apply (Chapter02.pma2_45_connected_reference (f '' E)).mpr
  exact ((Chapter02.pma2_45_connected_reference E).mp hE).image f hf.continuousOn

/-! ### PMA-4.23: Intermediate value theorem -/
def pma4_23_contract : Prop :=
  ∀ {a b : ℝ}, a < b → ∀ (f : ℝ → ℝ), ContinuousOn f (Icc a b) →
    ∀ c, ((f a < c ∧ c < f b) ∨ (f b < c ∧ c < f a)) →
      ∃ x ∈ Ioo a b, f x = c

theorem pma4_23 : pma4_23_contract := by
  intro a b hab f hf c hc
  have himage : c ∈ f '' Icc a b := by
    rcases hc with hc | hc
    · exact intermediate_value_Icc hab.le hf ⟨hc.1.le, hc.2.le⟩
    · exact intermediate_value_Icc' hab.le hf ⟨hc.1.le, hc.2.le⟩
  obtain ⟨x, hx, hfx⟩ := himage
  refine ⟨x, ⟨?_, ?_⟩, hfx⟩
  · apply lt_of_le_of_ne hx.1
    intro hax
    subst x
    rcases hc with hc | hc <;> linarith
  · apply lt_of_le_of_ne hx.2
    intro hxb
    subst x
    rcases hc with hc | hc <;> linarith

/-! ### PMA-4.25: Finite one-sided limits, including interval endpoints. -/

def RightLimitOn {Y : Type*} [MetricSpace Y]
    (a b : ℝ) (f : ℝ → Y) (x : ℝ) (q : Y) : Prop :=
  a ≤ x ∧ x < b ∧ Tendsto f (𝓝[Ioo x b] x) (𝓝 q)

def LeftLimitOn {Y : Type*} [MetricSpace Y]
    (a b : ℝ) (f : ℝ → Y) (x : ℝ) (q : Y) : Prop :=
  a < x ∧ x ≤ b ∧ Tendsto f (𝓝[Ioo a x] x) (𝓝 q)

def Statement_4_25 : Prop :=
  ∀ (Y : Type*) [MetricSpace Y] (a b : ℝ) (f : ℝ → Y),
    (∀ x q, a ≤ x → x < b →
      (RightLimitOn a b f x q ↔
        ∀ u : ℕ → ℝ, (∀ n, u n ∈ Ioo x b) → Tendsto u atTop (𝓝 x) →
          Tendsto (f ∘ u) atTop (𝓝 q))) ∧
    (∀ x q, a < x → x ≤ b →
      (LeftLimitOn a b f x q ↔
        ∀ u : ℕ → ℝ, (∀ n, u n ∈ Ioo a x) → Tendsto u atTop (𝓝 x) →
          Tendsto (f ∘ u) atTop (𝓝 q))) ∧
    (∀ x ∈ Ioo a b, ∀ q,
      FunctionLimitOn (Ioo a b) f x q ↔ LeftLimitOn a b f x q ∧ RightLimitOn a b f x q) ∧
    (∀ x ∈ Ioo a b,
      (∃ q, FunctionLimitOn (Ioo a b) f x q) ↔
        ∃ l r, LeftLimitOn a b f x l ∧ RightLimitOn a b f x r ∧ l = r)


theorem interval_punctured_nhds {a b x : ℝ} (hx : x ∈ Ioo a b) :
    𝓝[Ioo a b \ {x}] x = 𝓝[≠] x := by
  change 𝓝[Ioo a b ∩ {x}ᶜ] x = 𝓝[≠] x
  exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx.1 hx.2))

theorem interval_limitPoint {a b x : ℝ} (hx : x ∈ Ioo a b) :
    Chapter02.IsLimitPoint x (Ioo a b) := by
  rw [functionLimitPoint_iff_neBot, interval_punctured_nhds hx]
  infer_instance

theorem interval_continuity_iff {Y : Type*} [MetricSpace Y]
    {a b x : ℝ} (f : ℝ → Y) (hx : x ∈ Ioo a b) :
    FunctionContinuousWithinAt (Ioo a b) f x ↔ ContinuousAt f x := by
  rw [functionContinuousWithinAt_iff _ _ _ hx,
    continuousWithinAt_iff_continuousAt (Ioo_mem_nhds hx.1 hx.2)]

theorem interval_limit_iff_sides {Y : Type*} [MetricSpace Y]
    {a b x : ℝ} (f : ℝ → Y) (q : Y) (hx : x ∈ Ioo a b) :
    FunctionLimitOn (Ioo a b) f x q ↔ LeftLimitOn a b f x q ∧ RightLimitOn a b f x q := by
  rw [functionLimitOn_iff_tendsto _ _ _ _ (interval_limitPoint hx),
    interval_punctured_nhds hx, punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, tendsto_sup]
  simp only [LeftLimitOn, RightLimitOn, hx.1, hx.2, hx.1.le, hx.2.le, true_and,
    nhdsWithin_Ioo_eq_nhdsLT hx.1, nhdsWithin_Ioo_eq_nhdsGT hx.2]

theorem node_4_25 : Statement_4_25 := by
  intro Y _ a b f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x q hax hxb
    simp only [RightLimitOn, hax, hxb, true_and]
    exact tendsto_within_iff_all_sequences _ _ _ _
  · intro x q hax hxb
    simp only [LeftLimitOn, hax, hxb, true_and]
    exact tendsto_within_iff_all_sequences _ _ _ _
  · intro x hx q
    exact interval_limit_iff_sides f q hx
  · intro x hx
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q, q, (interval_limit_iff_sides f q hx).mp hq |>.1,
        (interval_limit_iff_sides f q hx).mp hq |>.2, rfl⟩
    · rintro ⟨l, r, hl, hr, rfl⟩
      exact ⟨l, (interval_limit_iff_sides f l hx).mpr ⟨hl, hr⟩⟩

/-! ### PMA-4.26: First- and second-kind discontinuities. -/

def FirstKindDiscontinuityOn {Y : Type*} [MetricSpace Y]
    (a b : ℝ) (f : ℝ → Y) (x : ℝ) : Prop :=
  x ∈ Ioo a b ∧ ¬ FunctionContinuousWithinAt (Ioo a b) f x ∧
    (∃ l, LeftLimitOn a b f x l) ∧ (∃ r, RightLimitOn a b f x r)

def SecondKindDiscontinuityOn {Y : Type*} [MetricSpace Y]
    (a b : ℝ) (f : ℝ → Y) (x : ℝ) : Prop :=
  x ∈ Ioo a b ∧ ¬ FunctionContinuousWithinAt (Ioo a b) f x ∧
    ¬ ((∃ l, LeftLimitOn a b f x l) ∧ (∃ r, RightLimitOn a b f x r))

def Statement_4_26 : Prop :=
  ∀ (Y : Type*) [MetricSpace Y] (a b : ℝ) (f : ℝ → Y) (x : ℝ),
    ((FirstKindDiscontinuityOn a b f x ∨ SecondKindDiscontinuityOn a b f x) ↔
      x ∈ Ioo a b ∧ ¬ FunctionContinuousWithinAt (Ioo a b) f x) ∧
    ¬ (FirstKindDiscontinuityOn a b f x ∧ SecondKindDiscontinuityOn a b f x) ∧
    (FirstKindDiscontinuityOn a b f x ↔
      x ∈ Ioo a b ∧ ∃ l r, LeftLimitOn a b f x l ∧ RightLimitOn a b f x r ∧
        (l ≠ r ∨ (l = r ∧ l ≠ f x)))


theorem continuous_iff_oneSided_eq {Y : Type*} [MetricSpace Y]
    {a b x : ℝ} (f : ℝ → Y) (hx : x ∈ Ioo a b) {l r : Y}
    (hl : LeftLimitOn a b f x l) (hr : RightLimitOn a b f x r) :
    FunctionContinuousWithinAt (Ioo a b) f x ↔ l = f x ∧ r = f x := by
  rw [interval_continuity_iff f hx]
  have hl' : Tendsto f (𝓝[<] x) (𝓝 l) := by
    simpa only [nhdsWithin_Ioo_eq_nhdsLT hx.1] using hl.2.2
  have hr' : Tendsto f (𝓝[>] x) (𝓝 r) := by
    simpa only [nhdsWithin_Ioo_eq_nhdsGT hx.2] using hr.2.2
  constructor
  · intro hc
    exact ⟨tendsto_nhds_unique hl' (hc.tendsto.mono_left nhdsWithin_le_nhds),
      tendsto_nhds_unique hr' (hc.tendsto.mono_left nhdsWithin_le_nhds)⟩
  · rintro ⟨hlv, hrv⟩
    rw [continuousAt_iff_punctured_nhds, punctured_nhds_eq_nhdsWithin_sup_nhdsWithin,
      tendsto_sup]
    exact ⟨hlv ▸ hl', hrv ▸ hr'⟩

theorem node_4_26 : Statement_4_26 := by
  classical
  intro Y _ a b f x
  refine ⟨?_, ?_, ?_⟩
  · unfold FirstKindDiscontinuityOn SecondKindDiscontinuityOn
    tauto
  · unfold FirstKindDiscontinuityOn SecondKindDiscontinuityOn
    tauto
  · constructor
    · rintro ⟨hx, hnc, ⟨l, hl⟩, ⟨r, hr⟩⟩
      refine ⟨hx, l, r, hl, hr, ?_⟩
      by_cases hlr : l = r
      · right
        refine ⟨hlr, ?_⟩
        intro hlf
        apply hnc
        exact (continuous_iff_oneSided_eq f hx hl hr).mpr ⟨hlf, hlr ▸ hlf⟩
      · exact Or.inl hlr
    · rintro ⟨hx, l, r, hl, hr, hd⟩
      refine ⟨hx, ?_, ⟨l, hl⟩, ⟨r, hr⟩⟩
      intro hc
      obtain ⟨hlf, hrf⟩ := (continuous_iff_oneSided_eq f hx hl hr).mp hc
      rcases hd with hne | ⟨_, hne⟩
      · exact hne (hlf.trans hrf.symm)
      · exact hne hlf

/-! ### PMA-4.27: Four discontinuity examples. -/

def DirichletFunction (x : ℝ) : ℝ := by
  classical
  exact if Irrational x then 0 else 1

def RationalIdentity (x : ℝ) : ℝ := by
  classical
  exact if Irrational x then 0 else x

def PiecewiseJump (x : ℝ) : ℝ :=
  if x < -2 then x + 2 else if x < 0 then -x - 2 else x + 2

def OscillatingSine (x : ℝ) : ℝ := if x = 0 then 0 else Real.sin (x⁻¹)

def Statement_4_27 : Prop :=
  (∀ x : ℝ,
    ¬ ContinuousAt DirichletFunction x ∧
    ¬ (∃ q : ℝ, Tendsto DirichletFunction (𝓝[<] x) (𝓝 q)) ∧
    ¬ (∃ q : ℝ, Tendsto DirichletFunction (𝓝[>] x) (𝓝 q))) ∧
  (∀ a b x : ℝ, x ∈ Ioo a b → SecondKindDiscontinuityOn a b DirichletFunction x) ∧
  (∀ x : ℝ, (ContinuousAt RationalIdentity x ↔ x = 0) ∧
    (x ≠ 0 →
      ¬ (∃ q : ℝ, Tendsto RationalIdentity (𝓝[<] x) (𝓝 q)) ∧
      ¬ (∃ q : ℝ, Tendsto RationalIdentity (𝓝[>] x) (𝓝 q)))) ∧
  (∀ x ∈ Ioo (-3 : ℝ) 1,
    FunctionContinuousWithinAt (Ioo (-3 : ℝ) 1) PiecewiseJump x ↔ x ≠ 0) ∧
  LeftLimitOn (-3) 1 PiecewiseJump 0 (-2) ∧ RightLimitOn (-3) 1 PiecewiseJump 0 2 ∧
  FirstKindDiscontinuityOn (-3) 1 PiecewiseJump 0 ∧
  (∀ x : ℝ, ContinuousAt OscillatingSine x ↔ x ≠ 0) ∧
  ¬ (∃ q : ℝ, Tendsto OscillatingSine (𝓝[<] (0 : ℝ)) (𝓝 q)) ∧
  ¬ (∃ q : ℝ, Tendsto OscillatingSine (𝓝[>] (0 : ℝ)) (𝓝 q)) ∧
  (∀ a b : ℝ, a < 0 → 0 < b → SecondKindDiscontinuityOn a b OscillatingSine 0)


def SideApproach (right : Bool) (x : ℝ) : Filter ℝ :=
  if right then 𝓝[>] x else 𝓝[<] x

theorem sideApproach_le_nhds (right : Bool) (x : ℝ) : SideApproach right x ≤ 𝓝 x := by
  cases right <;> exact nhdsWithin_le_nhds

theorem dense_sideApproach_neBot (right : Bool) (x : ℝ) {S : Set ℝ} (hS : Dense S) :
    (SideApproach right x ⊓ 𝓟 S).NeBot := by
  cases right
  · apply (nhdsLT_basis x).inf_principal_neBot_iff.mpr
    intro a ha
    obtain ⟨y, hyS, hy⟩ := hS.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr ha)
    exact ⟨y, hy, hyS⟩
  · apply (nhdsGT_basis x).inf_principal_neBot_iff.mpr
    intro b hb
    obtain ⟨y, hyS, hy⟩ := hS.exists_mem_open isOpen_Ioo (nonempty_Ioo.mpr hb)
    exact ⟨y, hy, hyS⟩

theorem side_limit_eq_of_dense (right : Bool) {x q : ℝ} {f g : ℝ → ℝ}
    {S : Set ℝ} (hS : Dense S) (hfg : ∀ y ∈ S, f y = g y)
    (hg : ContinuousAt g x) (hf : Tendsto f (SideApproach right x) (𝓝 q)) : q = g x := by
  let F := SideApproach right x ⊓ 𝓟 S
  have : F.NeBot := dense_sideApproach_neBot right x hS
  have he : f =ᶠ[F] g := by
    have hs : S ∈ F := mem_inf_of_right (by simp)
    filter_upwards [hs] with y hy
    exact hfg y hy
  exact tendsto_nhds_unique_of_eventuallyEq (hf.mono_left inf_le_left)
    (hg.tendsto.mono_left (inf_le_left.trans (sideApproach_le_nhds right x))) he

theorem dense_rational_points : Dense {x : ℝ | ¬ Irrational x} := by
  apply (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).mono
  rintro x ⟨q, rfl⟩
  exact q.not_irrational

theorem dirichlet_no_side_limit (right : Bool) (x : ℝ) :
    ¬ ∃ q : ℝ, Tendsto DirichletFunction (SideApproach right x) (𝓝 q) := by
  classical
  rintro ⟨q, hq⟩
  have h0 : q = 0 := side_limit_eq_of_dense right dense_irrational
    (g := fun _ => 0) (by intro y hy; change Irrational y at hy; simp [DirichletFunction, hy]) continuousAt_const hq
  have h1 : q = 1 := side_limit_eq_of_dense right dense_rational_points
    (g := fun _ => 1) (by intro y hy; change ¬ Irrational y at hy; simp [DirichletFunction, hy]) continuousAt_const hq
  linarith

theorem dirichlet_not_continuousAt (x : ℝ) : ¬ ContinuousAt DirichletFunction x := by
  intro hc
  exact dirichlet_no_side_limit false x
    ⟨DirichletFunction x, hc.tendsto.mono_left nhdsWithin_le_nhds⟩

theorem rationalIdentity_no_side_limit (right : Bool) {x : ℝ} (hx : x ≠ 0) :
    ¬ ∃ q : ℝ, Tendsto RationalIdentity (SideApproach right x) (𝓝 q) := by
  classical
  rintro ⟨q, hq⟩
  have h0 : q = 0 := side_limit_eq_of_dense right dense_irrational
    (g := fun _ => 0) (by intro y hy; change Irrational y at hy; simp [RationalIdentity, hy]) continuousAt_const hq
  have hxq : q = x := side_limit_eq_of_dense right dense_rational_points
    (g := id) (by intro y hy; change ¬ Irrational y at hy; simp [RationalIdentity, hy]) continuousAt_id hq
  exact hx (hxq.symm.trans h0)

theorem rationalIdentity_continuousAt_zero : ContinuousAt RationalIdentity 0 := by
  classical
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  by_cases hi : Irrational y
  · simp [RationalIdentity, hi, hε]
  · simpa [RationalIdentity, hi] using hy

theorem rationalIdentity_continuousAt_iff (x : ℝ) : ContinuousAt RationalIdentity x ↔ x = 0 := by
  constructor
  · intro hc
    by_contra hx
    exact rationalIdentity_no_side_limit false hx
      ⟨RationalIdentity x, hc.tendsto.mono_left nhdsWithin_le_nhds⟩
  · rintro rfl
    exact rationalIdentity_continuousAt_zero

theorem oscillatingSine_neg (x : ℝ) : OscillatingSine (-x) = -OscillatingSine x := by
  by_cases hx : x = 0
  · simp [hx, OscillatingSine]
  · simp [OscillatingSine, hx, inv_neg, Real.sin_neg]

theorem oscillatingSine_attains_near_zero_right {b c : ℝ}
    (hb : 0 < b) (hc : -1 ≤ c ∧ c ≤ 1) :
    ∃ x ∈ Ioo 0 b, OscillatingSine x = c := by
  have hp : 0 < 2 * Real.pi := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((b⁻¹ - Real.arcsin c) / (2 * Real.pi))
  have hphase : b⁻¹ < Real.arcsin c + (n : ℝ) * (2 * Real.pi) := by
    have h := (div_lt_iff₀ hp).mp hn
    linarith
  have hphasepos : 0 < Real.arcsin c + (n : ℝ) * (2 * Real.pi) :=
    (inv_pos.mpr hb).trans hphase
  refine ⟨(Real.arcsin c + (n : ℝ) * (2 * Real.pi))⁻¹,
    ⟨inv_pos.mpr hphasepos, ?_⟩, ?_⟩
  · simpa only [inv_inv] using
      (inv_lt_inv₀ hphasepos (inv_pos.mpr hb)).mpr hphase
  · simp only [OscillatingSine, ne_of_gt (inv_pos.mpr hphasepos), ↓reduceIte, inv_inv,
      Real.sin_add_nat_mul_two_pi, Real.sin_arcsin hc.1 hc.2]

theorem oscillatingSine_attains_near_zero_left {a c : ℝ}
    (ha : a < 0) (hc : -1 ≤ c ∧ c ≤ 1) :
    ∃ x ∈ Ioo a 0, OscillatingSine x = c := by
  obtain ⟨x, hx, hxc⟩ := oscillatingSine_attains_near_zero_right (neg_pos.mpr ha)
    (c := -c) ⟨by linarith [hc.2], by linarith [hc.1]⟩
  refine ⟨-x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
  rw [oscillatingSine_neg, hxc, neg_neg]

theorem oscillatingSine_mem_unit_interval (x : ℝ) :
    -1 ≤ OscillatingSine x ∧ OscillatingSine x ≤ 1 := by
  by_cases hx : x = 0
  · simp [OscillatingSine, hx]
  · simp only [OscillatingSine, hx, ↓reduceIte]
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩

theorem oscillatingSine_continuousAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt OscillatingSine x := by
  apply (Real.continuous_sin.continuousAt.comp (continuousAt_inv₀ hx)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx] with y hy
  simp only [OscillatingSine, hy, ↓reduceIte, Function.comp_apply]


theorem piecewiseJump_eq_if_abs (x : ℝ) :
    PiecewiseJump x = if x < 0 then -|x + 2| else x + 2 := by
  by_cases hx : x < -2
  · have hx0 : x < 0 := by linarith
    simp only [PiecewiseJump, hx, hx0, ↓reduceIte, abs_of_neg (by linarith : x + 2 < 0), neg_neg]
  · by_cases hx0 : x < 0
    · simp only [PiecewiseJump, hx, hx0, ↓reduceIte,
        abs_of_nonneg (by linarith : 0 ≤ x + 2)]
      ring
    · simp only [PiecewiseJump, hx, hx0, ↓reduceIte]

theorem piecewiseJump_continuousAt_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt PiecewiseJump x := by
  by_cases hx0 : x < 0
  · apply ((continuous_id.add continuous_const).abs.neg :
      Continuous (fun x : ℝ => -|x + 2|)).continuousAt.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx0] with y hy
    change y < 0 at hy
    change PiecewiseJump y = -|y + 2|
    simp only [piecewiseJump_eq_if_abs, hy, ↓reduceIte]
  · have hxpos : 0 < x := lt_of_le_of_ne (le_of_not_gt hx0) (Ne.symm hx)
    apply (continuous_id.add continuous_const : Continuous (fun x : ℝ => x + 2)).continuousAt.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    change 0 < y at hy
    change PiecewiseJump y = y + 2
    simp only [piecewiseJump_eq_if_abs, not_lt.mpr hy.le, ↓reduceIte]

theorem piecewiseJump_not_continuousWithin_zero :
    ¬ FunctionContinuousWithinAt (Ioo (-3 : ℝ) 1) PiecewiseJump 0 := by
  rintro ⟨_, hε⟩
  obtain ⟨δ, hδ, hclose⟩ := hε 1 zero_lt_one
  have hm : 0 < min δ 1 := lt_min hδ zero_lt_one
  let x : ℝ := -(min δ 1) / 2
  have hx0 : x < 0 := by dsimp [x]; linarith
  have hxneg2 : ¬ x < -2 := by dsimp [x]; linarith [min_le_right δ 1]
  have hxE : x ∈ Ioo (-3 : ℝ) 1 := by
    dsimp [x]
    constructor <;> linarith [min_le_right δ 1]
  have hxd : dist x 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_neg hx0]
    dsimp [x]
    linarith [min_le_left δ 1]
  have hc := hclose x hxE hxd
  have hfx : PiecewiseJump x = -x - 2 := by
    simp only [PiecewiseJump, hxneg2, hx0, ↓reduceIte]
  have hf0 : PiecewiseJump 0 = 2 := by norm_num [PiecewiseJump]
  rw [hfx, hf0, Real.dist_eq, abs_of_neg (by dsimp [x]; linarith [min_le_right δ 1] : -x - 2 - 2 < 0)] at hc
  dsimp [x] at hc
  linarith [min_le_right δ 1]

theorem piecewiseJump_leftLimit : LeftLimitOn (-3) 1 PiecewiseJump 0 (-2) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hc : Tendsto (fun x : ℝ => -x - 2) (𝓝 0) (𝓝 (-2)) := by
    convert (continuous_id.neg.sub continuous_const :
      Continuous (fun x : ℝ => -x - 2)).continuousAt (x := 0) |>.tendsto using 1
    · ext x
      rfl
    · norm_num
  have heq : PiecewiseJump =ᶠ[𝓝[Ioo (-3 : ℝ) 0] 0] (fun x => -x - 2) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (-2 : ℝ) < 0))] with y hy hnear
    change -2 < y at hnear
    simp only [PiecewiseJump, not_lt.mpr hnear.le, hy.2, ↓reduceIte]
  exact (hc.mono_left nhdsWithin_le_nhds).congr' heq.symm

theorem piecewiseJump_rightLimit : RightLimitOn (-3) 1 PiecewiseJump 0 2 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hc : Tendsto (fun x : ℝ => x + 2) (𝓝 0) (𝓝 2) := by
    convert (continuous_id.add continuous_const :
      Continuous (fun x : ℝ => x + 2)).continuousAt (x := 0) |>.tendsto using 1
    · ext x
      rfl
    · norm_num
  have heq : PiecewiseJump =ᶠ[𝓝[Ioo (0 : ℝ) 1] 0] (fun x => x + 2) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy2 : ¬ y < -2 := by linarith [hy.1]
    simp only [PiecewiseJump, hy2, not_lt.mpr hy.1.le, ↓reduceIte]
  exact (hc.mono_left nhdsWithin_le_nhds).congr' heq.symm

theorem piecewiseJump_example_contract :
    (∀ x ∈ Ioo (-3 : ℝ) 1,
      FunctionContinuousWithinAt (Ioo (-3 : ℝ) 1) PiecewiseJump x ↔ x ≠ 0) ∧
    LeftLimitOn (-3) 1 PiecewiseJump 0 (-2) ∧ RightLimitOn (-3) 1 PiecewiseJump 0 2 ∧
    FirstKindDiscontinuityOn (-3) 1 PiecewiseJump 0 := by
  refine ⟨?_, piecewiseJump_leftLimit, piecewiseJump_rightLimit,
    ⟨by norm_num, piecewiseJump_not_continuousWithin_zero,
      ⟨-2, piecewiseJump_leftLimit⟩, ⟨2, piecewiseJump_rightLimit⟩⟩⟩
  intro x hxE
  constructor
  · intro hc hx
    subst x
    exact piecewiseJump_not_continuousWithin_zero hc
  · intro hx
    refine ⟨hxE, ?_⟩
    exact Metric.continuousWithinAt_iff.mp
      (piecewiseJump_continuousAt_of_ne_zero hx).continuousWithinAt



theorem oscillatingSine_no_side_limit (right : Bool) :
    ¬ ∃ q : ℝ, Tendsto OscillatingSine (SideApproach right 0) (𝓝 q) := by
  rintro ⟨q, hq⟩
  have he : ∀ᶠ t in SideApproach right 0, dist (OscillatingSine t) q < 1 :=
    hq.eventually (Metric.ball_mem_nhds q zero_lt_one)
  cases right
  · obtain ⟨a, ha, has⟩ := (nhdsLT_basis (0 : ℝ)).mem_iff.mp he
    obtain ⟨u, hu, hv⟩ := oscillatingSine_attains_near_zero_left ha (c := 1) ⟨by norm_num, le_rfl⟩
    obtain ⟨v, hvs, hvv⟩ := oscillatingSine_attains_near_zero_left ha (c := -1) ⟨le_rfl, by norm_num⟩
    have h1 : dist (1 : ℝ) q < 1 := hv ▸ has hu
    have hm1 : dist (-1 : ℝ) q < 1 := hvv ▸ has hvs
    rw [Real.dist_eq] at h1 hm1
    linarith [(abs_lt.mp h1).2, (abs_lt.mp hm1).1]
  · obtain ⟨b, hb, hbs⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp he
    obtain ⟨u, hu, hv⟩ := oscillatingSine_attains_near_zero_right hb (c := 1) ⟨by norm_num, le_rfl⟩
    obtain ⟨v, hvs, hvv⟩ := oscillatingSine_attains_near_zero_right hb (c := -1) ⟨le_rfl, by norm_num⟩
    have h1 : dist (1 : ℝ) q < 1 := hv ▸ hbs hu
    have hm1 : dist (-1 : ℝ) q < 1 := hvv ▸ hbs hvs
    rw [Real.dist_eq] at h1 hm1
    linarith [(abs_lt.mp h1).2, (abs_lt.mp hm1).1]

theorem oscillatingSine_not_continuousAt_zero : ¬ ContinuousAt OscillatingSine 0 := by
  intro hc
  exact oscillatingSine_no_side_limit false
    ⟨OscillatingSine 0, hc.tendsto.mono_left nhdsWithin_le_nhds⟩

theorem oscillatingSine_continuousAt_iff (x : ℝ) : ContinuousAt OscillatingSine x ↔ x ≠ 0 := by
  constructor
  · intro hc hx
    subst x
    exact oscillatingSine_not_continuousAt_zero hc
  · exact oscillatingSine_continuousAt_of_ne_zero

theorem secondKind_of_no_left {a b x : ℝ} {f : ℝ → ℝ} (hx : x ∈ Ioo a b)
    (hnc : ¬ ContinuousAt f x) (hnl : ¬ ∃ q : ℝ, Tendsto f (𝓝[<] x) (𝓝 q)) :
    SecondKindDiscontinuityOn a b f x := by
  refine ⟨hx, fun hc => hnc ((interval_continuity_iff f hx).mp hc), ?_⟩
  rintro ⟨⟨q, hq⟩, _⟩
  apply hnl
  exact ⟨q, by simpa only [nhdsWithin_Ioo_eq_nhdsLT hx.1] using hq.2.2⟩

theorem node_4_27 : Statement_4_27 := by
  refine ⟨?_, ?_, ?_, piecewiseJump_example_contract.1,
    piecewiseJump_leftLimit, piecewiseJump_rightLimit,
    piecewiseJump_example_contract.2.2.2,
    oscillatingSine_continuousAt_iff,
    oscillatingSine_no_side_limit false, oscillatingSine_no_side_limit true, ?_⟩
  · intro x
    exact ⟨dirichlet_not_continuousAt x, dirichlet_no_side_limit false x,
      dirichlet_no_side_limit true x⟩
  · intro a b x hx
    exact secondKind_of_no_left hx (dirichlet_not_continuousAt x)
      (dirichlet_no_side_limit false x)
  · intro x
    exact ⟨rationalIdentity_continuousAt_iff x, fun hx =>
      ⟨rationalIdentity_no_side_limit false hx, rationalIdentity_no_side_limit true hx⟩⟩
  · intro a b ha hb
    exact secondKind_of_no_left ⟨ha, hb⟩ oscillatingSine_not_continuousAt_zero
      (oscillatingSine_no_side_limit false)

/-! ### PMA-4.24: Intermediate values without continuity -/
def pma4_24_contract : Prop :=
  (∀ {a b : ℝ}, a < b → ∀ c,
    ((OscillatingSine a < c ∧ c < OscillatingSine b) ∨
      (OscillatingSine b < c ∧ c < OscillatingSine a)) →
    ∃ x ∈ Ioo a b, OscillatingSine x = c) ∧
  ¬ ContinuousAt OscillatingSine 0

theorem pma4_24 : pma4_24_contract := by
  constructor
  · intro a b hab c hbetween
    by_cases hz : 0 ∈ Icc a b
    · have hc : -1 ≤ c ∧ c ≤ 1 := by
        obtain ⟨hla, hua⟩ := oscillatingSine_mem_unit_interval a
        obtain ⟨hlb, hub⟩ := oscillatingSine_mem_unit_interval b
        rcases hbetween with hbetween | hbetween <;> constructor <;> linarith
      by_cases hb : 0 < b
      · obtain ⟨x, hx, hxc⟩ := oscillatingSine_attains_near_zero_right hb hc
        exact ⟨x, ⟨lt_of_le_of_lt hz.1 hx.1, hx.2⟩, hxc⟩
      · have hbeq : b = 0 := le_antisymm (le_of_not_gt hb) hz.2
        have ha : a < 0 := by simpa only [hbeq] using hab
        obtain ⟨x, hx, hxc⟩ := oscillatingSine_attains_near_zero_left ha hc
        exact ⟨x, ⟨hx.1, by simpa only [hbeq] using hx.2⟩, hxc⟩
    · have hf : ContinuousOn OscillatingSine (Icc a b) := by
        intro x hx
        apply (oscillatingSine_continuousAt_of_ne_zero ?_).continuousWithinAt
        intro hxeq
        exact hz (hxeq ▸ hx)
      exact pma4_23 hab OscillatingSine hf c hbetween
  · intro hcont
    obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont (1 / 2) (by norm_num)
    obtain ⟨x, hx, hfx⟩ := oscillatingSine_attains_near_zero_right hδ (c := 1) (by norm_num)
    have hd : dist x 0 < δ := by simpa only [dist_zero_right, Real.norm_of_nonneg hx.1.le] using hx.2
    have hc := hclose hd
    have hz : OscillatingSine 0 = 0 := by simp only [OscillatingSine, ↓reduceIte]
    rw [hfx, hz] at hc
    norm_num [dist_zero_right] at hc
/-! ### PMA-4.28: Non-strict interval monotonicity. -/

def IntervalIncreasing (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, a < x → x < y → y < b → f x ≤ f y

def IntervalDecreasing (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, a < x → x < y → y < b → f y ≤ f x

def IntervalMonotonic (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  IntervalIncreasing a b f ∨ IntervalDecreasing a b f

def Statement_4_28 : Prop :=
  ∀ (a b : ℝ) (f : ℝ → ℝ),
    (IntervalIncreasing a b f ↔ MonotoneOn f (Ioo a b)) ∧
    (IntervalDecreasing a b f ↔ AntitoneOn f (Ioo a b)) ∧
    (IntervalMonotonic a b f ↔ MonotoneOn f (Ioo a b) ∨ AntitoneOn f (Ioo a b))


theorem intervalIncreasing_iff_monotoneOn (a b : ℝ) (f : ℝ → ℝ) :
    IntervalIncreasing a b f ↔ MonotoneOn f (Ioo a b) := by
  constructor
  · intro hf x hx y hy hxy
    rcases hxy.eq_or_lt with h | h
    · simp [h]
    · exact hf x y hx.1 h hy.2
  · intro hf x y hax hxy hyb
    exact hf ⟨hax, hxy.trans hyb⟩ ⟨hax.trans hxy, hyb⟩ hxy.le

theorem intervalDecreasing_iff_antitoneOn (a b : ℝ) (f : ℝ → ℝ) :
    IntervalDecreasing a b f ↔ AntitoneOn f (Ioo a b) := by
  constructor
  · intro hf x hx y hy hxy
    rcases hxy.eq_or_lt with h | h
    · simp [h]
    · exact hf x y hx.1 h hy.2
  · intro hf x y hax hxy hyb
    exact hf ⟨hax, hxy.trans hyb⟩ ⟨hax.trans hxy, hyb⟩ hxy.le

theorem node_4_28 : Statement_4_28 := by
  intro a b f
  exact ⟨intervalIncreasing_iff_monotoneOn a b f, intervalDecreasing_iff_antitoneOn a b f,
    or_congr (intervalIncreasing_iff_monotoneOn a b f) (intervalDecreasing_iff_antitoneOn a b f)⟩

/-! ### PMA-4.29: Finite one-sided limits of monotonic functions. -/

def IntervalLeftSup (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := sSup (f '' Ioo a x)
def IntervalRightInf (b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := sInf (f '' Ioo x b)
def IntervalLeftInf (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := sInf (f '' Ioo a x)
def IntervalRightSup (b : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := sSup (f '' Ioo x b)

def Statement_4_29 : Prop :=
  ∀ (a b : ℝ) (f : ℝ → ℝ),
    (IntervalIncreasing a b f →
      (∀ x ∈ Ioo a b,
        LeftLimitOn a b f x (IntervalLeftSup a f x) ∧
        RightLimitOn a b f x (IntervalRightInf b f x) ∧
        IntervalLeftSup a f x ≤ f x ∧ f x ≤ IntervalRightInf b f x) ∧
      (∀ x y : ℝ, a < x → x < y → y < b →
        IntervalRightInf b f x ≤ IntervalLeftSup a f y)) ∧
    (IntervalDecreasing a b f →
      (∀ x ∈ Ioo a b,
        LeftLimitOn a b f x (IntervalLeftInf a f x) ∧
        RightLimitOn a b f x (IntervalRightSup b f x) ∧
        f x ≤ IntervalLeftInf a f x ∧ IntervalRightSup b f x ≤ f x) ∧
      (∀ x y : ℝ, a < x → x < y → y < b →
        IntervalLeftInf a f y ≤ IntervalRightSup b f x))


theorem increasing_interval_limits {a b : ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f (Ioo a b)) :
    (∀ x ∈ Ioo a b,
      LeftLimitOn a b f x (IntervalLeftSup a f x) ∧
      RightLimitOn a b f x (IntervalRightInf b f x) ∧
      IntervalLeftSup a f x ≤ f x ∧ f x ≤ IntervalRightInf b f x) ∧
    (∀ x y : ℝ, a < x → x < y → y < b →
      IntervalRightInf b f x ≤ IntervalLeftSup a f y) := by
  have hLB (x : ℝ) (hx : x ∈ Ioo a b) : BddAbove (f '' Ioo a x) := by
    refine ⟨f x, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hf ⟨ht.1, ht.2.trans hx.2⟩ hx ht.2.le
  have hRB (x : ℝ) (hx : x ∈ Ioo a b) : BddBelow (f '' Ioo x b) := by
    refine ⟨f x, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hf hx ⟨hx.1.trans ht.1, ht.2⟩ ht.1.le
  constructor
  · intro x hx
    have hML : MonotoneOn f (Ioo a x) := hf.mono fun t ht => ⟨ht.1, ht.2.trans hx.2⟩
    have hMR : MonotoneOn f (Ioo x b) := hf.mono fun t ht => ⟨hx.1.trans ht.1, ht.2⟩
    refine ⟨⟨hx.1, hx.2.le, ?_⟩, ⟨hx.1.le, hx.2, ?_⟩, ?_, ?_⟩
    · rw [nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact hML.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hx.1) (hLB x hx)
    · rw [nhdsWithin_Ioo_eq_nhdsGT hx.2]
      exact hMR.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hx.2) (hRB x hx)
    · apply csSup_le ((nonempty_Ioo.mpr hx.1).image f)
      rintro _ ⟨t, ht, rfl⟩
      exact hf ⟨ht.1, ht.2.trans hx.2⟩ hx ht.2.le
    · apply le_csInf ((nonempty_Ioo.mpr hx.2).image f)
      rintro _ ⟨t, ht, rfl⟩
      exact hf hx ⟨hx.1.trans ht.1, ht.2⟩ ht.1.le
  · intro x y hax hxy hyb
    obtain ⟨z, hxz, hzy⟩ := exists_between hxy
    exact (csInf_le (hRB x ⟨hax, hxy.trans hyb⟩)
      (mem_image_of_mem f ⟨hxz, hzy.trans hyb⟩)).trans
      (le_csSup (hLB y ⟨hax.trans hxy, hyb⟩)
        (mem_image_of_mem f ⟨hax.trans hxz, hzy⟩))

theorem decreasing_interval_limits {a b : ℝ} {f : ℝ → ℝ}
    (hf : AntitoneOn f (Ioo a b)) :
    (∀ x ∈ Ioo a b,
      LeftLimitOn a b f x (IntervalLeftInf a f x) ∧
      RightLimitOn a b f x (IntervalRightSup b f x) ∧
      f x ≤ IntervalLeftInf a f x ∧ IntervalRightSup b f x ≤ f x) ∧
    (∀ x y : ℝ, a < x → x < y → y < b →
      IntervalLeftInf a f y ≤ IntervalRightSup b f x) := by
  have hLB (x : ℝ) (hx : x ∈ Ioo a b) : BddBelow (f '' Ioo a x) := by
    refine ⟨f x, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hf ⟨ht.1, ht.2.trans hx.2⟩ hx ht.2.le
  have hRB (x : ℝ) (hx : x ∈ Ioo a b) : BddAbove (f '' Ioo x b) := by
    refine ⟨f x, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hf hx ⟨hx.1.trans ht.1, ht.2⟩ ht.1.le
  constructor
  · intro x hx
    have hML : AntitoneOn f (Ioo a x) := hf.mono fun t ht => ⟨ht.1, ht.2.trans hx.2⟩
    have hMR : AntitoneOn f (Ioo x b) := hf.mono fun t ht => ⟨hx.1.trans ht.1, ht.2⟩
    refine ⟨⟨hx.1, hx.2.le, ?_⟩, ⟨hx.1.le, hx.2, ?_⟩, ?_, ?_⟩
    · rw [nhdsWithin_Ioo_eq_nhdsLT hx.1]
      exact hML.tendsto_nhdsWithin_Ioo_left (nonempty_Ioo.mpr hx.1) (hLB x hx)
    · rw [nhdsWithin_Ioo_eq_nhdsGT hx.2]
      exact hMR.tendsto_nhdsWithin_Ioo_right (nonempty_Ioo.mpr hx.2) (hRB x hx)
    · apply le_csInf ((nonempty_Ioo.mpr hx.1).image f)
      rintro _ ⟨t, ht, rfl⟩
      exact hf ⟨ht.1, ht.2.trans hx.2⟩ hx ht.2.le
    · apply csSup_le ((nonempty_Ioo.mpr hx.2).image f)
      rintro _ ⟨t, ht, rfl⟩
      exact hf hx ⟨hx.1.trans ht.1, ht.2⟩ ht.1.le
  · intro x y hax hxy hyb
    obtain ⟨z, hxz, hzy⟩ := exists_between hxy
    exact (csInf_le (hLB y ⟨hax.trans hxy, hyb⟩)
      (mem_image_of_mem f ⟨hax.trans hxz, hzy⟩)).trans
      (le_csSup (hRB x ⟨hax, hxy.trans hyb⟩)
        (mem_image_of_mem f ⟨hxz, hzy.trans hyb⟩))

theorem node_4_29 : Statement_4_29 := by
  intro a b f
  exact ⟨fun hf => increasing_interval_limits ((intervalIncreasing_iff_monotoneOn a b f).mp hf),
    fun hf => decreasing_interval_limits ((intervalDecreasing_iff_antitoneOn a b f).mp hf)⟩

end Rudin.PMA.Chapter04
