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

end Rudin.PMA.Chapter04
