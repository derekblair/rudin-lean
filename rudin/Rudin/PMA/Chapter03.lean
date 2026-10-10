import Mathlib
import Rudin.PMA.Chapter02

noncomputable section
open scoped BigOperators ComplexConjugate
open Set Filter Topology

/-!
# Rudin, *Principles of Mathematical Analysis* (3rd ed.)

## Chapter 3: Numerical Sequences and Series

Every definition, theorem, and corollary from this chapter is
formalized below in dependency order. Zero `sorry`s: anything
not yet proved is tracked in `QUEUE.md`, never as a `sorry` here.
-/

namespace Rudin.PMA.Chapter03

/-! ### PMA-3.1: metric convergence and the complete sequence examples. -/
def ConvergesTo {X : Type*} [MetricSpace X] (s : ℕ → X) (p : X) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (s n) p < ε
def SequenceConverges {X : Type*} [MetricSpace X] (s : ℕ → X) : Prop :=
  ∃ p, ConvergesTo s p
def SequenceDiverges {X : Type*} [MetricSpace X] (s : ℕ → X) : Prop :=
  ¬ SequenceConverges s
def SequenceBounded {X : Type*} [MetricSpace X] (s : ℕ → X) : Prop :=
  Chapter02.IsBoundedSet (range s)
def ReciprocalSequence (n : ℕ) : ℂ := (n + 1 : ℂ)⁻¹
def SquareSequence (n : ℕ) : ℂ := (n + 1 : ℂ)^2
def OscillatingReciprocalSequence (n : ℕ) : ℂ :=
  1 + (-1 : ℂ)^(n+1) / (n + 1 : ℂ)
def ImaginaryPowerSequence (n : ℕ) : ℂ := Complex.I^(n+1)
def ConstantOneSequence (_ : ℕ) : ℂ := 1
abbrev PositiveReals := {x : ℝ // 0 < x}
def PositiveReciprocalSequence (n : ℕ) : PositiveReals :=
  ⟨1 / (n + 1 : ℝ), one_div_pos.mpr (by positivity)⟩

theorem pma3_1_reference {X : Type*} [MetricSpace X] (s : ℕ → X) (p : X) :
    ConvergesTo s p ↔ Tendsto s atTop (𝓝 p) := Metric.tendsto_atTop.symm

theorem pma3_1_bounded_reference {X : Type*} [MetricSpace X] (s : ℕ → X) :
    SequenceBounded s ↔ Bornology.IsBounded (range s) := by
  let : Nonempty X := ⟨s 0⟩
  exact Chapter02.isBoundedSet_iff_isBounded _

theorem reciprocalSequence_tendsto : Tendsto ReciprocalSequence atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => (n+1 : ℂ)⁻¹) atTop (𝓝 0)
  simpa [one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ))

theorem reciprocalSequence_injective : Function.Injective ReciprocalSequence := by
  intro m n h
  have hcast : (m + 1 : ℂ) = (n + 1 : ℂ) := inv_injective h
  have hnat : m + 1 = n + 1 := by exact_mod_cast hcast
  omega

theorem squareSequence_norm (n : ℕ) : ‖SquareSequence n‖ = (n+1 : ℝ)^2 := by
  simpa [SquareSequence, norm_pow] using congrArg (fun x : ℝ => x^2)
    (norm_natCast (α := ℂ) (n+1))

theorem squareSequence_not_bounded : ¬ SequenceBounded SquareSequence := by
  intro h
  obtain ⟨R, hR⟩ := ((pma3_1_bounded_reference _).mp h).exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hbound := hR (SquareSequence n) (mem_range_self n)
  rw [squareSequence_norm] at hbound
  have hnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  nlinarith

theorem squareSequence_injective : Function.Injective SquareSequence := by
  intro m n h
  have heq := congrArg norm h
  rw [squareSequence_norm, squareSequence_norm] at heq
  have hcast : (m+1 : ℝ) = (n+1 : ℝ) :=
    (sq_eq_sq₀ (by positivity) (by positivity)).mp heq
  have hnat : m+1 = n+1 := by exact_mod_cast hcast
  omega

theorem oscillatingReciprocalSequence_norm_difference (n : ℕ) :
    ‖OscillatingReciprocalSequence n - 1‖ = 1/(n+1 : ℝ) := by
  simp only [OscillatingReciprocalSequence, add_sub_cancel_left, norm_div, norm_pow,
    norm_neg, norm_one, one_pow]
  norm_cast

theorem oscillatingReciprocalSequence_tendsto :
    Tendsto OscillatingReciprocalSequence atTop (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [oscillatingReciprocalSequence_norm_difference] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem oscillatingReciprocalSequence_injective :
    Function.Injective OscillatingReciprocalSequence := by
  intro m n h
  have heq := congrArg (fun z : ℂ => ‖z-1‖) h
  rw [oscillatingReciprocalSequence_norm_difference,
    oscillatingReciprocalSequence_norm_difference] at heq
  have hcast : (m+1 : ℝ) = (n+1 : ℝ) := inv_injective (by simpa [one_div] using heq)
  have hnat : m+1 = n+1 := by exact_mod_cast hcast
  omega

theorem imaginaryPowerSequence_finite : (range ImaginaryPowerSequence).Finite := by
  have h4 : Complex.I^4 = 1 := by norm_num [pow_succ, Complex.I_mul_I]
  apply (Set.finite_range (fun i : Fin 4 => Complex.I^i.val)).subset
  rintro z ⟨n, rfl⟩
  refine ⟨⟨(n+1)%4, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  dsimp [ImaginaryPowerSequence]
  nth_rw 2 [← Nat.mod_add_div (n+1) 4]
  rw [pow_add, pow_mul, h4, one_pow, mul_one]

theorem imaginaryPowerSequence_diverges : SequenceDiverges ImaginaryPowerSequence := by
  rintro ⟨p, hp⟩
  have hlim := (pma3_1_reference _ _).mp hp
  have h4 : Complex.I^4 = 1 := by norm_num [pow_succ, Complex.I_mul_I]
  have hm1 : StrictMono (fun n : ℕ => 4*n+3) := by
    intro m n hmn
    dsimp
    omega
  have hm2 : StrictMono (fun n : ℕ => 4*n+1) := by
    intro m n hmn
    dsimp
    omega
  have hsub1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 p) := by
    convert hlim.comp hm1.tendsto_atTop using 1
    ext n
    dsimp [Function.comp_def, ImaginaryPowerSequence]
    rw [show 4*n+3+1 = 4*(n+1) by omega, pow_mul, h4, one_pow]
  have hsub2 : Tendsto (fun _ : ℕ => (-1 : ℂ)) atTop (𝓝 p) := by
    convert hlim.comp hm2.tendsto_atTop using 1
    ext n
    dsimp [Function.comp_def, ImaginaryPowerSequence]
    rw [show 4*n+1+1 = 4*n+2 by omega, pow_add, pow_mul, h4, one_pow, one_mul]
    norm_num [Complex.I_sq]
  have hp1 : p = 1 := tendsto_nhds_unique hsub1 tendsto_const_nhds
  have hp2 : p = -1 := tendsto_nhds_unique hsub2 tendsto_const_nhds
  norm_num [hp1] at hp2

theorem pma3_1_examples :
    (ConvergesTo ReciprocalSequence 0 ∧ SequenceBounded ReciprocalSequence ∧
      (range ReciprocalSequence).Infinite) ∧
    (SequenceDiverges SquareSequence ∧ ¬ SequenceBounded SquareSequence ∧
      (range SquareSequence).Infinite) ∧
    (ConvergesTo OscillatingReciprocalSequence 1 ∧
      SequenceBounded OscillatingReciprocalSequence ∧
      (range OscillatingReciprocalSequence).Infinite) ∧
    (SequenceDiverges ImaginaryPowerSequence ∧ SequenceBounded ImaginaryPowerSequence ∧
      (range ImaginaryPowerSequence).Finite) ∧
    (ConvergesTo ConstantOneSequence 1 ∧ SequenceBounded ConstantOneSequence ∧
      (range ConstantOneSequence).Finite) := by
  have recBound : SequenceBounded ReciprocalSequence :=
    (pma3_1_bounded_reference _).mpr
      (Metric.isBounded_range_of_tendsto _ reciprocalSequence_tendsto)
  have oscBound : SequenceBounded OscillatingReciprocalSequence :=
    (pma3_1_bounded_reference _).mpr
      (Metric.isBounded_range_of_tendsto _ oscillatingReciprocalSequence_tendsto)
  have sqDiv : SequenceDiverges SquareSequence := by
    rintro ⟨p, hp⟩
    exact squareSequence_not_bounded ((pma3_1_bounded_reference _).mpr
      (Metric.isBounded_range_of_tendsto _ ((pma3_1_reference _ _).mp hp)))
  have constLim : Tendsto ConstantOneSequence atTop (𝓝 1) := tendsto_const_nhds
  exact ⟨⟨(pma3_1_reference _ _).mpr reciprocalSequence_tendsto, recBound,
      Set.infinite_range_of_injective reciprocalSequence_injective⟩,
    ⟨sqDiv, squareSequence_not_bounded, Set.infinite_range_of_injective squareSequence_injective⟩,
    ⟨(pma3_1_reference _ _).mpr oscillatingReciprocalSequence_tendsto, oscBound,
      Set.infinite_range_of_injective oscillatingReciprocalSequence_injective⟩,
    ⟨imaginaryPowerSequence_diverges,
      (pma3_1_bounded_reference _).mpr imaginaryPowerSequence_finite.isBounded,
      imaginaryPowerSequence_finite⟩,
    ⟨(pma3_1_reference _ _).mpr constLim,
      (pma3_1_bounded_reference _).mpr (Metric.isBounded_range_of_tendsto _ constLim),
      by change (range (fun _ : ℕ => (1 : ℂ))).Finite; simp⟩⟩

theorem pma3_1_ambient :
    ConvergesTo (fun n : ℕ => (1/(n+1 : ℝ))) 0 ∧
    SequenceDiverges PositiveReciprocalSequence := by
  have hreal := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine ⟨(pma3_1_reference _ _).mpr hreal, ?_⟩
  rintro ⟨p, hp⟩
  have hval : Tendsto (fun n : ℕ => (1/(n+1 : ℝ))) atTop (𝓝 p.val) := by
    simpa [Function.comp_def, PositiveReciprocalSequence] using
      (continuous_subtype_val.tendsto p).comp ((pma3_1_reference _ _).mp hp)
  have heq : p.val = 0 := tendsto_nhds_unique hval hreal
  exact (ne_of_gt p.property) heq
/-! ### PMA-3.2: neighborhoods, uniqueness, boundedness, and limit points. -/

theorem pma3_2_neighborhood {X : Type*} [MetricSpace X] (s : ℕ → X) (p : X) :
    ConvergesTo s p ↔ ∀ r > 0, {n | s n ∉ Chapter02.neighborhood p r}.Finite := by
  rw [pma3_1_reference, Metric.tendsto_nhds]
  simp only [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite,
    Chapter02.neighborhood, mem_ofPred_eq, dist_comm]

theorem pma3_2_unique {X : Type*} [MetricSpace X] {s : ℕ → X} {p q : X}
    (hp : ConvergesTo s p) (hq : ConvergesTo s q) : p = q :=
  tendsto_nhds_unique ((pma3_1_reference _ _).mp hp) ((pma3_1_reference _ _).mp hq)

theorem pma3_2_bounded {X : Type*} [MetricSpace X] {s : ℕ → X}
    (h : SequenceConverges s) : SequenceBounded s := by
  obtain ⟨p, hp⟩ := h
  exact (pma3_1_bounded_reference _).mpr
    (Metric.isBounded_range_of_tendsto _ ((pma3_1_reference _ _).mp hp))

theorem pma3_2_limitPoint {X : Type*} [MetricSpace X] {E : Set X} {p : X}
    (h : Chapter02.IsLimitPoint p E) :
    ∃ s : ℕ → X, (∀ n, s n ∈ E) ∧ ConvergesTo s p := by
  classical
  have hex (n : ℕ) : ∃ q ∈ E, q ≠ p ∧ dist p q < 1/(n+1 : ℝ) :=
    h _ (by positivity)
  choose s hE hne hd using hex
  refine ⟨s, hE, (pma3_1_reference _ _).mpr ?_⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => (by simpa only [dist_comm] using (hd n).le))
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ### PMA-3.3: algebra of complex limits. -/

theorem pma3_3 {s t : ℕ → ℂ} {a b : ℂ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) (c : ℂ) :
    ConvergesTo (fun n => s n + t n) (a+b) ∧
    ConvergesTo (fun n => c * s n) (c*a) ∧
    ConvergesTo (fun n => c + s n) (c+a) ∧
    ConvergesTo (fun n => s n * t n) (a*b) := by
  have hs' := (pma3_1_reference _ _).mp hs
  have ht' := (pma3_1_reference _ _).mp ht
  exact ⟨(pma3_1_reference _ _).mpr (hs'.add ht'),
    (pma3_1_reference _ _).mpr (tendsto_const_nhds.mul hs'),
    (pma3_1_reference _ _).mpr (tendsto_const_nhds.add hs'),
    (pma3_1_reference _ _).mpr (hs'.mul ht')⟩

theorem pma3_3_reciprocal {s : ℕ → ℂ} {a : ℂ}
    (hs : ConvergesTo s a) (_hn : ∀ n, s n ≠ 0) (ha : a ≠ 0) :
    ConvergesTo (fun n => (s n)⁻¹) a⁻¹ :=
  (pma3_1_reference _ _).mpr (((pma3_1_reference _ _).mp hs).inv₀ ha)
/-! ### PMA-3.4: Euclidean coordinates and algebra. -/

theorem pma3_4_coordinates {k : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin k))
    (p : EuclideanSpace ℝ (Fin k)) :
    ConvergesTo s p ↔ ∀ i, ConvergesTo (fun n => s n i) (p i) := by
  constructor
  · intro hs i
    exact (pma3_1_reference _ _).mpr
      (((PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) i).tendsto p).comp
        ((pma3_1_reference _ _).mp hs))
  · intro hs
    have hpi : Tendsto (fun n => WithLp.ofLp (s n)) atTop (𝓝 (WithLp.ofLp p)) :=
      tendsto_pi_nhds.mpr (fun i => (pma3_1_reference _ _).mp (hs i))
    exact (pma3_1_reference _ _).mpr
      (((PiLp.continuous_toLp 2 (fun _ : Fin k => ℝ)).tendsto _).comp hpi)

theorem pma3_4_algebra {k : ℕ} {s t : ℕ → EuclideanSpace ℝ (Fin k)}
    {a b : EuclideanSpace ℝ (Fin k)} {β : ℕ → ℝ} {c : ℝ}
    (hs : ConvergesTo s a) (ht : ConvergesTo t b) (hc : ConvergesTo β c) :
    ConvergesTo (fun n => s n + t n) (a+b) ∧
    ConvergesTo (fun n => inner ℝ (s n) (t n)) (inner ℝ a b) ∧
    ConvergesTo (fun n => β n • s n) (c • a) := by
  have hs' := (pma3_1_reference _ _).mp hs
  have ht' := (pma3_1_reference _ _).mp ht
  have hc' := (pma3_1_reference _ _).mp hc
  exact ⟨(pma3_1_reference _ _).mpr (hs'.add ht'),
    (pma3_1_reference _ _).mpr (hs'.inner ht'),
    (pma3_1_reference _ _).mpr (hc'.smul hs')⟩

/-! ### PMA-3.5: subsequences and their limits. -/

def IsSubsequenceIndex (φ : ℕ → ℕ) : Prop := StrictMono φ
def Subsequence {X : Type*} (s : ℕ → X) (φ : ℕ → ℕ) : ℕ → X := s ∘ φ
def IsSubsequentialLimit {X : Type*} [TopologicalSpace X] (s : ℕ → X) (p : X) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (s ∘ φ) atTop (𝓝 p)

theorem pma3_5 {X : Type*} [MetricSpace X] (s : ℕ → X) (p : X) :
    ConvergesTo s p ↔
      ∀ φ : ℕ → ℕ, IsSubsequenceIndex φ → ConvergesTo (Subsequence s φ) p := by
  constructor
  · intro hs φ hφ
    exact (pma3_1_reference _ _).mpr
      (((pma3_1_reference _ _).mp hs).comp hφ.tendsto_atTop)
  · intro h
    exact h id strictMono_id

theorem pma3_5_reference {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    (s : ℕ → X) (p : X) : IsSubsequentialLimit s p ↔ MapClusterPt p atTop s := by
  constructor
  · rintro ⟨φ, hφ, hp⟩
    exact hp.mapClusterPt.of_comp hφ.tendsto_atTop
  · exact MapClusterPt.tendsto_subseq

/-! ### PMA-3.6: compact and bounded Euclidean subsequences. -/

theorem pma3_6_compact {X : Type*} [MetricSpace X] {K : Set X}
    (hK : IsCompact K) (s : ℕ → X) (hs : ∀ n, s n ∈ K) :
    ∃ p ∈ K, IsSubsequentialLimit s p := by
  obtain ⟨p, hp, φ, hφ, hlim⟩ := hK.tendsto_subseq hs
  exact ⟨p, hp, φ, hφ, hlim⟩

theorem pma3_6_euclidean {k : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin k))
    (h : SequenceBounded s) : ∃ p, IsSubsequentialLimit s p := by
  obtain ⟨p, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded
    ((pma3_1_bounded_reference _).mp h) (fun n => mem_range_self n)
  exact ⟨p, φ, hφ, hlim⟩

/-! ### PMA-3.7: the set of subsequential limits is closed. -/

theorem pma3_7 {X : Type*} [MetricSpace X] (s : ℕ → X) :
    IsClosed {p | IsSubsequentialLimit s p} := by
  simpa only [pma3_5_reference, MapClusterPt] using
    (isClosed_setOfPred_clusterPt (f := map s atTop))

/-! ### PMA-3.8: the literal Cauchy criterion. -/

def RudinCauchy {X : Type*} [MetricSpace X] (s : ℕ → X) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (s m) (s n) < ε

theorem pma3_8_reference {X : Type*} [MetricSpace X] (s : ℕ → X) :
    RudinCauchy s ↔ CauchySeq s := Metric.cauchySeq_iff.symm
/-! ### PMA-3.9: extended diameter and the tail-diameter criterion. -/

def RudinDiameter {X : Type*} [MetricSpace X] (E : Set X) : ENNReal := Metric.ediam E
def TailRange {X : Type*} (s : ℕ → X) (N : ℕ) : Set X := s '' Ici N

theorem pma3_9_reference {X : Type*} [MetricSpace X] (E : Set X) :
    RudinDiameter E = sSup (Set.image2 edist E E) := Metric.ediam_eq_sSup E

theorem pma3_9_tail {X : Type*} [MetricSpace X] (s : ℕ → X) :
    RudinCauchy s ↔ Tendsto (fun N => RudinDiameter (TailRange s N)) atTop (𝓝 0) := by
  rw [pma3_8_reference, EMetric.cauchySeq_iff, ENNReal.tendsto_nhds_zero]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine eventually_atTop.mpr ⟨N, fun M hM => ?_⟩
    apply Metric.ediam_le
    rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩
    exact (hN i (hM.trans hi) j (hM.trans hj)).le
  · intro h ε hε
    obtain ⟨δ, hδ, hδε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h δ hδ)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hm' : s m ∈ TailRange s N := ⟨m, hm, rfl⟩
    have hn' : s n ∈ TailRange s N := ⟨n, hn, rfl⟩
    exact lt_of_le_of_lt ((Metric.edist_le_ediam_of_mem hm' hn').trans (hN N le_rfl)) hδε

/-! ### PMA-3.10: closure diameters and singleton compact intersections. -/

theorem pma3_10_closure {X : Type*} [MetricSpace X] (E : Set X) :
    RudinDiameter (closure E) = RudinDiameter E := Metric.ediam_closure E

theorem pma3_10_intersection {X : Type*} [MetricSpace X] (K : ℕ → Set X)
    (hc : ∀ n, IsCompact (K n)) (hne : ∀ n, (K n).Nonempty)
    (hdec : ∀ n, K (n+1) ⊆ K n)
    (hd : Tendsto (fun n => RudinDiameter (K n)) atTop (𝓝 0)) :
    ∃! p, p ∈ ⋂ n, K n := by
  obtain ⟨p, hp⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hdec hne (hc 0) (fun n => (hc n).isClosed)
  refine ⟨p, hp, fun q hq => ?_⟩
  have hbound (n : ℕ) : edist q p ≤ RudinDiameter (K n) :=
    Metric.edist_le_ediam_of_mem (mem_iInter.mp hq n) (mem_iInter.mp hp n)
  have hzero : edist q p ≤ 0 := ge_of_tendsto hd (Eventually.of_forall hbound)
  exact edist_eq_zero.mp (le_antisymm hzero bot_le)

/-! ### PMA-3.11: convergence and Cauchy sequences. -/

theorem pma3_11_convergent {X : Type*} [MetricSpace X] {s : ℕ → X}
    (h : SequenceConverges s) : RudinCauchy s := by
  obtain ⟨p, hp⟩ := h
  exact (pma3_8_reference _).mpr ((pma3_1_reference _ _).mp hp).cauchySeq

theorem pma3_11_compact {X : Type*} [MetricSpace X] [CompactSpace X]
    {s : ℕ → X} (h : RudinCauchy s) : SequenceConverges s := by
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete ((pma3_8_reference _).mp h)
  exact ⟨p, (pma3_1_reference _ _).mpr hp⟩

theorem pma3_11_euclidean {k : ℕ} (s : ℕ → EuclideanSpace ℝ (Fin k)) :
    SequenceConverges s ↔ RudinCauchy s := by
  refine ⟨pma3_11_convergent, fun h => ?_⟩
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete ((pma3_8_reference _).mp h)
  exact ⟨p, (pma3_1_reference _ _).mpr hp⟩

/-! ### PMA-3.12: completeness, closed subspaces, and rational incompleteness. -/

def RudinComplete (X : Type*) [MetricSpace X] : Prop :=
  ∀ s : ℕ → X, RudinCauchy s → SequenceConverges s

theorem pma3_12_reference (X : Type*) [MetricSpace X] :
    RudinComplete X ↔ CompleteSpace X := by
  constructor
  · intro h
    apply Metric.complete_of_cauchySeq_tendsto
    intro s hs
    obtain ⟨p, hp⟩ := h s ((pma3_8_reference _).mpr hs)
    exact ⟨p, (pma3_1_reference _ _).mp hp⟩
  · intro h
    let := h
    intro s hs
    obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete ((pma3_8_reference _).mp hs)
    exact ⟨p, (pma3_1_reference _ _).mpr hp⟩

theorem pma3_12_compact (X : Type*) [MetricSpace X] [CompactSpace X] :
    RudinComplete X := (pma3_12_reference _).mpr inferInstance

theorem pma3_12_euclidean (k : ℕ) : RudinComplete (EuclideanSpace ℝ (Fin k)) :=
  (pma3_12_reference _).mpr inferInstance

theorem pma3_12_closed {X : Type*} [MetricSpace X] (hX : RudinComplete X)
    {E : Set X} (hE : IsClosed E) : RudinComplete E := by
  let : CompleteSpace X := (pma3_12_reference _).mp hX
  exact (pma3_12_reference _).mpr hE.isComplete.completeSpace_coe

theorem pma3_12_rational : ¬ RudinComplete ℚ := by
  intro h
  let : CompleteSpace ℚ := (pma3_12_reference _).mp h
  have hclosed : IsClosed (range ((↑) : ℚ → ℝ)) :=
    Rat.isUniformEmbedding_coe_real.isClosedEmbedding.isClosed_range
  have hfull : range ((↑) : ℚ → ℝ) = univ := by
    have hdense : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
    simpa only [hclosed.closure_eq] using hdense.closure_range
  apply irrational_sqrt_two
  rw [hfull]
  exact mem_univ _

/-! ### PMA-3.13: non-strict real monotonicity. -/

def IncreasingSequence (s : ℕ → ℝ) : Prop := ∀ n, s n ≤ s (n+1)
def DecreasingSequence (s : ℕ → ℝ) : Prop := ∀ n, s (n+1) ≤ s n
def MonotonicSequence (s : ℕ → ℝ) : Prop := IncreasingSequence s ∨ DecreasingSequence s

theorem pma3_13_increasing_reference (s : ℕ → ℝ) :
    IncreasingSequence s ↔ Monotone s := by
  exact ⟨monotone_nat_of_le_succ, fun h n => h (Nat.le_succ n)⟩

theorem pma3_13_decreasing_reference (s : ℕ → ℝ) :
    DecreasingSequence s ↔ Antitone s := by
  exact ⟨antitone_nat_of_succ_le, fun h n => h (Nat.le_succ n)⟩

/-! ### PMA-3.14: convergence of bounded monotonic real sequences. -/

theorem pma3_14 (s : ℕ → ℝ) (hm : MonotonicSequence s) :
    SequenceConverges s ↔ SequenceBounded s := by
  refine ⟨pma3_2_bounded, fun hb => ?_⟩
  have hbound := (pma3_1_bounded_reference _).mp hb
  obtain ⟨R, hR⟩ := hbound.exists_norm_le
  have hupper : BddAbove (range s) := by
    refine ⟨R, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hR _ (mem_range_self n))
  have hlower : BddBelow (range s) := by
    refine ⟨-R, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hnorm := hR _ (mem_range_self n)
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hnorm)).1
  rcases hm with hi | hd
  · exact ⟨⨆ n, s n, (pma3_1_reference _ _).mpr
      (tendsto_atTop_ciSup ((pma3_13_increasing_reference _).mp hi) hupper)⟩
  · exact ⟨⨅ n, s n, (pma3_1_reference _ _).mpr
      (tendsto_atTop_ciInf ((pma3_13_decreasing_reference _).mp hd) hlower)⟩
/-! ### PMA-3.15: limits to the two infinities. -/

def TendsToPositiveInfinity (s : ℕ → ℝ) : Prop := ∀ M : ℝ, ∃ N, ∀ n ≥ N, M ≤ s n
def TendsToNegativeInfinity (s : ℕ → ℝ) : Prop := ∀ M : ℝ, ∃ N, ∀ n ≥ N, s n ≤ M

theorem pma3_15_positive_reference (s : ℕ → ℝ) :
    TendsToPositiveInfinity s ↔ Tendsto s atTop atTop := by
  simp only [TendsToPositiveInfinity, tendsto_atTop, eventually_atTop]

theorem pma3_15_negative_reference (s : ℕ → ℝ) :
    TendsToNegativeInfinity s ↔ Tendsto s atTop atBot := by
  simp only [TendsToNegativeInfinity, tendsto_atBot, eventually_atTop]

theorem pma3_15_positive_ereal (s : ℕ → ℝ) :
    TendsToPositiveInfinity s ↔ Tendsto (fun n => (s n : EReal)) atTop (𝓝 ⊤) := by
  rw [pma3_15_positive_reference, EReal.tendsto_coe_nhds_top_iff]

theorem pma3_15_negative_ereal (s : ℕ → ℝ) :
    TendsToNegativeInfinity s ↔ Tendsto (fun n => (s n : EReal)) atTop (𝓝 ⊥) := by
  rw [pma3_15_negative_reference, EReal.tendsto_coe_nhds_bot_iff]

/-! ### PMA-3.16: upper and lower limits of real sequences. -/

def ExtendedSubsequentialLimits (s : ℕ → ℝ) : Set EReal :=
  {x | IsSubsequentialLimit (fun n => (s n : EReal)) x}
def UpperLimit (s : ℕ → ℝ) : EReal := sSup (ExtendedSubsequentialLimits s)
def LowerLimit (s : ℕ → ℝ) : EReal := sInf (ExtendedSubsequentialLimits s)

theorem pma3_16_upper_reference (s : ℕ → ℝ) :
    UpperLimit s = limsup (fun n => (s n : EReal)) atTop := by
  unfold UpperLimit ExtendedSubsequentialLimits
  simp_rw [pma3_5_reference]
  exact (isGreatest_mapClusterPt_limsup (u := fun n => (s n : EReal)) (f := atTop)).csSup_eq

theorem pma3_16_lower_reference (s : ℕ → ℝ) :
    LowerLimit s = liminf (fun n => (s n : EReal)) atTop := by
  unfold LowerLimit ExtendedSubsequentialLimits
  simp_rw [pma3_5_reference]
  exact (isLeast_mapClusterPt_liminf (u := fun n => (s n : EReal)) (f := atTop)).csInf_eq

/-! ### PMA-3.17: the characterizations of upper and lower limits. -/

def IsUpperLimitCharacterization (s : ℕ → ℝ) (u : EReal) : Prop :=
  u ∈ ExtendedSubsequentialLimits s ∧
  ∀ x : EReal, u < x → ∃ N, ∀ n ≥ N, (s n : EReal) < x
def IsLowerLimitCharacterization (s : ℕ → ℝ) (l : EReal) : Prop :=
  l ∈ ExtendedSubsequentialLimits s ∧
  ∀ x : EReal, x < l → ∃ N, ∀ n ≥ N, x < (s n : EReal)

theorem pma3_17_upper (s : ℕ → ℝ) :
    IsUpperLimitCharacterization s (UpperLimit s) ∧
    ∀ u, IsUpperLimitCharacterization s u → u = UpperLimit s := by
  constructor
  · constructor
    · change IsSubsequentialLimit (fun n => (s n : EReal)) (UpperLimit s)
      rw [pma3_5_reference, pma3_16_upper_reference]
      exact MapClusterPt.limsup
    · intro x hx
      rw [pma3_16_upper_reference] at hx
      exact eventually_atTop.mp (eventually_lt_of_limsup_lt hx)
  · rintro u ⟨hu, hbound⟩
    apply le_antisymm
    · rw [pma3_16_upper_reference]
      exact ((pma3_5_reference _ _).mp hu).le_limsup
    · rw [pma3_16_upper_reference]
      exact (limsup_le_iff).mpr (fun x hx => eventually_atTop.mpr (hbound x hx))

theorem pma3_17_lower (s : ℕ → ℝ) :
    IsLowerLimitCharacterization s (LowerLimit s) ∧
    ∀ l, IsLowerLimitCharacterization s l → l = LowerLimit s := by
  constructor
  · constructor
    · change IsSubsequentialLimit (fun n => (s n : EReal)) (LowerLimit s)
      rw [pma3_5_reference, pma3_16_lower_reference]
      exact MapClusterPt.liminf
    · intro x hx
      rw [pma3_16_lower_reference] at hx
      exact eventually_atTop.mp (eventually_lt_of_lt_liminf hx)
  · rintro l ⟨hl, hbound⟩
    apply le_antisymm
    · rw [pma3_16_lower_reference]
      exact (le_liminf_iff).mpr (fun x hx => eventually_atTop.mpr (hbound x hx))
    · rw [pma3_16_lower_reference]
      exact ((pma3_5_reference _ _).mp hl).liminf_le

/-! ### PMA-3.18: rational, oscillatory, and convergent examples. -/

private theorem rational_tail_dense (q : ℕ → ℚ) (hq : Function.Surjective q) (N : ℕ) :
    Dense ((fun n => ((q n : ℝ) : EReal)) '' Set.Ici N) := by
  let f : ℕ → EReal := fun n => ((q n : ℝ) : EReal)
  have hd : Dense (range f) := by
    change Dense (range ((fun r : ℚ => ((r : ℝ) : EReal)) ∘ q))
    rw [Set.range_comp, hq.range_eq, Set.image_univ]
    exact EReal.denseRange_ratCast
  have hfin : (f '' Set.Iio N).Finite := (Set.finite_Iio N).image f
  have hd' := hd.sdiff_finite hfin
  apply hd'.mono
  intro x hx
  rcases hx.1 with ⟨n, rfl⟩
  have hn : N ≤ n := by
    by_contra h
    exact hx.2 ⟨n, by simp only [Set.mem_Iio]; omega, rfl⟩
  exact ⟨n, Set.mem_Ici.mpr hn, rfl⟩

private theorem rational_cluster_every_ereal (q : ℕ → ℚ) (hq : Function.Surjective q)
    (x : EReal) : MapClusterPt x atTop (fun n => ((q n : ℝ) : EReal)) := by
  rw [mapClusterPt_atTop_iff_forall_mem_closure]
  intro N
  rw [(rational_tail_dense q hq N).closure_eq]
  trivial

theorem pma3_18_rational (q : ℕ → ℚ) (hq : Function.Surjective q) :
    (∀ x : ℝ, IsSubsequentialLimit (fun n => (q n : ℝ)) x) ∧
    UpperLimit (fun n => (q n : ℝ)) = ⊤ ∧ LowerLimit (fun n => (q n : ℝ)) = ⊥ := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    obtain ⟨φ, hφ, ht⟩ := (pma3_5_reference _ (x : EReal)).mpr
      (rational_cluster_every_ereal q hq x)
    refine ⟨φ, hφ, ?_⟩
    apply EReal.tendsto_coe.mp
    simpa [Function.comp_def] using ht
  · apply eq_top_iff.mpr
    exact le_sSup ((pma3_5_reference _ ⊤).mpr (rational_cluster_every_ereal q hq ⊤))
  · apply eq_bot_iff.mpr
    exact sInf_le ((pma3_5_reference _ ⊥).mpr (rational_cluster_every_ereal q hq ⊥))

def AlternatingLimitSequence (n : ℕ) : ℝ :=
  (-1 : ℝ)^(n+1) / (1 + 1/(n+1 : ℝ))

private theorem alternating_limit_sequence_bounds (n : ℕ) :
    -1 ≤ AlternatingLimitSequence n ∧ AlternatingLimitSequence n ≤ 1 := by
  have hpos : 0 < (1 + 1/(n+1 : ℝ)) := by positivity
  have hge : 1 ≤ (1 + 1/(n+1 : ℝ)) := by
    have hnonneg : 0 ≤ 1/(n+1 : ℝ) := by positivity
    linarith
  apply abs_le.mp
  calc
    |AlternatingLimitSequence n| = 1/(1 + 1/(n+1 : ℝ)) := by
      simp only [AlternatingLimitSequence, abs_div, abs_pow, abs_neg, abs_one,
        one_pow, abs_of_pos hpos]
    _ ≤ 1 := by
      simpa using one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hge

private theorem alternating_subsequential_bounds {x : EReal}
    (hx : x ∈ ExtendedSubsequentialLimits AlternatingLimitSequence) : -1 ≤ x ∧ x ≤ 1 := by
  obtain ⟨φ, hφ, ht⟩ := hx
  apply IsClosed.mem_of_tendsto isClosed_Icc ht
  apply Eventually.of_forall
  intro n
  constructor
  · change (-1 : EReal) ≤ (AlternatingLimitSequence (φ n) : EReal)
    simpa only [EReal.coe_neg, EReal.coe_one] using
      EReal.coe_le_coe_iff.mpr (alternating_limit_sequence_bounds (φ n)).1
  · change (AlternatingLimitSequence (φ n) : EReal) ≤ 1
    simpa only [EReal.coe_one] using
      EReal.coe_le_coe_iff.mpr (alternating_limit_sequence_bounds (φ n)).2

private theorem alternating_reciprocal_denominator_tendsto :
    Tendsto (fun n : ℕ => 1/(1 + 1/(n+1 : ℝ))) atTop (𝓝 1) := by
  have hden : Tendsto (fun n : ℕ => 1 + 1/(n+1 : ℝ)) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  convert hden.inv₀ (show (1 : ℝ) ≠ 0 by norm_num) using 1
  ext n
  simp only [one_div]
  simp

private theorem alternating_limit_positive_subsequence :
    IsSubsequentialLimit (fun n => (AlternatingLimitSequence n : EReal)) 1 := by
  have hb := alternating_reciprocal_denominator_tendsto
  have hφ : StrictMono (fun n : ℕ => 2*n+1) := by
    intro a b hab
    change 2*a+1 < 2*b+1
    omega
  have ht : Tendsto (AlternatingLimitSequence ∘ fun n : ℕ => 2*n+1) atTop (𝓝 1) := by
    convert hb.comp hφ.tendsto_atTop using 1
    ext n
    simp [AlternatingLimitSequence, pow_add, pow_mul]
  refine ⟨fun n => 2*n+1, hφ, ?_⟩
  simpa [Function.comp_def] using EReal.tendsto_coe.mpr ht

private theorem alternating_limit_negative_subsequence :
    IsSubsequentialLimit (fun n => (AlternatingLimitSequence n : EReal)) (-1) := by
  have hb := alternating_reciprocal_denominator_tendsto
  have hφ : StrictMono (fun n : ℕ => 2*n) := by
    intro a b hab
    change 2*a < 2*b
    omega
  have ht : Tendsto (AlternatingLimitSequence ∘ fun n : ℕ => 2*n) atTop (𝓝 (-1)) := by
    convert (hb.comp hφ.tendsto_atTop).neg using 1
    ext n
    simp [AlternatingLimitSequence, pow_add, pow_mul, div_eq_mul_inv]
  refine ⟨fun n => 2*n, hφ, ?_⟩
  simpa [Function.comp_def] using EReal.tendsto_coe.mpr ht

theorem pma3_18_alternating :
    UpperLimit AlternatingLimitSequence = 1 ∧ LowerLimit AlternatingLimitSequence = -1 := by
  constructor
  · apply le_antisymm
    · exact sSup_le (fun x hx => (alternating_subsequential_bounds hx).2)
    · exact le_sSup alternating_limit_positive_subsequence
  · apply le_antisymm
    · exact sInf_le alternating_limit_negative_subsequence
    · exact le_sInf (fun x hx => (alternating_subsequential_bounds hx).1)

theorem pma3_18_convergence (s : ℕ → ℝ) (x : ℝ) :
    ConvergesTo s x ↔ UpperLimit s = (x : EReal) ∧ LowerLimit s = (x : EReal) := by
  rw [pma3_1_reference, pma3_16_upper_reference, pma3_16_lower_reference]
  constructor
  · intro ht
    have he := EReal.tendsto_coe.mpr ht
    exact ⟨he.limsup_eq, he.liminf_eq⟩
  · rintro ⟨hupper, hlower⟩
    exact EReal.tendsto_coe.mp (tendsto_of_liminf_eq_limsup hlower hupper)
/-! ### PMA-3.19: eventual inequalities compare upper and lower limits. -/

theorem pma3_19 (s t : ℕ → ℝ) (h : ∃ N, ∀ n ≥ N, s n ≤ t n) :
    LowerLimit s ≤ LowerLimit t ∧ UpperLimit s ≤ UpperLimit t := by
  have he : ∀ᶠ n in atTop, (s n : EReal) ≤ (t n : EReal) := by
    obtain ⟨N, hN⟩ := h
    exact eventually_atTop.mpr ⟨N, fun n hn => EReal.coe_le_coe_iff.mpr (hN n hn)⟩
  rw [pma3_16_lower_reference, pma3_16_lower_reference,
    pma3_16_upper_reference, pma3_16_upper_reference]
  exact ⟨liminf_le_liminf he, limsup_le_limsup he⟩
/-! ### PMA-3.20: the five special sequence limits, with positive indices. -/

private theorem positive_natCast_tendsto :
    Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop := by
  simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)

theorem pma3_20_reciprocal (p : ℝ) (hp : 0 < p) :
    ConvergesTo (fun n : ℕ => 1 / (n+1 : ℝ)^p) 0 := by
  apply (pma3_1_reference _ _).mpr
  convert ((tendsto_rpow_atTop hp).comp positive_natCast_tendsto).inv_tendsto_atTop using 1
  ext n
  simp only [one_div]
  rfl

theorem pma3_20_root_const (p : ℝ) (hp : 0 < p) :
    ConvergesTo (fun n : ℕ => p^(1/(n+1 : ℝ))) 1 := by
  apply (pma3_1_reference _ _).mpr
  simpa only [Function.comp_def, Real.rpow_zero] using
    (Real.continuousAt_const_rpow (ne_of_gt hp)).tendsto.comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem pma3_20_root_index :
    ConvergesTo (fun n : ℕ => (n+1 : ℝ)^(1/(n+1 : ℝ))) 1 := by
  exact (pma3_1_reference _ _).mpr (tendsto_rpow_div.comp positive_natCast_tendsto)

theorem pma3_20_power_over_exp (p α : ℝ) (hp : 0 < p) :
    ConvergesTo (fun n : ℕ => (n+1 : ℝ)^α / (1+p)^(n+1)) 0 := by
  apply (pma3_1_reference _ _).mpr
  have hb : 0 < Real.log (1+p) := Real.log_pos (by linarith)
  have h := (tendsto_exp_mul_div_rpow_atTop α (Real.log (1+p)) hb).inv_tendsto_atTop
  have hs := h.comp positive_natCast_tendsto
  convert hs using 1
  ext n
  change (n+1 : ℝ)^α / (1+p)^(n+1) =
    (Real.exp (Real.log (1+p) * (n+1 : ℝ)) / (n+1 : ℝ)^α)⁻¹
  rw [inv_div]
  congr 1
  rw [mul_comm]
  rw [show (n : ℝ) + 1 = ((n+1 : ℕ) : ℝ) by norm_cast]
  rw [Real.exp_nat_mul, Real.exp_log (by linarith)]

theorem pma3_20_geometric (x : ℝ) (hx : |x| < 1) :
    ConvergesTo (fun n : ℕ => x^(n+1)) 0 := by
  exact (pma3_1_reference _ _).mpr
    ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one hx).comp (tendsto_add_atTop_nat 1))
/-! ### PMA-3.21: Ordered series definitions and statement contracts.

`PartialSums a N` contains the first `N` zero-indexed terms. Rudin explicitly
allows indexing from zero. Positive-indexed notation is represented by `a (n+1)`;
its exact comparison to sums from 1 through N is part of the definition contract.
Mathlib's conditional summation filter, rather than its default unconditional
filter, is the reference for ordinary series convergence.
-/
def BlockSum {V : Type*} [AddCommMonoid V] (a : ℕ → V) (p q : ℕ) : V :=
  ∑ k ∈ Finset.Icc p q, a k

def PartialSums {V : Type*} [AddCommMonoid V] (a : ℕ → V) (N : ℕ) : V :=
  ∑ n ∈ Finset.range N, a n

def SeriesHasSum {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (a : ℕ → V) (s : V) : Prop := Tendsto (PartialSums a) atTop (𝓝 s)

def SeriesConverges {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (a : ℕ → V) : Prop := ∃ s, SeriesHasSum a s

def SeriesDiverges {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (a : ℕ → V) : Prop := ¬ SeriesConverges a

def Statement_3_21 {V : Type*} [AddCommMonoid V] [TopologicalSpace V] : Prop :=
  (∀ (a : ℕ → V) N, PartialSums (fun n => a (n+1)) N = BlockSum a 1 N) ∧
  (∀ (a : ℕ → V) s, SeriesHasSum a s ↔
    HasSum a s (SummationFilter.conditional ℕ)) ∧
  (∀ a : ℕ → V, SeriesConverges a ↔ Summable a (SummationFilter.conditional ℕ))

/-! PMA-3.21 proof details: Verified ordered-series reference comparisons. -/
theorem partialSums_positive_index {V : Type*} [AddCommMonoid V]
    (a : ℕ → V) (N : ℕ) : PartialSums (fun n => a (n+1)) N = BlockSum a 1 N := by
  induction N with
  | zero => simp [PartialSums, BlockSum]
  | succ N ih =>
    change (∑ k ∈ Finset.range (N+1), a (k+1)) = ∑ k ∈ Finset.Icc 1 (N+1), a k
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (by omega)]
    exact congrArg (fun x => x + a (N+1)) ih

theorem seriesHasSum_iff_conditional {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (a : ℕ → V) (s : V) : SeriesHasSum a s ↔ HasSum a s (.conditional ℕ) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  rfl

theorem seriesConverges_iff_conditional {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (a : ℕ → V) : SeriesConverges a ↔ Summable a (.conditional ℕ) :=
  exists_congr fun s => seriesHasSum_iff_conditional a s

theorem node_3_21 {V : Type*} [AddCommMonoid V] [TopologicalSpace V] :
    Statement_3_21 (V := V) :=
  ⟨partialSums_positive_index, seriesHasSum_iff_conditional, seriesConverges_iff_conditional⟩

/-! ### PMA-3.22: Cauchy's criterion for ordinary complex series. -/
def SeriesCauchyCriterion (a : ℕ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → n ≤ m → ‖BlockSum a n m‖ ≤ ε

def Statement_3_22 : Prop :=
  ∀ a : ℕ → ℂ, SeriesConverges a ↔ SeriesCauchyCriterion a

/-! PMA-3.22 proof details: Verified ordinary Cauchy criterion. -/
theorem seriesConverges_iff_cauchySeq {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    (a : ℕ → V) : SeriesConverges a ↔ CauchySeq (PartialSums a) := by
  constructor
  · rintro ⟨s,hs⟩
    exact hs.cauchySeq
  · intro h
    exact cauchySeq_tendsto_of_complete h

theorem blockSum_eq_sub_partialSums {V : Type*} [AddCommGroup V]
    (a : ℕ → V) {n m : ℕ} (hnm : n ≤ m) :
    BlockSum a n m = PartialSums a (m+1) - PartialSums a n := by
  unfold BlockSum PartialSums
  have heq : Finset.Icc n m = Finset.Ico n (m+1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [heq,Finset.sum_Ico_eq_sub a (by omega)]

theorem node_3_22 : Statement_3_22 := by
  intro a
  rw [seriesConverges_iff_cauchySeq, Metric.cauchySeq_iff]
  constructor
  · intro h ε hε
    obtain ⟨N,hN⟩ := h ε hε
    refine ⟨N,?_⟩
    intro n m hn hnm
    rw [blockSum_eq_sub_partialSums a hnm]
    exact le_of_lt (by simpa only [dist_eq_norm] using hN (m+1) (by omega) n hn)
  · intro h ε hε
    obtain ⟨N,hN⟩ := h (ε/2) (by linarith)
    refine ⟨N,?_⟩
    intro m hm n hn
    rcases lt_trichotomy n m with hnm | rfl | hmn
    · have hh := hN n (m-1) hn (by omega)
      rw [blockSum_eq_sub_partialSums a (by omega),Nat.sub_add_cancel (by omega)] at hh
      exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hh) (by linarith)
    · simpa using hε
    · have hh := hN m (n-1) hm (by omega)
      rw [blockSum_eq_sub_partialSums a (by omega),Nat.sub_add_cancel (by omega)] at hh
      exact lt_of_le_of_lt (by simpa only [dist_eq_norm, norm_sub_rev] using hh) (by linarith)

/-! PMA-3.22 proof details: The necessary zero-term condition as a preliminary lemma. -/
theorem series_terms_tendsto_zero {V : Type*} [NormedAddCommGroup V]
    {a : ℕ → V} (h : SeriesConverges a) : Tendsto a atTop (𝓝 0) := by
  obtain ⟨s,hs⟩ := h
  have hs' : Tendsto (fun n => PartialSums a (n+1)) atTop (𝓝 s) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have hdiff := hs'.sub hs
  simpa only [PartialSums,Finset.sum_range_succ,add_sub_cancel_left,sub_self] using hdiff

/-! PMA-3.22 proof details: Finite prefixes do not change ordinary convergence. -/
theorem partialSums_shift {V : Type*} [AddCommGroup V] (a : ℕ → V) (N M : ℕ) :
    PartialSums (fun n => a (n+N)) M = PartialSums a (M+N) - PartialSums a N := by
  unfold PartialSums
  rw [Nat.add_comm M N,Finset.sum_range_add]
  simp only [add_sub_cancel_left]
  congr 1
  funext n
  rw [Nat.add_comm]

theorem seriesConverges_nat_add_iff {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) (N : ℕ) : SeriesConverges (fun n => a (n+N)) ↔ SeriesConverges a := by
  constructor
  · rintro ⟨s,hs⟩
    have hh := hs.add_const (PartialSums a N)
    have heq : (fun M => PartialSums (fun n => a (n+N)) M + PartialSums a N) =
        (fun M => PartialSums a (M+N)) := by
      funext M
      rw [partialSums_shift,sub_add_cancel]
    rw [heq] at hh
    exact ⟨_,(tendsto_add_atTop_iff_nat N).mp hh⟩
  · rintro ⟨s,hs⟩
    have hh := (hs.comp (tendsto_add_atTop_nat N)).sub_const (PartialSums a N)
    have heq : (fun M => PartialSums a (M+N) - PartialSums a N) =
        PartialSums (fun n => a (n+N)) := by
      funext M
      exact (partialSums_shift a N M).symm
    simp only [Function.comp_def] at hh
    rw [heq] at hh
    exact ⟨_,hh⟩

/-! ### PMA-3.24: Nonnegative series and bounded partial sums. -/
def Statement_3_24 : Prop :=
  ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) →
    (SeriesConverges a ↔ Bornology.IsBounded (Set.range (PartialSums a)))

/-! PMA-3.24 proof details: Nonnegative series are equivalent to bounded partial sums. -/
theorem seriesConverges_iff_summable_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) :
    SeriesConverges a ↔ Summable a := by
  unfold SeriesConverges
  exact exists_congr fun s => (hasSum_iff_tendsto_nat_of_nonneg ha s).symm

theorem seriesConverges_of_summable {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    {a : ℕ → V} (ha : Summable a) : SeriesConverges a :=
  ⟨_,ha.hasSum.tendsto_sum_nat⟩

theorem node_3_24 : Statement_3_24 := by
  intro a ha
  constructor
  · rintro ⟨s,hs⟩
    exact Metric.isBounded_range_of_tendsto (PartialSums a) hs
  · intro h
    rw [seriesConverges_iff_summable_nonneg ha]
    obtain ⟨C,hC⟩ := h.bddAbove
    apply summable_of_sum_range_le ha
    intro n
    exact hC (Set.mem_range_self n)

/-! ### PMA-3.25: Eventual comparison tests. -/
def Statement_3_25 : Prop :=
  (∀ (a : ℕ → ℂ) (c : ℕ → ℝ), (∀ᶠ n in atTop, ‖a n‖ ≤ c n) →
    SeriesConverges c → SeriesConverges a) ∧
  (∀ a d : ℕ → ℝ, (∀ᶠ n in atTop, 0 ≤ d n ∧ d n ≤ a n) →
    SeriesDiverges d → SeriesDiverges a)

/-! PMA-3.25 proof details: Verified eventual comparison tests. -/
theorem series_comparison {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {a : ℕ → V} {c : ℕ → ℝ} (hdom : ∀ᶠ n in atTop, ‖a n‖ ≤ c n)
    (hc : SeriesConverges c) : SeriesConverges a := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hdom
  have hc' := (seriesConverges_nat_add_iff c N).mpr hc
  rw [seriesConverges_iff_cauchySeq] at hc'
  have ha' : CauchySeq (PartialSums (fun n => a (n+N))) :=
    cauchySeq_range_of_norm_bounded hc' (fun n => hN (n+N) (by omega))
  apply (seriesConverges_nat_add_iff a N).mp
  exact (seriesConverges_iff_cauchySeq _).mpr ha'

theorem node_3_25 : Statement_3_25 := by
  refine ⟨fun _ _ h hc => series_comparison h hc, ?_⟩
  intro a d hdom hd ha
  apply hd
  apply series_comparison (c := a) _ ha
  filter_upwards [hdom] with n hn
  simpa only [Real.norm_eq_abs,abs_of_nonneg hn.1] using hn.2

/-! ### PMA-3.26: Nonnegative geometric series. -/
def Statement_3_26 : Prop :=
  (∀ x : ℝ, 0 ≤ x → x < 1 → SeriesHasSum (fun n : ℕ => x^n) (1/(1-x))) ∧
  (∀ x : ℝ, 1 ≤ x → SeriesDiverges (fun n : ℕ => x^n))

/-! PMA-3.26 proof details: Verified geometric series. -/
theorem node_3_26 : Statement_3_26 := by
  constructor
  · intro x hx hx1
    change Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, x^n) atTop (𝓝 (1/(1-x)))
    simpa only [one_div] using (hasSum_geometric_of_lt_one hx hx1).tendsto_sum_nat
  · intro x hx hconv
    have hz := series_terms_tendsto_zero hconv
    have hp : ∀ n : ℕ, 1 ≤ x^n := fun n => one_le_pow₀ hx
    have hh := hz.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨n,hn⟩ := hh.exists
    exact not_lt_of_ge (hp n) hn

/-! ### PMA-3.27: Cauchy condensation, with the source's positive indices. -/
def Statement_3_27 : Prop :=
  ∀ a : ℕ → ℝ, (∀ n, 1 ≤ n → 0 ≤ a n) →
    (∀ m n, 1 ≤ m → m ≤ n → a n ≤ a m) →
    (SeriesConverges (fun n => a (n+1)) ↔
      SeriesConverges (fun k : ℕ => (2 : ℝ)^k * a (2^k)))

/-! PMA-3.27 proof details: Verified condensation with positive-index coefficients. -/
theorem node_3_27 : Statement_3_27 := by
  intro a ha hmono
  have hnonneg : ∀ n : ℕ, 0 ≤ a (n+1) := fun n => ha (n+1) (by omega)
  have hdnonneg : ∀ k : ℕ, 0 ≤ (2 : ℝ)^k * a (2^k) := by
    intro k
    exact mul_nonneg (by positivity) (ha _ (Nat.one_le_two_pow))
  rw [seriesConverges_iff_summable_nonneg hnonneg,
    seriesConverges_iff_summable_nonneg hdnonneg,summable_nat_add_iff 1]
  symm
  exact summable_condensed_iff_of_eventually_nonneg
    (eventually_atTop.mpr ⟨1,ha⟩)
    (eventually_atTop.mpr ⟨1,fun n hn => hmono n (n+1) hn (by omega)⟩)

/-! ### PMA-3.28: Real p-series, including the divergent equality case. -/
def PSeriesTerm (p : ℝ) (n : ℕ) : ℝ := 1 / ((n+1 : ℝ) ^ p)

def Statement_3_28 : Prop := ∀ p : ℝ, SeriesConverges (PSeriesTerm p) ↔ 1 < p

/-! PMA-3.28 proof details: Verified p-series, supplying PMA-3.23's counterexample. -/
theorem pSeries_nonneg (p : ℝ) (n : ℕ) : 0 ≤ PSeriesTerm p n := by
  unfold PSeriesTerm
  positivity

theorem node_3_28 : Statement_3_28 := by
  intro p
  rw [seriesConverges_iff_summable_nonneg (pSeries_nonneg p)]
  unfold PSeriesTerm
  convert (summable_nat_add_iff (f := fun n : ℕ => 1/((n : ℝ)^p)) 1).trans
    (Real.summable_one_div_nat_rpow (p := p)) using 1; simp


/-! ### PMA-3.23: Terms of a convergent series and the harmonic counterexample. -/
def Statement_3_23 : Prop :=
  (∀ a : ℕ → ℂ, SeriesConverges a → Tendsto a atTop (𝓝 0)) ∧
  Tendsto (PSeriesTerm 1) atTop (𝓝 0) ∧ SeriesDiverges (PSeriesTerm 1)

/-! PMA-3.23 proof details: Verified zero-term condition and harmonic counterexample. -/
theorem node_3_23 : Statement_3_23 := by
  refine ⟨fun _ h => series_terms_tendsto_zero h, ?_, ?_⟩
  · have heq : PSeriesTerm 1 = (fun n : ℕ => 1/((n : ℝ)+1)) := by
      funext n
      simp [PSeriesTerm]
    rw [heq]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact (node_3_28 1).not.mpr (by norm_num)


/-! ### PMA-3.29: Logarithmic and iterated-logarithmic series. -/
def LogSeriesTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / ((n+2 : ℝ) * (Real.log (n+2 : ℝ))^p)

def IteratedLogSeriesTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / ((n+3 : ℝ) * Real.log (n+3 : ℝ) * (Real.log (Real.log (n+3 : ℝ)))^p)

def Statement_3_29 : Prop :=
  (∀ p : ℝ, SeriesConverges (LogSeriesTerm p) ↔ 1 < p) ∧
  SeriesDiverges (IteratedLogSeriesTerm 1) ∧ SeriesConverges (IteratedLogSeriesTerm 2)


def unshiftedLogTerm (p : ℝ) (n : ℕ) : ℝ := 1 / ((n : ℝ) * (Real.log (n : ℝ))^p)

lemma logTerm_nonneg (p : ℝ) (n : ℕ) : 0 ≤ LogSeriesTerm p n := by
  unfold LogSeriesTerm
  have hl : 0 < Real.log (n+2 : ℝ) := Real.log_pos (by norm_cast; omega)
  exact one_div_nonneg.mpr (mul_nonneg (by positivity) (Real.rpow_nonneg (le_of_lt hl) p))

lemma logTerm_summable_iff (p : ℝ) :
    SeriesConverges (LogSeriesTerm p) ↔ Summable (unshiftedLogTerm p) := by
  rw [seriesConverges_iff_summable_nonneg (logTerm_nonneg p)]
  change Summable (fun n : ℕ => 1 / ((n+2 : ℝ) * (Real.log (n+2 : ℝ))^p)) ↔ _
  simpa only [unshiftedLogTerm, Nat.cast_add, Nat.cast_ofNat] using
    (summable_nat_add_iff (f := unshiftedLogTerm p) 2)

lemma unshiftedLog_condensation (p : ℝ) (hp : 0 ≤ p) :
    Summable (unshiftedLogTerm p) ↔ 1 < p := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcond : (Summable fun k : ℕ => (2 : ℝ)^k * unshiftedLogTerm p (2^k)) ↔
      Summable (unshiftedLogTerm p) := by
    apply summable_condensed_iff_of_eventually_nonneg
    · apply eventually_atTop.mpr
      refine ⟨2, fun n hn => ?_⟩
      unfold unshiftedLogTerm
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    · apply eventually_atTop.mpr
      refine ⟨2, fun n hn => ?_⟩
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hnn : (n : ℝ) ≤ (n+1 : ℝ) := by norm_cast; omega
      have hlle := Real.log_le_log hnpos hnn
      have hrle := Real.rpow_le_rpow (le_of_lt hl) hlle hp
      unfold unshiftedLogTerm
      apply one_div_le_one_div_of_le (mul_pos hnpos (Real.rpow_pos_of_pos hl p))
      simpa only [Nat.cast_add, Nat.cast_one] using
        (mul_le_mul hnn hrle (Real.rpow_nonneg (le_of_lt hl) _) (by positivity))
  have heq : (fun k : ℕ => (2 : ℝ)^k * unshiftedLogTerm p (2^k)) =ᶠ[atTop]
      (fun k : ℕ => (1 / (Real.log 2)^p) * (1 / (k : ℝ)^p)) := by
    apply eventually_atTop.mpr
    refine ⟨1, fun k hk => ?_⟩
    have hknonneg : 0 ≤ (k : ℝ) := by positivity
    have htwo : (2 : ℝ)^k ≠ 0 := by positivity
    have hkp : (k : ℝ)^p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < k by omega)) p)
    have hlp : (Real.log 2)^p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hlog p)
    simp only [unshiftedLogTerm, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    rw [Real.mul_rpow hknonneg (le_of_lt hlog)]
    field_simp
  rw [← hcond, summable_congr_atTop heq, summable_mul_left_iff (by positivity)]
  exact Real.summable_one_div_nat_rpow

lemma logSeries_criterion (p : ℝ) : SeriesConverges (LogSeriesTerm p) ↔ 1 < p := by
  rw [logTerm_summable_iff]
  by_cases hp : 0 ≤ p
  · exact unshiftedLog_condensation p hp
  have hp0 : p ≤ 0 := le_of_lt (lt_of_not_ge hp)
  have hnonsummable : ¬ Summable (unshiftedLogTerm p) := by
    intro hs
    have hh : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      apply hs.of_norm_bounded_eventually_nat
      have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
      filter_upwards [hlog, eventually_ge_atTop 1] with n hl hn
      change 1 ≤ Real.log (n : ℝ) at hl
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hpow := Real.rpow_le_one_of_one_le_of_nonpos hl hp0
      have hpowpos : 0 < (Real.log (n : ℝ))^p := Real.rpow_pos_of_pos (by linarith) p
      simp only [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hnpos), unshiftedLogTerm]
      apply one_div_le_one_div_of_le (mul_pos hnpos hpowpos)
      simpa using mul_le_mul_of_nonneg_left hpow (le_of_lt hnpos)
    have hbad := Real.summable_one_div_nat_rpow (p := 1)
    simp only [Real.rpow_one] at hbad
    have : (1 : ℝ) < 1 := hbad.mp hh
    exact lt_irrefl _ this
  exact iff_of_false hnonsummable (by linarith)

def unshiftedIteratedLogTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log (n : ℝ) * (Real.log (Real.log (n : ℝ)))^p)

def condensedIteratedLogTerm (p : ℝ) (k : ℕ) : ℝ :=
  1 / ((k : ℝ) * Real.log 2 * (Real.log ((k : ℝ) * Real.log 2))^p)

lemma log_nat_large (n : ℕ) (hn : 4 ≤ n) : 1 < Real.log (n : ℝ) := by
  have h4 : 1 < Real.log 4 := by
    have h2 := Real.log_two_gt_d9
    have he : Real.log 4 = 2 * Real.log 2 := by
      convert Real.log_pow (2 : ℝ) 2 using 1; norm_num
    linarith
  exact h4.trans_le (Real.log_le_log (by norm_num) (by exact_mod_cast hn))

lemma iteratedLog_condensation (p : ℝ) (hp : 0 ≤ p) :
    Summable (unshiftedIteratedLogTerm p) ↔ Summable (condensedIteratedLogTerm p) := by
  have hc : (Summable fun k : ℕ => (2 : ℝ)^k * unshiftedIteratedLogTerm p (2^k)) ↔
      Summable (unshiftedIteratedLogTerm p) := by
    apply summable_condensed_iff_of_eventually_nonneg
    · apply eventually_atTop.mpr
      refine ⟨4, fun n hn => ?_⟩
      have hl := log_nat_large n hn
      have hll : 0 < Real.log (Real.log (n : ℝ)) := Real.log_pos hl
      unfold unshiftedIteratedLogTerm
      positivity
    · apply eventually_atTop.mpr
      refine ⟨4, fun n hn => ?_⟩
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hl := log_nat_large n hn
      have hlpos : 0 < Real.log (n : ℝ) := by linarith
      have hllpos := Real.log_pos hl
      have hnn : (n : ℝ) ≤ (n+1 : ℝ) := by norm_cast; omega
      have hlle := Real.log_le_log hnpos hnn
      have hllle := Real.log_le_log hlpos hlle
      have hrle := Real.rpow_le_rpow (le_of_lt hllpos) hllle hp
      have hmul := mul_le_mul hnn hlle (le_of_lt hlpos) (by positivity)
      have hmul3 := mul_le_mul hmul hrle (Real.rpow_nonneg (le_of_lt hllpos) p)
        (mul_nonneg (by positivity) ((le_of_lt hlpos).trans hlle))
      unfold unshiftedIteratedLogTerm
      apply one_div_le_one_div_of_le (mul_pos (mul_pos hnpos hlpos) (Real.rpow_pos_of_pos hllpos p))
      simpa only [Nat.cast_add, Nat.cast_one] using hmul3
  have heq : (fun k : ℕ => (2 : ℝ)^k * unshiftedIteratedLogTerm p (2^k)) =ᶠ[atTop]
      condensedIteratedLogTerm p := by
    apply eventually_atTop.mpr
    refine ⟨2, fun k hk => ?_⟩
    have hkn : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : (2 : ℝ)^k ≠ 0 := by positivity
    unfold unshiftedIteratedLogTerm condensedIteratedLogTerm
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    field_simp
  rw [← hc, summable_congr_atTop heq]

lemma iteratedLog_comparison (p : ℝ) (hp : 0 ≤ p) :
    ∀ᶠ n in atTop,
      0 ≤ unshiftedLogTerm p n ∧ 0 ≤ condensedIteratedLogTerm p n ∧
      condensedIteratedLogTerm p n ≤ ((2 : ℝ)^p / Real.log 2) * unshiftedLogTerm p n ∧
      unshiftedLogTerm p n ≤ (Real.log 2 * (2 : ℝ)^p) * condensedIteratedLogTerm p n := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < (2 : ℝ)^p := Real.rpow_pos_of_pos (by norm_num) p
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop
    (max 1 (2 * |Real.log (Real.log 2)|))
  filter_upwards [hlog, eventually_ge_atTop 1] with n hl hn
  change max 1 (2 * |Real.log (Real.log 2)|) ≤ Real.log (n : ℝ) at hl
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 < Real.log (n : ℝ) := lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans hl)
  have hab : 2 * |Real.log (Real.log 2)| ≤ Real.log (n : ℝ) := (le_max_right _ _).trans hl
  have he : Real.log ((n : ℝ) * Real.log 2) = Real.log (n : ℝ) + Real.log (Real.log 2) :=
    Real.log_mul (ne_of_gt hnp) (ne_of_gt hl2)
  have hlow : Real.log (n : ℝ) / 2 ≤ Real.log ((n : ℝ) * Real.log 2) := by
    rw [he]
    have := neg_abs_le (Real.log (Real.log 2))
    linarith
  have hupp : Real.log ((n : ℝ) * Real.log 2) ≤ 2 * Real.log (n : ℝ) := by
    rw [he]
    have := le_abs_self (Real.log (Real.log 2))
    linarith
  have hM : 0 < Real.log ((n : ℝ) * Real.log 2) := (half_pos hL).trans_le hlow
  have hLp := Real.rpow_pos_of_pos hL p
  have hMp := Real.rpow_pos_of_pos hM p
  have hpup := Real.rpow_le_rpow (le_of_lt hM) hupp hp
  rw [Real.mul_rpow (by norm_num) (le_of_lt hL)] at hpup
  have hplo := Real.rpow_le_rpow (by positivity : 0 ≤ Real.log (n : ℝ) / 2) hlow hp
  rw [Real.div_rpow (le_of_lt hL) (by norm_num) p] at hplo
  have hLMA : (Real.log (n : ℝ))^p ≤ (2 : ℝ)^p * (Real.log ((n : ℝ) * Real.log 2))^p := by
    have hh := (div_le_iff₀ hA).mp hplo
    simpa only [mul_comm] using hh
  have h1 := one_div_le_one_div_of_le (mul_pos hnp hLp)
    (mul_le_mul_of_nonneg_left hLMA (le_of_lt hnp))
  have h2 := one_div_le_one_div_of_le (mul_pos (mul_pos hnp hl2) hMp)
    (mul_le_mul_of_nonneg_left hpup (le_of_lt (mul_pos hnp hl2)))
  refine ⟨by unfold unshiftedLogTerm; positivity,
    by unfold condensedIteratedLogTerm; positivity, ?_, ?_⟩
  · unfold condensedIteratedLogTerm unshiftedLogTerm
    have hh := mul_le_mul_of_nonneg_left h1 (le_of_lt (div_pos hA hl2))
    convert hh using 1; field_simp
  · unfold condensedIteratedLogTerm unshiftedLogTerm
    have hh := mul_le_mul_of_nonneg_left h2 (le_of_lt (mul_pos hl2 hA))
    convert hh using 1; field_simp

lemma iteratedLog_summable_iff (p : ℝ) (hp : 0 ≤ p) :
    Summable (unshiftedIteratedLogTerm p) ↔ 1 < p := by
  rw [iteratedLog_condensation p hp]
  have hc := iteratedLog_comparison p hp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA : 0 < (2 : ℝ)^p := Real.rpow_pos_of_pos (by norm_num) p
  have heq : Summable (condensedIteratedLogTerm p) ↔ Summable (unshiftedLogTerm p) := by
    constructor
    · intro hf
      apply (hf.mul_left (Real.log 2 * (2 : ℝ)^p)).of_norm_bounded_eventually_nat
      filter_upwards [hc] with n hn
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn.1] using hn.2.2.2
    · intro hg
      apply (hg.mul_left ((2 : ℝ)^p / Real.log 2)).of_norm_bounded_eventually_nat
      filter_upwards [hc] with n hn
      simpa only [Real.norm_eq_abs, abs_of_nonneg hn.2.1] using hn.2.2.1
  rw [heq]
  exact unshiftedLog_condensation p hp

lemma iteratedLogTerm_nonneg (p : ℝ) (n : ℕ) : 0 ≤ IteratedLogSeriesTerm p n := by
  have h3 : 1 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hl : 1 < Real.log (n+3 : ℝ) :=
    h3.trans_le (Real.log_le_log (by norm_num) (by norm_cast; omega))
  have hll : 0 < Real.log (Real.log (n+3 : ℝ)) := Real.log_pos hl
  unfold IteratedLogSeriesTerm
  positivity

lemma iteratedLogSeries_criterion (p : ℝ) (hp : 0 ≤ p) :
    SeriesConverges (IteratedLogSeriesTerm p) ↔ 1 < p := by
  rw [seriesConverges_iff_summable_nonneg (iteratedLogTerm_nonneg p)]
  have hs : Summable (IteratedLogSeriesTerm p) ↔ Summable (unshiftedIteratedLogTerm p) := by
    change Summable (fun n : ℕ => 1 / ((n+3 : ℝ) * Real.log (n+3 : ℝ) * (Real.log (Real.log (n+3 : ℝ)))^p)) ↔ _
    simpa only [unshiftedIteratedLogTerm, Nat.cast_add, Nat.cast_ofNat] using
      (summable_nat_add_iff (f := unshiftedIteratedLogTerm p) 3)
  rw [hs]
  exact iteratedLog_summable_iff p hp

theorem node_3_29 : Statement_3_29 := by
  refine ⟨logSeries_criterion, ?_, ?_⟩
  · unfold SeriesDiverges
    rw [iteratedLogSeries_criterion 1 (by norm_num)]
    norm_num
  · exact (iteratedLogSeries_criterion 2 (by norm_num)).mpr (by norm_num)

/-! ### PMA-3.30: The factorial series defines e. -/
noncomputable def EulerNumber : ℝ := ∑' n : ℕ, 1 / (n.factorial : ℝ)

def FactorialPartialSum (n : ℕ) : ℝ := PartialSums (fun k => 1/(k.factorial : ℝ)) (n+1)

def Statement_3_30 : Prop :=
  Nat.factorial 0 = 1 ∧
  (∀ n : ℕ, Nat.factorial (n+1) = (n+1) * Nat.factorial n) ∧
  SeriesHasSum (fun n : ℕ => 1/(n.factorial : ℝ)) EulerNumber ∧ EulerNumber = Real.exp 1

/-! PMA-3.30 proof details: Verified definition of e and its exponential comparator. -/
theorem factorialSeries_hasSum : HasSum (fun n : ℕ => 1/(n.factorial : ℝ)) (Real.exp 1) := by
  simpa only [one_pow,← Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (1 : ℝ)

theorem eulerNumber_eq_exp_one : EulerNumber = Real.exp 1 := factorialSeries_hasSum.tsum_eq

theorem node_3_30 : Statement_3_30 := by
  exact ⟨rfl,Nat.factorial_succ,by rw [eulerNumber_eq_exp_one]; exact factorialSeries_hasSum.tendsto_sum_nat,
    eulerNumber_eq_exp_one⟩

/-! ### PMA-3.31: A second limit for e and the factorial tail estimate. -/
def Statement_3_31 : Prop :=
  Tendsto (fun n : ℕ => (1 + 1/(n : ℝ))^n) atTop (𝓝 EulerNumber) ∧
  ∀ n : ℕ, 1 ≤ n →
    0 < EulerNumber - FactorialPartialSum n ∧
      EulerNumber - FactorialPartialSum n < 1/((n.factorial : ℝ) * n)

/-! PMA-3.31 proof details: Verified exponential limit and strict factorial-tail estimate. -/
theorem factorialTail_positive (n : ℕ) : 0 < EulerNumber - FactorialPartialSum n := by
  have hnonneg : ∀ k : ℕ, 0 ≤ 1/(k.factorial : ℝ) := fun k => by positivity
  have hle := factorialSeries_hasSum.summable.sum_le_tsum (Finset.range (n+2))
    (fun k _ => hnonneg k)
  have hpos : 0 < 1/((n+1).factorial : ℝ) := by positivity
  change (∑ k ∈ Finset.range (n+2), 1/(k.factorial : ℝ)) ≤ EulerNumber at hle
  rw [show n+2 = (n+1)+1 by omega,Finset.sum_range_succ] at hle
  unfold FactorialPartialSum PartialSums
  linarith

theorem factorialTail_upper {n : ℕ} (hn : 1 ≤ n) :
    EulerNumber - FactorialPartialSum n < 1/((n.factorial : ℝ)*n) := by
  have hbound : |Real.exp 1 - FactorialPartialSum n| ≤
      ((n+1 : ℕ)+1 : ℝ)/(((n+1).factorial : ℝ)*(n+1 : ℕ)) := by
    simpa only [FactorialPartialSum,PartialSums,one_pow,abs_one,one_mul,
      Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one]
      using Real.exp_bound (x := 1) (by norm_num) (n := n+1) (by omega)
  rw [← eulerNumber_eq_exp_one] at hbound
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfac : 0 < (n.factorial : ℝ) := by positivity
  have hlt : ((n+1 : ℕ)+1 : ℝ)/(((n+1).factorial : ℝ)*(n+1 : ℕ)) <
      1/((n.factorial : ℝ)*n) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    nlinarith
  exact lt_of_le_of_lt (le_trans (le_abs_self _) hbound) hlt

theorem node_3_31 : Statement_3_31 := by
  constructor
  · rw [eulerNumber_eq_exp_one]
    simpa only [one_div] using Real.tendsto_one_add_div_pow_exp 1
  · intro n hn
    exact ⟨factorialTail_positive n,factorialTail_upper hn⟩

/-! ### PMA-3.32: The irrationality of e. -/
def Statement_3_32 : Prop := Irrational EulerNumber

/-! PMA-3.32 proof details: Verified irrationality by factorial-scaled integer gaps. -/
theorem factorialPartialSum_scaled_integer (N : ℕ) :
    ∃ z : ℤ, (N.factorial : ℝ) * FactorialPartialSum N = z := by
  refine ⟨((∑ k ∈ Finset.range (N+1), N.factorial / k.factorial : ℕ) : ℤ),?_⟩
  unfold FactorialPartialSum PartialSums
  rw [Finset.mul_sum]
  rw [Int.cast_natCast,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkN : k ≤ N := by have := Finset.mem_range.mp hk;omega
  rw [Nat.cast_div (Nat.factorial_dvd_factorial hkN) (by positivity)]
  ring

theorem node_3_32 : Statement_3_32 := by
  intro hrat
  obtain ⟨q,hq⟩ := hrat
  let N : ℕ := q.den+1
  have hN : 1 ≤ N := by dsimp [N];omega
  have hden : q.den ∣ N.factorial := Nat.dvd_factorial q.den_pos (by dsimp [N];omega)
  obtain ⟨k,hk⟩ := hden
  have heint : (N.factorial : ℝ) * EulerNumber = ((k : ℤ)*q.num : ℤ) := by
    rw [← hq,Rat.cast_def,hk]
    push_cast
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
    field_simp
  obtain ⟨z,hz⟩ := factorialPartialSum_scaled_integer N
  let Z : ℤ := (k : ℤ)*q.num-z
  have hgap : (Z : ℝ) = (N.factorial : ℝ)*(EulerNumber-FactorialPartialSum N) := by
    dsimp [Z]
    push_cast
    rw [mul_sub,heint,hz]
    push_cast
    rfl
  have hfac : 0 < (N.factorial : ℝ) := by positivity
  have hZpos : (0 : ℝ) < Z := by rw [hgap];exact mul_pos hfac (factorialTail_positive N)
  have hZlt : (Z : ℝ) < 1 := by
    rw [hgap]
    have hupper := mul_lt_mul_of_pos_left (factorialTail_upper hN) hfac
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have heq : (N.factorial : ℝ)*(1/((N.factorial : ℝ)*N)) = 1/(N : ℝ) := by
      field_simp
    rw [heq] at hupper
    have hone : 1/(N : ℝ) ≤ 1 := (div_le_one hNreal).mpr (by exact_mod_cast hN)
    exact hupper.trans_le hone
  have hZpos' : (0 : ℤ) < Z := by exact_mod_cast hZpos
  have hZlt' : Z < (1 : ℤ) := by exact_mod_cast hZlt
  omega

/-! ### PMA-3.33: Root test with nonnegative extended-real limits.

For n ≥ 1, `NthRootNorm` is exactly the source's nth root. Its totalized value
at n = 0 does not affect limits at infinity. ENNReal includes the case +∞.
-/
noncomputable def NthRootNorm {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) (n : ℕ) : ℝ := ‖a n‖ ^ (1/(n : ℝ))

noncomputable def RootLimsup {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) : ENNReal := limsup (fun n => ENNReal.ofReal (NthRootNorm a n)) atTop

noncomputable def RootLiminf {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) : ENNReal := liminf (fun n => ENNReal.ofReal (NthRootNorm a n)) atTop

def Statement_3_33 : Prop :=
  (∀ a : ℕ → ℂ, RootLimsup a < 1 → SeriesConverges a) ∧
  (∀ a : ℕ → ℂ, 1 < RootLimsup a → SeriesDiverges a) ∧
  RootLimsup (PSeriesTerm 1) = 1 ∧ RootLimsup (PSeriesTerm 2) = 1 ∧
  SeriesDiverges (PSeriesTerm 1) ∧ SeriesConverges (PSeriesTerm 2)

/-! PMA-3.33 proof details: Root test via the Cauchy-Hadamard reference. -/
theorem rootLimsup_eq_radius_inv {𝕜 : Type*} [RCLike 𝕜] (a : ℕ → 𝕜) :
    RootLimsup a = (FormalMultilinearSeries.ofScalars 𝕜 a).radius⁻¹ := by
  rw [FormalMultilinearSeries.radius_inv_eq_limsup]
  unfold RootLimsup
  congr 1
  funext n
  rw [← ENNReal.ofReal_coe_nnreal]
  congr 1
  rw [NNReal.coe_rpow]
  simp only [NthRootNorm,coe_nnnorm,FormalMultilinearSeries.ofScalars_norm]

theorem root_test_summable_norm {𝕜 : Type*} [RCLike 𝕜] {a : ℕ → 𝕜}
    (hroot : RootLimsup a < 1) : Summable (fun n => ‖a n‖) := by
  let p := FormalMultilinearSeries.ofScalars 𝕜 a
  have hr : (1 : ENNReal) < p.radius := by
    apply ENNReal.inv_lt_inv.mp
    rw [rootLimsup_eq_radius_inv] at hroot
    simpa only [inv_one,p] using hroot
  simpa only [p,FormalMultilinearSeries.ofScalars_norm,NNReal.coe_one,one_pow,mul_one]
    using p.summable_norm_mul_pow (r := 1) hr

theorem root_test_not_terms_zero {𝕜 : Type*} [RCLike 𝕜] {a : ℕ → 𝕜}
    (hroot : 1 < RootLimsup a) : ¬ Tendsto a atTop (𝓝 0) := by
  intro ha
  let p := FormalMultilinearSeries.ofScalars 𝕜 a
  have hnorm : Tendsto (fun n => ‖p n‖ * ((1 : NNReal) : ℝ)^n) atTop (𝓝 0) := by
    simpa only [p,FormalMultilinearSeries.ofScalars_norm,NNReal.coe_one,one_pow,mul_one,norm_zero]
      using ha.norm
  have hr : (1 : ENNReal) ≤ p.radius := p.le_radius_of_tendsto hnorm
  have hr' := (ENNReal.inv_lt_one).mpr hroot
  rw [rootLimsup_eq_radius_inv,inv_inv] at hr'
  exact not_lt_of_ge hr hr'

theorem pSeries_ratio_tendsto (p : ℝ) :
    Tendsto (fun n => ‖PSeriesTerm p (n+1)‖ / ‖PSeriesTerm p n‖) atTop (𝓝 1) := by
  have hsmall : Tendsto (fun n : ℕ => 1/((n : ℝ)+2)) atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/((n : ℝ)+1)) atTop (𝓝 0)).comp (tendsto_add_atTop_nat 1)
    convert hh using 1
    funext n
    simp only [Function.comp_def,Nat.cast_add,Nat.cast_one]
    congr 1
    ring_nf
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ)+1)/((n : ℝ)+2)) atTop (𝓝 1) := by
    have hb := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hsmall
    simp only [sub_zero] at hb
    convert hb using 1
    funext n
    field_simp [show (n : ℝ)+2 ≠ 0 by positivity]
    ring_nf
  have hp := hbase.rpow_const (p := p) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  simpa only [Real.one_rpow] using hp.congr (fun n => by
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pSeries_nonneg p (n+1)),
      abs_of_nonneg (pSeries_nonneg p n)]
    simp only [PSeriesTerm,Nat.cast_add,Nat.cast_one]
    rw [Real.div_rpow (by positivity) (by positivity)]
    field_simp [(Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1) p).ne',
      (Real.rpow_pos_of_pos (by positivity : 0 < (n : ℝ)+1+1) p).ne']
    ring_nf)

theorem pSeries_rootLimsup (p : ℝ) : RootLimsup (PSeriesTerm p) = 1 := by
  rw [rootLimsup_eq_radius_inv]
  have h := FormalMultilinearSeries.ofScalars_radius_eq_inv_of_tendsto
    ℝ (PSeriesTerm p) (r := 1) (by norm_num) (pSeries_ratio_tendsto p)
  simp only [h,ENNReal.coe_one,inv_one]

theorem node_3_33 : Statement_3_33 := by
  refine ⟨fun a h => seriesConverges_of_summable (root_test_summable_norm h).of_norm,
    fun a h hs => root_test_not_terms_zero h (series_terms_tendsto_zero hs),
    pSeries_rootLimsup 1,pSeries_rootLimsup 2,?_,?_⟩
  · exact fun hs => (by norm_num : ¬ (1 : ℝ) < 1) ((node_3_28 1).mp hs)
  · exact (node_3_28 2).mpr (by norm_num)

/-! ### PMA-3.34: Ratio test with explicitly defined eventual denominators. -/
noncomputable def RatioNorm {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) (n : ℕ) : ℝ := ‖a (n+1)‖ / ‖a n‖

noncomputable def RatioLimsup {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) : ENNReal := limsup (fun n => ENNReal.ofReal (RatioNorm a n)) atTop

noncomputable def RatioLiminf {V : Type*} [NormedAddCommGroup V]
    (a : ℕ → V) : ENNReal := liminf (fun n => ENNReal.ofReal (RatioNorm a n)) atTop

def Statement_3_34 : Prop :=
  (∀ a : ℕ → ℂ, (∀ᶠ n in atTop, a n ≠ 0) →
    RatioLimsup a < 1 → SeriesConverges a) ∧
  (∀ a : ℕ → ℂ, (∀ᶠ n in atTop, a n ≠ 0) →
    (∀ᶠ n in atTop, 1 ≤ RatioNorm a n) → SeriesDiverges a) ∧
  Tendsto (RatioNorm (PSeriesTerm 1)) atTop (𝓝 1) ∧
  Tendsto (RatioNorm (PSeriesTerm 2)) atTop (𝓝 1) ∧
  SeriesDiverges (PSeriesTerm 1) ∧ SeriesConverges (PSeriesTerm 2)

/-! PMA-3.34 proof details: Verified norm-ratio convergence and divergence criteria. -/
theorem ratio_test_summable_norm {V : Type*} [NormedAddCommGroup V] {a : ℕ → V}
    (hnz : ∀ᶠ n in atTop, a n ≠ 0) (h : RatioLimsup a < 1) :
    Summable (fun n => ‖a n‖) := by
  obtain ⟨b,hb,hb1⟩ := exists_between h
  have hbtop : b ≠ ⊤ := ne_top_of_lt hb1
  have hb1real : b.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal hbtop (by simp)).mpr hb1
  have he : ∀ᶠ n in atTop, ENNReal.ofReal (RatioNorm a n) < b :=
    eventually_lt_of_limsup_lt hb
  apply summable_of_ratio_norm_eventually_le hb1real
  filter_upwards [he,hnz] with n hn hnz'
  simp only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hratio : RatioNorm a n < b.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by unfold RatioNorm;positivity) hbtop).mp hn
  exact le_of_lt ((div_lt_iff₀ (norm_pos_iff.mpr hnz')).mp hratio)

theorem ratio_test_not_terms_zero {V : Type*} [NormedAddCommGroup V] {a : ℕ → V}
    (hnz : ∀ᶠ n in atTop, a n ≠ 0)
    (h : ∀ᶠ n in atTop, 1 ≤ RatioNorm a n) : ¬ Tendsto a atTop (𝓝 0) := by
  intro ha
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hnz.and h)
  have hbound : ∀ n, N ≤ n → ‖a N‖ ≤ ‖a n‖ := by
    intro n hn
    induction n,hn using Nat.le_induction with
    | base => exact le_rfl
    | succ n hn ih =>
      have hstep := (le_div_iff₀ (norm_pos_iff.mpr (hN n hn).1)).mp (hN n hn).2
      simp only [one_mul] at hstep
      exact ih.trans hstep
  have hnorm := ha.norm
  simp only [norm_zero] at hnorm
  have hsmall := hnorm.eventually_lt_const (norm_pos_iff.mpr (hN N le_rfl).1)
  obtain ⟨n,hn,hnN⟩ := (hsmall.and (eventually_ge_atTop N)).exists
  exact not_lt_of_ge (hbound n hnN) hn

theorem node_3_34 : Statement_3_34 := by
  refine ⟨fun a hnz h => seriesConverges_of_summable (ratio_test_summable_norm hnz h).of_norm,
    fun a hnz h hs => ratio_test_not_terms_zero hnz h (series_terms_tendsto_zero hs),
    pSeries_ratio_tendsto 1,pSeries_ratio_tendsto 2,?_,?_⟩
  · exact fun hs => (by norm_num : ¬ (1 : ℝ) < 1) ((node_3_28 1).mp hs)
  · exact (node_3_28 2).mpr (by norm_num)

/-! ### PMA-3.35: Two convergent series whose ratio convergence test fails.

The definitions use a zero head at index 0 and exactly Rudin's coefficients
at positive indices, as specified separately in the contracts.
-/
noncomputable def RatioExampleA (n : ℕ) : ℝ :=
  if n = 0 then 0 else if n % 2 = 1 then 1/(2 : ℝ)^((n+1)/2) else 1/(3 : ℝ)^(n/2)

noncomputable def RatioExampleB (n : ℕ) : ℝ :=
  if n = 0 then 0 else if n % 2 = 1 then 1/((2 : ℝ)*4^(n/2)) else 1/(4 : ℝ)^(n/2-1)

def Statement_3_35 : Prop :=
  (∀ n : ℕ, 1 ≤ n → RatioExampleA (2*n-1) = 1/(2 : ℝ)^n ∧
    RatioExampleA (2*n) = 1/(3 : ℝ)^n) ∧
  RatioLiminf RatioExampleA = 0 ∧ RatioLimsup RatioExampleA = ⊤ ∧
  RootLiminf RatioExampleA = ENNReal.ofReal (1/Real.sqrt 3) ∧
  RootLimsup RatioExampleA = ENNReal.ofReal (1/Real.sqrt 2) ∧
  SeriesConverges RatioExampleA ∧ ¬ RatioLimsup RatioExampleA < 1 ∧
  (∀ n : ℕ, 1 ≤ n → RatioExampleB (2*n-1) = 1/((2 : ℝ)*4^(n-1)) ∧
    RatioExampleB (2*n) = 1/(4 : ℝ)^(n-1)) ∧
  RatioLiminf RatioExampleB = ENNReal.ofReal (1/8) ∧
  RatioLimsup RatioExampleB = 2 ∧
  Tendsto (NthRootNorm RatioExampleB) atTop (𝓝 (1/2)) ∧
  SeriesConverges RatioExampleB ∧ ¬ RatioLimsup RatioExampleB < 1

/-! PMA-3.35 proof details: Splitting limits into even and odd indices. -/
theorem nat_atTop_even_odd :
    (atTop : Filter ℕ) = map (fun n => 2*n) atTop ⊔ map (fun n => 2*n+1) atTop := by
  ext S
  simp only [Filter.mem_sup,Filter.mem_map]
  change (∀ᶠ n in atTop, n ∈ S) ↔
    (∀ᶠ n in atTop, 2*n ∈ S) ∧ (∀ᶠ n in atTop, 2*n+1 ∈ S)
  simp only [eventually_atTop]
  constructor
  · rintro ⟨N,hN⟩
    exact ⟨⟨N,fun n hn => hN (2*n) (by omega)⟩,
      ⟨N,fun n hn => hN (2*n+1) (by omega)⟩⟩
  · rintro ⟨⟨N,hN⟩,⟨M,hM⟩⟩
    refine ⟨2*(N+M+1),fun n hn => ?_⟩
    have hd : n%2 = 0 ∨ n%2 = 1 := by omega
    rcases hd with hd | hd
    · have he : n = 2*(n/2) := by omega
      rw [he]
      exact hN (n/2) (by omega)
    · have he : n = 2*(n/2)+1 := by omega
      rw [he]
      exact hM (n/2) (by omega)

theorem tendsto_of_even_odd {X : Type*} [TopologicalSpace X] {u : ℕ → X} {x : X}
    (he : Tendsto (fun n => u (2*n)) atTop (𝓝 x))
    (ho : Tendsto (fun n => u (2*n+1)) atTop (𝓝 x)) : Tendsto u atTop (𝓝 x) := by
  rw [nat_atTop_even_odd]
  exact tendsto_sup.mpr ⟨(tendsto_map'_iff).mpr he,(tendsto_map'_iff).mpr ho⟩

theorem limsup_even_odd {u : ℕ → ENNReal} :
    limsup u atTop = max (limsup (fun n => u (2*n)) atTop)
      (limsup (fun n => u (2*n+1)) atTop) := by
  nth_rw 1 [nat_atTop_even_odd]
  rw [limsup_sup_filter]
  rfl

theorem liminf_even_odd {u : ℕ → ENNReal} :
    liminf u atTop = min (liminf (fun n => u (2*n)) atTop)
      (liminf (fun n => u (2*n+1)) atTop) := by
  nth_rw 1 [nat_atTop_even_odd]
  rw [liminf_sup_filter]
  rfl

theorem ratioExampleA_odd (n : ℕ) : RatioExampleA (2*n+1) = 1/(2 : ℝ)^(n+1) := by
  simp [RatioExampleA,show (2*n+1)%2 = 1 by omega,
    show (2*n+1+1)/2 = n+1 by omega]

theorem ratioExampleA_even (n : ℕ) : RatioExampleA (2*n+2) = 1/(3 : ℝ)^(n+1) := by
  simp [RatioExampleA,
    show (2*n+2)/2 = n+1 by omega]

theorem ratioExampleB_odd (n : ℕ) : RatioExampleB (2*n+1) = 1/((2 : ℝ)*4^n) := by
  simp [RatioExampleB,show (2*n+1)%2 = 1 by omega,
    show (2*n+1)/2 = n by omega]

theorem ratioExampleB_even (n : ℕ) : RatioExampleB (2*n+2) = 1/(4 : ℝ)^n := by
  simp [RatioExampleB,
    show (2*n+2)/2 = n+1 by omega]

theorem ratioExampleA_ratio_odd (n : ℕ) :
    RatioNorm RatioExampleA (2*n+1) = (2/3 : ℝ)^(n+1) := by
  unfold RatioNorm
  rw [show 2*n+1+1 = 2*n+2 by omega,ratioExampleA_even,ratioExampleA_odd]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity),abs_of_pos (by positivity)]
  rw [div_pow]
  field_simp

theorem ratioExampleA_ratio_even (n : ℕ) :
    RatioNorm RatioExampleA (2*n+2) = (1/2 : ℝ)*(3/2 : ℝ)^(n+1) := by
  unfold RatioNorm
  rw [show 2*n+2+1 = 2*(n+1)+1 by omega,ratioExampleA_odd,ratioExampleA_even]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity),abs_of_pos (by positivity)]
  rw [div_pow,pow_succ]
  field_simp

theorem ratioExampleB_ratio_odd (n : ℕ) : RatioNorm RatioExampleB (2*n+1) = 2 := by
  unfold RatioNorm
  rw [show 2*n+1+1 = 2*n+2 by omega,ratioExampleB_even,ratioExampleB_odd]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity),abs_of_pos (by positivity)]
  field_simp

theorem ratioExampleB_ratio_even (n : ℕ) : RatioNorm RatioExampleB (2*n+2) = 1/8 := by
  unfold RatioNorm
  rw [show 2*n+2+1 = 2*(n+1)+1 by omega,ratioExampleB_odd,ratioExampleB_even]
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (by positivity),abs_of_pos (by positivity)]
  rw [pow_succ]
  field_simp
  ring

theorem root_one_div_pow (b : ℝ) (hb : 0 < b) (k m : ℕ) :
    (1/b^k)^(1/(m : ℝ)) = b^(-(k : ℝ)/(m : ℝ)) := by
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_natCast,
    ← Real.rpow_mul hb.le,← Real.rpow_neg hb.le]
  congr 1
  ring

theorem rpow_negative_half (b : ℝ) (hb : 0 ≤ b) :
    b^(-(1/2 : ℝ)) = 1/Real.sqrt b := by
  rw [Real.rpow_neg hb,← Real.sqrt_eq_rpow]
  simp only [one_div]

theorem ratioExampleA_root_even (n : ℕ) :
    NthRootNorm RatioExampleA (2*n+2) = 1/Real.sqrt 3 := by
  unfold NthRootNorm
  rw [ratioExampleA_even,Real.norm_eq_abs,abs_of_pos (by positivity),
    root_one_div_pow 3 (by norm_num)]
  have he : -((n+1 : ℕ) : ℝ)/(2*n+2 : ℕ) = -(1/2 : ℝ) := by
    push_cast
    field_simp
  rw [he,rpow_negative_half 3 (by norm_num)]

theorem ratioExampleA_root_odd_tendsto :
    Tendsto (fun n => NthRootNorm RatioExampleA (2*n+1)) atTop (𝓝 (1/Real.sqrt 2)) := by
  have hlinear : Tendsto (fun n : ℕ => ((n : ℝ)+1)/(2*n+1)) atTop (𝓝 (1/2 : ℝ)) := by
    simpa only [one_mul,mul_one,add_comm,mul_comm] using
      tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 1 1 1 (d := 2) (by norm_num)
  have hexp := hlinear.neg
  have hpow := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).rpow hexp
    (Or.inl (by norm_num : (2 : ℝ) ≠ 0))
  rw [rpow_negative_half 2 (by norm_num)] at hpow
  convert hpow using 1
  funext n
  unfold NthRootNorm
  rw [ratioExampleA_odd,Real.norm_eq_abs,abs_of_pos (by positivity),
    root_one_div_pow 2 (by norm_num)]
  push_cast
  congr 1
  ring

theorem ratioExampleB_root_odd (n : ℕ) : NthRootNorm RatioExampleB (2*n+1) = 1/2 := by
  unfold NthRootNorm
  rw [ratioExampleB_odd,Real.norm_eq_abs,abs_of_pos (by positivity)]
  have he : (2 : ℝ)*4^n = 2^(2*n+1) := by
    rw [pow_succ,pow_mul]
    norm_num
    ring
  rw [he,root_one_div_pow 2 (by norm_num)]
  have he' : -((2*n+1 : ℕ) : ℝ)/(2*n+1 : ℕ) = -(1 : ℝ) := by
    rw [neg_div,div_self (by positivity)]
  rw [he',Real.rpow_neg_one]
  norm_num

theorem ratioExampleB_root_even_tendsto :
    Tendsto (fun n => NthRootNorm RatioExampleB (2*n+2)) atTop (𝓝 (1/2 : ℝ)) := by
  have hlinear : Tendsto (fun n : ℕ => (n : ℝ)/(2*n+2)) atTop (𝓝 (1/2 : ℝ)) := by
    simpa only [one_mul,mul_one,zero_add,add_zero,add_comm,mul_comm] using
      tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ) 0 2 1 (d := 2) (by norm_num)
  have hpow := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (𝓝 4)).rpow hlinear.neg
    (Or.inl (by norm_num : (4 : ℝ) ≠ 0))
  rw [rpow_negative_half 4 (by norm_num)] at hpow
  norm_num at hpow
  convert hpow using 1
  funext n
  unfold NthRootNorm
  rw [ratioExampleB_even,Real.norm_eq_abs,abs_of_pos (by positivity),
    root_one_div_pow 4 (by norm_num)]
  push_cast
  congr 1
  ring

theorem tendsto_even_of_shift {X : Type*} {l : Filter X} {u : ℕ → X}
    (h : Tendsto (fun n => u (2*n+2)) atTop l) : Tendsto (fun n => u (2*n)) atTop l := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [Nat.mul_add,mul_one] using h

theorem ratioExampleA_ratio_limits :
    RatioLiminf RatioExampleA = 0 ∧ RatioLimsup RatioExampleA = ⊤ := by
  have ho : Tendsto (fun n => RatioNorm RatioExampleA (2*n+1)) atTop (𝓝 0) := by
    simpa only [ratioExampleA_ratio_odd,Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2/3)
        (by norm_num : (2/3 : ℝ) < 1)).comp (tendsto_add_atTop_nat 1)
  have he' : Tendsto (fun n => RatioNorm RatioExampleA (2*n+2)) atTop atTop := by
    simpa only [ratioExampleA_ratio_even,Function.comp_def] using
      ((tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 3/2)).comp
        (tendsto_add_atTop_nat 1)).const_mul_atTop (by norm_num : (0 : ℝ) < 1/2)
  have he := ENNReal.tendsto_ofReal_nhds_top.mpr (tendsto_even_of_shift he')
  have ho' := ENNReal.tendsto_ofReal ho
  simp only [ENNReal.ofReal_zero] at ho'
  constructor
  · unfold RatioLiminf
    rw [liminf_even_odd,he.liminf_eq,ho'.liminf_eq]
    simp
  · unfold RatioLimsup
    rw [limsup_even_odd,he.limsup_eq,ho'.limsup_eq]
    simp

theorem ratioExampleA_root_limits :
    RootLiminf RatioExampleA = ENNReal.ofReal (1/Real.sqrt 3) ∧
      RootLimsup RatioExampleA = ENNReal.ofReal (1/Real.sqrt 2) := by
  have he' : Tendsto (fun n => NthRootNorm RatioExampleA (2*n+2)) atTop
      (𝓝 (1/Real.sqrt 3)) := by
    simp only [ratioExampleA_root_even]
    exact tendsto_const_nhds
  have he := ENNReal.tendsto_ofReal (tendsto_even_of_shift he')
  have ho := ENNReal.tendsto_ofReal ratioExampleA_root_odd_tendsto
  have hle : ENNReal.ofReal (1/Real.sqrt 3) ≤ ENNReal.ofReal (1/Real.sqrt 2) := by
    apply ENNReal.ofReal_le_ofReal
    exact one_div_le_one_div_of_le (by positivity) (Real.sqrt_le_sqrt (by norm_num))
  constructor
  · unfold RootLiminf
    rw [liminf_even_odd,he.liminf_eq,ho.liminf_eq,min_eq_left hle]
  · unfold RootLimsup
    rw [limsup_even_odd,he.limsup_eq,ho.limsup_eq,max_eq_right hle]

theorem ratioExampleB_ratio_limits :
    RatioLiminf RatioExampleB = ENNReal.ofReal (1/8) ∧ RatioLimsup RatioExampleB = 2 := by
  have he' : Tendsto (fun n => RatioNorm RatioExampleB (2*n+2)) atTop (𝓝 (1/8 : ℝ)) := by
    simp only [ratioExampleB_ratio_even]
    exact tendsto_const_nhds
  have ho' : Tendsto (fun n => RatioNorm RatioExampleB (2*n+1)) atTop (𝓝 (2 : ℝ)) := by
    simp only [ratioExampleB_ratio_odd]
    exact tendsto_const_nhds
  have he := ENNReal.tendsto_ofReal (tendsto_even_of_shift he')
  have ho := ENNReal.tendsto_ofReal ho'
  have hle : ENNReal.ofReal (1/8) ≤ ENNReal.ofReal 2 := by norm_num
  constructor
  · unfold RatioLiminf
    rw [liminf_even_odd,he.liminf_eq,ho.liminf_eq,min_eq_left hle]
  · unfold RatioLimsup
    rw [limsup_even_odd,he.limsup_eq,ho.limsup_eq,max_eq_right hle]
    norm_num

theorem ratioExampleB_root_tendsto :
    Tendsto (NthRootNorm RatioExampleB) atTop (𝓝 (1/2 : ℝ)) := by
  apply tendsto_of_even_odd
  · exact tendsto_even_of_shift ratioExampleB_root_even_tendsto
  · simp only [ratioExampleB_root_odd]
    exact tendsto_const_nhds

theorem node_3_35 : Statement_3_35 := by
  have ha := ratioExampleA_ratio_limits
  have har := ratioExampleA_root_limits
  have hb := ratioExampleB_ratio_limits
  refine ⟨?_,ha.1,ha.2,har.1,har.2,?_,?_,?_,hb.1,hb.2,ratioExampleB_root_tendsto,?_,?_⟩
  · intro n hn
    constructor
    · have he : 2*n-1 = 2*(n-1)+1 := by omega
      rw [he,ratioExampleA_odd,show n-1+1 = n by omega]
    · have he : 2*n = 2*(n-1)+2 := by omega
      rw [he,ratioExampleA_even,show n-1+1 = n by omega]
  · apply seriesConverges_of_summable
    apply Summable.of_norm
    apply root_test_summable_norm
    rw [har.2,ENNReal.ofReal_lt_one]
    apply (div_lt_one (by positivity : 0 < Real.sqrt 2)).mpr
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnonneg := Real.sqrt_nonneg 2
    nlinarith
  · rw [ha.2]
    simp
  · intro n hn
    constructor
    · have he : 2*n-1 = 2*(n-1)+1 := by omega
      rw [he,ratioExampleB_odd]
    · have he : 2*n = 2*(n-1)+2 := by omega
      rw [he,ratioExampleB_even]
  · apply seriesConverges_of_summable
    apply Summable.of_norm
    apply root_test_summable_norm
    have hr := (ENNReal.tendsto_ofReal ratioExampleB_root_tendsto).limsup_eq
    change RootLimsup RatioExampleB = ENNReal.ofReal (1/2) at hr
    rw [hr]
    norm_num
  · rw [hb.2]
    norm_num

/-! ### PMA-3.37: Positive real roots lie between ratio lower and upper limits. -/
def Statement_3_37 : Prop :=
  ∀ c : ℕ → ℝ, (∀ n, 0 < c n) →
    RatioLiminf c ≤ RootLiminf c ∧ RootLimsup c ≤ RatioLimsup c

/-! PMA-3.37 proof details: Ratio upper bounds control roots through weighted series. -/
theorem rootLimsup_le_ratioLimsup {𝕜 : Type*} [RCLike 𝕜] {a : ℕ → 𝕜}
    (hnz : ∀ᶠ n in atTop, a n ≠ 0) : RootLimsup a ≤ RatioLimsup a := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro B hB
  by_cases hBtop : B = ⊤
  · simp [hBtop]
  obtain ⟨C,hC,hCB⟩ := exists_between hB
  have hCtop : C ≠ ⊤ := ne_top_of_lt hCB
  let b : NNReal := B.toNNReal
  let r : NNReal := b⁻¹
  have hbcoe : (b : ENNReal) = B := ENNReal.coe_toNNReal hBtop
  have hbpos : 0 < b := by
    apply NNReal.coe_pos.mp
    change 0 < B.toReal
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_le_of_lt (zero_le : (0 : ENNReal) ≤ RatioLimsup a) hB)) hBtop
  have hBre : (b : ℝ) = B.toReal := rfl
  have hCre : C.toReal < (b : ℝ) := by
    rw [hBre]
    exact (ENNReal.toReal_lt_toReal hCtop hBtop).mpr hCB
  have hgeom : C.toReal*(r : ℝ) < 1 := by
    simp only [r,NNReal.coe_inv]
    rw [← div_eq_mul_inv,div_lt_one (NNReal.coe_pos.mpr hbpos)]
    exact hCre
  have he : ∀ᶠ n in atTop, ENNReal.ofReal (RatioNorm a n) < C :=
    eventually_lt_of_limsup_lt hC
  have hs : Summable (fun n => ‖a n‖*(r : ℝ)^n) := by
    apply summable_of_ratio_norm_eventually_le hgeom
    filter_upwards [he,hnz] with n hn hnz'
    have hratio : RatioNorm a n < C.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (by unfold RatioNorm;positivity) hCtop).mp hn
    have hstep : ‖a (n+1)‖ ≤ C.toReal*‖a n‖ :=
      le_of_lt ((div_lt_iff₀ (norm_pos_iff.mpr hnz')).mp hratio)
    rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity)]
    calc
      ‖a (n+1)‖*(r : ℝ)^(n+1) = (‖a (n+1)‖*(r : ℝ)^n)*(r : ℝ) := by rw [pow_succ];ring
      _ ≤ (C.toReal*‖a n‖*(r : ℝ)^n)*(r : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hstep (by positivity)) (by positivity)
      _ = (C.toReal*(r : ℝ))*(‖a n‖*(r : ℝ)^n) := by ring
  have hr : (r : ENNReal) ≤ (FormalMultilinearSeries.ofScalars 𝕜 a).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    simpa only [FormalMultilinearSeries.ofScalars_norm] using hs
  rw [rootLimsup_eq_radius_inv]
  have h := ENNReal.inv_le_inv.mpr hr
  simpa only [r,ENNReal.coe_inv hbpos.ne',inv_inv,hbcoe] using h

theorem rootLimsup_reciprocal {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) :
    RootLimsup (fun n => 1/c n) = (RootLiminf c)⁻¹ := by
  unfold RootLimsup RootLiminf
  rw [ENNReal.inv_liminf]
  congr 1
  funext n
  simp only [NthRootNorm,Real.norm_eq_abs,abs_of_pos (hc n),one_div,
    abs_of_pos (inv_pos.mpr (hc n))]
  rw [Real.inv_rpow (hc n).le,
    ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos (hc n) _)]

theorem ratioLimsup_reciprocal {c : ℕ → ℝ} (hc : ∀ n, 0 < c n) :
    RatioLimsup (fun n => 1/c n) = (RatioLiminf c)⁻¹ := by
  unfold RatioLimsup RatioLiminf
  rw [ENNReal.inv_liminf]
  congr 1
  funext n
  have heq : RatioNorm (fun n => 1/c n) n = (RatioNorm c n)⁻¹ := by
    simp only [RatioNorm,Real.norm_eq_abs,abs_of_pos (hc n),abs_of_pos (hc (n+1)),
      abs_of_pos (one_div_pos.mpr (hc n)),abs_of_pos (one_div_pos.mpr (hc (n+1)))]
    field_simp
  rw [heq,ENNReal.ofReal_inv_of_pos]
  unfold RatioNorm
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (hc n),abs_of_pos (hc (n+1))]
  exact div_pos (hc (n+1)) (hc n)

theorem node_3_37 : Statement_3_37 := by
  intro c hc
  constructor
  · have hi := rootLimsup_le_ratioLimsup (a := fun n => 1/c n)
      (Eventually.of_forall (fun n => ne_of_gt (one_div_pos.mpr (hc n))))
    rw [rootLimsup_reciprocal hc,ratioLimsup_reciprocal hc] at hi
    exact ENNReal.inv_le_inv.mp hi
  · exact rootLimsup_le_ratioLimsup (Eventually.of_forall (fun n => (hc n).ne'))

/-! ### PMA-3.36: Precise dominance of the convergence criteria.

The source's inconclusiveness remark is interpreted as referring to convergence
criteria. The constant sequence records the failure of the stronger full-test
interpretation: root limsup 1 coexists with eventual ratios 1 and divergence.
-/
def Statement_3_36 : Prop :=
  (∀ a : ℕ → ℂ, (∀ᶠ n in atTop, a n ≠ 0) →
    RatioLimsup a < 1 → RootLimsup a < 1) ∧
  (∀ a : ℕ → ℂ, (∀ᶠ n in atTop, a n ≠ 0) →
    1 ≤ RootLimsup a → 1 ≤ RatioLimsup a) ∧
  (∀ a : ℕ → ℂ, 1 < RootLimsup a → ¬ Tendsto a atTop (𝓝 0)) ∧
  (∀ a : ℕ → ℂ, (∀ᶠ n in atTop, a n ≠ 0) →
    (∀ᶠ n in atTop, 1 ≤ RatioNorm a n) → ¬ Tendsto a atTop (𝓝 0)) ∧
  RootLimsup (fun _ : ℕ => (1 : ℂ)) = 1 ∧
  (∀ n : ℕ, RatioNorm (fun _ : ℕ => (1 : ℂ)) n = 1) ∧
  SeriesDiverges (fun _ : ℕ => (1 : ℂ))

/-! PMA-3.36 proof details: Verified dominance and the full-test counterexample. -/
theorem node_3_36 : Statement_3_36 := by
  refine ⟨fun a hnz h => lt_of_le_of_lt (rootLimsup_le_ratioLimsup hnz) h,
    fun a hnz h => h.trans (rootLimsup_le_ratioLimsup hnz),
    fun a h => root_test_not_terms_zero h,
    fun a hnz h => ratio_test_not_terms_zero hnz h,?_,?_,?_⟩
  · simp [RootLimsup,NthRootNorm]
  · intro n
    simp [RatioNorm]
  · intro hs
    have hz := series_terms_tendsto_zero hs
    have h1 : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
    have he := tendsto_nhds_unique h1 hz
    norm_num at he
/-! ### PMA-3.38: power series coefficients and terms. -/

open scoped NNReal ENNReal

def PowerSeriesTerms (c : ℕ → ℂ) (z : ℂ) (n : ℕ) : ℂ := c n * z ^ n

def PowerSeriesRadius (c : ℕ → ℂ) : ℝ≥0∞ := (RootLimsup c)⁻¹

def pma3_38_contract : Prop :=
  (∀ c z N, PartialSums (PowerSeriesTerms c z) N = ∑ n ∈ Finset.range N, c n * z ^ n) ∧
  ∀ c : ℕ → ℂ, ∃ R : ℝ≥0∞,
    (∀ z : ℂ, (‖z‖₊ : ℝ≥0∞) < R → SeriesConverges (PowerSeriesTerms c z)) ∧
    (∀ z : ℂ, R < (‖z‖₊ : ℝ≥0∞) → ¬ SeriesConverges (PowerSeriesTerms c z))

theorem seriesHasSum_term_tendsto_zero {V : Type*} [NormedAddCommGroup V]
    {a : ℕ → V} {A : V} (h : SeriesHasSum a A) : Tendsto a atTop (𝓝 0) := by
  have hs : Tendsto (fun n => PartialSums a (n + 1)) atTop (𝓝 A) :=
    h.comp (tendsto_add_atTop_nat 1)
  simpa [PartialSums, Finset.sum_range_succ] using hs.sub h

theorem powerSeriesRadius_reference (c : ℕ → ℂ) :
    PowerSeriesRadius c = (FormalMultilinearSeries.ofScalars ℂ c).radius := by
  have h := (FormalMultilinearSeries.ofScalars ℂ c).radius_inv_eq_limsup
  have he : RootLimsup c = (FormalMultilinearSeries.ofScalars ℂ c).radius⁻¹ := by
    rw [h]
    apply Filter.limsup_congr
    apply Filter.Eventually.of_forall
    intro n
    have hn : ‖FormalMultilinearSeries.ofScalars ℂ c n‖₊ = ‖c n‖₊ := by
      apply NNReal.eq
      exact FormalMultilinearSeries.ofScalars_norm ℂ c n
    simp only [NthRootNorm] at *
    rw [hn, ← ENNReal.ofReal_coe_nnreal, NNReal.coe_rpow]
    rfl
  simp [PowerSeriesRadius, he]

theorem powerSeries_interior_summable_norm (c : ℕ → ℂ) (z : ℂ)
    (hz : (‖z‖₊ : ℝ≥0∞) < PowerSeriesRadius c) :
    Summable (fun n => ‖PowerSeriesTerms c z n‖) := by
  rw [powerSeriesRadius_reference] at hz
  simpa [PowerSeriesTerms, norm_mul, norm_pow, FormalMultilinearSeries.ofScalars_norm] using
    (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow hz

theorem seriesConverges_of_summable_norm {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    {a : ℕ → V} (h : Summable (fun n => ‖a n‖)) : SeriesConverges a :=
  ⟨∑' n, a n, h.of_norm.hasSum.tendsto_sum_nat⟩

theorem powerSeries_interior (c : ℕ → ℂ) (z : ℂ)
    (hz : (‖z‖₊ : ℝ≥0∞) < PowerSeriesRadius c) : SeriesConverges (PowerSeriesTerms c z) :=
  seriesConverges_of_summable_norm (powerSeries_interior_summable_norm c z hz)

theorem powerSeries_exterior (c : ℕ → ℂ) (z : ℂ)
    (hz : PowerSeriesRadius c < (‖z‖₊ : ℝ≥0∞)) : ¬ SeriesConverges (PowerSeriesTerms c z) := by
  rintro ⟨A, hA⟩
  have hzero := (seriesHasSum_term_tendsto_zero hA).norm
  have hle := (FormalMultilinearSeries.ofScalars ℂ c).le_radius_of_tendsto
    (r := ‖z‖₊) (by simpa [PowerSeriesTerms, norm_mul, norm_pow,
      FormalMultilinearSeries.ofScalars_norm] using hzero)
  rw [← powerSeriesRadius_reference] at hle
  exact (not_le_of_gt hz) hle

theorem pma3_38 : pma3_38_contract := by
  refine ⟨fun _ _ _ => rfl, ?_⟩
  intro c
  exact ⟨PowerSeriesRadius c, powerSeries_interior c, powerSeries_exterior c⟩

/-! ### PMA-3.39: Cauchy–Hadamard radius, including zero and infinite radii. -/

def pma3_39_contract : Prop :=
  (∀ c, RootLimsup c = 0 → PowerSeriesRadius c = ⊤) ∧
  (∀ c, RootLimsup c = ⊤ → PowerSeriesRadius c = 0) ∧
  (∀ c z, (‖z‖₊ : ℝ≥0∞) < PowerSeriesRadius c →
    SeriesConverges (PowerSeriesTerms c z)) ∧
  (∀ c z, PowerSeriesRadius c < (‖z‖₊ : ℝ≥0∞) →
    ¬ SeriesConverges (PowerSeriesTerms c z))

theorem pma3_39 : pma3_39_contract := by
  refine ⟨?_, ?_, powerSeries_interior, powerSeries_exterior⟩
  · intro c hc
    simp [PowerSeriesRadius, hc]
  · intro c hc
    simp [PowerSeriesRadius, hc]

/-! ### PMA-3.41: summation by parts, with the empty initial partial sum. -/

def pma3_41_contract : Prop := ∀ (a b : ℕ → ℂ) (p q : ℕ), p ≤ q →
  (∑ n ∈ Finset.Icc p q, a n * b n) =
    (∑ n ∈ Finset.Ico p q, PartialSums a (n + 1) * (b n - b (n + 1))) +
    PartialSums a (q + 1) * b q - PartialSums a p * b p

theorem pma3_41 : pma3_41_contract := by
  intro a b p q hpq
  have h : (∑ n ∈ Finset.Icc p q, b n * a n) =
      b q * PartialSums a (q + 1) - b p * PartialSums a p -
      ∑ n ∈ Finset.Ico p q, (b (n + 1) - b n) * PartialSums a (n + 1) := by
    simpa [PartialSums, Finset.Ico_add_one_right_eq_Icc, smul_eq_mul] using
      Finset.sum_Ico_by_parts b a (show p < q + 1 by omega)
  have hs : (∑ n ∈ Finset.Ico p q, PartialSums a (n + 1) * (b n - b (n + 1))) =
      -(∑ n ∈ Finset.Ico p q, (b (n + 1) - b n) * PartialSums a (n + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  calc
    (∑ n ∈ Finset.Icc p q, a n * b n) = ∑ n ∈ Finset.Icc p q, b n * a n := by
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ = _ := by rw [h, hs]; ring

/-! ### PMA-3.42: Dirichlet's test with ordinary convergence. -/

def pma3_42_contract : Prop := ∀ (a : ℕ → ℂ) (b : ℕ → ℝ),
  (∃ M : ℝ, ∀ N, ‖PartialSums a N‖ ≤ M) → Antitone b → Tendsto b atTop (𝓝 0) →
  SeriesConverges (fun n => a n * (b n : ℂ))

theorem pma3_42 : pma3_42_contract := by
  intro a b hb hba hb0
  obtain ⟨M, hM⟩ := hb
  have hc := hba.cauchySeq_series_mul_of_tendsto_zero_of_bounded hb0 hM
  obtain ⟨s, hs⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨s, ?_⟩
  change Tendsto (fun N => ∑ n ∈ Finset.range N, a n * (b n : ℂ)) atTop (𝓝 s)
  simpa [Complex.real_smul, mul_comm] using hs

/-! ### PMA-3.43: alternating-sign and decreasing-magnitude criterion. -/

def pma3_43_contract : Prop := ∀ c : ℕ → ℝ,
  Antitone (fun n => |c n|) → (∀ m, 0 ≤ c (2 * m) ∧ c (2 * m + 1) ≤ 0) →
  Tendsto c atTop (𝓝 0) → SeriesConverges c

theorem pma3_43 : pma3_43_contract := by
  intro c hc hs hc0
  have habs : Tendsto (fun n => |c n|) atTop (𝓝 0) := by simpa using hc0.abs
  obtain ⟨s, hsum⟩ := hc.tendsto_alternating_series_of_tendsto_zero habs
  have he : ∀ n, (-1 : ℝ) ^ n * |c n| = c n := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have hn' : n = 2 * (n / 2) := by omega
      rw [hn']
      simp [pow_mul, abs_of_nonneg (hs (n / 2)).1]
    · have hn' : n = 2 * (n / 2) + 1 := by omega
      rw [hn']
      simp [pow_add, pow_mul, abs_of_nonpos (hs (n / 2)).2]
  refine ⟨s, ?_⟩
  change Tendsto (fun N => ∑ n ∈ Finset.range N, c n) atTop (𝓝 s)
  simpa [he] using hsum

end Rudin.PMA.Chapter03
