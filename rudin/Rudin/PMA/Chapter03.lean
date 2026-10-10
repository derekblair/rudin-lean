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

end Rudin.PMA.Chapter03
