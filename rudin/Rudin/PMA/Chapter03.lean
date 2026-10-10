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
end Rudin.PMA.Chapter03
