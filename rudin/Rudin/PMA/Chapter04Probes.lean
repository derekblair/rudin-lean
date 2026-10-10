import Rudin.PMA.Chapter04

/-! Independent boundary and counterexample probes for PMA Chapter 4. -/
noncomputable section
open Set Filter Topology

namespace Rudin.PMA.Chapter04.FidelityProbes

/-- An isolated domain point admits continuity, but never a punctured function limit. -/
theorem singleton_continuous_but_no_limit (f : ℝ → ℝ) (p q : ℝ) :
    FunctionContinuousWithinAt {p} f p ∧ ¬ FunctionLimitOn {p} f p q := by
  constructor
  · refine ⟨by simp, fun ε hε => ⟨1, by norm_num, ?_⟩⟩
    intro x hx _
    simpa only [mem_singleton_iff.mp hx, dist_self] using hε
  · intro h
    obtain ⟨x, hx, hne, _⟩ := h.1 1 (by norm_num)
    exact hne (mem_singleton_iff.mp hx)

private theorem zero_accumulates_from_right : Chapter02.IsLimitPoint (0 : ℝ) (Ioi 0) := by
  intro r hr
  refine ⟨r / 2, by simpa using half_pos hr, ne_of_gt (half_pos hr), ?_⟩
  rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (half_pos hr)]
  linarith

/-- The approach point lies outside the domain, yet the nonvacuous limit exists. -/
theorem limit_outside_domain :
    (0 : ℝ) ∉ Ioi 0 ∧ FunctionLimitOn (Ioi 0) (fun x : ℝ => x) 0 0 := by
  refine ⟨by simp, zero_accumulates_from_right, ?_⟩
  exact fun ε hε => ⟨ε, hε, fun _ _ _ h => h⟩

private theorem zero_accumulates_univ : Chapter02.IsLimitPoint (0 : ℝ) univ := by
  intro r hr
  obtain ⟨x, _, hne, hd⟩ := zero_accumulates_from_right r hr
  exact ⟨x, mem_univ _, hne, hd⟩

/-- Changing the value at the approach point changes continuity but not the limit. -/
theorem removable_value_disagrees :
    let f : ℝ → ℝ := fun x => if x = 0 then 1 else 0
    FunctionLimitOn univ f 0 0 ∧ f 0 ≠ 0 ∧ ¬ FunctionContinuousWithinAt univ f 0 := by
  dsimp only
  have hl : FunctionLimitOn univ (fun x : ℝ => if x = 0 then (1 : ℝ) else 0) 0 0 := by
    refine ⟨zero_accumulates_univ, fun ε hε => ⟨1, by norm_num, ?_⟩⟩
    intro x _ hx _
    simpa [ne_of_gt hx, dist_pos.mp hx] using hε
  refine ⟨hl, by norm_num, ?_⟩
  intro hc
  have hv := (pma4_6 univ _ 0 (mem_univ _) zero_accumulates_univ).mp hc
  have he := functionLimitOn_unique univ _ 0 0 _ hl hv
  norm_num at he

/-- No requirement that the denominator be nonzero throughout the original domain. -/
theorem denominator_may_vanish_away_from_approach :
    let g : ℝ → ℂ := fun x => if x = 2 then 0 else 1
    g 2 = 0 ∧ FunctionLimitOn (QuotientDomain univ g)
      (ComplexQuotient (fun _ => 1) g) 0 1 := by
  dsimp only
  let g : ℝ → ℂ := fun x => if x = 2 then 0 else 1
  have hg : FunctionLimitOn univ g 0 1 := by
    refine ⟨zero_accumulates_univ, fun ε hε => ⟨1, by norm_num, ?_⟩⟩
    intro x _ _ hx
    have hne : x ≠ 2 := by
      intro he
      norm_num [he] at hx
    simpa [g, hne] using hε
  have hf : FunctionLimitOn univ (fun _ : ℝ => (1 : ℂ)) 0 1 :=
    ⟨zero_accumulates_univ, fun ε hε => ⟨1, by norm_num, fun _ _ _ _ => by simpa using hε⟩⟩
  refine ⟨by simp, ?_⟩
  simpa using (pma4_4.{0, 0}.1 univ (fun _ : ℝ => (1 : ℂ)) g 0 1 1 hf hg).2.2 one_ne_zero

/-- Removing the nonzero denominator-limit hypothesis gives the wrong answer 0/0. -/
theorem zero_over_zero_limit_counterexample :
    let f : ℝ → ℂ := fun x => (x : ℂ)
    FunctionLimitOn univ f 0 0 ∧
      FunctionLimitOn (QuotientDomain univ f) (ComplexQuotient f f) 0 1 ∧
      ¬ FunctionLimitOn (QuotientDomain univ f) (ComplexQuotient f f) 0 (0 / 0 : ℂ) := by
  dsimp only
  let f : ℝ → ℂ := fun x => (x : ℂ)
  have hf : FunctionLimitOn univ f 0 0 := by
    refine (functionLimitOn_iff_tendsto univ f 0 0 zero_accumulates_univ).mpr ?_
    exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hp : Chapter02.IsLimitPoint (0 : ℝ) (QuotientDomain univ f) := by
    intro r hr
    obtain ⟨x, hx, hne, hd⟩ := zero_accumulates_from_right r hr
    refine ⟨x, ⟨mem_univ _, ?_⟩, hne, hd⟩
    simpa [f] using hne
  have hq : FunctionLimitOn (QuotientDomain univ f) (ComplexQuotient f f) 0 1 := by
    refine ⟨hp, fun ε hε => ⟨1, by norm_num, ?_⟩⟩
    intro x hx _ _
    simpa [ComplexQuotient, div_self hx.2] using hε
  refine ⟨hf, hq, ?_⟩
  intro hbad
  have he := functionLimitOn_unique _ _ 0 1 _ hq hbad
  norm_num at he

/-- Empty compact domains are legitimate; attaining an extremum needs nonemptiness. -/
theorem empty_compact_cannot_attain :
    IsCompact (∅ : Set ℝ) ∧
      ¬ ∃ _x : (∅ : Set ℝ), ∀ _y : (∅ : Set ℝ), (0 : ℝ) ≤ 0 := by
  exact ⟨isCompact_empty, fun ⟨x, _⟩ => x.property⟩

/-- Rudin's connectedness and its image formulation retain the empty set. -/
theorem empty_connected_image (f : ℝ → ℝ) :
    Chapter02.RudinConnected (∅ : Set ℝ) ∧ Chapter02.RudinConnected (f '' ∅) := by
  constructor
  · exact (Chapter02.pma2_45_connected_reference _).mpr isPreconnected_empty
  · simpa only [image_empty] using
      (Chapter02.pma2_45_connected_reference (∅ : Set ℝ)).mpr isPreconnected_empty

/-- Right limits include the left interval endpoint, despite that point being outside the domain. -/
theorem one_sided_boundary_asymmetry :
    RightLimitOn 0 1 (fun x : ℝ => x) 0 0 ∧
      ¬ LeftLimitOn 0 1 (fun x : ℝ => x) 0 0 := by
  exact ⟨⟨le_rfl, by norm_num, tendsto_id.mono_left nhdsWithin_le_nhds⟩,
    fun h => (lt_irrefl 0) h.1⟩

/-- Constants meet both non-strict monotonicity definitions. -/
theorem constants_are_both_monotonic (a b c : ℝ) :
    IntervalIncreasing a b (fun _ => c) ∧ IntervalDecreasing a b (fun _ => c) := by
  exact ⟨fun _ _ _ _ _ => le_rfl, fun _ _ _ _ _ => le_rfl⟩

/-- Existence of both one-sided limits alone does not define a first-kind discontinuity. -/
theorem constant_not_first_kind (a b c x : ℝ) :
    ¬ FirstKindDiscontinuityOn a b (fun _ => c) x := by
  intro h
  apply h.2.1
  exact ⟨h.1, fun ε hε => ⟨1, by norm_num, fun _ _ _ => by simpa using hε⟩⟩

/-- Both branch boundaries are tested, together with a rational input distinguishing x from 1. -/
theorem literal_example_values :
    PiecewiseJump (-2) = 0 ∧ PiecewiseJump 0 = 2 ∧ RationalIdentity 2 = 2 := by
  norm_num [PiecewiseJump, RationalIdentity, irrational_iff_ne_rational]

/-- Empty jump families are valid and yield the zero function on both conventions. -/
theorem empty_jump_family (p c : Empty → ℝ) (x : ℝ) :
    JumpSumLeft p c x = 0 ∧ JumpSumRight p c x = 0 := by
  simp [JumpSumLeft, JumpSumRight]

/-- A one-point family distinguishes the left and right values at the jump. -/
theorem singleton_jump_family :
    JumpSumLeft (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 3) 0 = 0 ∧
      JumpSumRight (fun _ : Fin 1 => (0 : ℝ)) (fun _ => 3) 0 = 3 := by
  simp [JumpSumLeft, JumpSumRight]

/-- Repeated point indices combine weights, demonstrating why injectivity is necessary. -/
theorem repeated_jump_points_combine :
    JumpSumRight (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1) 0 -
      JumpSumLeft (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1) 0 = 2 := by
  norm_num [JumpSumLeft, JumpSumRight, tsum_fintype, Fin.sum_univ_two]

/-- The corrected extended definition rejects the book's isolated-point vacuity. -/
theorem singleton_extended_limit_rejected (p : ℝ) (f : ℝ → ℝ) (A : EReal) :
    ¬ ExtendedLimitOn {p} f (p : EReal) A := by
  intro h
  have hV : ExtendedNeighborhood (p : EReal) (Ioo (p - 1) (p + 1)) := by
    simp only [ExtendedNeighborhood, EReal.coe_ne_top, ↓reduceIte, EReal.coe_ne_bot,
      EReal.toReal_coe]
    exact ⟨p - 1, p + 1, by linarith, by linarith, rfl⟩
  obtain ⟨t, ht, hne, _⟩ := h.1 _ hV
  exact hne (congrArg (fun z : ℝ => (z : EReal)) (mem_singleton_iff.mp ht))

/-- Every forbidden infinite addition and zero-times-infinity case is excluded. -/
theorem forbidden_extended_sum_product :
    ¬ ExtendedAddDefined ⊤ ⊥ ∧ ¬ ExtendedAddDefined ⊥ ⊤ ∧
      ¬ ExtendedMulDefined 0 ⊤ ∧ ¬ ExtendedMulDefined 0 ⊥ ∧
      ¬ ExtendedMulDefined ⊤ 0 ∧ ¬ ExtendedMulDefined ⊥ 0 := by
  simp [ExtendedAddDefined, ExtendedMulDefined]

/-- Every infinity/infinity combination and every zero denominator is excluded. -/
theorem forbidden_extended_quotients (A : EReal) :
    ¬ ExtendedDivDefined ⊤ ⊤ ∧ ¬ ExtendedDivDefined ⊤ ⊥ ∧
      ¬ ExtendedDivDefined ⊥ ⊤ ∧ ¬ ExtendedDivDefined ⊥ ⊥ ∧
      ¬ ExtendedDivDefined A 0 := by
  simp [ExtendedDivDefined]

/-- Admissibility does not exclude legitimate finite/infinite operations. -/
theorem permitted_extended_arithmetic :
    ExtendedAddDefined ⊤ ⊤ ∧ ExtendedAddDefined ⊥ ⊥ ∧
      ExtendedAddDefined 0 ⊤ ∧ ExtendedMulDefined 0 0 ∧
      ExtendedMulDefined (-1) ⊤ ∧ ExtendedMulDefined ⊥ ⊤ ∧
      ExtendedDivDefined 0 ⊤ ∧ ExtendedDivDefined 1 ⊥ ∧
      ExtendedDivDefined ⊤ (-1) := by
  norm_num [ExtendedAddDefined, ExtendedMulDefined, ExtendedDivDefined]
  exact ⟨⟨EReal.coe_ne_top 1, EReal.coe_ne_bot 1⟩, EReal.coe_ne_bot 1, EReal.coe_ne_top 1⟩

end Rudin.PMA.Chapter04.FidelityProbes
