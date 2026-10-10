import Rudin.PMA.Chapter02

/-!
Independent fidelity probes for Chapter 2: concrete boundary cases and
counterexamples to tempting weakened or overstrong informal contracts.
-/

namespace Rudin.PMA.Chapter02.FidelityProbes
open Set

theorem finite_at_most_but_not_countably_infinite :
    RudinAtMostCountable (Fin 1) ∧ ¬ RudinCountable (Fin 1) := by
  refine ⟨(pma2_4_atMost_reference _).mpr inferInstance, ?_⟩
  intro h
  exact ((pma2_4_countable_reference _).mp h).2.false

theorem zero_length_tuples_not_countably_infinite :
    ¬ RudinCountable (Fin 0 → ℕ) := by
  intro h
  exact ((pma2_4_countable_reference _).mp h).2.false

theorem singleton_has_no_limit_point : ¬ IsLimitPoint (0 : ℝ) {0} :=
  finite_no_limitPoint (Set.finite_singleton 0) 0

theorem zero_radius_neighborhood_empty : neighborhood (0 : ℝ) 0 = ∅ := by
  rw [neighborhood_eq_ball]
  exact Metric.ball_zero

theorem empty_ambient_literal_boundedness {X : Type*} [MetricSpace X] [IsEmpty X] :
    ¬ IsBoundedSet (∅ : Set X) := by
  rintro ⟨_, q, _⟩
  exact isEmptyElim q

theorem empty_ambient_mathlib_boundedness {X : Type*} [MetricSpace X] :
    Bornology.IsBounded (∅ : Set X) := Bornology.isBounded_empty

theorem empty_real_set_bounded : IsBoundedSet (∅ : Set ℝ) := by
  refine ⟨1, 0, ?_⟩
  simp

theorem empty_perfect_open : IsPerfectSet (∅ : Set ℂ) ∧ IsOpenSet (∅ : Set ℂ) := by
  refine ⟨⟨(isClosedSet_iff_isClosed _).mpr isClosed_empty, ?_⟩,
    (isOpenSet_iff_isOpen _).mpr isOpen_empty⟩
  simp

theorem perfect_uncountability_requires_nonempty :
    ¬ (∀ P : Set ℝ, IsPerfectSet P → ¬ P.Countable) := by
  intro h
  apply h ∅
  · refine ⟨(isClosedSet_iff_isClosed _).mpr isClosed_empty, ?_⟩
    simp
  · exact Set.countable_empty

theorem rudin_empty_connected_but_not_mathlib_connected :
    RudinConnected (∅ : Set ℝ) ∧ ¬ IsConnected (∅ : Set ℝ) := by
  refine ⟨(pma2_45_connected_reference _).mpr isPreconnected_empty, ?_⟩
  intro h
  exact Set.not_nonempty_empty h.1

theorem first_cantor_stage_exact : CantorStages 1 =
    Icc (0 : ℝ) (1/3) ∪ Icc (2/3) 1 := by
  ext x
  rw [cantor_intervals_reference]
  norm_num [CantorIntervals, Set.mem_union]

theorem deleted_midpoint_not_cantor : (1/2 : ℝ) ∉ CantorSet := by
  intro hx
  have hx1 : (1/2 : ℝ) ∈ CantorStages 1 :=
    Set.mem_iInter.mp (show (1/2 : ℝ) ∈ ⋂ n, CantorStages n from hx) 1
  rw [first_cantor_stage_exact] at hx1
  norm_num at hx1

theorem source_interval_family_endpoint :
    (⟨1, by norm_num⟩ : IntervalFamilyIndex).val = 1 := rfl

end Rudin.PMA.Chapter02.FidelityProbes
