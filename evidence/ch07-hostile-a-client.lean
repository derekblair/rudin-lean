import Rudin.PMA.Chapter07.Examples
import Rudin.PMA.Chapter07.RationalIndicator
import Rudin.PMA.Chapter07.MTest
import Rudin.PMA.Chapter07.Continuity
import Rudin.PMA.Chapter07.Calculus
import Rudin.PMA.Chapter07.Nowhere
import Rudin.PMA.Chapter07.NoSubsequence
import Rudin.PMA.Chapter07.Equicontinuity
import Rudin.PMA.Chapter07.Algebra

noncomputable section
open Set Filter Topology
open Rudin.PMA Rudin.PMA.Chapter07
namespace Chapter07HostileA

theorem empty_majorant (F : ℕ → ℝ → ℂ) :
    ∃ f, UniformSeriesConvergesOn F f ∅ := by
  exact pma7_10.1 F ∅ Chapter03.AlternatingHarmonic (by simp)
    Chapter03.alternatingHarmonic_converges

theorem right_limit_without_membership :
    (0 : ℝ) ∉ Ioi 0 ∧
      ∃ a : ℂ, Tendsto (fun _ : ℕ => (Complex.I : ℂ)) atTop (𝓝 a) ∧
        Chapter04.FunctionLimitOn (Ioi (0 : ℝ)) (fun _ => Complex.I) 0 a := by
  have hp : Chapter02.IsLimitPoint (0 : ℝ) (Ioi 0) := by
    intro r hr
    refine ⟨r/2, half_pos hr, (half_pos hr).ne', ?_⟩
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_pos (half_pos hr)] using
      half_lt_self hr
  refine ⟨by simp, ?_⟩
  apply pma7_11 (Ioi 0) (fun _ _ => Complex.I) (fun _ => Complex.I) 0
    (fun _ => Complex.I) (calculus_constFamily_uniform _ _) hp
  intro n
  exact ⟨hp, fun ε hε => ⟨1, zero_lt_one, fun _ _ _ _ => by simpa using hε⟩⟩

theorem countable_empty (F : ℕ → ℝ → ℂ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℂ,
      ∀ x ∈ (∅ : Set ℝ), Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by
  exact pma7_23 ∅ F Set.countable_empty (by intro x hx; simp at hx)

theorem compact_empty (F : ℕ → ℝ → ℂ) :
    UniformlyBoundedOn F ∅ ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℝ → ℂ,
      ContinuousOn f ∅ ∧ TendstoUniformlyOn (fun n x => F (φ n) x) f atTop ∅ := by
  apply pma7_25 ∅ F isCompact_empty (fun n => continuousOn_empty (F n))
  · intro x hx
    simp at hx
  · intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    simp at hx

theorem polynomial_singleton (f : ℝ → ℂ) (a : ℝ) :
    ∃ P : ℕ → Polynomial ℂ,
      TendstoUniformlyOn (fun n (x : ℝ) => (P n).eval (x : ℂ)) f atTop (Icc a a) := by
  apply pma7_26.1 a a le_rfl f
  simpa only [Icc_self] using continuousOn_singleton f a

theorem abs_zero_radius :
    ∃ P : ℕ → Polynomial ℝ, (∀ n, (P n).eval 0 = 0) ∧
      TendstoUniformlyOn (fun n x => (P n).eval x) abs atTop (Icc 0 0) := by
  simpa only [neg_zero] using pma7_27 0 le_rfl

def twoPointZeroAlgebra : Set (Bool → ℝ) := {f | f false = 0}

theorem zero_algebra_nonunital :
    IsFunctionAlgebra twoPointZeroAlgebra ∧
      (fun _ : Bool => (1 : ℝ)) ∉ twoPointZeroAlgebra := by
  refine ⟨⟨⟨fun _ => 0, rfl⟩, ?_, ?_, ?_⟩, by norm_num [twoPointZeroAlgebra]⟩
  · intro f hf g hg
    change f false + g false = 0
    rw [hf, hg, add_zero]
  · intro f hf g hg
    change f false * g false = 0
    rw [hf, zero_mul]
  · intro c f hf
    change c * f false = 0
    rw [hf, mul_zero]

theorem closure_nonunital_without_topology :
    IsFunctionAlgebra (AlgebraUniformClosure twoPointZeroAlgebra) ∧
      IsAlgebraUniformlyClosed (AlgebraUniformClosure twoPointZeroAlgebra) := by
  have hb : ∀ f ∈ twoPointZeroAlgebra, AlgebraFunctionBounded f := by
    intro f _
    refine ⟨‖f false‖ + ‖f true‖, ?_⟩
    intro x
    cases x
    · exact le_add_of_nonneg_right (norm_nonneg _)
    · exact le_add_of_nonneg_left (norm_nonneg _)
  exact ⟨(pma7_29.1 Bool twoPointZeroAlgebra zero_algebra_nonunital.1 hb).1,
    (pma7_29.1 Bool twoPointZeroAlgebra zero_algebra_nonunital.1 hb).2.1⟩

theorem discontinuous_functions_allowed_729
    (A : Set (ℝ → ℂ)) (hA : IsFunctionAlgebra A)
    (hb : ∀ f ∈ A, AlgebraFunctionBounded f) :
    IsFunctionAlgebra (AlgebraUniformClosure A) ∧
      IsAlgebraUniformlyClosed (AlgebraUniformClosure A) :=
  ⟨(pma7_29.2 ℝ A hA hb).1, (pma7_29.2 ℝ A hA hb).2.1⟩

#print axioms empty_majorant
#print axioms right_limit_without_membership
#print axioms countable_empty
#print axioms compact_empty
#print axioms polynomial_singleton
#print axioms abs_zero_radius
#print axioms zero_algebra_nonunital
#print axioms closure_nonunital_without_topology
#print axioms discontinuous_functions_allowed_729

#print axioms pma7_2
#print axioms pma7_3
#print axioms pma7_4
#print axioms pma7_5
#print axioms pma7_6
#print axioms pma7_10
#print axioms pma7_11
#print axioms pma7_12
#print axioms pma7_13
#print axioms pma7_14
#print axioms pma7_15
#print axioms pma7_16
#print axioms pma7_17
#print axioms pma7_18
#print axioms pma7_19
#print axioms pma7_20
#print axioms pma7_21
#print axioms pma7_22
#print axioms pma7_23
#print axioms pma7_24
#print axioms pma7_25
#print axioms pma7_26
#print axioms pma7_27
#print axioms pma7_28
#print axioms pma7_29
#print axioms pma7_30
#print axioms pma7_31
#print axioms pma7_32
#print axioms pma7_33

end Chapter07HostileA
