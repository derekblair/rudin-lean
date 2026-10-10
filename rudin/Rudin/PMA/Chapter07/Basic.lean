import Mathlib
import Rudin.PMA.Chapter03

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

namespace Rudin.PMA.Chapter07

/-! Shared definitions independently approved before publication.
Sequences use zero-based internal indices. For the source's positive-indexed
examples, internal index n denotes source index n+1. Partial sums contain the
first N terms in that order; no unconditional-series semantics is substituted. -/

def PointwiseConvergesOn {X V : Type*} [TopologicalSpace V]
    (F : ℕ → X → V) (f : X → V) (E : Set X) : Prop :=
  ∀ x ∈ E, Tendsto (fun n => F n x) atTop (𝓝 (f x))

def UniformConvergesOn {X V : Type*} [UniformSpace V]
    (F : ℕ → X → V) (f : X → V) (E : Set X) : Prop :=
  TendstoUniformlyOn F f atTop E

def PointwiseSeriesConvergesOn {X V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (F : ℕ → X → V) (f : X → V) (E : Set X) : Prop :=
  ∀ x ∈ E, Chapter03.SeriesHasSum (fun n => F n x) (f x)

def UniformSeriesConvergesOn {X V : Type*} [AddCommMonoid V] [UniformSpace V]
    (F : ℕ → X → V) (f : X → V) (E : Set X) : Prop :=
  UniformConvergesOn (fun N x => Chapter03.PartialSums (fun n => F n x) N) f E

def UniformCauchyOn {X V : Type*} [NormedAddCommGroup V]
    (F : ℕ → X → V) (E : Set X) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ E, ‖F m x - F n x‖ ≤ ε

def UniformError {X V : Type*} [NormedAddCommGroup V]
    (g f : X → V) (E : Set X) : ℝ≥0∞ :=
  ⨆ x : E, ENNReal.ofReal ‖g x - f x‖

def IntegralSpikeSquared (n : ℕ) (x : ℝ) : ℝ :=
  (n + 1 : ℝ)^2 * x * (1 - x^2)^(n+1)

def IntegralSpikeLinear (n : ℕ) (x : ℝ) : ℝ :=
  (n + 1 : ℝ) * x * (1 - x^2)^(n+1)

def DiniCounterexample (n : ℕ) (x : ℝ) : ℝ := 1 / ((n+1 : ℝ) * x + 1)

def BCFUniformlyClosed {X : Type*} [MetricSpace X] (A : Set (X →ᵇ ℂ)) : Prop :=
  ∀ (F : ℕ → X →ᵇ ℂ) (f : X →ᵇ ℂ), (∀ n, F n ∈ A) →
    UniformConvergesOn (fun n x => F n x) (fun x => f x) univ → f ∈ A

def BCFUniformClosure {X : Type*} [MetricSpace X] (A : Set (X →ᵇ ℂ)) :
    Set (X →ᵇ ℂ) :=
  {f | ∃ F : ℕ → X →ᵇ ℂ, (∀ n, F n ∈ A) ∧
    UniformConvergesOn (fun n x => F n x) (fun x => f x) univ}

end Rudin.PMA.Chapter07
