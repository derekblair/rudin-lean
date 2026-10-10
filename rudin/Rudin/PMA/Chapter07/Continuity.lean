import Mathlib
import Rudin.PMA.Chapter07.Basic
import Rudin.PMA.Chapter04
import Rudin.PMA.Chapter07.Calculus
import Rudin.PMA.Chapter07.Examples

noncomputable section
open Set Filter Topology
open scoped BigOperators BoundedContinuousFunction
namespace Rudin.PMA.Chapter07

def pma7_11_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] (E : Set X) (F : ℕ → X → ℂ)
      (f : X → ℂ) (x : X) (A : ℕ → ℂ),
    UniformConvergesOn F f E → Chapter02.IsLimitPoint x E →
    (∀ n, Chapter04.FunctionLimitOn E (F n) x (A n)) →
      ∃ a : ℂ, Tendsto A atTop (𝓝 a) ∧ Chapter04.FunctionLimitOn E f x a


def pma7_12_contract : Prop :=
  (∀ {X : Type*} [MetricSpace X] (E : Set X) (F : ℕ → X → ℂ) (f : X → ℂ),
    (∀ n, ContinuousOn (F n) E) → UniformConvergesOn F f E → ContinuousOn f E) ∧
  ((∀ n, ContinuousOn (IntegralSpikeSquared n) (Icc 0 1)) ∧
    PointwiseConvergesOn IntegralSpikeSquared (fun _ => 0) (Icc 0 1) ∧
    ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc 0 1) ∧
    ¬ UniformConvergesOn IntegralSpikeSquared (fun _ => 0) (Icc 0 1))


def pma7_13_contract : Prop :=
  (∀ {X : Type*} [MetricSpace X] (K : Set X) (F : ℕ → X → ℝ) (f : X → ℝ),
    IsCompact K → (∀ n, ContinuousOn (F n) K) → ContinuousOn f K →
    PointwiseConvergesOn F f K → (∀ x ∈ K, Antitone (fun n => F n x)) →
      UniformConvergesOn F f K) ∧
  ((∀ n, ContinuousOn (DiniCounterexample n) (Ioo 0 1)) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, Antitone (fun n => DiniCounterexample n x)) ∧
    PointwiseConvergesOn DiniCounterexample (fun _ => 0) (Ioo 0 1) ∧
    ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Ioo 0 1) ∧
    ¬ UniformConvergesOn DiniCounterexample (fun _ => 0) (Ioo 0 1))


def pma7_14_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X],
    (∀ g : X → ℂ,
      (∃ h : X →ᵇ ℂ, ∀ x, h x = g x) ↔
        Continuous g ∧ ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M) ∧
    (∀ h : X →ᵇ ℂ,
      ‖h‖ = ⨆ x, ‖h x‖) ∧
    (∀ h : X →ᵇ ℂ, (‖h‖ = 0 ↔ ∀ x, h x = 0)) ∧
    (∀ h g : X →ᵇ ℂ, ‖h + g‖ ≤ ‖h‖ + ‖g‖ ∧ dist h g = ‖h - g‖) ∧
    (∀ (F : ℕ → X →ᵇ ℂ) (f : X →ᵇ ℂ),
      Tendsto F atTop (𝓝 f) ↔
        UniformConvergesOn (fun n x => F n x) (fun x => f x) univ) ∧
    (∀ A : Set (X →ᵇ ℂ),
      (BCFUniformlyClosed A ↔ IsClosed A) ∧ BCFUniformClosure A = closure A) ∧
    (IsCompact (univ : Set X) →
      ∀ g : X → ℂ, Continuous g → ∃ M : ℝ, ∀ x, ‖g x‖ ≤ M)


def pma7_15_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X],
    CompleteSpace (X →ᵇ ℂ) ∧
      ∀ F : ℕ → X →ᵇ ℂ, CauchySeq F → ∃ f : X →ᵇ ℂ, Tendsto F atTop (𝓝 f)


theorem pma7_11 : pma7_11_contract := by
  intro X _ E F f x A hF hx hA
  let : (𝓝[E \ {x}] x).NeBot := (Chapter04.functionLimitPoint_iff_neBot E x).mp hx
  have hA' (n : ℕ) : Tendsto (F n) (𝓝[E \ {x}] x) (𝓝 (A n)) :=
    (Chapter04.functionLimitOn_iff_tendsto E (F n) x (A n) hx).mp (hA n)
  have hAC : CauchySeq A := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hF.uniformCauchySeqOn (ε/2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    have hb : dist (A m) (A n) ≤ ε/2 := by
      apply le_of_tendsto ((hA' m).dist (hA' n))
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact le_of_lt (hN m hm n hn y hy.1)
    exact hb.trans_lt (half_lt_self hε)
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hAC
  refine ⟨a, ha, (Chapter04.functionLimitOn_iff_tendsto E f x a hx).mpr ?_⟩
  have hle : (𝓝[E \ {x}] x) ≤ 𝓟 E :=
    le_trans inf_le_right (principal_mono.mpr sdiff_subset)
  have hu := hF.tendstoUniformlyOnFilter.mono_right hle
  exact hu.tendsto_of_eventually_tendsto (Eventually.of_forall hA') ha

theorem bcf_convergence_iff {X : Type*} [MetricSpace X]
    (F : ℕ → X →ᵇ ℂ) (f : X →ᵇ ℂ) :
    Tendsto F atTop (𝓝 f) ↔ UniformConvergesOn (fun n x => F n x) (fun x => f x) univ := by
  exact BoundedContinuousFunction.tendsto_iff_tendstoUniformly.trans tendstoUniformlyOn_univ.symm

theorem pma7_14 : pma7_14_contract := by
  intro X _
  refine ⟨?_, ?_, ?_, ?_, bcf_convergence_iff, ?_, ?_⟩
  · intro g
    constructor
    · rintro ⟨h, hh⟩
      have he : g = h := (funext hh).symm
      rw [he]
      exact ⟨h.continuous, ‖h‖, h.norm_coe_le_norm⟩
    · rintro ⟨hc, M, hM⟩
      exact ⟨BoundedContinuousFunction.ofNormedAddCommGroup g hc M hM, fun _ => rfl⟩
  · exact BoundedContinuousFunction.norm_eq_iSup_norm
  · intro h
    rw [norm_eq_zero]
    exact ⟨fun hh x => by rw [hh]; rfl, fun hh => BoundedContinuousFunction.ext hh⟩
  · intro h g
    exact ⟨norm_add_le h g, dist_eq_norm h g⟩
  · intro A
    constructor
    · have he : BCFUniformlyClosed A ↔ IsSeqClosed A := by
        constructor
        · intro h F f hF ht
          exact h F f hF ((bcf_convergence_iff F f).mp ht)
        · intro h F f hF ht
          exact h hF ((bcf_convergence_iff F f).mpr ht)
      exact he.trans isSeqClosed_iff_isClosed
    · ext f
      simp only [BCFUniformClosure, mem_ofPred_eq, mem_closure_iff_seq_limit]
      exact exists_congr (fun F => and_congr_right (fun _ => (bcf_convergence_iff F f).symm))
  · intro hK g hg
    obtain ⟨M, hM⟩ := (hK.image hg.norm).bddAbove
    exact ⟨M, fun x => hM ⟨x, mem_univ x, rfl⟩⟩

theorem pma7_15 : pma7_15_contract := by
  intro X _
  exact ⟨inferInstance, fun _ h => cauchySeq_tendsto_of_complete h⟩

theorem diniCounterexample_continuous (n : ℕ) :
    ContinuousOn (DiniCounterexample n) (Ioo 0 1) := by
  apply continuousOn_const.div ((continuousOn_const.mul continuousOn_id).add continuousOn_const)
  intro x hx
  have hx0 := hx.1
  have hn : 0 < (n+1 : ℝ) := by positivity
  change (n+1 : ℝ)*x+1 ≠ 0
  exact ne_of_gt (by positivity)

theorem diniCounterexample_antitone (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Antitone (fun n => DiniCounterexample n x) := by
  intro m n hmn
  have hx0 := hx.1
  unfold DiniCounterexample
  apply one_div_le_one_div_of_le
  · positivity
  · have hn : (m : ℝ) ≤ n := by exact_mod_cast hmn
    nlinarith [hx.1]

theorem diniCounterexample_pointwise :
    PointwiseConvergesOn DiniCounterexample (fun _ => 0) (Ioo 0 1) := by
  intro x hx
  have hden : Tendsto (fun n : ℕ => (n+1 : ℝ)*x+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith [hx.1])
      (Tendsto.atTop_mul_const hx.1 (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa [DiniCounterexample, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hden

theorem diniCounterexample_not_uniform :
    ¬ UniformConvergesOn DiniCounterexample (fun _ => 0) (Ioo 0 1) := by
  intro hU
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hU (1/2 : ℝ) (by norm_num))
  let x : ℝ := (2*((N : ℝ)+1))⁻¹
  have hn : 0 < (N : ℝ)+1 := by positivity
  have hx : x ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · dsimp [x]; positivity
    · apply inv_lt_one_of_one_lt₀
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
  have hv : DiniCounterexample N x = 2/3 := by
    unfold DiniCounterexample
    dsimp [x]
    field_simp
    ring
  have hh := hN N le_rfl x hx
  norm_num [Real.dist_eq, hv] at hh

theorem pma7_13 : pma7_13_contract := by
  constructor
  · intro X _ K F f hK hF hf hlim hanti
    exact Antitone.tendstoUniformlyOn_of_forall_tendsto hK hF hanti hf hlim
  · exact ⟨diniCounterexample_continuous, diniCounterexample_antitone,
      diniCounterexample_pointwise, continuousOn_const, diniCounterexample_not_uniform⟩

theorem integralSpikeSquared_not_uniform :
    ¬ UniformConvergesOn IntegralSpikeSquared (fun _ => 0) (Icc 0 1) := by
  intro hU
  have ht := (rsIntegral_tendsto_of_uniformLimit
    (fun n => (integralSpikeSquared_integral n).1) hU).2
  exact not_tendsto_nhds_of_tendsto_atTop integralSpikeSquared_integrals_atTop _ ht

theorem pma7_12 : pma7_12_contract := by
  constructor
  · intro X _ E F f hF hU
    exact hU.continuousOn (Frequently.of_forall hF)
  · exact ⟨fun n => (integralSpikeSquared_continuous n).continuousOn,
      integralSpikeSquared_pointwise, continuousOn_const, integralSpikeSquared_not_uniform⟩

end Rudin.PMA.Chapter07
