import Rudin.PMA.Chapter07.Basic
import Rudin.PMA.Chapter04

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal BoundedContinuousFunction

namespace Rudin.PMA.Chapter07

/-! ### PMA-7.1: Pointwise function limits and ordered function series. -/

def pma7_1_contract : Prop :=
  ∀ {X : Type*} (F : ℕ → X → ℂ) (f : X → ℂ) (E : Set X),
    (PointwiseConvergesOn F f E ↔
      ∀ x ∈ E, ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ‖F n x - f x‖ < ε) ∧
    ((∀ x ∈ E, ∃ z : ℂ, Tendsto (fun n => F n x) atTop (𝓝 z)) ↔
      ∃ g : X → ℂ, PointwiseConvergesOn F g E) ∧
    (PointwiseSeriesConvergesOn F f E ↔
      PointwiseConvergesOn
        (fun N x => Chapter03.PartialSums (fun n => F n x) N) f E)

/-! ### PMA-7.7: Uniform convergence and its ordered-series specialization. -/

def pma7_7_contract : Prop :=
  ∀ {X V : Type*} [NormedAddCommGroup V]
      (F : ℕ → X → V) (f : X → V) (E : Set X),
    (UniformConvergesOn F f E ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ E, ‖F n x - f x‖ ≤ ε) ∧
    (UniformConvergesOn F f E → PointwiseConvergesOn F f E) ∧
    (UniformSeriesConvergesOn F f E ↔ UniformConvergesOn
      (fun N x => Chapter03.PartialSums (fun n => F n x) N) f E)

/-! ### PMA-7.8: The uniform Cauchy criterion includes existence of the limit. -/

def pma7_8_contract : Prop :=
  ∀ {X V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
      (F : ℕ → X → V) (E : Set X),
    (∃ f : X → V, UniformConvergesOn F f E) ↔ UniformCauchyOn F E

/-! ### PMA-7.9: Extended supremum errors and their bounded real comparator. -/

def pma7_9_contract : Prop :=
  (∀ {X V : Type*} [NormedAddCommGroup V]
      (F : ℕ → X → V) (f : X → V) (E : Set X),
    PointwiseConvergesOn F f E →
      (UniformConvergesOn F f E ↔
        Tendsto (fun n => UniformError (F n) f E) atTop (𝓝 0))) ∧
  (∀ {X V : Type*} [NormedAddCommGroup V] (g f : X → V) (E : Set X),
    BddAbove ((fun x => ‖g x - f x‖) '' E) →
      UniformError g f E = ENNReal.ofReal (sSup ((fun x => ‖g x - f x‖) '' E)) ∧
      (UniformError g f E).toReal = sSup ((fun x => ‖g x - f x‖) '' E)) ∧
  (∀ {X V : Type*} [NormedAddCommGroup V] (g f : X → V),
    UniformError g f ∅ = 0)

theorem pma7_1 : pma7_1_contract := by
  intro X F f E
  refine ⟨?_, ?_, Iff.rfl⟩
  · simp only [PointwiseConvergesOn, Metric.tendsto_atTop, dist_eq_norm]
  · constructor
    · intro h
      classical
      let g : X → ℂ := fun x => if hx : x ∈ E then Classical.choose (h x hx) else 0
      refine ⟨g, fun x hx => ?_⟩
      simpa [g, hx] using Classical.choose_spec (h x hx)
    · rintro ⟨g, hg⟩ x hx
      exact ⟨g x, hg x hx⟩

theorem uniformConvergesOn_iff_norm_le {X V : Type*} [NormedAddCommGroup V]
    (F : ℕ → X → V) (f : X → V) (E : Set X) :
    UniformConvergesOn F f E ↔
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ E, ‖F n x - f x‖ ≤ ε := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((Metric.tendstoUniformlyOn_iff.mp h) ε hε)
    refine ⟨N, fun n hn x hx => ?_⟩
    simpa only [dist_eq_norm, norm_sub_rev] using (hN n hn x hx).le
  · intro h
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    refine eventually_atTop.mpr ⟨N, fun n hn x hx => ?_⟩
    rw [dist_comm, dist_eq_norm]
    exact (hN n hn x hx).trans_lt (half_lt_self hε)

theorem pma7_7 : pma7_7_contract := by
  intro X V _ F f E
  refine ⟨uniformConvergesOn_iff_norm_le F f E, ?_, Iff.rfl⟩
  intro h x hx
  exact h.tendsto_at hx

theorem uniformCauchyOn_iff_mathlib {X V : Type*} [NormedAddCommGroup V]
    (F : ℕ → X → V) (E : Set X) :
    UniformCauchyOn F E ↔ UniformCauchySeqOn F atTop E := by
  constructor
  · intro h
    apply Metric.uniformCauchySeqOn_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := h (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    rw [dist_eq_norm]
    exact (hN m hm n hn x hx).trans_lt (half_lt_self hε)
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp h ε hε
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    simpa only [dist_eq_norm] using (hN m hm n hn x hx).le

theorem pma7_8 : pma7_8_contract := by
  intro X V _ _ F E
  constructor
  · rintro ⟨f, h⟩
    exact (uniformCauchyOn_iff_mathlib F E).mpr h.uniformCauchySeqOn
  · intro h
    have hc := (uniformCauchyOn_iff_mathlib F E).mp h
    have hp : ∀ x ∈ E, ∃ v : V, Tendsto (fun n => F n x) atTop (𝓝 v) :=
      fun x hx => cauchySeq_tendsto_of_complete (hc.cauchySeq hx)
    classical
    let f : X → V := fun x => if hx : x ∈ E then Classical.choose (hp x hx) else 0
    refine ⟨f, hc.tendstoUniformlyOn_of_tendsto ?_⟩
    intro x hx
    simpa [f, hx] using Classical.choose_spec (hp x hx)

theorem uniformConvergesOn_iff_uniformError_tendsto {X V : Type*}
    [NormedAddCommGroup V] (F : ℕ → X → V) (f : X → V) (E : Set X) :
    UniformConvergesOn F f E ↔
      Tendsto (fun n => UniformError (F n) f E) atTop (𝓝 0) := by
  constructor
  · intro h
    apply ENNReal.tendsto_nhds_zero.mpr
    intro ε hε
    filter_upwards [(EMetric.tendstoUniformlyOn_iff.mp h) ε hε] with n hn
    apply iSup_le
    intro x
    simpa only [edist_dist, dist_eq_norm, norm_sub_rev] using (hn x x.property).le
  · intro h
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    have he := (ENNReal.tendsto_nhds_zero.mp h) (ENNReal.ofReal (ε / 2))
      (ENNReal.ofReal_pos.mpr (half_pos hε))
    filter_upwards [he] with n hn
    intro x hx
    have hpoint : ENNReal.ofReal ‖F n x - f x‖ ≤ ENNReal.ofReal (ε / 2) :=
      (le_iSup_of_le (⟨x, hx⟩ : E) le_rfl).trans hn
    rw [dist_comm, dist_eq_norm]
    exact ((ENNReal.ofReal_le_ofReal_iff (half_pos hε).le).mp hpoint).trans_lt
      (half_lt_self hε)

theorem uniformError_eq_real_sup {X V : Type*} [NormedAddCommGroup V]
    (g f : X → V) (E : Set X)
    (hb : BddAbove ((fun x => ‖g x - f x‖) '' E)) :
    UniformError g f E = ENNReal.ofReal (sSup ((fun x => ‖g x - f x‖) '' E)) ∧
      (UniformError g f E).toReal = sSup ((fun x => ‖g x - f x‖) '' E) := by
  rcases E.eq_empty_or_nonempty with rfl | hE
  · simp [UniformError]
  have hupper : UniformError g f E ≤
      ENNReal.ofReal (sSup ((fun x => ‖g x - f x‖) '' E)) := by
    apply iSup_le
    intro x
    exact ENNReal.ofReal_le_ofReal (le_csSup hb ⟨x, x.property, rfl⟩)
  have hfinite : UniformError g f E ≠ ⊤ :=
    (hupper.trans_lt ENNReal.ofReal_lt_top).ne
  have hlower : ENNReal.ofReal (sSup ((fun x => ‖g x - f x‖) '' E)) ≤
      UniformError g f E := by
    apply (ENNReal.ofReal_le_iff_le_toReal hfinite).mpr
    apply csSup_le (hE.image _)
    rintro y ⟨x, hx, rfl⟩
    exact (ENNReal.ofReal_le_iff_le_toReal hfinite).mp
      (le_iSup_of_le (⟨x, hx⟩ : E) le_rfl)
  have heq := le_antisymm hupper hlower
  refine ⟨heq, ?_⟩
  obtain ⟨x, hx⟩ := hE
  have hn : 0 ≤ sSup ((fun x => ‖g x - f x‖) '' E) :=
    (norm_nonneg _).trans (le_csSup hb ⟨x, hx, rfl⟩)
  rw [heq, ENNReal.toReal_ofReal hn]

theorem pma7_9 : pma7_9_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro X V _ F f E _
    exact uniformConvergesOn_iff_uniformError_tendsto F f E
  · intro X V _ g f E hb
    exact uniformError_eq_real_sup g f E hb
  · intro X V _ g f
    simp [UniformError]

end Rudin.PMA.Chapter07
