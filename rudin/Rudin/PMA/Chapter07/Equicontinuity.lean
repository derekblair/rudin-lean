import Mathlib
import Rudin.PMA.Chapter07.Basic
import Rudin.PMA.Chapter07.Examples

/-!
PMA 7.19 and 7.21–7.25, with independently accepted typed contracts.
Root oversight accepted the exact contract draft before proof implementation.

Abstract sequences use `ℕ`; index `n` represents the source's positive index
`n + 1` in the two explicit examples below. All subsequences use `StrictMono`.
-/

noncomputable section
open Set Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace Rudin.PMA.Chapter07

/-- One finite bound for each domain point, uniform over the family index. -/
def PointwiseBoundedOn {ι X V : Type*} [NormedAddCommGroup V]
    (F : ι → X → V) (E : Set X) : Prop :=
  ∀ x ∈ E, ∃ M : ℝ, ∀ i, ‖F i x‖ ≤ M

/-- One finite bound for every family member and every domain point. -/
def UniformlyBoundedOn {ι X V : Type*} [NormedAddCommGroup V]
    (F : ι → X → V) (E : Set X) : Prop :=
  ∃ M : ℝ, ∀ i, ∀ x ∈ E, ‖F i x‖ ≤ M

/-- Each individual function is bounded; its bound may depend on the index. -/
def IndividuallyBoundedOn {ι X V : Type*} [NormedAddCommGroup V]
    (F : ι → X → V) (E : Set X) : Prop :=
  ∀ i, ∃ M : ℝ, ∀ x ∈ E, ‖F i x‖ ≤ M

/-- The source's equicontinuity is uniform over both points and all indices. -/
def SourceEquicontinuousOn {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : ι → X → Y) (E : Set X) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, ∀ y ∈ E,
    dist x y < δ → ∀ i, dist (F i x) (F i y) < ε

/-! ### PMA-7.19: Boundedness definitions and countable-subset selection -/

def pma7_19_contract : Prop :=
  (∀ {ι X V : Type*} [NormedAddCommGroup V] (F : ι → X → V) (E : Set X),
    (PointwiseBoundedOn F E ↔ ∀ x ∈ E, ∃ M : ℝ, ∀ i, ‖F i x‖ ≤ M) ∧
    (UniformlyBoundedOn F E ↔ ∃ M : ℝ, ∀ i, ∀ x ∈ E, ‖F i x‖ ≤ M)) ∧
  (∀ {X : Type*} (F : ℕ → X → ℂ) (E D : Set X),
    PointwiseBoundedOn F E → D ⊆ E → D.Countable →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
        ∀ x ∈ D, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)))

/-! ### PMA-7.21: Moving peaks and the two boundedness observations -/

/-- The exact real-valued source example, with positive indices shifted by one. -/
def equicontinuityPeak (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 / (x ^ 2 + (1 - ((n : ℝ) + 1) * x) ^ 2)

/-- The n²-scaled PMA-7.6 bump, viewed as complex-valued for the boundedness caution.
This definition identifies the witness only; no duplicate PMA-7.6 proof is asserted. -/
def boundednessBump (n : ℕ) (x : ℝ) : ℂ :=
  (((n : ℝ) + 1) ^ 2 * x * (1 - x ^ 2) ^ (n + 1) : ℝ)

def pma7_21_contract : Prop :=
  (∀ n : ℕ, ContinuousOn (equicontinuityPeak n) (Icc 0 1)) ∧
  (∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) 1,
    0 ≤ equicontinuityPeak n x ∧ equicontinuityPeak n x ≤ 1) ∧
  UniformlyBoundedOn equicontinuityPeak (Icc 0 1) ∧
  (∀ x ∈ Icc (0 : ℝ) 1,
    Tendsto (fun n => equicontinuityPeak n x) atTop (𝓝 0)) ∧
  (∀ n : ℕ, (((n : ℝ) + 1)⁻¹ ∈ Icc (0 : ℝ) 1) ∧
    equicontinuityPeak n (((n : ℝ) + 1)⁻¹) = 1) ∧
  (∀ φ : ℕ → ℕ, StrictMono φ →
    ¬ ∃ f : ℝ → ℝ,
      TendstoUniformlyOn (fun n x => equicontinuityPeak (φ n) x) f atTop (Icc 0 1)) ∧
  (IndividuallyBoundedOn boundednessBump (Icc 0 1) ∧
    (∀ x ∈ Icc (0 : ℝ) 1,
      Tendsto (fun n => boundednessBump n x) atTop (𝓝 0)) ∧
    ¬ UniformlyBoundedOn boundednessBump (Icc 0 1)) ∧
  (∀ {X V : Type*} [NormedAddCommGroup V] (F : ℕ → X → V) (f : X → V) (E : Set X),
    IndividuallyBoundedOn F E → TendstoUniformlyOn F f atTop E →
      UniformlyBoundedOn F E)

/-! ### PMA-7.22: Uniform equicontinuity and its failure for the moving peaks -/

def pma7_22_contract : Prop :=
  (∀ {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : ι → X → Y) (E : Set X),
    (SourceEquicontinuousOn F E ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x ∈ E, ∀ y ∈ E,
        dist x y < δ → ∀ i, dist (F i x) (F i y) < ε) ∧
    (SourceEquicontinuousOn F E ↔ UniformEquicontinuousOn F E) ∧
    (SourceEquicontinuousOn F E → ∀ i, UniformContinuousOn (F i) E)) ∧
  ¬ SourceEquicontinuousOn equicontinuityPeak (Icc 0 1)

/-! ### PMA-7.23: Diagonal selection on a countable set, without domain topology -/

def pma7_23_contract : Prop :=
  ∀ {X : Type*} (E : Set X) (F : ℕ → X → ℂ),
    E.Countable → PointwiseBoundedOn F E →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
        ∀ x ∈ E, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x))

/-! ### PMA-7.24: Uniform convergence yields equicontinuity of the full sequence -/

def pma7_24_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] (K : Set X) (F : ℕ → X → ℂ) (f : X → ℂ),
    IsCompact K → (∀ n, ContinuousOn (F n) K) →
    TendstoUniformlyOn F f atTop K → SourceEquicontinuousOn F K

/-! ### PMA-7.25: Uniform boundedness and a uniformly convergent subsequence -/

def pma7_25_contract : Prop :=
  ∀ {X : Type*} [MetricSpace X] (K : Set X) (F : ℕ → X → ℂ),
    IsCompact K → (∀ n, ContinuousOn (F n) K) →
    PointwiseBoundedOn F K → SourceEquicontinuousOn F K →
      UniformlyBoundedOn F K ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
          ContinuousOn f K ∧ TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K

theorem sourceEquicontinuousOn_iff_uniformEquicontinuousOn
    {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (F : ι → X → Y) (E : Set X) :
    SourceEquicontinuousOn F E ↔ UniformEquicontinuousOn F E := by
  rw [← uniformEquicontinuous_restrict_iff, Metric.uniformEquicontinuous_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x y hxy i => h x x.property y y.property hxy i⟩
  · intro h ε hε
    obtain ⟨δ, hδ, h⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx y hy hxy i => h ⟨x, hx⟩ ⟨y, hy⟩ hxy i⟩

theorem SourceEquicontinuousOn.uniformContinuousOn
    {ι X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {F : ι → X → Y} {E : Set X} (h : SourceEquicontinuousOn F E) (i : ι) :
    UniformContinuousOn (F i) E :=
  ((sourceEquicontinuousOn_iff_uniformEquicontinuousOn F E).mp h).uniformContinuousOn i

theorem pointwiseBounded_countable_selection {X : Type*} (E : Set X)
    (F : ℕ → X → ℂ) (hE : E.Countable) (hb : PointwiseBoundedOn F E) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
      ∀ x ∈ E, Tendsto (fun n => F (φ n) x) atTop (𝓝 (f x)) := by
  classical
  let : Countable E := hE.to_subtype
  choose M hM using (fun x : E => hb x x.property)
  let G : ℕ → E → ℂ := fun n x => F n x
  have hc : IsCompact (Set.univ.pi (fun x : E => Metric.closedBall (0 : ℂ) (M x))) :=
    isCompact_univ_pi (fun x => isCompact_closedBall 0 (M x))
  have hg : ∀ n, G n ∈ Set.univ.pi (fun x : E => Metric.closedBall (0 : ℂ) (M x)) := by
    intro n x _
    simpa [G, Metric.mem_closedBall, dist_zero_right] using hM x n
  obtain ⟨g, _, φ, hφ, ht⟩ := hc.tendsto_subseq hg
  refine ⟨φ, hφ, fun x => if hx : x ∈ E then g ⟨x, hx⟩ else 0, ?_⟩
  intro x hx
  simpa [G, Function.comp_def, hx] using (tendsto_pi_nhds.mp ht) ⟨x, hx⟩

theorem pma7_23 : pma7_23_contract := pointwiseBounded_countable_selection

theorem pma7_19 : pma7_19_contract := by
  refine ⟨fun _ _ => ⟨Iff.rfl, Iff.rfl⟩, ?_⟩
  intro X F E D hb hDE hD
  exact pointwiseBounded_countable_selection D F hD (fun x hx => hb x (hDE hx))

theorem pointwiseBounded_equicontinuous_uniformlyBounded
    {X : Type*} [MetricSpace X] {K : Set X} {F : ℕ → X → ℂ}
    (hK : IsCompact K) (hb : PointwiseBoundedOn F K)
    (he : SourceEquicontinuousOn F K) : UniformlyBoundedOn F K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  choose M hM using (fun x : K => hb x x.property)
  obtain ⟨δ, hδ, hd⟩ := he 1 zero_lt_one
  obtain ⟨s, _, hs⟩ := (isCompact_univ : IsCompact (univ : Set K)).elim_nhds_subcover
    (fun x => Metric.ball x δ) (fun x _ => Metric.ball_mem_nhds x hδ)
  refine ⟨(∑ y ∈ s, |M y|) + 1, ?_⟩
  intro n x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ (⟨x, hx⟩ : K)))
  have hd' := hd x hx y y.property (show dist x y < δ from hxy) n
  have hsum := Finset.single_le_sum (fun y (_ : y ∈ s) => abs_nonneg (M y)) hy
  calc
    ‖F n x‖ ≤ dist (F n x) (F n y) + ‖F n y‖ := by
      simpa [dist_eq_norm] using norm_add_le (F n x - F n y) (F n y)
    _ ≤ 1 + |M y| := add_le_add hd'.le ((hM y n).trans (le_abs_self _))
    _ ≤ (∑ y ∈ s, |M y|) + 1 := by linarith

theorem compact_equicontinuous_subsequence
    {X : Type*} [MetricSpace X] {K : Set X} {F : ℕ → X → ℂ}
    (hK : IsCompact K) (hc : ∀ n, ContinuousOn (F n) K)
    (hb : UniformlyBoundedOn F K) (he : SourceEquicontinuousOn F K) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → ℂ,
      ContinuousOn f K ∧ TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let G : ℕ → K →ᵇ ℂ := fun n =>
    BoundedContinuousFunction.mkOfCompact ⟨K.domRestrict (F n), (hc n).domRestrict⟩
  obtain ⟨M, hM⟩ := hb
  have hin : ∀ (g : K →ᵇ ℂ) (x : K), g ∈ range G → g x ∈ Metric.closedBall 0 M := by
    rintro g x ⟨n, rfl⟩
    simpa [G, Metric.mem_closedBall, dist_zero_right] using hM n x x.property
  have he' : Equicontinuous ((↑) : range G → K → ℂ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := he ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy g
    obtain ⟨n, hn⟩ := g.property
    have hg : (g.val : K → ℂ) = G n := congrArg DFunLike.coe hn.symm
    rw [hg]
    exact hd x x.property y y.property
      (by simpa only [Subtype.dist_eq, dist_comm] using hy) n
  have hcompact := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℂ) M)
    (isCompact_closedBall 0 M) (range G) hin he'
  obtain ⟨g, _, φ, hφ, ht⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  let f : X → ℂ := fun x => if hx : x ∈ K then g ⟨x, hx⟩ else 0
  have hunif : TendstoUniformlyOn (fun n x => F (φ n) x) f atTop K := by
    have ht' := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp ht
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.mp ht' ε hε] with n hn x hx
    simpa [f, hx, G, Function.comp_def] using hn (⟨x, hx⟩ : K)
  exact ⟨φ, hφ, f, hunif.continuousOn (Frequently.of_forall (fun n => hc (φ n))), hunif⟩

theorem pma7_25 : pma7_25_contract := by
  intro X _ K F hK hc hb he
  have hbound := pointwiseBounded_equicontinuous_uniformlyBounded hK hb he
  exact ⟨hbound, compact_equicontinuous_subsequence hK hc hbound he⟩

theorem uniformlyConvergent_continuous_equicontinuous
    {X : Type*} [MetricSpace X] {K : Set X} {F : ℕ → X → ℂ} {f : X → ℂ}
    (hK : IsCompact K) (hc : ∀ n, ContinuousOn (F n) K)
    (hu : TendstoUniformlyOn F f atTop K) : SourceEquicontinuousOn F K := by
  have hfc := hu.continuousOn (Frequently.of_forall hc)
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu (ε / 3) hthird)
  have hp : UniformEquicontinuous (fun j : Fin N => K.domRestrict (F j)) :=
    uniformEquicontinuous_finite.mpr (fun j =>
      uniformContinuousOn_iff_restrict.mp (hK.uniformContinuousOn_of_continuous (hc j)))
  obtain ⟨δ₁, hδ₁, hp⟩ := Metric.uniformEquicontinuous_iff.mp hp (ε / 3) hthird
  obtain ⟨δ₂, hδ₂, hf⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hfc) (ε / 3) hthird
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro x hx y hy hxy n
  rcases lt_or_ge n N with hn | hn
  · exact (hp ⟨x, hx⟩ ⟨y, hy⟩ (hxy.trans_le (min_le_left _ _)) ⟨n, hn⟩).trans
      (by linarith)
  · have hx' := hN n hn x hx
    have hy' := hN n hn y hy
    have hf' := hf x hx y hy (hxy.trans_le (min_le_right _ _))
    have ht := dist_triangle (F n x) (f x) (F n y)
    have ht' := dist_triangle (f x) (f y) (F n y)
    rw [dist_comm (F n x) (f x)] at ht
    linarith

theorem pma7_24 : pma7_24_contract := by
  intro X _ K F f hK hc hu
  exact uniformlyConvergent_continuous_equicontinuous hK hc hu

theorem individuallyBounded_uniformLimit_uniformlyBounded
    {X V : Type*} [NormedAddCommGroup V] {F : ℕ → X → V} {f : X → V} {E : Set X}
    (hb : IndividuallyBoundedOn F E) (hu : TendstoUniformlyOn F f atTop E) :
    UniformlyBoundedOn F E := by
  classical
  choose M hM using hb
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hu 1 zero_lt_one)
  have hsum (i : ℕ) (hi : i ≤ N) : M i ≤ ∑ j ∈ Finset.range (N + 1), |M j| :=
    (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (M j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi)))
  refine ⟨(∑ j ∈ Finset.range (N + 1), |M j|) + 2, ?_⟩
  intro n x hx
  by_cases hn : n ≤ N
  · linarith [hM n x hx, hsum n hn]
  · have hlate := hN n (by omega) x hx
    have hbase := hN N le_rfl x hx
    have ht : ‖F n x‖ ≤ dist (F n x) (f x) + ‖f x‖ := by
      simpa [dist_eq_norm] using norm_add_le (F n x - f x) (f x)
    have ht' : ‖f x‖ ≤ dist (f x) (F N x) + ‖F N x‖ := by
      simpa [dist_eq_norm] using norm_add_le (f x - F N x) (F N x)
    rw [dist_comm (F n x) (f x)] at ht
    linarith [hM N x hx, hsum N le_rfl]

theorem equicontinuityPeak_denominator_pos (n : ℕ) (x : ℝ) :
    0 < x ^ 2 + (1 - ((n : ℝ) + 1) * x) ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hx) (sq_nonneg _)

theorem equicontinuityPeak_continuous (n : ℕ) : Continuous (equicontinuityPeak n) := by
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro x
  exact (equicontinuityPeak_denominator_pos n x).ne'

theorem equicontinuityPeak_bounds (n : ℕ) (x : ℝ) :
    0 ≤ equicontinuityPeak n x ∧ equicontinuityPeak n x ≤ 1 := by
  have hd := equicontinuityPeak_denominator_pos n x
  constructor
  · exact div_nonneg (sq_nonneg _) hd.le
  · apply (div_le_one hd).mpr
    linarith [sq_nonneg (1 - ((n : ℝ) + 1) * x)]

theorem equicontinuityPeak_at_reciprocal (n : ℕ) :
    (((n : ℝ) + 1)⁻¹ ∈ Icc (0 : ℝ) 1) ∧
      equicontinuityPeak n (((n : ℝ) + 1)⁻¹) = 1 := by
  have hn : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨⟨inv_nonneg.mpr hn.le, (inv_le_one₀ hn).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n])⟩, ?_⟩
  simp [equicontinuityPeak, hn.ne']

theorem equicontinuityPeak_pointwise (x : ℝ) :
    Tendsto (fun n => equicontinuityPeak n x) atTop (𝓝 0) := by
  by_cases hx : x = 0
  · simp [hx, equicontinuityPeak]
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  have hnum : Tendsto (fun n : ℕ => x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (ht.pow 2)
  have hden : Tendsto (fun n : ℕ => x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2 +
      (((n : ℝ) + 1)⁻¹ - x) ^ 2) atTop (𝓝 (x ^ 2)) := by
    simpa using hnum.add ((ht.sub_const x).pow 2)
  have hlim := hnum.div hden (pow_ne_zero 2 hx)
  suffices heq : (fun n => equicontinuityPeak n x) =
      (fun n : ℕ => (x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2) /
        (x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2 + (((n : ℝ) + 1)⁻¹ - x) ^ 2)) by
    simpa only [heq, Pi.div_def, zero_div] using hlim
  funext n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  dsimp [equicontinuityPeak]
  field_simp

theorem equicontinuityPeak_no_uniform_subsequence (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    ¬ ∃ f : ℝ → ℝ,
      TendstoUniformlyOn (fun n x => equicontinuityPeak (φ n) x) f atTop (Icc 0 1) := by
  rintro ⟨f, hu⟩
  have hf : ∀ x ∈ Icc (0 : ℝ) 1, f x = 0 := by
    intro x hx
    exact tendsto_nhds_unique (hu.tendsto_at hx)
      ((equicontinuityPeak_pointwise x).comp hφ.tendsto_atTop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp hu (1 / 2) (by norm_num))
  obtain ⟨hmem, hpeak⟩ := equicontinuityPeak_at_reciprocal (φ N)
  have h := hN N le_rfl _ hmem
  rw [hf _ hmem, hpeak] at h
  norm_num at h

theorem equicontinuityPeak_not_equicontinuous :
    ¬ SourceEquicontinuousOn equicontinuityPeak (Icc 0 1) := by
  intro he
  obtain ⟨δ, hδ, hd⟩ := he (1 / 2) (by norm_num)
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (by
      simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1))
  obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds hδ)).exists
  obtain ⟨hmem, hpeak⟩ := equicontinuityPeak_at_reciprocal n
  have hdist : dist (((n : ℝ) + 1)⁻¹) 0 < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hmem.1] using hn
  have h := hd _ hmem 0 (by norm_num) hdist n
  rw [hpeak] at h
  norm_num [equicontinuityPeak] at h

theorem pma7_22 : pma7_22_contract := by
  refine ⟨?_, equicontinuityPeak_not_equicontinuous⟩
  intro ι X Y _ _ F E
  exact ⟨Iff.rfl, sourceEquicontinuousOn_iff_uniformEquicontinuousOn F E,
    fun h i => h.uniformContinuousOn i⟩

theorem boundednessBump_individuallyBounded :
    IndividuallyBoundedOn boundednessBump (Icc 0 1) := by
  intro n
  obtain ⟨M, hM⟩ := Chapter06.continuousOn_boundedOn
    (a := 0) (b := 1) (integralSpikeSquared_continuous n).continuousOn
  refine ⟨M, ?_⟩
  intro x hx
  change ‖(IntegralSpikeSquared n x : ℂ)‖ ≤ M
  simpa only [Complex.norm_real, Real.norm_eq_abs] using hM x hx

theorem boundednessBump_pointwise (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => boundednessBump n x) atTop (𝓝 0) := by
  change Tendsto (fun n => (IntegralSpikeSquared n x : ℂ)) atTop (𝓝 0)
  simpa only [Function.comp_def, Complex.ofReal_zero] using
    (Complex.continuous_ofReal.tendsto 0).comp (integralSpikeSquared_pointwise x hx)

theorem boundednessBump_not_uniformlyBounded :
    ¬ UniformlyBoundedOn boundednessBump (Icc 0 1) := by
  rintro ⟨M, hM⟩
  obtain ⟨n, hn⟩ := ((tendsto_atTop.mp integralSpikeSquared_integrals_atTop) (M + 1)).exists
  have hbound := Chapter06.rsIntegral_abs_le_bound (integralSpikeSquared_integral n).1
    (M := M) (fun x hx => by
      have h := hM n x hx
      change ‖(IntegralSpikeSquared n x : ℂ)‖ ≤ M at h
      simpa only [Complex.norm_real, Real.norm_eq_abs] using h)
  change |Chapter06.RIntegral (IntegralSpikeSquared n) 0 1| ≤ M * (1 - 0) at hbound
  have hle := le_abs_self (Chapter06.RIntegral (IntegralSpikeSquared n) 0 1)
  linarith

theorem pma7_21 : pma7_21_contract := by
  refine ⟨fun n => (equicontinuityPeak_continuous n).continuousOn,
    fun n x _ => equicontinuityPeak_bounds n x,
    ⟨1, fun n x _ => ?_⟩,
    fun x _ => equicontinuityPeak_pointwise x,
    equicontinuityPeak_at_reciprocal,
    equicontinuityPeak_no_uniform_subsequence,
    ⟨boundednessBump_individuallyBounded, boundednessBump_pointwise,
      boundednessBump_not_uniformlyBounded⟩,
    fun _ _ _ hb hu => individuallyBounded_uniformLimit_uniformlyBounded hb hu⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (equicontinuityPeak_bounds n x).1] using
    (equicontinuityPeak_bounds n x).2

#print axioms pma7_19
#print axioms pma7_21
#print axioms pma7_22
#print axioms pma7_23
#print axioms pma7_24
#print axioms pma7_25

end Rudin.PMA.Chapter07
