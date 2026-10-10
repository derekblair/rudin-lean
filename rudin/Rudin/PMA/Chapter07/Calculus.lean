import Rudin.PMA.Chapter06

/-!
Typed calculus contracts for the accepted PMA Chapter 7 inventory.
Internal sequence index `n : ℕ` enumerates the source's positive-indexed
terms in order (internal `n` corresponds to source `n+1`). Series use the
ordered finite partial sums from Chapter 3, never unconditional summation.
These contracts passed independent review before the proofs below were written.
-/

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter07

open Chapter06

/-! ### PMA-7.16: Native complex Stieltjes integration of uniform limits and series -/

/-- Both convergence assertions are genuine numerical limits of the native
Chapter 6 complex integrals. The second assertion uses ordered series. -/
def pma7_16_contract : Prop :=
  (∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ),
    a ≤ b → MonotoneOn α (Icc a b) →
    (∀ n, ComplexRSIntegrable (F n) α a b) →
    TendstoUniformlyOn F f atTop (Icc a b) →
    ComplexRSIntegrable f α a b ∧
      Tendsto (fun n => ComplexRSIntegral (F n) α a b) atTop
        (𝓝 (ComplexRSIntegral f α a b))) ∧
  (∀ (F : ℕ → ℝ → ℂ) (f : ℝ → ℂ) (α : ℝ → ℝ) (a b : ℝ),
    a ≤ b → MonotoneOn α (Icc a b) →
    (∀ n, ComplexRSIntegrable (F n) α a b) →
    TendstoUniformlyOn
      (fun N x => Chapter03.PartialSums (fun n => F n x) N) f atTop (Icc a b) →
    ComplexRSIntegrable f α a b ∧
      Chapter03.SeriesHasSum (fun n => ComplexRSIntegral (F n) α a b)
        (ComplexRSIntegral f α a b))

/-! ### PMA-7.17: Uniform convergence and differentiation from one convergent point -/

/-- The derivative data are actual derivatives relative to the full closed
interval, including its endpoints. No derivative continuity, boundedness,
integrability, or ambient extension regularity is assumed. -/
def UniformDerivativeLimitProperty (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Prop :=
  ∀ (F D : ℕ → ℝ → V) (d : ℝ → V) (a b x₀ : ℝ) (L : V),
    a < b → x₀ ∈ Icc a b →
    (∀ n, ∀ x ∈ Icc a b, HasDerivWithinAt (F n) (D n x) (Icc a b) x) →
    Tendsto (fun n => F n x₀) atTop (𝓝 L) →
    TendstoUniformlyOn D d atTop (Icc a b) →
    ∃ f : ℝ → V,
      TendstoUniformlyOn F f atTop (Icc a b) ∧ f x₀ = L ∧
        ∀ x ∈ Icc a b,
          HasDerivWithinAt f (d x) (Icc a b) x ∧
            Tendsto (fun n => D n x) atTop (𝓝 (d x))

/-- The complex statement is the default source theorem; the real statement
records its real-valued specialization without relying on an implicit coercion. -/
def pma7_17_contract : Prop :=
  UniformDerivativeLimitProperty ℂ ∧ UniformDerivativeLimitProperty ℝ

theorem cell_gap_le_of_uniform_dist {f g : ℝ → ℝ} {a b δ : ℝ}
    (hg : BoundedOn g a b) (hfg : ∀ x ∈ Icc a b, dist (f x) (g x) ≤ δ)
    (P : Partition a b) (i : Fin P.n) :
    cellUpper f P i - cellLower f P i ≤
      2 * δ + (cellUpper g P i - cellLower g P i) := by
  apply cell_gap_le_of_oscillation P i
  intro x hx y hy
  have hx' := abs_le.mp (show |f x - g x| ≤ δ by
    simpa only [Real.dist_eq] using hfg x (P.cell_subset i hx))
  have hy' := abs_le.mp (show |f y - g y| ≤ δ by
    simpa only [Real.dist_eq] using hfg y (P.cell_subset i hy))
  have hxl := cellLower_le_value hg P i hx
  have hxu := value_le_cellUpper hg P i hx
  have hyl := cellLower_le_value hg P i hy
  have hyu := value_le_cellUpper hg P i hy
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rsIntegrable_of_uniformLimit {F : ℕ → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ n, RSIntegrable (F n) α a b)
    (hlim : TendstoUniformlyOn F f atTop (Icc a b)) : RSIntegrable f α a b := by
  have hab := (hF 0).1
  have hα := (hF 0).2.2.1
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hlim 1 (by norm_num)).exists
  obtain ⟨M, hM⟩ := (hF N).2.1
  have hb : BoundedOn f a b := by
    refine ⟨1 + M, fun x hx => ?_⟩
    have hnx : |f x - F N x| < 1 := by simpa only [Real.dist_eq] using hN x hx
    calc
      |f x| = |(f x - F N x) + F N x| := by congr 1; ring
      _ ≤ |f x - F N x| + |F N x| := abs_add_le _ _
      _ ≤ 1 + M := add_le_add hnx.le (hM x hx)
  apply (rsIntegrable_iff_gap hab hb hα).mpr
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let δ := ε / (4 * (A + 1))
  have hden : 0 < 4 * (A + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (4 * (A + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformlyOn_iff.mp hlim δ hδ).exists
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hab (hF n).2.1 hα).mp (hF n)
    (ε / 2) (by positivity)
  refine ⟨P, ?_⟩
  have hgap := gap_le_of_cell_affine_gaps (f := F n) (h := f) (η := 2 * δ)
    (C := 1) hα P (fun i => by
      simpa only [one_mul] using
        cell_gap_le_of_uniform_dist (hF n).2.1 (fun x hx => (hn x hx).le) P i)
  dsimp only [A] at heq
  nlinarith

theorem rsIntegral_sub_bound {f g α : ℝ → ℝ} {a b M : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b)
    (hM : ∀ x ∈ Icc a b, |f x - g x| ≤ M) :
    |RSIntegral f α a b - RSIntegral g α a b| ≤ M * (α b - α a) := by
  have hn := rsIntegrable_const_mul hg (-1)
  have hs := rsIntegrable_add hf hn.1
  rw [hn.2] at hs
  have hd : RSIntegrable (fun x => f x - g x) α a b ∧
      RSIntegral (fun x => f x - g x) α a b = RSIntegral f α a b - RSIntegral g α a b := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hs
  rw [← hd.2]
  exact rsIntegral_abs_le_bound hd.1 hM

theorem rsIntegral_tendsto_of_uniformLimit {F : ℕ → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ n, RSIntegrable (F n) α a b)
    (hlim : TendstoUniformlyOn F f atTop (Icc a b)) :
    RSIntegrable f α a b ∧
      Tendsto (fun n => RSIntegral (F n) α a b) atTop (𝓝 (RSIntegral f α a b)) := by
  have hf := rsIntegrable_of_uniformLimit hF hlim
  refine ⟨hf, Metric.tendsto_nhds.mpr ?_⟩
  intro ε hε
  let A := α b - α a
  have hA : 0 ≤ A := sub_nonneg.mpr (hf.2.2.1 ⟨le_rfl, hf.1⟩ ⟨hf.1, le_rfl⟩ hf.1)
  let δ := ε / (A + 1)
  have hden : 0 < A + 1 := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (A + 1) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with n hn
  rw [Real.dist_eq]
  have hb := rsIntegral_sub_bound (hF n) hf (fun x hx =>
    show |F n x - f x| ≤ δ by
      simpa only [Real.dist_eq, abs_sub_comm] using (hn x hx).le)
  dsimp only [A] at heq
  nlinarith

theorem complexRSIntegral_tendsto_of_uniformLimit {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    {α : ℝ → ℝ} {a b : ℝ} (hF : ∀ n, ComplexRSIntegrable (F n) α a b)
    (hlim : TendstoUniformlyOn F f atTop (Icc a b)) :
    ComplexRSIntegrable f α a b ∧
      Tendsto (fun n => ComplexRSIntegral (F n) α a b) atTop
        (𝓝 (ComplexRSIntegral f α a b)) := by
  have hr := rsIntegral_tendsto_of_uniformLimit (fun n => (hF n).1)
    (Complex.uniformContinuous_re.comp_tendstoUniformlyOn hlim)
  have hi := rsIntegral_tendsto_of_uniformLimit (fun n => (hF n).2)
    (Complex.uniformContinuous_im.comp_tendstoUniformlyOn hlim)
  refine ⟨⟨hr.1, hi.1⟩, ?_⟩
  exact (Complex.continuous_ofReal.tendsto _ |>.comp hr.2).add
    ((Complex.continuous_ofReal.tendsto _ |>.comp hi.2).mul_const Complex.I)

theorem complexRSIntegral_finite_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℂ)
    {α : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hα : MonotoneOn α (Icc a b))
    (hF : ∀ j ∈ s, ComplexRSIntegrable (F j) α a b) :
    ComplexRSIntegrable (fun x => ∑ j ∈ s, F j x) α a b ∧
      ComplexRSIntegral (fun x => ∑ j ∈ s, F j x) α a b =
        ∑ j ∈ s, ComplexRSIntegral (F j) α a b := by
  have hr := vector_scalar_finite_sum s (fun j x => (F j x).re) hab hα
    (fun j hj => (hF j hj).1)
  have hi := vector_scalar_finite_sum s (fun j x => (F j x).im) hab hα
    (fun j hj => (hF j hj).2)
  constructor
  · exact ⟨by simpa using hr.1, by simpa using hi.1⟩
  · apply Complex.ext
    · simpa [ComplexRSIntegral] using hr.2
    · simpa [ComplexRSIntegral] using hi.2

theorem pma7_16 : pma7_16_contract := by
  constructor
  · intro F f α a b _ _ hF hlim
    exact complexRSIntegral_tendsto_of_uniformLimit hF hlim
  · intro F f α a b hab hα hF hlim
    have hs (N : ℕ) := complexRSIntegral_finite_sum (Finset.range N) F hab hα
      (fun j _ => hF j)
    have hh := complexRSIntegral_tendsto_of_uniformLimit (fun N => (hs N).1) hlim
    refine ⟨hh.1, ?_⟩
    change Tendsto (fun N => ∑ j ∈ Finset.range N, ComplexRSIntegral (F j) α a b)
      atTop (𝓝 (ComplexRSIntegral f α a b))
    simpa only [(hs _).2] using hh.2

#print axioms pma7_16

theorem uniformCauchySeqOn_of_derivative_anchor
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F D : ℕ → ℝ → V} {a b x₀ : ℝ} (hab : a ≤ b) (hx₀ : x₀ ∈ Icc a b)
    (hF : ∀ n, ∀ x ∈ Icc a b, HasDerivWithinAt (F n) (D n x) (Icc a b) x)
    (hD : UniformCauchySeqOn D atTop (Icc a b))
    (hx : CauchySeq (fun n => F n x₀)) : UniformCauchySeqOn F atTop (Icc a b) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  let δ := ε / (2 * (b - a + 1))
  have hden : 0 < 2 * (b - a + 1) := by linarith
  have hδ : 0 < δ := div_pos hε hden
  have heq : δ * (2 * (b - a + 1)) = ε := div_mul_cancel₀ _ (ne_of_gt hden)
  obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp hD δ hδ
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.mp hx (ε / 2) (by positivity)
  refine ⟨max N K, ?_⟩
  intro m hm n hn x hxs
  have hmn : ∀ y ∈ Icc a b, ‖D m y - D n y‖ ≤ δ := by
    intro y hy
    simpa only [dist_eq_norm] using (hN m (le_trans (le_max_left _ _) hm)
      n (le_trans (le_max_left _ _) hn) y hy).le
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun y hy => (hF m y hy).sub (hF n y hy)) hmn (convex_Icc a b) hx₀ hxs
  simp only [Pi.sub_apply] at hmv
  have hlen : ‖x - x₀‖ ≤ b - a := by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hxs.1, hxs.2, hx₀.1, hx₀.2],
      by linarith [hxs.1, hxs.2, hx₀.1, hx₀.2]⟩
  have hanchor : ‖F m x₀ - F n x₀‖ < ε / 2 := by
    simpa only [dist_eq_norm] using hK m (le_trans (le_max_right _ _) hm)
      n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm]
  have htriangle : ‖F m x - F n x‖ ≤
      ‖(F m x - F n x) - (F m x₀ - F n x₀)‖ + ‖F m x₀ - F n x₀‖ := by
    calc
      _ = ‖((F m x - F n x) - (F m x₀ - F n x₀)) + (F m x₀ - F n x₀)‖ := by
        congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hprod := mul_le_mul_of_nonneg_left hlen hδ.le
  nlinarith

theorem hasDerivWithinAt_of_uniform_derivative_limit
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {F D : ℕ → ℝ → V} {f d : ℝ → V} {a b x : ℝ} (hx : x ∈ Icc a b)
    (hF : ∀ n, ∀ y ∈ Icc a b, HasDerivWithinAt (F n) (D n y) (Icc a b) y)
    (hD : TendstoUniformlyOn D d atTop (Icc a b))
    (hf : ∀ y ∈ Icc a b, Tendsto (fun n => F n y) atTop (𝓝 (f y))) :
    HasDerivWithinAt f (d x) (Icc a b) x := by
  apply HasDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let δ := ε / 4
  have hδ : 0 < δ := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hD δ hδ)
  have hpair (m : ℕ) (hm : N ≤ m) (y : ℝ) (hy : y ∈ Icc a b) :
      ‖D m y - D N y‖ ≤ 2 * δ := by
    have hm' : ‖D m y - d y‖ ≤ δ := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hN m hm y hy).le
    have hN' : ‖d y - D N y‖ ≤ δ := by
      simpa only [dist_eq_norm] using (hN N le_rfl y hy).le
    have ht : ‖D m y - D N y‖ ≤ ‖D m y - d y‖ + ‖d y - D N y‖ := by
      simpa only [dist_eq_norm] using dist_triangle (D m y) (d y) (D N y)
    linarith
  have happ (y : ℝ) (hy : y ∈ Icc a b) :
      ‖(f y - F N y) - (f x - F N x)‖ ≤ (2 * δ) * ‖y - x‖ := by
    have ht := (((hf y hy).sub_const (F N y)).sub ((hf x hx).sub_const (F N x))).norm
    apply le_of_tendsto ht
    apply eventually_atTop.mpr
    refine ⟨N, fun m hm => ?_⟩
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => (hF m z hz).sub (hF N z hz)) (hpair m hm) (convex_Icc a b) hx hy
  have hdx : ‖D N x - d x‖ ≤ δ := by
    simpa only [dist_eq_norm, norm_sub_rev] using (hN N le_rfl x hx).le
  filter_upwards [(hF N x hx).isLittleO.bound hδ, self_mem_nhdsWithin] with y hy hys
  calc
    ‖f y - f x - (y - x) • d x‖ =
        ‖((f y - F N y) - (f x - F N x)) +
          (F N y - F N x - (y - x) • D N x) + (y - x) • (D N x - d x)‖ := by
      congr 1
      simp only [smul_sub]
      abel
    _ ≤ (‖(f y - F N y) - (f x - F N x)‖ +
        ‖F N y - F N x - (y - x) • D N x‖) + ‖(y - x) • (D N x - d x)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ((2 * δ) * ‖y - x‖ + δ * ‖y - x‖) + δ * ‖y - x‖ := by
      apply add_le_add
      · exact add_le_add (happ y hys) hy
      · rw [norm_smul, mul_comm δ]
        exact mul_le_mul_of_nonneg_left hdx (norm_nonneg _)
    _ = ε * ‖y - x‖ := by dsimp only [δ]; ring

theorem uniformDerivativeLimitProperty
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] :
    UniformDerivativeLimitProperty V := by
  intro F D d a b x₀ L hab hx₀ hF hL hD
  classical
  have hC := uniformCauchySeqOn_of_derivative_anchor hab.le hx₀ hF
    hD.uniformCauchySeqOn hL.cauchySeq
  have hp : ∀ x : ℝ, ∃ l : V, x ∈ Icc a b →
      Tendsto (fun n => F n x) atTop (𝓝 l) := by
    intro x
    by_cases hx : x ∈ Icc a b
    · obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete (hC.cauchySeq hx)
      exact ⟨l, fun _ => hl⟩
    · exact ⟨0, fun h => False.elim (hx h)⟩
  choose f hf using hp
  have hlim := hC.tendstoUniformlyOn_of_tendsto hf
  refine ⟨f, hlim, tendsto_nhds_unique (hf x₀ hx₀) hL, ?_⟩
  intro x hx
  exact ⟨hasDerivWithinAt_of_uniform_derivative_limit hx hF hD hf, hD.tendsto_at hx⟩

theorem pma7_17 : pma7_17_contract :=
  ⟨uniformDerivativeLimitProperty ℂ, uniformDerivativeLimitProperty ℝ⟩

#print axioms pma7_17

theorem calculus_constFamily_uniform {X V : Type*} [PseudoMetricSpace V]
    (f : X → V) (S : Set X) : TendstoUniformlyOn (fun _ : ℕ => f) f atTop S := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  exact Eventually.of_forall (fun _ _ _ => by simpa using hε)

theorem complexRSIntegral_const_unit (z : ℂ) :
    ComplexRSIntegrable (fun _ : ℝ => z) id 0 1 ∧
      ComplexRSIntegral (fun _ : ℝ => z) id 0 1 = z := by
  have hr := rsIntegral_const (c := z.re) (α := id) (a := 0) (b := 1)
    (by norm_num) (monotone_id.monotoneOn _)
  have hi := rsIntegral_const (c := z.im) (α := id) (a := 0) (b := 1)
    (by norm_num) (monotone_id.monotoneOn _)
  refine ⟨⟨hr.1, hi.1⟩, ?_⟩
  apply Complex.ext
  · simpa [ComplexRSIntegral] using hr.2
  · simpa [ComplexRSIntegral] using hi.2

/-- A discontinuous imaginary-valued step is admissible for the sequence theorem. -/
theorem uniform_integral_imaginary_step_probe :
    ComplexRSIntegrable (fun x => (UnitStep x : ℂ) * Complex.I) id (-1) 1 ∧
      Tendsto (fun _ : ℕ =>
        ComplexRSIntegral (fun x => (UnitStep x : ℂ) * Complex.I) id (-1) 1) atTop
        (𝓝 (ComplexRSIntegral (fun x => (UnitStep x : ℂ) * Complex.I) id (-1) 1)) := by
  have hm : Monotone UnitStep := by
    intro x y hxy
    simpa only [TranslatedStep, sub_zero] using translatedStep_monotone 0 hxy
  have hi := rsIntegrable_monotone (α := id) (a := (-1)) (b := 1) (by norm_num)
    (hm.monotoneOn _) (monotone_id.monotoneOn _) continuous_id.continuousOn
  have hr := (rsIntegral_const (c := 0) (α := id) (a := (-1)) (b := 1)
    (by norm_num) (monotone_id.monotoneOn _)).1
  have hh : ComplexRSIntegrable (fun x => (UnitStep x : ℂ) * Complex.I) id (-1) 1 :=
    ⟨by simpa using hr, by simpa using hi⟩
  exact pma7_16.1 _ _ id (-1) 1 (by norm_num) (monotone_id.monotoneOn _)
    (fun _ => hh) (calculus_constFamily_uniform _ _)

/-- Zero-mass integrators do not require positive-mass denominator assumptions. -/
theorem uniform_integral_zero_mass_probe {f : ℝ → ℝ} (hf : BoundedOn f 0 1) :
    RSIntegrable f (fun _ => 0) 0 1 ∧
      Tendsto (fun _ : ℕ => RSIntegral f (fun _ => 0) 0 1) atTop (𝓝 0) := by
  have hz := rsIntegral_const_integrator (c := 0) (by norm_num : (0 : ℝ) ≤ 1) hf
  have hh := rsIntegral_tendsto_of_uniformLimit (fun _ => hz.1)
    (calculus_constFamily_uniform f (Icc 0 1))
  exact ⟨hh.1, by simpa only [hz.2] using hh.2⟩

/-- The right endpoint can be the anchor even when an approximant has no ambient
derivative at the left endpoint. Both interval-relative endpoint derivatives remain. -/
theorem uniform_derivative_endpoint_probe :
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 ∧
      ∃ f : ℝ → ℝ,
        TendstoUniformlyOn (fun _ : ℕ => abs) f atTop (Icc 0 1) ∧
        HasDerivWithinAt f 1 (Icc 0 1) 0 ∧ HasDerivWithinAt f 1 (Icc 0 1) 1 := by
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt abs 1 (Icc 0 1) x :=
    (hasDerivWithinAt_id x (Icc 0 1)).congr_of_mem
      (fun y hy => abs_of_nonneg hy.1) hx
  obtain ⟨f, hf, _, hdf⟩ := pma7_17.2 (fun _ => abs) (fun _ _ => 1) (fun _ => 1)
    0 1 1 1 (by norm_num) (by norm_num) (fun _ => hd)
    (by simp)
    (calculus_constFamily_uniform _ _)
  exact ⟨not_differentiableAt_abs_zero, f, hf, (hdf 0 (by norm_num)).1,
    (hdf 1 (by norm_num)).1⟩

/-- Conditional ordered convergence is enough, including an imaginary-valued series. -/
theorem uniform_integral_conditional_series_probe :
    ¬ Chapter03.SeriesAbsolutelyConverges Chapter03.AlternatingHarmonic ∧
      ∃ L : ℝ, Chapter03.SeriesHasSum Chapter03.AlternatingHarmonic L ∧
        Chapter03.SeriesHasSum
          (fun n => ComplexRSIntegral
            (fun _ : ℝ => (Chapter03.AlternatingHarmonic n : ℂ) * Complex.I) id 0 1)
          ((L : ℂ) * Complex.I) := by
  obtain ⟨L, hL⟩ := Chapter03.alternatingHarmonic_converges
  refine ⟨Chapter03.alternatingHarmonic_not_absolute, L, hL, ?_⟩
  let F : ℕ → ℝ → ℂ := fun n _ => (Chapter03.AlternatingHarmonic n : ℂ) * Complex.I
  have hs (N : ℕ) (x : ℝ) : Chapter03.PartialSums (fun n => F n x) N =
      ((Chapter03.PartialSums Chapter03.AlternatingHarmonic N : ℝ) : ℂ) * Complex.I := by
    simp [F, Chapter03.PartialSums, Finset.sum_mul]
  have hc : Tendsto (fun N => ((Chapter03.PartialSums Chapter03.AlternatingHarmonic N : ℝ) : ℂ) *
      Complex.I) atTop (𝓝 ((L : ℂ) * Complex.I)) :=
    ((Complex.continuous_ofReal.tendsto _).comp hL).mul_const Complex.I
  have hu : TendstoUniformlyOn (fun N x => Chapter03.PartialSums (fun n => F n x) N)
      (fun _ => (L : ℂ) * Complex.I) atTop (Icc 0 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [Metric.tendsto_nhds.mp hc ε hε] with n hn
    intro x _
    simpa only [hs, dist_comm] using hn
  have hh := pma7_16.2 F (fun _ => (L : ℂ) * Complex.I) id 0 1
    (by norm_num) (monotone_id.monotoneOn _)
    (fun n => (complexRSIntegral_const_unit _).1) hu
  simpa only [(complexRSIntegral_const_unit ((L : ℂ) * Complex.I)).2] using hh.2

#print axioms uniform_integral_imaginary_step_probe
#print axioms uniform_integral_zero_mass_probe
#print axioms uniform_derivative_endpoint_probe
#print axioms uniform_integral_conditional_series_probe

end Rudin.PMA.Chapter07
