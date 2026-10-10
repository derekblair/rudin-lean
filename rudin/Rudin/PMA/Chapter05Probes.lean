import Rudin.PMA.Chapter05

noncomputable section
open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter05.FidelityProbes

/-- Domain membership prevents extending an open-domain function to its endpoints. -/
theorem open_endpoints_excluded (a b : ℝ) (f : ℝ → ℝ) :
    ¬ DomainDifferentiableAt (Ioo a b) f a ∧
    ¬ DomainDifferentiableAt (Ioo a b) f b := by
  constructor
  · rintro ⟨d, hd⟩
    exact (lt_irrefl a) hd.1.1
  · rintro ⟨d, hd⟩
    exact (lt_irrefl b) hd.1.2

/-- A library within-derivative on an isolated set is insufficient for the source limit. -/
theorem singleton_derivative_rejected (f : ℝ → ℝ) (x d : ℝ) :
    ¬ HasDomainDerivative {x} f x d := by
  intro hd
  have hne := (Chapter04.functionLimitPoint_iff_neBot ({x} : Set ℝ) x).mp hd.2.1
  have h : (⊥ : Filter ℝ).NeBot := by simpa using hne
  exact h.ne rfl

theorem zero_integer_power_at_zero :
    HasDomainDerivative univ (fun t : ℝ => t ^ (0 : ℤ)) 0 0 := by
  rcases pma5_4 with ⟨_, _, _, hz, _, _⟩
  exact hz 0

theorem negative_integer_power_excludes_zero :
    (0 : ℝ) ∉ IntegerPowerDomain (-1) := by
  norm_num [IntegerPowerDomain]

/-- Relative outer derivatives make the endpoint chain rule applicable to absolute value. -/
theorem chain_rule_outer_endpoint_abs :
    HasDomainDerivative (Icc (0 : ℝ) 1) (abs ∘ id) 0 1 ∧
    ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 := by
  have hx : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hid : HasDomainDerivative (Icc (0 : ℝ) 1) id 0 1 :=
    (hasDomainDerivative_Icc_iff zero_lt_one hx id 1).mpr (hasDerivWithinAt_id 0 _)
  have habs : HasDomainDerivative (Icc (0 : ℝ) 1) abs 0 1 :=
    (hasDomainDerivative_Icc_iff zero_lt_one hx abs 1).mpr
      (middle_probe_oneSided_abs.1 0 hx)
  refine ⟨?_, not_differentiableAt_abs_zero⟩
  simpa using pma5_5 0 1 (Icc 0 1) id abs 0 1 1 zero_lt_one hx
    (ordConnected_Icc) ((Chapter04.functionContinuousOn_iff (Icc 0 1) id).mpr continuous_id.continuousOn)
    (fun _ h => h) hid habs

/-- Mean value does not require even a finite one-sided endpoint derivative. -/
theorem mvt_without_oneSided_endpoint_derivative :
    (∃ x ∈ Ioo (0 : ℝ) 1,
      OscillationLinear 1 - OscillationLinear 0 = (1 - 0) * deriv OscillationLinear x) ∧
    ¬ DomainDifferentiableAt (Icc (0 : ℝ) 1) OscillationLinear 0 := by
  constructor
  · exact pma5_10 OscillationLinear (deriv OscillationLinear) 0 1 zero_lt_one
      oscillationLinear_continuous.continuousOn
      (fun x hx => (oscillationLinear_hasDerivAt hx.1.ne').differentiableAt.hasDerivAt)
  · rintro ⟨d, hd⟩
    have hr := (hasDomainDerivative_leftEndpoint_iff zero_lt_one OscillationLinear d).mp hd
    have ht : Tendsto (DifferenceQuotient OscillationLinear 0) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
      simpa only [nhdsWithin_Ioo_eq_nhdsGT zero_lt_one] using hr.2.2
    apply Chapter04.oscillatingSine_no_side_limit true
    refine ⟨d, ?_⟩
    change Tendsto Chapter04.OscillatingSine (𝓝[>] (0 : ℝ)) (𝓝 d)
    simpa only [differenceQuotient_eq_slope, funext oscillationLinear_slope] using ht

/-- The derivative example supplies the second-kind possibility in the Darboux corollary. -/
theorem derivative_secondKind_discontinuity :
    Chapter04.SecondKindDiscontinuityOn (-1) 1 (deriv OscillationQuadratic) 0 := by
  have hi : (0 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hnc : ¬ Chapter04.FunctionContinuousWithinAt (Ioo (-1) 1)
      (deriv OscillationQuadratic) 0 := by
    intro hc
    exact oscillationQuadratic_deriv_not_continuousAt_zero
      ((Chapter04.interval_continuity_iff (deriv OscillationQuadratic) hi).mp hc)
  refine ⟨hi, hnc, ?_⟩
  intro hlim
  have hn := (pma5_12 OscillationQuadratic (deriv OscillationQuadratic) (-1) 1
    (by norm_num) (fun x _ =>
      (oscillationQuadratic_differentiable x).hasDerivAt.hasDerivWithinAt)).2.2.2 0
  exact hn ⟨hi, hnc, hlim⟩

/-- Reverse orientation retains the negative sign of an odd-order remainder. -/
theorem reversed_third_order_remainder (f : ℝ → ℝ)
    (hf : TaylorHypotheses f 0 1 3) :
    ∃ x ∈ Ioo (0 : ℝ) 1,
      f 0 = TaylorPolynomialValue f 0 1 3 1 0 -
        iteratedDerivWithin 3 f (Icc 0 1) x / 6 := by
  obtain ⟨x, hx, h⟩ := taylor_remainder (α := (1 : ℝ)) (β := (0 : ℝ))
    zero_lt_one (by norm_num : 1 ≤ (3 : ℕ)) hf
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨x, by simpa [uIoo] using hx, ?_⟩
  norm_num at h
  linarith

/-- A totalized second derivative cannot repair a failed first derivative. -/
theorem higher_order_cusp_rejected :
    ¬ HigherExistsWithin abs (Icc (-1 : ℝ) 1) 2 0 := by
  intro h
  exact higherExists_abs_zero_probe (h.lower (by norm_num) (by norm_num : 1 ≤ (2 : ℕ)))

end Rudin.PMA.Chapter05.FidelityProbes
