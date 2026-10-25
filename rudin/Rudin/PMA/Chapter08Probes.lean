import Rudin.PMA.Chapter08.PowerSeries
import Rudin.PMA.Chapter08.Abel
import Rudin.PMA.Chapter08.DoubleSeries
import Rudin.PMA.Chapter08.Taylor
import Rudin.PMA.Chapter08.Operations

/-! Independent clients for Chapter 8's domain, indexing, conditional-sum,
infinite-radius, and accumulation-point boundaries. Authored separately from
production proofs; these assertions do not merely restate the node contracts. -/

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal NNReal
open Rudin.PMA Rudin.PMA.Chapter08

namespace Rudin.PMA.Chapter08.FidelityProbes

/-- A genuinely nonreal coefficient tests the intended complex codomain. -/
def imaginaryConstantCoeffs (n : ℕ) : ℂ := if n = 0 then Complex.I else 0

theorem imaginary_constant_entire :
    Represents imaginaryConstantCoeffs (fun _ : ℝ => Complex.I) ⊤ := by
  intro x _
  have h : HasSum (fun n : ℕ => if n = 0 then Complex.I else 0) Complex.I :=
    hasSum_ite_eq 0 Complex.I
  have hs : HasSum (fun n => x ^ n • imaginaryConstantCoeffs n) Complex.I := by
    convert h using 1
    funext n
    by_cases hn : n = 0
    · simp [imaginaryConstantCoeffs, hn]
    · simp [imaginaryConstantCoeffs, hn]
  exact hs.tendsto_sum_nat

/-- The uniform conclusion includes the radius-zero compact set `{0}`. -/
theorem singleton_uniform_boundary (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞)
    (hR : 0 < R) (h : Represents c f R) :
    TendstoUniformlyOn (fun N x => Chapter03.PartialSums (fun n => x ^ n • c n) N)
      f atTop ({0} : Set ℝ) := by
  simpa using (pma8_1.1 c f R hR h).1 0 (by simpa using hR)

/-- Infinite radius really permits arbitrarily large compact intervals. -/
theorem imaginary_constant_uniform_all_compacts (r : ℝ≥0) :
    TendstoUniformlyOn
      (fun N x => Chapter03.PartialSums (fun n => x ^ n • imaginaryConstantCoeffs n) N)
      (fun _ : ℝ => Complex.I) atTop (Icc (-(r : ℝ)) r) := by
  exact (pma8_1.1 imaginaryConstantCoeffs (fun _ : ℝ => Complex.I) ⊤
    (by simp) imaginary_constant_entire).1 r (by simp)

/-- The zeroth derivative/coefficient convention must retain the constant term. -/
theorem constant_coefficient_at_origin (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞)
    (hR : 0 < R) (h : Represents c f R) : f 0 = c 0 := by
  simpa using (pma8_1.1 c f R hR h).2.2.2.1 0

/-- The first derivative has coefficient `c 1`, with no spurious index shift. -/
theorem first_coefficient_is_derivative (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞)
    (hR : 0 < R) (h : Represents c f R) : HasDerivAt f (c 1) 0 := by
  have hd := ((pma8_1.1 c f R hR h).2.2.1 0 0 (by simpa using hR)).1
  have hc : iteratedDeriv 1 f 0 = c 1 := by
    simpa using (pma8_1.1 c f R hR h).2.2.2.1 1
  simpa only [iteratedDeriv_zero, zero_add, hc] using hd

/-- A conditionally convergent endpoint is accepted by Abel's theorem. -/
theorem abel_accepts_alternating_harmonic :
    ∃ A : ℝ,
      ¬ Chapter03.SeriesAbsolutelyConverges
        (fun n => (Chapter03.AlternatingHarmonic n : ℂ)) ∧
      Tendsto (abelPowerSeries (fun n => (Chapter03.AlternatingHarmonic n : ℂ)))
        (𝓝[<] (1 : ℝ)) (𝓝 (A : ℂ)) := by
  obtain ⟨A, hA⟩ := Chapter03.alternatingHarmonic_converges
  have hc : Chapter03.SeriesHasSum
      (fun n => (Chapter03.AlternatingHarmonic n : ℂ)) (A : ℂ) := by
    have h := (Complex.ofRealCLM.continuous.tendsto A).comp hA
    change Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N,
      (Chapter03.AlternatingHarmonic n : ℂ)) atTop (𝓝 (A : ℂ))
    simpa [Chapter03.SeriesHasSum, Chapter03.PartialSums, Function.comp_def] using h
  refine ⟨A, ?_, (pma8_2.1 _ _ hc).2.1⟩
  intro habs
  apply Chapter03.alternatingHarmonic_not_absolute
  simpa [Chapter03.SeriesAbsolutelyConverges, Complex.norm_real, Real.norm_eq_abs] using habs

/-- The double-series theorem guarantees each column's ordered convergence,
including a column whose own norm sum was not an original premise. -/
theorem double_series_all_columns_exist (a : ℕ → ℕ → ℂ) (b : ℕ → ℝ)
    (hrows : ∀ i, Chapter03.SeriesHasSum (fun j => ‖a i j‖) (b i))
    (hb : Chapter03.SeriesConverges b) (j : ℕ) :
    Chapter03.SeriesConverges (fun i => a i j) := by
  obtain ⟨rows, columns, s, _, hcols, _, _⟩ := pma8_3 a b hrows hb
  exact ⟨columns j, hcols j⟩

/-- Entire power series can be recentered at the nonzero point 1, for any target. -/
theorem taylor_entire_nonzero_center (c : ℕ → ℂ) (f : ℝ → ℂ)
    (h : Represents c f ⊤) (x : ℝ) :
    Chapter03.SeriesHasSum
      (fun n => (((n.factorial : ℝ)⁻¹) * (x - 1) ^ n) • iteratedDeriv n f 1)
      (f x) := by
  exact pma8_4 c f ⊤ (by simp) h 1 (by simp) x (by simp)

/-- Equality only to the right of 1 already forces all entire-series coefficients
into agreement. The accumulation point is deliberately not the original center. -/
theorem identity_from_nonzero_accumulation (c d : ℕ → ℂ) (f g : ℝ → ℂ)
    (hc : Represents c f ⊤) (hd : Represents d g ⊤)
    (heq : ∀ x : ℝ, 1 < x → f x = g x) : c = d := by
  have hsub : Ioi (1 : ℝ) ⊆ {x | f x = g x} \ {1} := by
    intro x hx
    exact ⟨heq x hx, by simpa using (ne_of_gt hx)⟩
  have hcl : (1 : ℝ) ∈ closure ({x | f x = g x} \ {1}) :=
    closure_mono hsub (by simp [closure_Ioi])
  exact (pma8_5 c d f g ⊤ (by simp) hc hd ⟨1, by simp, hcl⟩).1

/-- A native complex monomial integral has a genuinely imaginary, nonzero value. -/
theorem imaginary_monomial_native_integral :
    Chapter06.ComplexRSIntegral (fun x : ℝ => x • Complex.I) id 0 1 = Complex.I / 2 ∧
      Chapter06.ComplexRSIntegral (fun x : ℝ => x • Complex.I) id 0 1 ≠ 0 := by
  have hr : Chapter06.ComplexRSIntegral (fun x : ℝ => x • Complex.I) id 0 1 =
      (1 / 2 : ℝ) • Complex.I := by
    simpa using powerSeries_term_integral Complex.I 1 (show (0 : ℝ) ≤ 1 by norm_num)
  have hc : Chapter06.ComplexRSIntegral (fun x : ℝ => x • Complex.I) id 0 1 =
      Complex.I / 2 := by
    rw [hr]
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  refine ⟨hc, ?_⟩
  rw [hc]
  exact div_ne_zero Complex.I_ne_zero (by norm_num)

/-- The termwise formula remains valid on a singleton, for an arbitrary
represented function, and forces its native integral to be zero. -/
theorem singleton_termwise_integral (c : ℕ → ℂ) (f : ℝ → ℂ) (R : ℝ≥0∞)
    (hR : 0 < R) (h : Represents c f R) (a : ℝ)
    (ha : (‖a‖₊ : ℝ≥0∞) < R) :
    Chapter06.ComplexRSIntegrable f id a a ∧
      Chapter06.ComplexRSIntegral f id a a = 0 := by
  have hI : Icc a a ⊆ Metric.eball (0 : ℝ) R := by
    intro x hx
    have hxa : x = a := le_antisymm hx.2 hx.1
    subst x
    simpa [enorm_eq_nnnorm] using ha
  have hi := powerSeries_integral_explicit hR h (a := a) (b := a) le_rfl hI
  have hs : Chapter03.SeriesHasSum (fun _ : ℕ => (0 : ℂ))
      (Chapter06.ComplexRSIntegral f id a a) := by
    simpa only [sub_self, zero_div, zero_smul] using hi.2
  have hz : Chapter03.SeriesHasSum (fun _ : ℕ => (0 : ℂ)) (0 : ℂ) :=
    hasSum_zero.tendsto_sum_nat
  exact ⟨hi.1, tendsto_nhds_unique hs hz⟩

end Rudin.PMA.Chapter08.FidelityProbes
