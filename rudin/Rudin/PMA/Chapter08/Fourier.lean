import Rudin.PMA.Chapter07.Calculus
import Rudin.PMA.Chapter08.RiemannBridge
import Mathlib.Analysis.Fourier.AddCircle

set_option autoImplicit false

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter08

/-- PMA 8.9: the integer-frequency exponential. -/
def fourierMonomial (n : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((n : ℂ) * (x : ℂ) * Complex.I)

/-- PMA 8.9: a finite trigonometric polynomial in exponential notation.
Finite integer support is equivalent to support in some symmetric interval.
The sine/cosine convention and that equivalence are proved separately below. -/
def TrigonometricPolynomial (f : ℝ → ℂ) : Prop :=
  ∃ c : ℤ →₀ ℂ, ∀ x, f x = c.sum (fun n a => a * fourierMonomial n x)

/-- PMA 8.9: Fourier coefficients use the native Chapter 6 complex Riemann
integral. Defining these numbers makes no assertion about convergence. -/
def riemannFourierCoeff (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * Chapter06.ComplexRSIntegral
    (fun x => f x * fourierMonomial (-n) x) id (-Real.pi) Real.pi

/-- PMA 8.9 and 8.13: symmetric sums include both endpoints and frequency zero. -/
def trigonometricPartialSum (c : ℤ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n * fourierMonomial n x

def riemannFourierSum (f : ℝ → ℂ) (N : ℕ) : ℝ → ℂ :=
  trigonometricPartialSum (riemannFourierCoeff f) N

/-- PMA 8.10: orthogonality includes existence of the native integrals, so it
does not use the value assigned to a divergent integral. Natural indices start
at zero rather than one; shifting every index gives the printed convention. -/
def RiemannOrthogonal (φ : ℕ → ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ m n, m ≠ n →
    Chapter06.ComplexRSIntegrable (fun x => φ m x * star (φ n x)) id a b ∧
    Chapter06.ComplexRSIntegral (fun x => φ m x * star (φ n x)) id a b = 0

def RiemannOrthonormal (φ : ℕ → ℝ → ℂ) (a b : ℝ) : Prop :=
  RiemannOrthogonal φ a b ∧
  ∀ n, Chapter06.RIntegrable (fun x => ‖φ n x‖ ^ 2) a b ∧
    Chapter06.RIntegral (fun x => ‖φ n x‖ ^ 2) a b = 1

def orthogonalFourierCoeff (f : ℝ → ℂ) (φ : ℕ → ℝ → ℂ)
    (a b : ℝ) (n : ℕ) : ℂ :=
  Chapter06.ComplexRSIntegral (fun x => f x * star (φ n x)) id a b

/-- PMA 8.13: the Dirichlet kernel in its finite exponential-sum form. -/
def dirichletKernel (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierMonomial n x

private instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

theorem fourierMonomial_eq_circle (n : ℤ) (x : ℝ) :
    fourierMonomial n x = fourier (T := 2 * Real.pi) n (x : AddCircle (2 * Real.pi)) := by
  rw [fourier_coe_apply]
  unfold fourierMonomial
  congr 1
  push_cast
  field_simp

theorem fourierMonomial_continuous (n : ℤ) : Continuous (fourierMonomial n) := by
  unfold fourierMonomial
  fun_prop

theorem fourierMonomial_periodic (n : ℤ) :
    Function.Periodic (fourierMonomial n) (2 * Real.pi) := by
  intro x
  rw [fourierMonomial_eq_circle, fourierMonomial_eq_circle, AddCircle.coe_add_period]

@[simp] theorem fourierMonomial_zero (x : ℝ) : fourierMonomial 0 x = 1 := by
  simp [fourierMonomial]

theorem fourierMonomial_add (m n : ℤ) (x : ℝ) :
    fourierMonomial (m + n) x = fourierMonomial m x * fourierMonomial n x := by
  simp [fourierMonomial, add_mul, Complex.exp_add]

theorem fourierMonomial_star (n : ℤ) (x : ℝ) :
    star (fourierMonomial n x) = fourierMonomial (-n) x := by
  simp only [fourierMonomial_eq_circle]
  exact (fourier_neg (T := 2 * Real.pi)).symm

theorem fourierMonomial_eq_cos_add_sin (n : ℤ) (x : ℝ) :
    fourierMonomial n x = (Real.cos (n * x) : ℂ) +
      (Real.sin (n * x) : ℂ) * Complex.I := by
  simp only [fourierMonomial, Complex.exp_mul_I, ← Complex.ofReal_intCast,
    ← Complex.ofReal_mul, Complex.ofReal_cos, Complex.ofReal_sin]

theorem fourierMonomial_add_neg (n : ℤ) (x : ℝ) :
    fourierMonomial n x + fourierMonomial (-n) x = 2 * (Real.cos (n * x) : ℂ) := by
  rw [fourierMonomial_eq_cos_add_sin, fourierMonomial_eq_cos_add_sin]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

theorem fourierMonomial_hasDerivAt (n : ℤ) (x : ℝ) :
    HasDerivAt (fourierMonomial n)
      ((n : ℂ) * Complex.I * fourierMonomial n x) x := by
  have h := hasDerivAt_fourier (2 * Real.pi) n x
  have he : (2 * (Real.pi : ℂ) * Complex.I * n / (2 * Real.pi)) =
      (n : ℂ) * Complex.I := by
    field_simp
  simpa only [← fourierMonomial_eq_circle, Complex.ofReal_mul,
    Complex.ofReal_ofNat, he] using h

theorem complexRiemann_integrable_of_continuousOn {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    Chapter06.ComplexRSIntegrable f id a b :=
  ⟨Chapter06.rsIntegrable_of_continuousOn hab (Complex.continuous_re.comp_continuousOn hf)
      (fun _ _ _ _ h => h),
    Chapter06.rsIntegrable_of_continuousOn hab (Complex.continuous_im.comp_continuousOn hf)
      (fun _ _ _ _ h => h)⟩

theorem complexRiemann_integrable_mul {f g : ℝ → ℂ} {a b : ℝ}
    (hf : Chapter06.ComplexRSIntegrable f id a b)
    (hg : Chapter06.ComplexRSIntegrable g id a b) :
    Chapter06.ComplexRSIntegrable (fun x => f x * g x) id a b := by
  have hrr := Chapter06.rsIntegrable_mul hf.1 hg.1
  have hii := Chapter06.rsIntegrable_mul hf.2 hg.2
  have hri := Chapter06.rsIntegrable_mul hf.1 hg.2
  have hir := Chapter06.rsIntegrable_mul hf.2 hg.1
  constructor
  · simpa only [Complex.mul_re, sub_eq_add_neg, neg_mul, one_mul] using
      (Chapter06.rsIntegrable_add hrr (Chapter06.rsIntegrable_const_mul hii (-1)).1).1
  · exact (Chapter06.rsIntegrable_add hri hir).1

theorem riemannFourierCoeff_eq_integral {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) (n : ℤ) :
    riemannFourierCoeff f n = (2 * Real.pi : ℂ)⁻¹ *
      ∫ x in (-Real.pi)..Real.pi, f x * fourierMonomial (-n) x := by
  unfold riemannFourierCoeff
  rw [native_complex_integral_eq (complexRiemann_integrable_mul hf
    (complexRiemann_integrable_of_continuousOn hf.1.1
      (fourierMonomial_continuous (-n)).continuousOn))]

/-- Comparison with Mathlib's interval Fourier coefficient at the same frequency. -/
theorem riemannFourierCoeff_eq_fourierCoeffOn {f : ℝ → ℂ}
    (hf : Chapter06.ComplexRSIntegrable f id (-Real.pi) Real.pi) (n : ℤ) :
    riemannFourierCoeff f n =
      fourierCoeffOn (show -Real.pi < Real.pi by linarith [Real.pi_pos]) f n := by
  rw [riemannFourierCoeff_eq_integral hf, fourierCoeffOn_eq_integral]
  have hlen : Real.pi - -Real.pi = 2 * Real.pi := by ring
  simp only [hlen, one_div, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  simp only [smul_eq_mul]
  have he : fourier (T := Real.pi - -Real.pi) (-n)
      (x : AddCircle (Real.pi - -Real.pi)) = fourierMonomial (-n) x := by
    rw [fourier_coe_apply]
    unfold fourierMonomial
    congr 1
    push_cast
    field_simp
    ring
  simpa only [he] using mul_comm (f x) (fourierMonomial (-n) x)

/-- Native Riemann integral orthogonality, including existence of the integral. -/
theorem fourierMonomial_integral (n : ℤ) :
    Chapter06.ComplexRSIntegrable (fourierMonomial n) id (-Real.pi) Real.pi ∧
    Chapter06.ComplexRSIntegral (fourierMonomial n) id (-Real.pi) Real.pi =
      if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  have hab : -Real.pi < Real.pi := by linarith [Real.pi_pos]
  have hi := complexRiemann_integrable_of_continuousOn hab.le
    (fourierMonomial_continuous n).continuousOn
  refine ⟨hi, ?_⟩
  by_cases hn : n = 0
  · subst n
    simp only [ite_true]
    have hr := Chapter06.rsIntegral_const (c := 1) hab.le
      (show MonotoneOn (id : ℝ → ℝ) (Icc (-Real.pi) Real.pi) from fun _ _ _ _ h => h)
    have hz := Chapter06.rsIntegral_const (c := 0) hab.le
      (show MonotoneOn (id : ℝ → ℝ) (Icc (-Real.pi) Real.pi) from fun _ _ _ _ h => h)
    simp only [Chapter06.ComplexRSIntegral, fourierMonomial_zero, Complex.one_re, Complex.one_im]
    rw [hr.2, hz.2]
    simp [id_eq, sub_neg_eq_add, two_mul]
  · rw [ite_eq_right_iff.mpr (fun h => (hn h).elim)]
    let F : ℝ → ℂ := fun x => ((n : ℂ) * Complex.I)⁻¹ * fourierMonomial n x
    have hni : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hd (x : ℝ) : HasDerivAt F (fourierMonomial n x) x := by
      simpa only [F, ← mul_assoc, inv_mul_cancel₀ hni, one_mul] using
        (fourierMonomial_hasDerivAt n x).const_mul (((n : ℂ) * Complex.I)⁻¹)
    have he := Chapter06.complexRSIntegral_ftc hab (fun x _ => (hd x).hasDerivWithinAt) hi
    rw [he]
    have hp := fourierMonomial_periodic n (-Real.pi)
    have hx : -Real.pi + 2 * Real.pi = Real.pi := by ring
    rw [hx] at hp
    simp [F, hp]

/-- The printed normalized orthogonality integral (8.9, equation 61). -/
theorem fourierMonomial_normalized_integral (n : ℤ) :
    (2 * Real.pi : ℂ)⁻¹ *
      Chapter06.ComplexRSIntegral (fourierMonomial n) id (-Real.pi) Real.pi =
        if n = 0 then 1 else 0 := by
  rw [(fourierMonomial_integral n).2]
  have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.two_pi_pos.ne'
  split_ifs <;> simp only [inv_mul_cancel₀ hp, mul_zero]

theorem fourierCoeff_finite_sum (s : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    riemannFourierCoeff (fun x => ∑ n ∈ s, c n * fourierMonomial n x) m =
      if m ∈ s then c m else 0 := by
  classical
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hi (n : ℤ) := (Chapter06.complexRSIntegrable_const_mul
    (fourierMonomial_integral (n - m)).1 (c n))
  have he : (fun x => (∑ n ∈ s, c n * fourierMonomial n x) * fourierMonomial (-m) x) =
      (fun x => ∑ n ∈ s, c n * fourierMonomial (n - m) x) := by
    funext x
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [sub_eq_add_neg, fourierMonomial_add, mul_assoc]
  unfold riemannFourierCoeff
  rw [he, (Chapter07.complexRSIntegral_finite_sum s
    (fun n x => c n * fourierMonomial (n - m) x) (α := id) hab (fun _ _ _ _ h => h)
      (fun n _ => (hi n).1)).2, Finset.mul_sum]
  simp_rw [(hi _).2]
  have ht (n : ℤ) : (2 * Real.pi : ℂ)⁻¹ *
      (c n * Chapter06.ComplexRSIntegral (fourierMonomial (n - m)) id (-Real.pi) Real.pi) =
        if n = m then c n else 0 := by
    rw [mul_left_comm, fourierMonomial_normalized_integral]
    simp only [sub_eq_zero]
    split_ifs <;> simp
  simp_rw [ht]
  simp

theorem fourierCoeff_finsupp (c : ℤ →₀ ℂ) (m : ℤ) :
    riemannFourierCoeff (fun x => c.sum (fun n a => a * fourierMonomial n x)) m = c m := by
  change riemannFourierCoeff (fun x => ∑ n ∈ c.support, c n * fourierMonomial n x) m = c m
  rw [fourierCoeff_finite_sum]
  split_ifs with hm
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hm).symm

theorem trigonometric_coefficients_unique (c d : ℤ →₀ ℂ)
    (h : ∀ x, c.sum (fun n a => a * fourierMonomial n x) =
      d.sum (fun n a => a * fourierMonomial n x)) : c = d := by
  ext n
  rw [← fourierCoeff_finsupp c n, ← fourierCoeff_finsupp d n]
  exact congrArg (fun f => riemannFourierCoeff f n) (funext h)

theorem fourierCoeff_trigonometricPartialSum (c : ℤ → ℂ) (N : ℕ) (m : ℤ) :
    riemannFourierCoeff (trigonometricPartialSum c N) m =
      if -(N : ℤ) ≤ m ∧ m ≤ N then c m else 0 := by
  change riemannFourierCoeff (fun x => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
    c n * fourierMonomial n x) m = _
  simpa only [Finset.mem_Icc] using
    fourierCoeff_finite_sum (Finset.Icc (-(N : ℤ)) N) c m

theorem dirichletKernel_succ (N : ℕ) (x : ℝ) :
    dirichletKernel (N + 1) x =
      2 * (Real.cos (((N : ℝ) + 1) * x) : ℂ) + dirichletKernel N x := by
  unfold dirichletKernel
  rw [Nat.cast_add_one, Finset.sum_Icc_succ_eq_add_endpoints]
  rw [fourierMonomial_add_neg]
  simp only [Int.cast_add, Int.cast_natCast, Int.cast_one]

/-- PMA 8.13, equation 77, first as a denominator-free identity valid everywhere. -/
theorem dirichletKernel_mul_sin (N : ℕ) (x : ℝ) :
    dirichletKernel N x * (Real.sin (x / 2) : ℂ) =
      (Real.sin (((N : ℝ) + 1 / 2) * x) : ℂ) := by
  induction N with
  | zero => simp [dirichletKernel, fourierMonomial, div_eq_mul_inv, mul_comm]
  | succ N ih =>
    rw [dirichletKernel_succ, add_mul, ih]
    have ht := Real.two_mul_sin_mul_cos (x / 2) (((N : ℝ) + 1) * x)
    have hminus : x / 2 - ((N : ℝ) + 1) * x = -(((N : ℝ) + 1 / 2) * x) := by ring
    have hplus : x / 2 + ((N : ℝ) + 1) * x = (((N : ℝ) + 1 + 1 / 2) * x) := by ring
    rw [hminus, hplus, Real.sin_neg] at ht
    push_cast
    have hc := congrArg (fun r : ℝ => (r : ℂ)) ht
    push_cast at hc
    linear_combination hc

/-- The quotient formula is stated only where its denominator is nonzero. -/
theorem dirichletKernel_eq_sin_quotient (N : ℕ) (x : ℝ)
    (hx : Real.sin (x / 2) ≠ 0) :
    dirichletKernel N x =
      ((Real.sin (((N : ℝ) + 1 / 2) * x) / Real.sin (x / 2) : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, eq_div_iff (by exact_mod_cast hx)]
  exact dirichletKernel_mul_sin N x

theorem trigonometricPolynomial_continuous {f : ℝ → ℂ}
    (hf : TrigonometricPolynomial f) : Continuous f := by
  obtain ⟨c, hc⟩ := hf
  have heq : f = fun x => ∑ n ∈ c.support, c n * fourierMonomial n x := funext hc
  rw [heq]
  exact continuous_finsetSum _ (fun n _ => continuous_const.mul (fourierMonomial_continuous n))

theorem trigonometricPolynomial_periodic {f : ℝ → ℂ}
    (hf : TrigonometricPolynomial f) : Function.Periodic f (2 * Real.pi) := by
  obtain ⟨c, hc⟩ := hf
  intro x
  simp only [hc, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [fourierMonomial_periodic n x]

/-- PMA 8.15, with complex values and an error bound on the entire real line. -/
def pma8_15_contract : Prop :=
  ∀ (f : ℝ → ℂ), Continuous f → Function.Periodic f (2 * Real.pi) →
  ∀ ε : ℝ, 0 < ε → ∃ P : ℝ → ℂ,
    TrigonometricPolynomial P ∧ ∀ x : ℝ, ‖P x - f x‖ < ε

theorem pma8_15 : pma8_15_contract := by
  intro f hf hp ε hε
  let F : C(AddCircle (2 * Real.pi), ℂ) :=
    ⟨hp.lift, hf.quotient_lift _⟩
  have hcl : F ∈ closure (↑(Submodule.span ℂ
      (Set.range (fourier (T := 2 * Real.pi)))) : Set C(AddCircle (2 * Real.pi), ℂ)) := by
    change F ∈ (Submodule.span ℂ (Set.range (fourier (T := 2 * Real.pi)))).topologicalClosure
    rw [span_fourier_closure_eq_top]
    trivial
  obtain ⟨Q, hQ, hdist⟩ := Metric.mem_closure_iff.mp hcl ε hε
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hQ
  refine ⟨fun x => Q (x : AddCircle (2 * Real.pi)), ⟨c, ?_⟩, ?_⟩
  · intro x
    rw [← hc]
    simp only [Finsupp.sum, ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [fourierMonomial_eq_circle]
  · intro x
    have hle := ContinuousMap.dist_apply_le_dist (f := F) (g := Q) (x : AddCircle (2 * Real.pi))
    have hlt := hle.trans_lt hdist
    change dist (f x) (Q (x : AddCircle (2 * Real.pi))) < ε at hlt
    rw [dist_eq_norm, norm_sub_rev] at hlt
    exact hlt

end Rudin.PMA.Chapter08
