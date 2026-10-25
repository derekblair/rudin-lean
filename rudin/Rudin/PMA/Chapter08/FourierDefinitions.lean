import Rudin.PMA.Chapter08.FourierExponentialExample

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter08

def sineCosinePolynomial (N : ℕ) (a b : ℕ → ℂ) (x : ℝ) : ℂ :=
  a 0 + ∑ n ∈ Finset.range N,
    (a (n + 1) * (Real.cos (((n : ℝ) + 1) * x) : ℂ) +
      b (n + 1) * (Real.sin (((n : ℝ) + 1) * x) : ℂ))

theorem trigonometricPartialSum_succ (c : ℤ → ℂ) (N : ℕ) (x : ℝ) :
    trigonometricPartialSum c (N + 1) x =
      c ((N : ℤ) + 1) * fourierMonomial ((N : ℤ) + 1) x +
      c (-((N : ℤ) + 1)) * fourierMonomial (-((N : ℤ) + 1)) x +
      trigonometricPartialSum c N x := by
  unfold trigonometricPartialSum
  rw [Nat.cast_add_one, Finset.sum_Icc_succ_eq_add_endpoints]

theorem trigonometricPartialSum_eq_sineCosine (c : ℤ → ℂ) (N : ℕ) (x : ℝ) :
    trigonometricPartialSum c N x = sineCosinePolynomial N
      (fun n => if n = 0 then c 0 else c n + c (-(n : ℤ)))
      (fun n => Complex.I * (c n - c (-(n : ℤ)))) x := by
  induction N with
  | zero => simp [trigonometricPartialSum, sineCosinePolynomial]
  | succ N ih =>
    rw [trigonometricPartialSum_succ, ih]
    simp only [sineCosinePolynomial, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one,
      Nat.succ_ne_zero, ite_false, ite_true]
    rw [fourierMonomial_eq_cos_add_sin, fourierMonomial_eq_cos_add_sin]
    simp only [Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, neg_mul,
      Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring

theorem trigonometricPolynomial_finite (s : Finset ℤ) (c : ℤ → ℂ) :
    TrigonometricPolynomial (fun x => ∑ n ∈ s, c n * fourierMonomial n x) := by
  classical
  refine ⟨∑ n ∈ s, Finsupp.single n (c n), ?_⟩
  intro x
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  simp only [Finsupp.sum_single_index, zero_mul]

theorem trigonometricPolynomial_iff_symmetric (f : ℝ → ℂ) :
    TrigonometricPolynomial f ↔
      ∃ (N : ℕ) (c : ℤ → ℂ), ∀ x, f x = trigonometricPartialSum c N x := by
  classical
  constructor
  · rintro ⟨c, hc⟩
    let N := c.support.sup Int.natAbs
    refine ⟨N, c, fun x => (hc x).trans ?_⟩
    change (∑ n ∈ c.support, c n * fourierMonomial n x) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n * fourierMonomial n x
    apply Finset.sum_subset
    · intro n hn
      have hh : n.natAbs ≤ N := Finset.le_sup (f := Int.natAbs) hn
      have hh' : |n| ≤ (N : ℤ) := by
        rw [← Int.natCast_natAbs]
        exact_mod_cast hh
      exact Finset.mem_Icc.mpr (abs_le.mp hh')
    · intro n _ hn
      rw [Finsupp.notMem_support_iff.mp hn, zero_mul]
  · rintro ⟨N, c, hc⟩
    have h := trigonometricPolynomial_finite (Finset.Icc (-(N : ℤ)) N) c
    exact (funext hc) ▸ h

theorem sineCosinePolynomial_is_trigonometric (N : ℕ) (a b : ℕ → ℂ) :
    TrigonometricPolynomial (sineCosinePolynomial N a b) := by
  let c : ℤ → ℂ := fun k => if k = 0 then a 0 else
    if 0 < k then (a k.natAbs - Complex.I * b k.natAbs) / 2
    else (a k.natAbs + Complex.I * b k.natAbs) / 2
  apply (trigonometricPolynomial_iff_symmetric _).mpr
  refine ⟨N, c, ?_⟩
  intro x
  rw [trigonometricPartialSum_eq_sineCosine]
  simp only [sineCosinePolynomial]
  have hc0 : c 0 = a 0 := by simp [c]
  simp only [ite_true, hc0]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  have hp : (0 : ℤ) < (n : ℤ) + 1 := by omega
  simp only [Nat.succ_ne_zero, ite_false, Nat.cast_add, Nat.cast_one]
  simp only [c, ne_of_gt hp, ne_of_lt (neg_neg_of_pos hp), ite_false, hp,
    ite_true, neg_pos, not_lt.mpr hp.le, Int.natAbs_neg]
  have habs : ((n : ℤ) + 1).natAbs = n + 1 := by
    exact Int.natAbs_natCast (n + 1)
  rw [habs]
  have hI := Complex.I_sq
  field_simp
  linear_combination 2 * hI * (b (n + 1) * (Real.sin (((n : ℝ) + 1) * x) : ℂ))

theorem trigonometricPolynomial_iff_sineCosine (f : ℝ → ℂ) :
    TrigonometricPolynomial f ↔
      ∃ (N : ℕ) (a b : ℕ → ℂ), f = sineCosinePolynomial N a b := by
  constructor
  · intro hf
    obtain ⟨N, c, hc⟩ := (trigonometricPolynomial_iff_symmetric f).mp hf
    refine ⟨N, (fun n => if n = 0 then c 0 else c n + c (-(n : ℤ))),
      (fun n => Complex.I * (c n - c (-(n : ℤ)))), ?_⟩
    funext x
    exact (hc x).trans (trigonometricPartialSum_eq_sineCosine c N x)
  · rintro ⟨N, a, b, rfl⟩
    exact sineCosinePolynomial_is_trigonometric N a b

theorem star_trigonometricPartialSum (c : ℤ → ℂ) (N : ℕ) (x : ℝ) :
    star (trigonometricPartialSum c N x) =
      trigonometricPartialSum (fun n => star (c (-n))) N x := by
  classical
  simp only [trigonometricPartialSum, star_sum, star_mul, fourierMonomial_star]
  apply Finset.sum_bij (fun n _ => -n)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n hn m hm h
    exact neg_injective h
  · intro n hn
    refine ⟨-n, ?_, neg_neg n⟩
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n _
    simp only [neg_neg]
    ring

/-- PMA 8.9: a finite symmetric trigonometric sum is real-valued precisely
when its coefficients have the printed conjugate symmetry. -/
theorem trigonometricPartialSum_real_iff (c : ℤ → ℂ) (N : ℕ) :
    (∀ x, (trigonometricPartialSum c N x).im = 0) ↔
      ∀ n : ℤ, -(N : ℤ) ≤ n → n ≤ N → c (-n) = star (c n) := by
  constructor
  · intro hr n hn hn'
    have he : trigonometricPartialSum (fun n => star (c (-n))) N =
        trigonometricPartialSum c N := by
      funext x
      rw [← star_trigonometricPartialSum]
      exact Complex.conj_eq_iff_im.mpr (hr x)
    have hh := congrArg (fun f => riemannFourierCoeff f n) he
    rw [fourierCoeff_trigonometricPartialSum, fourierCoeff_trigonometricPartialSum,
      ite_eq_left ⟨hn, hn'⟩, ite_eq_left ⟨hn, hn'⟩] at hh
    simpa only [star_star] using congrArg star hh
  · intro hc x
    apply Complex.conj_eq_iff_im.mp
    change star (trigonometricPartialSum c N x) = trigonometricPartialSum c N x
    rw [star_trigonometricPartialSum]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only
    rw [hc n (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2, star_star]


open Chapter06

theorem fourierDefinitions_native_gram (m n : ℤ) :
    ComplexRSIntegrable (fun x => fourierMonomial m x * star (fourierMonomial n x))
      id (-Real.pi) Real.pi ∧
    ComplexRSIntegral (fun x => fourierMonomial m x * star (fourierMonomial n x))
      id (-Real.pi) Real.pi = if m = n then (2 * Real.pi : ℂ) else 0 := by
  simpa only [fourierMonomial_star, ← fourierMonomial_add, ← sub_eq_add_neg,
    sub_eq_zero] using fourierMonomial_integral (m - n)

theorem fourier_finite_native_pair {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (k : ι → ℤ) (l : κ → ℤ) (c : ι → ℂ) (d : κ → ℂ) :
    ComplexRSIntegrable (fun x => (∑ i ∈ s, c i * fourierMonomial (k i) x) *
      star (∑ j ∈ t, d j * fourierMonomial (l j) x)) id (-Real.pi) Real.pi ∧
    ComplexRSIntegral (fun x => (∑ i ∈ s, c i * fourierMonomial (k i) x) *
      star (∑ j ∈ t, d j * fourierMonomial (l j) x)) id (-Real.pi) Real.pi =
      ∑ i ∈ s, ∑ j ∈ t, c i * star (d j) *
        (if k i = l j then (2 * Real.pi : ℂ) else 0) := by
  have hab : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hr (i : ι) := native_pair_finsum_right hab t d
    (fun j _ => (fourierDefinitions_native_gram (k i) (l j)).1)
  have hl := native_pair_finsum_left hab s c (fun i _ => (hr i).1)
  refine ⟨hl.1, hl.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  rw [(hr i).2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [(fourierDefinitions_native_gram (k i) (l j)).2]
  ring

def pairedFourier (k : ℤ) (a b : ℂ) (x : ℝ) : ℂ :=
  a * fourierMonomial k x + b * fourierMonomial (-k) x

theorem pairedFourier_native_pair (k l : ℤ) (a b c d : ℂ) :
    ComplexRSIntegrable (fun x => pairedFourier k a b x * star (pairedFourier l c d x))
      id (-Real.pi) Real.pi ∧
    ComplexRSIntegral (fun x => pairedFourier k a b x * star (pairedFourier l c d x))
      id (-Real.pi) Real.pi =
      a * star c * (if k = l then (2 * Real.pi : ℂ) else 0) +
      a * star d * (if k = -l then (2 * Real.pi : ℂ) else 0) +
      b * star c * (if -k = l then (2 * Real.pi : ℂ) else 0) +
      b * star d * (if k = l then (2 * Real.pi : ℂ) else 0) := by
  have h := fourier_finite_native_pair (Finset.univ : Finset Bool) Finset.univ
    (fun i => if i then k else -k) (fun j : Bool => if j then l else -l)
    (fun i => if i then a else b) (fun j : Bool => if j then c else d)
  simpa [Fintype.sum_bool, pairedFourier, neg_inj, add_comm, add_left_comm, add_assoc] using h

/-- A generic native Gram criterion, including existence of every integral. -/
theorem riemannOrthonormal_of_gram (φ : ℕ → ℝ → ℂ) (a b : ℝ)
    (h : ∀ m n, ComplexRSIntegrable (fun x => φ m x * star (φ n x)) id a b ∧
      ComplexRSIntegral (fun x => φ m x * star (φ n x)) id a b =
        if m = n then 1 else 0) : RiemannOrthonormal φ a b := by
  refine ⟨fun m n hmn => ?_, fun n => ?_⟩
  · simpa only [hmn, ite_false] using h m n
  · have hn := h n n
    have hi : RIntegrable (fun x => ‖φ n x‖ ^ 2) a b := by
      simpa only [complex_mul_star, Complex.ofReal_re] using hn.1.1
    refine ⟨hi, ?_⟩
    have he := congrArg Complex.re hn.2
    simpa only [ite_true, Complex.one_re, complex_mul_star, ComplexRSIntegral,
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using he


def realFourierAtom : Option (Bool × ℕ) → ℝ → ℂ
  | none => pairedFourier 0 ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹) 0
  | some (false, n) => pairedFourier ((n : ℤ) + 1)
      ((2 * (Real.sqrt Real.pi : ℂ))⁻¹) ((2 * (Real.sqrt Real.pi : ℂ))⁻¹)
  | some (true, n) => pairedFourier ((n : ℤ) + 1)
      (-Complex.I * (2 * (Real.sqrt Real.pi : ℂ))⁻¹)
      (Complex.I * (2 * (Real.sqrt Real.pi : ℂ))⁻¹)

theorem realFourierAtom_native_gram (u v : Option (Bool × ℕ)) :
    ComplexRSIntegrable (fun x => realFourierAtom u x * star (realFourierAtom v x))
      id (-Real.pi) Real.pi ∧
    ComplexRSIntegral (fun x => realFourierAtom u x * star (realFourierAtom v x))
      id (-Real.pi) Real.pi = if u = v then 1 else 0 := by
  have hp : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
  have hp2 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.2 (by positivity : 0 < 2 * Real.pi))
  have hs : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hs2 : (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = (2 * Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi)
  cases u with
  | none =>
    cases v with
    | none =>
      simp only [realFourierAtom]
      constructor
      · exact (pairedFourier_native_pair _ _ _ _ _ _).1
      · rw [(pairedFourier_native_pair _ _ _ _ _ _).2]
        simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal, star_zero,
          mul_zero, zero_mul, add_zero, ite_true]
        field_simp [hp2]
        simpa only [pow_two] using hs2.symm
    | some v =>
      rcases v with ⟨b, n⟩
      cases b <;> simp only [realFourierAtom]
      all_goals constructor
      all_goals first
        | exact (pairedFourier_native_pair _ _ _ _ _ _).1
        | rw [(pairedFourier_native_pair _ _ _ _ _ _).2]
          have hn : (0 : ℤ) ≠ (n : ℤ) + 1 := by omega
          have hn' : (0 : ℤ) ≠ -((n : ℤ) + 1) := by omega
          simp only [neg_zero, hn, hn', reduceCtorEq, ite_false, mul_zero, zero_mul, add_zero]
  | some u =>
    rcases u with ⟨b, m⟩
    cases v with
    | none =>
      cases b <;> simp only [realFourierAtom]
      all_goals constructor
      all_goals first
        | exact (pairedFourier_native_pair _ _ _ _ _ _).1
        | rw [(pairedFourier_native_pair ((m : ℤ) + 1) 0 _ _ _ _).2]
          have hm : (m : ℤ) + 1 ≠ 0 := by omega
          have hm' : -((m : ℤ) + 1) ≠ 0 := by omega
          simp only [neg_zero, hm, hm', reduceCtorEq, ite_false, mul_zero, add_zero]
    | some v =>
      rcases v with ⟨c, n⟩
      have hmn : (m : ℤ) + 1 ≠ -((n : ℤ) + 1) := by omega
      have hnm : -((m : ℤ) + 1) ≠ (n : ℤ) + 1 := by omega
      cases b <;> cases c <;> simp only [realFourierAtom]
      all_goals constructor
      all_goals first
        | exact (pairedFourier_native_pair _ _ _ _ _ _).1
        | rw [(pairedFourier_native_pair _ _ _ _ _ _).2]
          by_cases h : m = n
          · subst n
            simp only [hmn, hnm, ite_false, ite_true, mul_zero, add_zero,
              star_inv₀, star_mul, star_neg, Complex.star_def, map_ofNat,
              Complex.conj_ofReal, Complex.conj_I, Option.some.injEq, Prod.mk.injEq,
              Bool.false_eq_true, Bool.true_eq_false, false_and]
            field_simp [hp]
            ring_nf <;> simp only [Complex.I_sq, hs] <;> ring
          · have hh : (m : ℤ) + 1 ≠ (n : ℤ) + 1 := by omega
            simp only [hmn, hnm, hh, h, Option.some.injEq, Prod.mk.injEq,
              and_false, ite_false, mul_zero, add_zero]

/-- The printed real system, enumerated as constant, cosine, sine, cosine, sine, ... -/
def realFourierIndex : ℕ → Option (Bool × ℕ)
  | 0 => none
  | n + 1 => some (Equiv.boolProdNatEquivNat.symm n)

def normalizedRealFourierSystem (n : ℕ) : ℝ → ℂ :=
  realFourierAtom (realFourierIndex n)

theorem realFourierIndex_injective : Function.Injective realFourierIndex := by
  intro m n h
  cases m with
  | zero => cases n <;> simp_all [realFourierIndex]
  | succ m =>
    cases n with
    | zero => simp [realFourierIndex] at h
    | succ n =>
      simp only [realFourierIndex, Option.some.injEq, Equiv.apply_eq_iff_eq] at h
      exact congrArg Nat.succ h

theorem normalizedRealFourierSystem_orthonormal :
    RiemannOrthonormal normalizedRealFourierSystem (-Real.pi) Real.pi := by
  apply riemannOrthonormal_of_gram
  intro m n
  simpa only [normalizedRealFourierSystem, realFourierIndex_injective.eq_iff] using
    realFourierAtom_native_gram (realFourierIndex m) (realFourierIndex n)


theorem realFourierAtom_constant (x : ℝ) :
    realFourierAtom none x = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ := by
  simp [realFourierAtom, pairedFourier]

theorem realFourierAtom_cos (n : ℕ) (x : ℝ) :
    realFourierAtom (some (false, n)) x =
      (Real.cos (((n : ℝ) + 1) * x) : ℂ) / (Real.sqrt Real.pi : ℂ) := by
  simp only [realFourierAtom, pairedFourier, fourierMonomial_eq_cos_add_sin,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, neg_mul,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring

theorem realFourierAtom_sin (n : ℕ) (x : ℝ) :
    realFourierAtom (some (true, n)) x =
      (Real.sin (((n : ℝ) + 1) * x) : ℂ) / (Real.sqrt Real.pi : ℂ) := by
  simp only [realFourierAtom, pairedFourier, fourierMonomial_eq_cos_add_sin,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Int.cast_neg, neg_mul,
    Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  ring_nf
  simp [Complex.I_sq]

theorem normalizedRealFourierSystem_zero (x : ℝ) :
    normalizedRealFourierSystem 0 x = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ :=
  realFourierAtom_constant x

theorem normalizedRealFourierSystem_cos (n : ℕ) (x : ℝ) :
    normalizedRealFourierSystem (2 * n + 1) x =
      (Real.cos (((n : ℝ) + 1) * x) : ℂ) / (Real.sqrt Real.pi : ℂ) := by
  have hi : Equiv.boolProdNatEquivNat.symm (2 * n) = (false, n) := by
    apply Equiv.boolProdNatEquivNat.symm_apply_eq.mpr
    simp [Equiv.boolProdNatEquivNat, Nat.bit, two_mul]
  simp only [normalizedRealFourierSystem, realFourierIndex, hi]
  exact realFourierAtom_cos n x

theorem normalizedRealFourierSystem_sin (n : ℕ) (x : ℝ) :
    normalizedRealFourierSystem (2 * n + 2) x =
      (Real.sin (((n : ℝ) + 1) * x) : ℂ) / (Real.sqrt Real.pi : ℂ) := by
  have hi : Equiv.boolProdNatEquivNat.symm (2 * n + 1) = (true, n) := by
    apply Equiv.boolProdNatEquivNat.symm_apply_eq.mpr
    simp [Equiv.boolProdNatEquivNat, Nat.bit, two_mul]
  change realFourierAtom (some (Equiv.boolProdNatEquivNat.symm (2 * n + 1))) x = _
  rw [hi]
  exact realFourierAtom_sin n x


/-- The Fourier-series notation in PMA 8.9 records coefficients; it asserts
no convergence of the symmetric partial sums. -/
def HasRiemannFourierSeries (f : ℝ → ℂ) (c : ℤ → ℂ) : Prop :=
  ComplexRSIntegrable f id (-Real.pi) Real.pi ∧ c = riemannFourierCoeff f

/-- The relative Fourier-series notation in PMA 8.10 records the existing
coefficient integrals, without imposing a convergence assertion. -/
def HasOrthogonalFourierSeries (f : ℝ → ℂ) (φ : ℕ → ℝ → ℂ)
    (a b : ℝ) (c : ℕ → ℂ) : Prop :=
  RiemannOrthonormal φ a b ∧ ∀ n, ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b ∧
    c n = orthogonalFourierCoeff f φ a b n

def pma8_9_contract : Prop :=
  (∀ f : ℝ → ℂ, TrigonometricPolynomial f ↔
    ∃ (N : ℕ) (a b : ℕ → ℂ), f = sineCosinePolynomial N a b) ∧
  (∀ f : ℝ → ℂ, TrigonometricPolynomial f ↔
    ∃ (N : ℕ) (c : ℤ → ℂ), ∀ x, f x = trigonometricPartialSum c N x) ∧
  (∀ f : ℝ → ℂ, TrigonometricPolynomial f →
    Continuous f ∧ Function.Periodic f (2 * Real.pi)) ∧
  (∀ n : ℤ, ComplexRSIntegrable (fourierMonomial n) id (-Real.pi) Real.pi ∧
    (2 * Real.pi : ℂ)⁻¹ * ComplexRSIntegral (fourierMonomial n) id (-Real.pi) Real.pi =
      if n = 0 then 1 else 0) ∧
  (∀ (c : ℤ → ℂ) (N : ℕ) (m : ℤ),
    riemannFourierCoeff (trigonometricPartialSum c N) m =
      if -(N : ℤ) ≤ m ∧ m ≤ N then c m else 0) ∧
  (∀ (c : ℤ → ℂ) (N : ℕ),
    (∀ x, (trigonometricPartialSum c N x).im = 0) ↔
      ∀ n : ℤ, -(N : ℤ) ≤ n → n ≤ N → c (-n) = star (c n)) ∧
  (∀ f : ℝ → ℂ, ComplexRSIntegrable f id (-Real.pi) Real.pi →
    HasRiemannFourierSeries f (riemannFourierCoeff f))

theorem pma8_9 : pma8_9_contract :=
  ⟨trigonometricPolynomial_iff_sineCosine, trigonometricPolynomial_iff_symmetric,
    fun _ hf => ⟨trigonometricPolynomial_continuous hf, trigonometricPolynomial_periodic hf⟩,
    fun n => ⟨(fourierMonomial_integral n).1, fourierMonomial_normalized_integral n⟩,
    fourierCoeff_trigonometricPartialSum, trigonometricPartialSum_real_iff,
    fun _ hf => ⟨hf, rfl⟩⟩

def pma8_10_contract : Prop :=
  RiemannOrthonormal normalizedFourierSystem (-Real.pi) Real.pi ∧
  (∀ k : ℤ, ∃ n : ℕ, normalizedFourierSystem n = normalizedFourier k) ∧
  RiemannOrthonormal normalizedRealFourierSystem (-Real.pi) Real.pi ∧
  (∀ x : ℝ, normalizedRealFourierSystem 0 x = (Real.sqrt (2 * Real.pi) : ℂ)⁻¹) ∧
  (∀ (n : ℕ) (x : ℝ), normalizedRealFourierSystem (2 * n + 1) x =
    (Real.cos (((n : ℝ) + 1) * x) : ℂ) / (Real.sqrt Real.pi : ℂ)) ∧
  (∀ (n : ℕ) (x : ℝ), normalizedRealFourierSystem (2 * n + 2) x =
    (Real.sin (((n : ℝ) + 1) * x) : ℂ) / (Real.sqrt Real.pi : ℂ)) ∧
  (∀ (f : ℝ → ℂ) (φ : ℕ → ℝ → ℂ) (a b : ℝ), RiemannOrthonormal φ a b →
    (∀ n, ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b) →
    HasOrthogonalFourierSeries f φ a b (orthogonalFourierCoeff f φ a b))

theorem pma8_10 : pma8_10_contract :=
  ⟨normalizedFourierSystem_orthonormal, normalizedFourierSystem_all_frequencies,
    normalizedRealFourierSystem_orthonormal, normalizedRealFourierSystem_zero,
    normalizedRealFourierSystem_cos, normalizedRealFourierSystem_sin,
    fun _ _ _ _ hφ hi => ⟨hφ, fun n => ⟨hi n, rfl⟩⟩⟩

end Rudin.PMA.Chapter08
