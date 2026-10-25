import Rudin.PMA.Chapter08.Fourier

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter08

open Chapter06

theorem complex_mul_star (z : ℂ) : z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  exact_mod_cast Complex.mul_conj' z

def orthogonalPartialSum (φ : ℕ → ℝ → ℂ) (c : ℕ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, c n * φ n x

theorem native_integral_ofReal {f : ℝ → ℝ} {a b : ℝ}
    (hf : RIntegrable f a b) :
    ComplexRSIntegrable (fun x => (f x : ℂ)) id a b ∧
      ComplexRSIntegral (fun x => (f x : ℂ)) id a b = (RIntegral f a b : ℂ) := by
  have hz := rsIntegral_const (c := (0 : ℝ)) hf.1 hf.2.2.1
  exact ⟨⟨hf, by simpa using hz.1⟩, by simp [ComplexRSIntegral, hz.2]⟩

theorem native_norm_sq_integrable {f : ℝ → ℂ} {a b : ℝ}
    (hf : ComplexRSIntegrable f id a b) : RIntegrable (fun x => ‖f x‖ ^ 2) a b := by
  have h := (rsIntegrable_add (rsIntegrable_square hf.1) (rsIntegrable_square hf.2)).1
  simp_rw [Complex.sq_norm, Complex.normSq_apply]
  simpa only [pow_two] using h

theorem orthonormal_native_gram {φ : ℕ → ℝ → ℂ} {a b : ℝ}
    (hφ : RiemannOrthonormal φ a b) (m n : ℕ) :
    ComplexRSIntegrable (fun x => φ m x * star (φ n x)) id a b ∧
      ComplexRSIntegral (fun x => φ m x * star (φ n x)) id a b = if m = n then 1 else 0 := by
  by_cases hmn : m = n
  · subst n
    have h := native_integral_ofReal (hφ.2 m).1
    simpa only [complex_mul_star, (hφ.2 m).2, Complex.ofReal_one,
      ite_true] using h
  · simpa only [hmn, ite_false] using hφ.1 m n hmn

theorem native_pair_sum_right {f : ℝ → ℂ} {φ : ℕ → ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (N : ℕ) (d : ℕ → ℂ)
    (hi : ∀ n ∈ Finset.range N,
      ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b) :
    ComplexRSIntegrable (fun x => f x * star (orthogonalPartialSum φ d N x)) id a b ∧
      ComplexRSIntegral (fun x => f x * star (orthogonalPartialSum φ d N x)) id a b =
        ∑ n ∈ Finset.range N, star (d n) * orthogonalFourierCoeff f φ a b n := by
  have hs := Chapter07.complexRSIntegral_finite_sum (Finset.range N)
    (fun n x => star (d n) * (f x * star (φ n x))) hab
    (show MonotoneOn (id : ℝ → ℝ) (Icc a b) from fun _ _ _ _ h => h)
    (fun n hn => (complexRSIntegrable_const_mul (hi n hn) _).1)
  have he : (fun x => f x * star (orthogonalPartialSum φ d N x)) =
      fun x => ∑ n ∈ Finset.range N, star (d n) * (f x * star (φ n x)) := by
    funext x
    simp only [orthogonalPartialSum, star_sum, star_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro n hn
  exact (complexRSIntegrable_const_mul (hi n hn) _).2

theorem native_pair_sum_left {g : ℝ → ℂ} {φ : ℕ → ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (N : ℕ) (d : ℕ → ℂ)
    (hi : ∀ n ∈ Finset.range N,
      ComplexRSIntegrable (fun x => φ n x * star (g x)) id a b) :
    ComplexRSIntegrable (fun x => orthogonalPartialSum φ d N x * star (g x)) id a b ∧
      ComplexRSIntegral (fun x => orthogonalPartialSum φ d N x * star (g x)) id a b =
        ∑ n ∈ Finset.range N, d n * ComplexRSIntegral
          (fun x => φ n x * star (g x)) id a b := by
  have hs := Chapter07.complexRSIntegral_finite_sum (Finset.range N)
    (fun n x => d n * (φ n x * star (g x))) hab
    (show MonotoneOn (id : ℝ → ℝ) (Icc a b) from fun _ _ _ _ h => h)
    (fun n hn => (complexRSIntegrable_const_mul (hi n hn) _).1)
  have he : (fun x => orthogonalPartialSum φ d N x * star (g x)) =
      fun x => ∑ n ∈ Finset.range N, d n * (φ n x * star (g x)) := by
    funext x
    simp only [orthogonalPartialSum, Finset.sum_mul, mul_assoc]
  rw [he]
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro n hn
  exact (complexRSIntegrable_const_mul (hi n hn) _).2

theorem orthonormal_sum_norm_sq {φ : ℕ → ℝ → ℂ} {a b : ℝ}
    (hφ : RiemannOrthonormal φ a b) (N : ℕ) (d : ℕ → ℂ) :
    RIntegrable (fun x => ‖orthogonalPartialSum φ d N x‖ ^ 2) a b ∧
      RIntegral (fun x => ‖orthogonalPartialSum φ d N x‖ ^ 2) a b =
        ∑ n ∈ Finset.range N, ‖d n‖ ^ 2 := by
  have hab := (hφ.2 0).1.1
  have hr (m : ℕ) := native_pair_sum_right hab N d
    (fun n _ => (orthonormal_native_gram hφ m n).1)
  have hl := native_pair_sum_left hab N d (fun m _ => (hr m).1)
  have he (m : ℕ) (hm : m ∈ Finset.range N) :
      ComplexRSIntegral (fun x => φ m x * star (orthogonalPartialSum φ d N x)) id a b =
        star (d m) := by
    rw [(hr m).2]
    simp only [orthogonalFourierCoeff, (orthonormal_native_gram hφ _ _).2]
    simp [hm]
  have hi : RIntegrable (fun x => ‖orthogonalPartialSum φ d N x‖ ^ 2) a b := by
    simpa only [complex_mul_star, Complex.ofReal_re] using hl.1.1
  refine ⟨hi, ?_⟩
  have hc := hl.2
  rw [Finset.sum_congr rfl (fun m hm => congrArg (d m * ·) (he m hm))] at hc
  simpa only [complex_mul_star, ComplexRSIntegral,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, ← Complex.ofReal_sum,
    Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    map_sum] using congrArg Complex.re hc

theorem complex_norm_sub_square (u v : ℂ) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * star v).re := by
  change ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (u * (starRingEnd ℂ) v).re
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem native_error_expansion {f g : ℝ → ℂ} {a b : ℝ}
    (hf : RIntegrable (fun x => ‖f x‖ ^ 2) a b)
    (hg : RIntegrable (fun x => ‖g x‖ ^ 2) a b)
    (hfg : ComplexRSIntegrable (fun x => f x * star (g x)) id a b) :
    RIntegrable (fun x => ‖f x - g x‖ ^ 2) a b ∧
    RIntegral (fun x => ‖f x - g x‖ ^ 2) a b =
      RIntegral (fun x => ‖f x‖ ^ 2) a b + RIntegral (fun x => ‖g x‖ ^ 2) a b -
        2 * (ComplexRSIntegral (fun x => f x * star (g x)) id a b).re := by
  have hsum := rsIntegrable_add hf hg
  have hscaled := rsIntegrable_const_mul hfg.1 (-2)
  have hh := rsIntegrable_add hsum.1 hscaled.1
  have he : (fun x => ‖f x - g x‖ ^ 2) =
      fun x => ‖f x‖ ^ 2 + ‖g x‖ ^ 2 + -2 * (f x * star (g x)).re := by
    funext x
    rw [complex_norm_sub_square]
    ring
  rw [he]
  refine ⟨hh.1, ?_⟩
  simp only [RIntegral]
  rw [hh.2, hsum.2, hscaled.2]
  simp only [ComplexRSIntegral, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
  ring

theorem complex_norm_sub_square' (u v : ℂ) :
    ‖u - v‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * (star u * v).re := by
  rw [complex_norm_sub_square]
  change _ = _ - 2 * ((starRingEnd ℂ) u * v).re
  change _ - 2 * (u * (starRingEnd ℂ) v).re = _
  simp [Complex.mul_re, mul_comm]

theorem orthonormal_error_identity {f : ℝ → ℂ} {φ : ℕ → ℝ → ℂ} {a b : ℝ}
    (hf : ComplexRSIntegrable f id a b) (hφ : RiemannOrthonormal φ a b)
    (hi : ∀ n, ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b)
    (N : ℕ) (d : ℕ → ℂ) :
    RIntegrable (fun x => ‖f x - orthogonalPartialSum φ d N x‖ ^ 2) a b ∧
    RIntegral (fun x => ‖f x - orthogonalPartialSum φ d N x‖ ^ 2) a b =
      RIntegral (fun x => ‖f x‖ ^ 2) a b -
        ∑ n ∈ Finset.range N, ‖orthogonalFourierCoeff f φ a b n‖ ^ 2 +
        ∑ n ∈ Finset.range N, ‖d n - orthogonalFourierCoeff f φ a b n‖ ^ 2 := by
  have hgg := orthonormal_sum_norm_sq hφ N d
  have hfg := native_pair_sum_right hf.1.1 N d (fun n _ => hi n)
  have hh := native_error_expansion (native_norm_sq_integrable hf) hgg.1 hfg.1
  refine ⟨hh.1, ?_⟩
  rw [hh.2, hgg.2, hfg.2]
  simp_rw [complex_norm_sub_square']
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Complex.re_sum]
  ring

theorem native_pair_finsum_right {ι : Type*} {f : ℝ → ℂ} {φ : ι → ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (s : Finset ι) (d : ι → ℂ)
    (hi : ∀ n ∈ s,
      ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b) :
    ComplexRSIntegrable (fun x => f x * star ((∑ n ∈ s, d n * φ n x))) id a b ∧
      ComplexRSIntegral (fun x => f x * star ((∑ n ∈ s, d n * φ n x))) id a b =
        ∑ n ∈ s, star (d n) * ComplexRSIntegral (fun x => f x * star (φ n x)) id a b := by
  have hs := Chapter07.complexRSIntegral_finite_sum (s)
    (fun n x => star (d n) * (f x * star (φ n x))) hab
    (show MonotoneOn (id : ℝ → ℝ) (Icc a b) from fun _ _ _ _ h => h)
    (fun n hn => (complexRSIntegrable_const_mul (hi n hn) _).1)
  have he : (fun x => f x * star ((∑ n ∈ s, d n * φ n x))) =
      fun x => ∑ n ∈ s, star (d n) * (f x * star (φ n x)) := by
    funext x
    simp only [star_sum, star_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [he]
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro n hn
  exact (complexRSIntegrable_const_mul (hi n hn) _).2

theorem native_pair_finsum_left {ι : Type*} {g : ℝ → ℂ} {φ : ι → ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (s : Finset ι) (d : ι → ℂ)
    (hi : ∀ n ∈ s,
      ComplexRSIntegrable (fun x => φ n x * star (g x)) id a b) :
    ComplexRSIntegrable (fun x => (∑ n ∈ s, d n * φ n x) * star (g x)) id a b ∧
      ComplexRSIntegral (fun x => (∑ n ∈ s, d n * φ n x) * star (g x)) id a b =
        ∑ n ∈ s, d n * ComplexRSIntegral
          (fun x => φ n x * star (g x)) id a b := by
  have hs := Chapter07.complexRSIntegral_finite_sum (s)
    (fun n x => d n * (φ n x * star (g x))) hab
    (show MonotoneOn (id : ℝ → ℝ) (Icc a b) from fun _ _ _ _ h => h)
    (fun n hn => (complexRSIntegrable_const_mul (hi n hn) _).1)
  have he : (fun x => (∑ n ∈ s, d n * φ n x) * star (g x)) =
      fun x => ∑ n ∈ s, d n * (φ n x * star (g x)) := by
    funext x
    simp only [Finset.sum_mul, mul_assoc]
  rw [he]
  refine ⟨hs.1, hs.2.trans ?_⟩
  apply Finset.sum_congr rfl
  intro n hn
  exact (complexRSIntegrable_const_mul (hi n hn) _).2

theorem native_finsum_norm_sq {ι : Type*} [DecidableEq ι]
    {φ : ι → ℝ → ℂ} {a b L : ℝ} (hab : a ≤ b) (s : Finset ι)
    (hφ : ∀ m ∈ s, ∀ n ∈ s,
      ComplexRSIntegrable (fun x => φ m x * star (φ n x)) id a b ∧
      ComplexRSIntegral (fun x => φ m x * star (φ n x)) id a b =
        if m = n then (L : ℂ) else 0) (d : ι → ℂ) :
    RIntegrable (fun x => ‖∑ n ∈ s, d n * φ n x‖ ^ 2) a b ∧
    RIntegral (fun x => ‖∑ n ∈ s, d n * φ n x‖ ^ 2) a b =
      L * ∑ n ∈ s, ‖d n‖ ^ 2 := by
  have hr (m : ι) (hm : m ∈ s) := native_pair_finsum_right hab s d
    (fun n hn => (hφ m hm n hn).1)
  have hl := native_pair_finsum_left hab s d (fun m hm => (hr m hm).1)
  have he (m : ι) (hm : m ∈ s) :
      ComplexRSIntegral (fun x => φ m x * star (∑ n ∈ s, d n * φ n x)) id a b =
        star (d m) * (L : ℂ) := by
    rw [(hr m hm).2]
    rw [Finset.sum_congr rfl (fun n hn => congrArg (star (d n) * ·) (hφ m hm n hn).2)]
    simp [hm]
  have hi : RIntegrable (fun x => ‖∑ n ∈ s, d n * φ n x‖ ^ 2) a b := by
    simpa only [complex_mul_star, Complex.ofReal_re] using hl.1.1
  refine ⟨hi, ?_⟩
  have hc := hl.2
  rw [Finset.sum_congr rfl (fun m hm => congrArg (d m * ·) (he m hm))] at hc
  simp_rw [← mul_assoc, complex_mul_star] at hc
  have hh := congrArg Complex.re hc
  simpa only [complex_mul_star, ComplexRSIntegral, Complex.ofReal_mul,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, Complex.mul_re,
    Complex.add_re, Complex.I_re, Complex.I_im, mul_zero, sub_zero,
    Complex.re_sum, ← Finset.sum_mul, ← Finset.mul_sum, mul_comm] using hh

theorem native_integral_nonneg {f : ℝ → ℝ} {a b : ℝ}
    (hf : RIntegrable f a b) (h : ∀ x ∈ Icc a b, 0 ≤ f x) : 0 ≤ RIntegral f a b := by
  have hz := rsIntegral_const (c := (0 : ℝ)) hf.1 hf.2.2.1
  have hh := rsIntegral_mono hz.1 hf h
  simpa only [hz.2, zero_mul] using hh

/-- PMA 8.11. The existence of the displayed coefficient integrals is explicit.
Source clarification: 8.10's orthogonality equations alone do not imply that
`f * conjugate φ_n` is integrable for arbitrary Riemann-integrable `f`.
We state that implicit existence requirement, without imposing continuity or
individual measurability on the orthonormal functions. Indices start at zero. -/
def pma8_11_contract : Prop :=
  ∀ (f : ℝ → ℂ) (φ : ℕ → ℝ → ℂ) (a b : ℝ),
  ComplexRSIntegrable f id a b → RiemannOrthonormal φ a b →
  (∀ n, ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b) →
  ∀ N : ℕ, let c := orthogonalFourierCoeff f φ a b
    (∀ d : ℕ → ℂ,
      RIntegrable (fun x => ‖f x - orthogonalPartialSum φ d N x‖ ^ 2) a b ∧
      RIntegral (fun x => ‖f x - orthogonalPartialSum φ c N x‖ ^ 2) a b ≤
        RIntegral (fun x => ‖f x - orthogonalPartialSum φ d N x‖ ^ 2) a b ∧
      (RIntegral (fun x => ‖f x - orthogonalPartialSum φ c N x‖ ^ 2) a b =
        RIntegral (fun x => ‖f x - orthogonalPartialSum φ d N x‖ ^ 2) a b ↔
        ∀ n < N, d n = c n)) ∧
    RIntegral (fun x => ‖orthogonalPartialSum φ c N x‖ ^ 2) a b =
      ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 ∧
    ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 ≤ RIntegral (fun x => ‖f x‖ ^ 2) a b

theorem pma8_11 : pma8_11_contract := by
  intro f φ a b hf hφ hi N
  let c := orthogonalFourierCoeff f φ a b
  have hc := orthonormal_error_identity hf hφ hi N c
  have hec : RIntegral (fun x => ‖f x - orthogonalPartialSum φ c N x‖ ^ 2) a b =
      RIntegral (fun x => ‖f x‖ ^ 2) a b - ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 := by
    simpa only [c, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, add_zero] using hc.2
  refine ⟨?_, (orthonormal_sum_norm_sq hφ N c).2, ?_⟩
  · intro d
    have hd := orthonormal_error_identity hf hφ hi N d
    have hnon : 0 ≤ ∑ n ∈ Finset.range N, ‖d n - c n‖ ^ 2 :=
      Finset.sum_nonneg (fun n _ => sq_nonneg _)
    refine ⟨hd.1, ?_, ?_⟩
    · rw [hec, hd.2]
      exact le_add_of_nonneg_right hnon
    · rw [hec, hd.2]
      constructor
      · intro he
        have hz : ∑ n ∈ Finset.range N, ‖d n - c n‖ ^ 2 = 0 := by linarith
        have hz' := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => sq_nonneg ‖d n - c n‖)).mp hz
        intro n hn
        have h := hz' n (Finset.mem_range.mpr hn)
        exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp h))
      · intro he
        have hz : ∑ n ∈ Finset.range N, ‖d n - c n‖ ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro n hn
          simp only [he n (Finset.mem_range.mp hn), c, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
        change _ = _ + ∑ n ∈ Finset.range N, ‖d n - c n‖ ^ 2
        rw [hz, add_zero]
  · have hnon := native_integral_nonneg hc.1 (fun x _ => sq_nonneg ‖f x - orthogonalPartialSum φ c N x‖)
    rw [hec] at hnon
    exact sub_nonneg.mp hnon

/-- PMA 8.12 uses the same explicit existence of coefficient integrals as 8.11.
The nonnegative series is summable, so its totalized sum is an actual sum. -/
def pma8_12_contract : Prop :=
  ∀ (f : ℝ → ℂ) (φ : ℕ → ℝ → ℂ) (a b : ℝ),
  ComplexRSIntegrable f id a b → RiemannOrthonormal φ a b →
  (∀ n, ComplexRSIntegrable (fun x => f x * star (φ n x)) id a b) →
  let c := orthogonalFourierCoeff f φ a b;
    Summable (fun n => ‖c n‖ ^ 2) ∧
    (∑' n, ‖c n‖ ^ 2) ≤ RIntegral (fun x => ‖f x‖ ^ 2) a b ∧
    Tendsto c atTop (𝓝 0)

theorem pma8_12 : pma8_12_contract := by
  intro f φ a b hf hφ hi
  let c := orthogonalFourierCoeff f φ a b
  have hbound (N : ℕ) : ∑ n ∈ Finset.range N, ‖c n‖ ^ 2 ≤
      RIntegral (fun x => ‖f x‖ ^ 2) a b := (pma8_11 f φ a b hf hφ hi N).2.2
  have hs := summable_of_sum_range_le (fun n => sq_nonneg ‖c n‖) hbound
  refine ⟨hs, hs.tsum_le_of_sum_range_le hbound, ?_⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := hs.tendsto_atTop_zero.sqrt
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh

end Rudin.PMA.Chapter08
