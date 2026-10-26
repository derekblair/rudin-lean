import Rudin.PMA.Chapter10.Partition

set_option autoImplicit false
noncomputable section
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- PMA 10.8, complex-valued corollary. The recovered `pma10_8` proves the
real-valued corollary; this supplement supplies the complex-valued case also
included in Rudin's notation `C(X)` (7.14). The partition remains real-valued. -/
theorem pma10_8_complex_corollary (n : ℕ) (ι : Type)
    (K : Set (Euclidean n)) (V : ι → Set (Euclidean n))
    (hK : IsCompact K) (hV : ∀ i, IsOpen (V i)) (hcover : K ⊆ ⋃ i, V i) :
    ∃ (s : Finset ι) (ψ : s → C(Euclidean n, ℝ)),
      (∀ i x, ψ i x ∈ Icc (0 : ℝ) 1) ∧
      (∀ i, tsupport (ψ i) ⊆ V i) ∧
      (∀ x ∈ K, ∑ i, ψ i x = 1) ∧
      (∀ f : C(Euclidean n, ℂ), tsupport f ⊆ K →
        (∀ x, f x = ∑ i, (ψ i x : ℂ) * f x) ∧
        ∀ i, Continuous (fun x => (ψ i x : ℂ) * f x) ∧
          tsupport (fun x => (ψ i x : ℂ) * f x) ⊆ V i) := by
  classical
  obtain ⟨s, ψ, hbounds, hsupp, hsum, _⟩ := pma10_8 n ι K V hK hV hcover
  refine ⟨s, ψ, hbounds, hsupp, hsum, ?_⟩
  intro f hf
  constructor
  · intro x
    by_cases hx : x ∈ K
    · have hsumC : ∑ i, (ψ i x : ℂ) = 1 := by exact_mod_cast hsum x hx
      rw [← Finset.sum_mul, hsumC, one_mul]
    · have hz : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
      simp only [hz, mul_zero, Finset.sum_const_zero]
  · intro i
    refine ⟨(Complex.continuous_ofReal.comp (ψ i).continuous).mul f.continuous, ?_⟩
    apply Subset.trans tsupport_mul_subset_left
    apply Subset.trans (closure_mono ?_) (hsupp i)
    intro x hx
    simpa only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hx

end Rudin.PMA.Chapter10
