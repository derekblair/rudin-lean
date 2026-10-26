import Rudin.PMA.Chapter10.IntegrationMeasure

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes

private def collapsedRectangle : Cell 2 where
  lower := ![2, -1]
  upper := ![2, 3]
  lower_le_upper := by intro i; fin_cases i <;> norm_num

/-- A collapsed first side gives zero even though the second side has positive
length, and all the native slice integrals still exist. -/
theorem collapsed_first_side_integral (f : Coord 2 → ℝ) (hf : Continuous f) :
    IteratedRIntegrable collapsedRectangle f ∧
      iteratedRIntegral collapsedRectangle f = 0 := by
  refine ⟨pma10_1.1 2 collapsedRectangle f hf.continuousOn, ?_⟩
  change Chapter06.RIntegral _ 2 2 = 0
  exact (Chapter06.rsIntegral_same_endpoint _ id 2).2

/-- The empty product has mass one: dimension zero evaluates the function,
rather than inheriting the zero integral of a collapsed positive-dimensional cell. -/
theorem zero_dimensional_integral_is_evaluation (C : Cell 0) (f : Coord 0 → ℝ) :
    iteratedRIntegral C f = f 0 ∧ (∫ x in C.carrier, f x) = f 0 := by
  have he : f = fun _ => f 0 := funext fun x => congrArg f (Subsingleton.elim x 0)
  have hf : Continuous f := by rw [he]; exact continuous_const
  have h := pma10_1.2.2.2 0 C f hf.continuousOn
  exact ⟨rfl, by simpa only [iteratedRIntegral] using h.2.symm⟩

private def asymmetricRectangle : Cell 2 where
  lower := ![0, 1]
  upper := ![2, 4]
  lower_le_upper := by intro i; fin_cases i <;> norm_num

/-- Swapping unequal coordinate intervals must swap the arguments as well;
the nonsymmetric affine integrand exposes a mistaken permutation direction. -/
theorem nonsymmetric_rectangle_order_swap :
    Chapter06.RIntegral (fun x => Chapter06.RIntegral (fun y => x + 2 * y) 1 4) 0 2 =
      Chapter06.RIntegral (fun y => Chapter06.RIntegral (fun x => x + 2 * y) 0 2) 1 4 := by
  have hf : Continuous (fun x : Coord 2 => x 0 + 2 * x 1) := by fun_prop
  have he := (pma10_2 2 asymmetricRectangle (fun x => x 0 + 2 * x 1)
    hf.continuousOn (Equiv.swap 0 1)).2
  simpa [iteratedRIntegral, nativeSliceIntegral, asymmetricRectangle,
    Cell.init, Cell.permute, unpermute] using he.symm

/-- Purely imaginary functions retain their full support and imaginary
integral; a real-part-only implementation would fail this client. -/
theorem imaginary_compact_integral (n : ℕ) (f : Coord n → ℝ)
    (hf : Continuous f) (hs : HasCompactSupport f) :
    tsupport (fun x => (f x : ℂ) * Complex.I) = tsupport f ∧
      complexWholeRIntegral (fun x => (f x : ℂ) * Complex.I) =
        (wholeRIntegral f : ℂ) * Complex.I := by
  have he : tsupport (fun x => (f x : ℂ) * Complex.I) = tsupport f := by
    rw [pma10_3.2.1 n _, pma10_3.1 n f]
    congr 1
    ext x
    simp
  have hc : Continuous (fun x => (f x : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp hf).mul continuous_const
  have hsc : HasCompactSupport (fun x => (f x : ℂ) * Complex.I) := by
    change IsCompact (tsupport (fun x => (f x : ℂ) * Complex.I))
    rw [he]
    exact hs
  refine ⟨he, ?_⟩
  rw [complexWholeRIntegral_eq_integral hc hsc, integral_mul_const,
    integral_complex_ofReal, wholeRIntegral_eq_integral hf hs]

end Rudin.PMA.Chapter10.FidelityProbes
