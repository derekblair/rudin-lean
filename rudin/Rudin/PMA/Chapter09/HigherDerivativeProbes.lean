import Rudin.PMA.Chapter09.HigherDerivatives

/-! Independent clients for the weak mixed-partial theorem and signed increments. -/
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace Rudin.PMA.Chapter09.FidelityProbes

/-- Existing first partials do not force the source's `C²` condition. -/
theorem global_first_partials_need_not_be_C2 :
    ∃ f : Euclidean 2 → ℝ,
      (∀ x j, ∃ d, HasCoordinatePartial f x j d) ∧ ¬ ScalarC2On f univ := by
  obtain ⟨f, a, b, hp, ha, hb, hab⟩ := pma9_39.2.2
  refine ⟨f, hp, ?_⟩
  intro hC
  have he := pma9_41.2 2 f univ isOpen_univ hC 0 (mem_univ _) 1 0
  have ha' : secondCoordinatePartial f 0 1 0 = a := ha.deriv
  have hb' : secondCoordinatePartial f 0 0 1 = b := hb.deriv
  exact hab (ha'.symm.trans (he.trans hb'))

private def coordinateProduct (p : Euclidean 2) : ℝ := p 0 * p 1

private theorem coordinateProduct_first (p : Euclidean 2) :
    HasCoordinatePartial coordinateProduct p 0 (p 1) := by
  have hd := ((hasDerivAt_id (0 : ℝ)).const_add (p 0)).mul_const (p 1)
  simpa [HasCoordinatePartial, coordinateProduct, coordinateVector,
    EuclideanSpace.basisFun_apply] using hd

private theorem coordinateProduct_first_value (p : Euclidean 2) :
    coordinatePartial coordinateProduct p 0 = p 1 :=
  (coordinateProduct_first p).deriv

private theorem coordinateProduct_mixed (p : Euclidean 2) :
    HasCoordinatePartial (fun q => coordinatePartial coordinateProduct q 0) p 1 1 := by
  simp only [coordinateProduct_first_value]
  simpa [HasCoordinatePartial, coordinateVector, EuclideanSpace.basisFun_apply] using
    (hasDerivAt_id (0 : ℝ)).const_add (p 1)

/-- The rectangle theorem handles a negative horizontal and positive vertical increment. -/
theorem rectangle_negative_horizontal_increment :
    ∃ x ∈ Ioo (-2 : ℝ) 1, ∃ y ∈ Ioo (-2 : ℝ) 2,
      secondCoordinatePartial coordinateProduct (planePoint x y) 1 0 = 1 := by
  obtain ⟨x, hx, y, hy, he⟩ := pma9_40 coordinateProduct univ
    1 (-2) (-3) 4 isOpen_univ (by norm_num) (by norm_num)
    (subset_univ _) (fun p _ => ⟨_, coordinateProduct_first p⟩)
    (fun p _ => ⟨_, coordinateProduct_mixed p⟩)
  refine ⟨x, ?_, y, ?_, ?_⟩
  · norm_num [uIoo] at hx ⊢
    exact hx
  · norm_num [uIoo] at hy ⊢
    exact hy
  · norm_num [coordinateProduct] at he
    linarith

end Rudin.PMA.Chapter09.FidelityProbes
