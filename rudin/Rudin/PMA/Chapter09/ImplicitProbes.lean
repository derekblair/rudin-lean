import Rudin.PMA.Chapter09.ImplicitExample

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section
open Set

namespace Rudin.PMA.Chapter09.FidelityProbes

/-- The local uniqueness is in the solved block, with the parameter fixed. -/
theorem implicit_unique_first_block {n m : ℕ}
    {f : Euclidean n × Euclidean m → Euclidean n}
    {E : Set (Euclidean n × Euclidean m)} {a : Euclidean n} {b : Euclidean m}
    {g : Euclidean m → Euclidean n} {U : Set (Euclidean n × Euclidean m)}
    {W : Set (Euclidean m)} (hN : ImplicitNeighborhood f E a b g U W)
    {y : Euclidean m} (hy : y ∈ W) :
    ∃! x, (x,y) ∈ U ∧ f (x,y) = 0 := by
  rcases hN with ⟨_, _, _, _, _, _, _, hgraph, huniq⟩
  exact ⟨g y, hgraph y hy, fun x hx => huniq x y hx.1 hy hx.2⟩

/-- An arbitrary invertible first block and arbitrary parameter block produce
exactly the expected negative inverse-composition derivative. -/
theorem linear_implicit_derivative {n m : ℕ}
    (A : Euclidean n ≃L[ℝ] Euclidean n) (B : Euclidean m →L[ℝ] Euclidean n) :
    ∃ g U W,
      ImplicitNeighborhood ((A : Euclidean n →L[ℝ] Euclidean n).coprod B)
        univ 0 0 g U W ∧
      HasFDerivAt g (-(A.symm : Euclidean n →L[ℝ] Euclidean n).comp B) 0 ∧
      ∀ y ∈ W, g y = -A.symm (B y) := by
  let L : Euclidean n × Euclidean m →L[ℝ] Euclidean n :=
    (A : Euclidean n →L[ℝ] Euclidean n).coprod B
  have hX : blockX L = (A : Euclidean n →L[ℝ] Euclidean n) := by
    simp only [blockX, L, ContinuousLinearMap.coprod_comp_inl]
  have hY : blockY L = B := by
    simp only [blockY, L, ContinuousLinearMap.coprod_comp_inr]
  have hi : (blockX L).IsInvertible := ⟨A, hX.symm⟩
  have hc : C1On L univ :=
    (c1On_iff_contDiffOn isOpen_univ).mpr L.contDiff.contDiffOn
  have hz : L ((0 : Euclidean n), (0 : Euclidean m)) = 0 := by
    change L 0 = 0
    exact L.map_zero
  obtain ⟨g,U,W,hN,hd,_⟩ := pma9_28 n m univ L 0 0 isOpen_univ
    (mem_univ _) hc hz (by simpa only [L.hasFDerivAt.fderiv] using hi)
  refine ⟨g,U,W,hN, ?_, ?_⟩
  · simpa only [L.hasFDerivAt.fderiv, hX, hY,
      ContinuousLinearMap.inverse_equiv] using hd
  · intro y hy
    have hzero := hN.2.2.2.2.2.2.2.1 y hy
    have he := ((pma9_27 n m L hi y).2 (g y)).mp hzero.2
    simpa only [hX, hY, ContinuousLinearMap.inverse_equiv,
      ContinuousLinearEquiv.coe_coe] using he

/-- Zero parameter dimension is admitted: the parameter neighborhood is the
entire singleton space, and the solution derivative is the zero map. -/
theorem implicit_zero_parameter_dimension {n : ℕ}
    {E : Set (Euclidean n × Euclidean 0)}
    {f : Euclidean n × Euclidean 0 → Euclidean n} {a : Euclidean n}
    (hE : IsOpen E) (ha : (a,0) ∈ E) (hc : C1On f E) (hz : f (a,0) = 0)
    (hi : (blockX (fderiv ℝ f (a,0))).IsInvertible) :
    ∃ (g : Euclidean 0 → Euclidean n) (U : Set (Euclidean n × Euclidean 0)),
      ImplicitNeighborhood f E a 0 g U univ ∧
      (∀ y, g y = a) ∧ HasFDerivAt g (0 : Euclidean 0 →L[ℝ] Euclidean n) 0 := by
  obtain ⟨g,U,W,hN,hd,_⟩ := pma9_28 n 0 E f a 0 hE ha hc hz hi
  have hb : (0 : Euclidean 0) ∈ W := hN.2.2.2.2.1
  have hgb : g 0 = a := hN.2.2.2.2.2.2.1
  have hW : W = univ := by
    ext y
    simp only [mem_univ, iff_true]
    simpa only [Subsingleton.elim y 0] using hb
  have hder : -(blockX (fderiv ℝ f (a,0))).inverse.comp
      (blockY (fderiv ℝ f (a,0))) = (0 : Euclidean 0 →L[ℝ] Euclidean n) := by
    ext y
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  refine ⟨g,U,by simpa only [hW] using hN, ?_, ?_⟩
  · intro y
    simpa only [Subsingleton.elim y 0] using hgb
  · simpa only [hder] using hd

/-- The worked nonlinear example gives the third-parameter partials with their
signs and denominators, while retaining the actual local solution graph. -/
theorem worked_example_third_parameter :
    ∃ g U W,
      ImplicitNeighborhood implicitExample univ implicitExampleA implicitExampleB g U W ∧
      componentPartial g implicitExampleB 0 2 = -(3 : ℝ) / 20 ∧
      componentPartial g implicitExampleB 1 2 = (1 : ℝ) / 10 := by
  obtain ⟨g,U,W,hN,hd⟩ := pma9_29.2.2.2.2.2
  have hgb : DifferentiableAt ℝ g implicitExampleB :=
    hN.2.2.2.2.2.1.1 _ hN.2.2.2.2.1
  have hp (i : Fin 2) : componentPartial g implicitExampleB i 2 =
      fderiv ℝ g implicitExampleB (coordinateVector 3 2) i :=
    (pma9_17 3 2 g _ implicitExampleB
      (hasTotalDerivative_iff.mpr hgb.hasFDerivAt)).2.1 i 2
  refine ⟨g,U,W,hN, ?_, ?_⟩
  · rw [hp, hd]
    norm_num [coordinateVector, EuclideanSpace.basisFun_apply]
  · rw [hp, hd]
    norm_num [coordinateVector, EuclideanSpace.basisFun_apply]

end Rudin.PMA.Chapter09.FidelityProbes
