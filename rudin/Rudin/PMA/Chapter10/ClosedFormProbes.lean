import Rudin.PMA.Chapter10.ClosedFormConsequences

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- A C1 primitive is sufficient for the flux of its C1 derivative form
through a three-chain boundary to vanish. No second derivatives of the
given primitive are available to this client. -/
theorem C1_primitive_surface_boundary_integral {E : Set (Euclidean 3)}
    {η ω : FormField 3} (hE : IsOpen E) (hη : IsCFormOn 1 E 1 η)
    (hω : IsCFormOn 1 E 2 ω) (he : EqOn (exteriorDerivative η) ω E)
    (Γ : SimplexChain 3 3 E) : chainIntegral ω (chainBoundary Γ) = 0 := by
  have hex : IsExactOn E 2 ω := ⟨η, hη, he⟩
  have hc := pma10_34.2.2 1 3 E ω hE hω hex
  exact pma10_35.2.2.2.2.1 2 3 E ω hE hc Γ

/-- Three chains need only have functionally related boundaries. A C1
scalar potential, whose differential is only known continuous, then gives
the corresponding additive identity for the actual chain integrals. -/
theorem C1_potential_functional_boundary_additivity {n : ℕ}
    {E : Set (Euclidean n)} (hE : IsOpen E) (f : Euclidean n → ℝ)
    (hf : ContDiffOn ℝ 1 f E) (Γ Δ Θ : SimplexChain 1 n E)
    (hb : ChainEq (chainBoundary (Γ + Δ)) (chainBoundary Θ)) :
    chainIntegral (scalarDifferential f) Γ + chainIntegral (scalarDifferential f) Δ =
      chainIntegral (scalarDifferential f) Θ := by
  have hη : IsCFormOn 1 E 0 (scalarForm f) := isCFormOn_scalarForm hf
  have hω : IsFormOn E 1 (scalarDifferential f) := by
    simpa only [exteriorDerivative_scalarForm] using (pma10_18.1 n 0 E _ hE hη).1
  have he : IsExactOn E 1 (scalarDifferential f) :=
    ⟨scalarForm f, hη, fun _ _ => congrFun (exteriorDerivative_scalarForm f) _⟩
  have h := pma10_35.2.2.1 0 n E (scalarDifferential f) hE hω he (Γ + Δ) Θ hb
  simpa only [map_add] using h

private lemma xdy_C1 : IsCFormOn 1 (univ : Set (Euclidean 2)) 1 (coordinateOneForm 0 1) := by
  refine ⟨(isFormOn_coordinateOneForm univ 0 1).1, ?_⟩
  intro S
  change ContDiffOn ℝ 1 (fun x : Euclidean 2 =>
    (exteriorBasis 2).repr (x 0 • dx 1) S) univ
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).contDiff.contDiffOn.mul contDiffOn_const

/-- The off-diagonal coordinate test rejects x dy: D_x of its dy
coefficient is one, while D_y of its dx coefficient is zero. -/
theorem xdy_fails_cross_partial_closedness :
    ¬ IsClosedOn (univ : Set (Euclidean 2)) 1 (coordinateOneForm 0 1) := by
  intro hc
  have h := (pma10_35.1 2 univ (coordinateOneForm 0 1) isOpen_univ xdy_C1).mp hc
    0 (mem_univ _) 0 1
  have h1 : formCoefficient (coordinateOneForm (0 : Fin 2) 1) {1} =
      fun x : Euclidean 2 => x 0 := by
    funext x
    simp [formCoefficient, coordinateOneForm, ← exteriorBasis_singleton,
      Module.Basis.repr_self]
  have h0 : formCoefficient (coordinateOneForm (0 : Fin 2) 1) {0} =
      fun _ : Euclidean 2 => (0 : ℝ) := by
    funext x
    simp [formCoefficient, coordinateOneForm, ← exteriorBasis_singleton,
      Module.Basis.repr_self]
  rw [h1, h0, coordinatePartial_const] at h
  have hd : coordinatePartial (fun x : Euclidean 2 => x 0) 0 0 = 1 := by
    have hh := (hasCoordinatePartial_of_hasFDerivAt
      (x := (0 : Euclidean 2))
      (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).hasFDerivAt 0).deriv
    simpa [coordinatePartial, EuclideanSpace.coe_proj, coordinateVector,
      EuclideanSpace.basisFun_apply, PiLp.single_apply] using! hh
  rw [hd] at h
  norm_num at h

end Rudin.PMA.Chapter10.FidelityProbes
