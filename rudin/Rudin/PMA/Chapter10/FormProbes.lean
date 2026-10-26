import Rudin.PMA.Chapter10.FormDefinitions

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

private def constantUnitSurface (k : ℕ) {n : ℕ} (c : Euclidean n) :
    Surface k n univ where
  domain := .cell (Cell.unit k)
  map := fun _ => c
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := contDiffOn_const
  mapsTo := fun _ _ => mem_univ _

/-- The integral of a zero-form over a point is its value, even though the
parameter dimension is zero and the parametrization is constant. -/
theorem point_zero_form_nonzero_value (c : Euclidean 3) :
    surfaceIntegral (constantUnitSurface 0 c) (scalarForm (fun _ => 7)) = 7 := by
  exact pma10_11.2.2.2.2.2 3 univ (constantUnitSurface 0 c) (fun _ => 7)

/-- A noninjective constant curve is an admissible surface. Every continuous
coefficient one-form has an existing native integral there, with value zero. -/
theorem constant_curve_native_integral (c : Euclidean 3)
    (a : (Fin 1 → Fin 3) → Euclidean 3 → ℝ) (ha : ∀ I, Continuous (a I)) :
    ¬ InjOn (constantUnitSurface 1 c).map (constantUnitSurface 1 c).domain.carrier ∧
      (constantUnitSurface 1 c).domain.Integrable
        (surfaceIntegrand (constantUnitSurface 1 c) (formFromCoefficients a)) ∧
      surfaceIntegral (constantUnitSurface 1 c) (formFromCoefficients a) = 0 := by
  have hω := (pma10_11.2.1 1 3 univ a (fun I => (ha I).continuousOn)).1
  refine ⟨?_, (pma10_11.1 1 3 univ (constantUnitSurface 1 c) _ hω).2, ?_⟩
  · intro hi
    have h0 : (0 : Coord 1) ∈ (constantUnitSurface 1 c).domain.carrier := by
      simp [constantUnitSurface, ParameterDomain.carrier, Cell.carrier, Cell.unit]
    have h1 : (1 : Coord 1) ∈ (constantUnitSurface 1 c).domain.carrier := by
      simp [constantUnitSurface, ParameterDomain.carrier, Cell.carrier, Cell.unit]
    have h := congrArg (fun x : Coord 1 => x 0) (hi h0 h1 rfl)
    norm_num at h
  · have hz : surfaceIntegrand (constantUnitSurface 1 c) (formFromCoefficients a) =
        fun _ => 0 := by
      funext u
      rw [surfaceIntegrand_fromCoefficients]
      have hdet : Matrix.det (fun _ _ : Fin 1 => (0 : ℝ)) = 0 := by
        change (0 : Matrix (Fin 1) (Fin 1) ℝ).det = 0
        exact Matrix.det_zero
      simp [constantUnitSurface, hdet]
    rw [surfaceIntegral, hz]
    change Chapter06.RIntegral (fun _ : ℝ => 0) 0 1 = 0
    simpa only [Chapter06.RIntegral, id_eq, zero_mul] using
      (Chapter06.rsIntegral_const (c := 0) (show (0 : ℝ) ≤ 1 by norm_num)
        (monotone_id.monotoneOn (Icc 0 1))).2

/-- Repeating an index in a three-form kills it even when the repeated
positions are separated by another coordinate. -/
theorem separated_repeated_coordinate_wedge :
    coordinateWedge (![0, 2, 0] : Fin 3 → Fin 4) = 0 :=
  coordinateWedge_repeat _ 0 2 (by decide) (by norm_num)

end Rudin.PMA.Chapter10.FidelityProbes
