import Rudin.PMA.Chapter10.SurfacePrecomposition

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10

private lemma snoc_one_eq_pair (x y : ℝ) :
    Fin.snoc (fun _ : Fin 1 => x) y = (![x, y] : Coord 2) := by
  ext i
  fin_cases i <;> simp [Fin.snoc]

lemma squareRIntegral_eq_doubleIntegral {f : Coord 2 → ℝ} (hf : Continuous f) :
    iteratedRIntegral (Cell.unit 2) f =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f ![x, y] := by
  change iteratedRIntegral (Cell.unit 1) (nativeSliceIntegral (Cell.unit 2) f) = _
  have hc : ContinuousOn (nativeSliceIntegral (Cell.unit 2) f) (Cell.unit 1).carrier :=
    nativeSliceIntegral_continuousOn hf.continuousOn
  rw [iteratedRIntegral_one_eq_intervalIntegral hc]
  apply intervalIntegral.integral_congr
  intro x hx
  change Chapter06.RIntegral (fun y => f (Fin.snoc (fun _ => x) y)) 0 1 = _
  rw [rIntegral_eq_intervalIntegral_of_continuousOn zero_le_one]
  · simp only [snoc_one_eq_pair]
  · exact (hf.comp (by fun_prop)).continuousOn

lemma simplexRIntegral_two_eq_doubleIntegral {f : Coord 2 → ℝ} (hf : Continuous f) :
    simplexRIntegral f = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), f ![x, y] := by
  change iteratedRIntegral (Cell.unit 1)
    (nativeSliceIntegral (Cell.unit 2) (simplexExtension f)) = _
  rw [iteratedRIntegral_one_eq_intervalIntegral (simplex_nativeSlice_continuousOn hf.continuousOn)]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx' : x ∈ Icc (0 : ℝ) 1 := by simpa [Cell.unit, uIcc_of_le zero_le_one] using hx
  have hu : (fun _ : Fin 1 => x) ∈ (Cell.unit 1).carrier :=
    ⟨fun _ => hx'.1, fun _ => hx'.2⟩
  have he := (simplex_slice_integrable_formula hf (fun _ _ => rfl) hu).2
  simpa only [simplexSliceFormula, Fin.sum_univ_one,
    max_eq_right (sub_nonneg.mpr hx'.2), snoc_one_eq_pair] using he

lemma continuous_pair_primitive {f : Coord 2 → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℝ => ∫ y in (0 : ℝ)..p.2, f ![p.1, y]) := by
  have hc : Continuous (Function.uncurry (fun x y : ℝ => f ![x, y])) := hf.comp (by fun_prop)
  exact intervalIntegral.continuous_parametric_primitive_of_continuous
    (μ := volume) (f := fun x y : ℝ => f ![x, y]) (a₀ := 0) hc

lemma doubleIntegral_square_split {f : Coord 2 → ℝ} (hf : Continuous f) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, f ![x, y]) =
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), f ![x, y]) +
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), f ![1 - x, 1 - y] := by
  let B : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, f ![x, y]
  let L : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..(1 - x), f ![x, y]
  let U : ℝ → ℝ := fun x => ∫ y in (1 - x)..1, f ![x, y]
  have hcB : Continuous B := (continuous_pair_primitive hf).comp (continuous_id.prodMk continuous_const)
  have hcL : Continuous L :=
    (continuous_pair_primitive hf).comp (continuous_id.prodMk (continuous_const.sub continuous_id))
  have hsplit (x : ℝ) : L x + U x = B x := by
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hf.comp (by fun_prop)).intervalIntegrable _ _)
      ((hf.comp (by fun_prop)).intervalIntegrable _ _)
  have hU : U = fun x => B x - L x := by funext x; linarith [hsplit x]
  have hcU : Continuous U := by rw [hU]; exact hcB.sub hcL
  have hrefl : (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..(1 - x), f ![1 - x, 1 - y]) =
      ∫ x in (0 : ℝ)..1, U x := by
    calc
      _ = ∫ x in (0 : ℝ)..1, U (1 - x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        simpa only [U, sub_sub_cancel, sub_zero] using
          (intervalIntegral.integral_comp_sub_left (fun y => f ![1 - x, y])
            (a := (0 : ℝ)) (b := 1 - x) 1)
      _ = _ := by
        simpa using intervalIntegral.integral_comp_sub_left U (a := (0 : ℝ)) (b := 1) 1
  rw [hrefl]
  change (∫ x in (0 : ℝ)..1, B x) = (∫ x in (0 : ℝ)..1, L x) + ∫ x in (0 : ℝ)..1, U x
  rw [← intervalIntegral.integral_add (hcL.intervalIntegrable _ _) (hcU.intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro x hx
  exact (hsplit x).symm

/-- Split the square into its two positively oriented affine triangles, using
the native integrals. The common diagonal is permitted in both domains. -/
lemma squareRIntegral_split {f : Coord 2 → ℝ}
    (hf : ContinuousOn f (Cell.unit 2).carrier) :
    iteratedRIntegral (Cell.unit 2) f =
      simplexRIntegral f + simplexRIntegral (fun u => f (1 - u)) := by
  obtain ⟨g, hg, he⟩ := exists_continuous_extension (Cell.unit 2).isClosed_carrier hf
  have hmaps : MapsTo (fun u : Coord 2 => 1 - u) (standardSimplex 2) (Cell.unit 2).carrier := by
    intro u hu
    have hh := standardSimplex_subset_unit 2 hu
    rw [Cell.mem_carrier] at hh ⊢
    intro i
    have hi := hh i
    change 0 ≤ u i ∧ u i ≤ 1 at hi
    change 0 ≤ 1 - u i ∧ 1 - u i ≤ 1
    constructor <;> linarith
  have hfg : iteratedRIntegral (Cell.unit 2) f = iteratedRIntegral (Cell.unit 2) g :=
    ParameterDomain.integral_congr (D := .cell (Cell.unit 2)) hf hg.continuousOn he.symm
  have hsg : simplexRIntegral f = simplexRIntegral g :=
    ParameterDomain.integral_congr (D := .simplex) (hf.mono (standardSimplex_subset_unit 2))
      hg.continuousOn (fun _ hu => (he (standardSimplex_subset_unit 2 hu)).symm)
  have hrg : simplexRIntegral (fun u => f (1 - u)) = simplexRIntegral (fun u => g (1 - u)) :=
    ParameterDomain.integral_congr (D := .simplex)
      (hf.comp (continuous_const.sub continuous_id).continuousOn hmaps)
      (hg.comp (continuous_const.sub continuous_id)).continuousOn (fun _ hu => (he (hmaps hu)).symm)
  have hc : Continuous (fun u : Coord 2 => g (1 - u)) :=
    hg.comp (continuous_const.sub continuous_id)
  rw [hfg, hsg, hrg, squareRIntegral_eq_doubleIntegral hg,
    simplexRIntegral_two_eq_doubleIntegral hg,
    simplexRIntegral_two_eq_doubleIntegral hc]
  have hv (x y : ℝ) : (1 : Coord 2) - ![x, y] = ![1 - x, 1 - y] := by
    ext i
    fin_cases i <;> rfl
  simp only [hv]
  exact doubleIntegral_square_split hg

end Rudin.PMA.Chapter10
