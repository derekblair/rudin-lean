import Rudin.PMA.Chapter10.CellNormalization

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

private lemma snoc_one_pair (x y : ℝ) :
    Fin.snoc (fun _ : Fin 1 => x) y = (![x, y] : Coord 2) := by
  ext i
  fin_cases i <;> simp [Fin.snoc]

lemma cellRIntegral_two_eq_doubleIntegral (C : Cell 2) {f : Coord 2 → ℝ} (hf : Continuous f) :
    iteratedRIntegral C f =
      ∫ x in C.lower 0..C.upper 0, ∫ y in C.lower 1..C.upper 1, f ![x, y] := by
  change iteratedRIntegral C.init (nativeSliceIntegral C f) = _
  have hc : ContinuousOn (nativeSliceIntegral C f) C.init.carrier :=
    nativeSliceIntegral_continuousOn hf.continuousOn
  rw [iteratedRIntegral_one_eq_intervalIntegral hc]
  apply intervalIntegral.integral_congr
  intro x hx
  change Chapter06.RIntegral (fun y => f (Fin.snoc (fun _ => x) y)) (C.lower 1) (C.upper 1) = _
  rw [rIntegral_eq_intervalIntegral_of_continuousOn (C.lower_le_upper 1)]
  · simp only [snoc_one_pair]
  · exact (hf.comp (by fun_prop)).continuousOn

lemma doubleIntegral_cell_normalize (C : Cell 2) (f : Coord 2 → ℝ) :
    ((C.upper 0 - C.lower 0) * (C.upper 1 - C.lower 1)) *
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        f ![C.lower 0 + (C.upper 0 - C.lower 0) * x,
            C.lower 1 + (C.upper 1 - C.lower 1) * y]) =
      ∫ x in C.lower 0..C.upper 0, ∫ y in C.lower 1..C.upper 1, f ![x, y] := by
  have h0 : C.lower 0 + (C.upper 0 - C.lower 0) = C.upper 0 := by ring
  have h1 : C.lower 1 + (C.upper 1 - C.lower 1) = C.upper 1 := by ring
  calc
    _ = (C.upper 0 - C.lower 0) *
        (∫ x in (0 : ℝ)..1, (C.upper 1 - C.lower 1) *
          ∫ y in (0 : ℝ)..1,
            f ![C.lower 0 + (C.upper 0 - C.lower 0) * x,
                C.lower 1 + (C.upper 1 - C.lower 1) * y]) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = (C.upper 0 - C.lower 0) *
        (∫ x in (0 : ℝ)..1, ∫ y in C.lower 1..C.upper 1,
          f ![C.lower 0 + (C.upper 0 - C.lower 0) * x, y]) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x hx
      simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, h1] using
        (intervalIntegral.smul_integral_comp_add_mul
          (fun y => f ![C.lower 0 + (C.upper 0 - C.lower 0) * x, y])
          (a := (0 : ℝ)) (b := 1) (C.upper 1 - C.lower 1) (C.lower 1))
    _ = _ := by
      simpa only [smul_eq_mul, mul_zero, mul_one, add_zero, h0] using
        (intervalIntegral.smul_integral_comp_add_mul
          (fun x => ∫ y in C.lower 1..C.upper 1, f ![x, y])
          (a := (0 : ℝ)) (b := 1) (C.upper 0 - C.lower 0) (C.lower 0))

lemma cellRIntegral_normalize_two (C : Cell 2) {f : Coord 2 → ℝ}
    (hf : ContinuousOn f C.carrier) :
    (∏ i, (C.upper i - C.lower i)) * iteratedRIntegral (Cell.unit 2) (fun u => f (cellNormalize C u)) =
      iteratedRIntegral C f := by
  obtain ⟨g, hg, he⟩ := exists_continuous_extension C.isClosed_carrier hf
  have hn : ContinuousOn (fun u => f (cellNormalize C u)) (Cell.unit 2).carrier :=
    hf.comp (cellNormalize_contDiff C 1).continuous.continuousOn (cellNormalize_mapsTo C)
  have hgn : Continuous (fun u => g (cellNormalize C u)) :=
    hg.comp (cellNormalize_contDiff C 1).continuous
  have hfg : iteratedRIntegral C f = iteratedRIntegral C g :=
    ParameterDomain.integral_congr (D := .cell C) hf hg.continuousOn he.symm
  have hfn : iteratedRIntegral (Cell.unit 2) (fun u => f (cellNormalize C u)) =
      iteratedRIntegral (Cell.unit 2) (fun u => g (cellNormalize C u)) :=
    ParameterDomain.integral_congr (D := .cell (Cell.unit 2)) hn hgn.continuousOn
      (fun _ hu => (he (cellNormalize_mapsTo C hu)).symm)
  rw [hfg, hfn, squareRIntegral_eq_doubleIntegral hgn, cellRIntegral_two_eq_doubleIntegral C hg,
    Fin.prod_univ_two]
  have hv (x y : ℝ) : cellNormalize C ![x, y] =
      ![C.lower 0 + (C.upper 0 - C.lower 0) * x,
        C.lower 1 + (C.upper 1 - C.lower 1) * y] := by
    ext i
    fin_cases i <;> rfl
  simp only [hv]
  exact doubleIntegral_cell_normalize C g

lemma surfaceIntegral_normalizeRectangle {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C)
    {ω : FormField n} (hω : IsFormOn E 2 ω) :
    surfaceIntegral (Φ.normalizeCell C hD) ω = surfaceIntegral Φ ω := by
  have hc := Φ.continuousOn_integrand hω
  have hn := (Φ.normalizeCell C hD).continuousOn_integrand hω
  have hmaps : MapsTo (cellNormalize C) (Cell.unit 2).carrier Φ.domain.carrier := by
    rw [hD]
    exact cellNormalize_mapsTo C
  have hcomp : ContinuousOn (fun u => surfaceIntegrand Φ ω (cellNormalize C u)) (Cell.unit 2).carrier :=
    hc.comp (cellNormalize_contDiff C 1).continuous.continuousOn hmaps
  have he : EqOn (surfaceIntegrand (Φ.normalizeCell C hD) ω)
      (fun u => (∏ i, (C.upper i - C.lower i)) * surfaceIntegrand Φ ω (cellNormalize C u))
      (Cell.unit 2).carrier := by
    intro u hu
    simpa only [Surface.normalizeCell, cellNormalize_det] using
      surfaceIntegrand_precompose Φ (.cell (Cell.unit 2)) (cellNormalize C)
        (cellNormalize_contDiff C 1) hmaps hω hu
  change iteratedRIntegral (Cell.unit 2) _ = Φ.domain.integral _
  rw [iteratedRIntegral_eq_setIntegral hn,
    setIntegral_congr_fun (Cell.unit 2).isClosed_carrier.measurableSet he,
    integral_const_mul, ← iteratedRIntegral_eq_setIntegral hcomp, hD]
  rw [hD] at hc
  exact cellRIntegral_normalize_two C hc

lemma cellNormalize_edgeMap (C : Cell 2) (i : Fin 4) (u : Coord 1) :
    cellNormalize C (rectangleEdgeMap (Cell.unit 2) i u) =
      rectangleEdgeMap C i (cellNormalize (rectangleEdgeCell C i) u) := by
  fin_cases i <;> ext j <;> fin_cases j <;>
    simp [cellNormalize, rectangleEdgeMap, rectangleEdgeCell, intervalCell, Cell.unit] <;> ring

lemma rectangleEdge_normalize_integral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C)
    (i : Fin 4) {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral (rectangleEdgeSurface (Φ.normalizeCell C hD) (Cell.unit 2) rfl i) ω =
      surfaceIntegral (rectangleEdgeSurface Φ C hD i) ω := by
  let γ := rectangleEdgeSurface Φ C hD i
  calc
    _ = surfaceIntegral (γ.normalizeCell (rectangleEdgeCell C i) rfl) ω := by
      refine surfaceIntegral_congr_map
        (Φ := rectangleEdgeSurface (Φ.normalizeCell C hD) (Cell.unit 2) rfl i)
        (Ψ := γ.normalizeCell (rectangleEdgeCell C i) rfl) ?_ ?_ ω
      · change ParameterDomain.cell (rectangleEdgeCell (Cell.unit 2) i) = .cell (Cell.unit 1)
        fin_cases i <;> rfl
      · funext u
        change Φ.map (cellNormalize C (rectangleEdgeMap (Cell.unit 2) i u)) =
          Φ.map (rectangleEdgeMap C i (cellNormalize (rectangleEdgeCell C i) u))
        rw [cellNormalize_edgeMap]
    _ = _ := surfaceIntegral_normalizeInterval γ _ rfl hω

lemma rectangleBoundary_normalize_integral {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 2 n E) (C : Cell 2) (hD : Φ.domain = .cell C)
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    rectangleBoundaryIntegral (Φ.normalizeCell C hD) (Cell.unit 2) rfl ω =
      rectangleBoundaryIntegral Φ C hD ω := by
  unfold rectangleBoundaryIntegral
  apply Finset.sum_congr rfl
  intro i hi
  exact rectangleEdge_normalize_integral Φ C hD i hω

end Rudin.PMA.Chapter10
