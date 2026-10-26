import Rudin.PMA.Chapter10.PullbackDefinitions
import Rudin.PMA.Chapter10.PullbackDifferentiation
import Rudin.PMA.Chapter10.SurfacePullbacks

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes
open Chapter09

/-- A constant map kills coordinate one-forms but preserves the value of a
zero-form. Neither assertion requires an injective map. -/
theorem constant_pullback_one_form_and_scalar (n m : ℕ) (c : Euclidean m)
    (i j : Fin m) (f : Euclidean m → ℝ) :
    pullbackForm (fun _ : Euclidean n => c) (coordinateOneForm i j) = 0 ∧
    pullbackForm (fun _ : Euclidean n => c) (scalarForm f) = scalarForm (fun _ => f c) := by
  constructor
  · funext x
    have hz : covectorPullback (0 : Operator n m) = 0 := by
      ext a l
      simp [covectorPullback]
    simp [pullbackForm, coordinateOneForm, dx, hz, ExteriorAlgebra.map_apply_ι]
  · simpa only [Function.comp_def] using pma10_21.2.2 n m (fun _ => c) f

/-- Pullback preserves closedness with only C1 coefficient regularity;
all map assumptions remain restricted to the given open sets. -/
theorem C1_closed_form_pullback {n m k : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} {T : Euclidean n → Euclidean m} {ω : FormField m}
    (hE : IsOpen E) (hV : IsOpen V) (hT : ContDiffOn ℝ 2 T E)
    (hTV : MapsTo T E V) (hω : IsCFormOn 1 V k ω)
    (hclosed : EqOn (exteriorDerivative ω) 0 V) :
    IsCFormOn 1 E k (pullbackForm T ω) ∧ EqOn (exteriorDerivative (pullbackForm T ω)) 0 E := by
  obtain ⟨hr, hd⟩ := pma10_22.2 n m k E V T ω hE hV hT hTV hω
  refine ⟨hr, ?_⟩
  intro x hx
  rw [hd hx]
  simp [pullbackForm, hclosed (hTV hx)]

/-- Identity-parameter pullback in dimension zero still evaluates the
scalar at the original surface point. -/
theorem point_surface_pullback_value {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (Φ : Surface 0 n E) (f : Euclidean n → ℝ)
    (hf : ContinuousOn f E) :
    Φ.domain.Integrable (surfaceIntegrand (identityParameterSurface Φ.domain)
      (pullbackForm Φ.euclideanMap (scalarForm f))) ∧
    surfaceIntegral (identityParameterSurface Φ.domain)
      (pullbackForm Φ.euclideanMap (scalarForm f)) = f (Φ.map 0) := by
  have h := pma10_24 n 0 E Φ (scalarForm f) hE (isFormOn_scalarForm hf)
  exact ⟨h.2.1, h.2.2.symm.trans (surfaceIntegral_scalar_zero_dimension Φ f)⟩

private def positiveTarget : Set (Euclidean 1) := {x | 0 < x 0}

private theorem positiveTarget_isOpen : IsOpen positiveTarget :=
  isOpen_lt continuous_const (EuclideanSpace.proj 0 : Euclidean 1 →L[ℝ] ℝ).continuous

private def positiveCurve : Surface 1 1 positiveTarget where
  domain := .cell (Cell.unit 1)
  map u := (1 + u 0) • coordinateVector 1 0
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := ((contDiff_const.add (contDiff_apply ℝ ℝ (0 : Fin 1))).smul
    contDiff_const).contDiffOn
  mapsTo := by
    intro u hu
    have h : (0 : ℝ) < 1 + u 0 := by
      have hu0 := (Cell.mem_carrier.mp hu) 0
      norm_num [Cell.unit] at hu0
      linarith
    simpa [positiveTarget, coordinateVector, EuclideanSpace.basisFun_apply] using h

private def constantImageCurve : Surface 1 1 univ :=
  positiveCurve.mapBy (fun _ => (3 : ℝ) • coordinateVector 1 0)
    positiveTarget_isOpen contDiffOn_const (mapsTo_univ _ _)

/-- The ambient extension leaves the open target, while its actual compact
curve lies inside. Composition remains valid and has a native zero integral. -/
theorem restricted_surface_composition :
    ¬ MapsTo positiveCurve.map univ positiveTarget ∧
    constantImageCurve.domain.Integrable
      (surfaceIntegrand constantImageCurve (coordinateOneForm 0 0)) ∧
    surfaceIntegral constantImageCurve (coordinateOneForm 0 0) = 0 := by
  have h := pma10_25 1 1 1 positiveTarget univ
    (fun _ => (3 : ℝ) • coordinateVector 1 0) positiveCurve (coordinateOneForm 0 0)
    positiveTarget_isOpen isOpen_univ contDiffOn_const (mapsTo_univ _ _)
    (isFormOn_coordinateOneForm univ 0 0)
  refine ⟨?_, h.2.2.1, ?_⟩
  · intro hglobal
    have hh := hglobal (mem_univ (fun _ : Fin 1 => (-2 : ℝ)))
    norm_num [positiveCurve, positiveTarget, coordinateVector, EuclideanSpace.basisFun_apply] at hh
  · have hz := (constant_pullback_one_form_and_scalar 1 1
      ((3 : ℝ) • coordinateVector 1 0) 0 0 (fun _ => 0)).1
    change surfaceIntegral (positiveCurve.mapBy _ _ _ _) _ = 0
    rw [h.2.2.2.2, hz, surfaceIntegral_zero]

private def doubleMap (x : Euclidean 1) : Euclidean 1 := (2 : ℝ) • x
private def shiftMap (x : Euclidean 1) : Euclidean 1 := x + coordinateVector 1 0

/-- Two noncommuting affine maps make the contravariant order observable
even on a zero-form, where the two values at zero are 1 and 2. -/
theorem noncommuting_pullback_order :
    pullbackForm doubleMap (pullbackForm shiftMap (scalarForm (fun x : Euclidean 1 => x 0))) 0 ≠
      pullbackForm shiftMap (pullbackForm doubleMap (scalarForm (fun x : Euclidean 1 => x 0))) 0 := by
  have hd : ContDiffOn ℝ 1 doubleMap univ := by
    change ContDiffOn ℝ 1 (fun x : Euclidean 1 => (2 : ℝ) • x) univ
    exact ((contDiff_const : ContDiff ℝ 1 (fun _ : Euclidean 1 => (2 : ℝ))).smul
      (contDiff_id : ContDiff ℝ 1 (fun x : Euclidean 1 => x))).contDiffOn
  have hs : ContDiffOn ℝ 1 shiftMap univ :=
    (contDiff_id.add contDiff_const).contDiffOn
  have hf : IsFormOn univ 0 (scalarForm (fun x : Euclidean 1 => x 0)) :=
    isFormOn_scalarForm (EuclideanSpace.proj 0 : Euclidean 1 →L[ℝ] ℝ).continuous.continuousOn
  have hds := pma10_23 1 1 1 0 univ univ univ doubleMap shiftMap _
    isOpen_univ isOpen_univ isOpen_univ hd hs (mapsTo_univ _ _) (mapsTo_univ _ _) hf
  have hsd := pma10_23 1 1 1 0 univ univ univ shiftMap doubleMap _
    isOpen_univ isOpen_univ isOpen_univ hs hd (mapsTo_univ _ _) (mapsTo_univ _ _) hf
  intro he
  have hc := (hds (mem_univ 0)).trans (he.trans (hsd (mem_univ 0)).symm)
  rw [pullbackForm_scalar, pullbackForm_scalar] at hc
  have hv := congrArg (evaluateForm 0 (fun i : Fin 0 => Fin.elim0 i)) hc
  simp only [scalarForm, evaluateForm_scalar] at hv
  norm_num [Function.comp_def, doubleMap, shiftMap,
    coordinateVector, EuclideanSpace.basisFun_apply] at hv

end Rudin.PMA.Chapter10.FidelityProbes
