import Rudin.PMA.Chapter10.ChainMaps
import Rudin.PMA.Chapter10.SimplexOrientation
import Rudin.PMA.Chapter10.ChangeOfVariables
import Mathlib.Analysis.Convex.Topology

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma standardSimplex_interior_nonempty (n : ℕ) :
    (interior (standardSimplex n)).Nonempty := by
  let V : Set (Coord n) := {u | (∀ i, 0 < u i) ∧ ∑ i, u i < 1}
  have hV : IsOpen V := by
    have he : V = (⋂ i : Fin n, {u : Coord n | 0 < u i}) ∩
        {u : Coord n | ∑ i, u i < 1} := by ext u; simp [V]
    rw [he]
    exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)).inter
      (isOpen_lt (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)
  have hVS : V ⊆ standardSimplex n := fun _ h => ⟨fun i => (h.1 i).le, h.2.le⟩
  refine ⟨fun _ => 1 / ((n : ℝ) + 1), hV.subset_interior_iff.mpr hVS ?_⟩
  constructor
  · intro i; positivity
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_div_assoc, mul_one, div_lt_one (by positivity)]
    linarith

lemma closure_interior_standardSimplex (n : ℕ) :
    closure (interior (standardSimplex n)) = standardSimplex n := by
  rw [(convex_standardSimplex n).closure_interior_eq_closure_of_nonempty_interior
    (standardSimplex_interior_nonempty n), (isClosed_standardSimplex n).closure_eq]

/-- Coordinates in the target, without changing the native parameter domain. -/
def C2Simplex.coordinateMap {n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex n n E) : Coord n → Coord n := (coordEquivEuclidean n).symm ∘ σ.map

lemma C2Simplex.coordinateMap_contDiffOn {n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex n n E) :
    ContDiffOn ℝ 2 σ.coordinateMap σ.toSurface.neighborhood :=
  (coordEquivEuclidean n).symm.contDiff.comp_contDiffOn σ.regularity.choose_spec.2.2

lemma C2Simplex.coordinateMap_c1 {n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex n n E) : C1On σ.coordinateMap σ.toSurface.neighborhood :=
  (c1On_iff_contDiffOn σ.toSurface.open_neighborhood).mpr
    (σ.coordinateMap_contDiffOn.of_le (by norm_num))

/-- Positivity is required only in the interior. Boundary derivatives are
allowed to be singular. -/
structure PositiveSimplex (n : ℕ) (E : Set (Euclidean n)) where
  simplex : C2Simplex n n E
  injective : InjOn simplex.map (standardSimplex n)
  positive : ∀ u ∈ interior (standardSimplex n), 0 < coordinateJacobian simplex.coordinateMap u

def PositiveSimplex.carrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : Set (Euclidean n) := P.simplex.map '' standardSimplex n

def PositiveSimplex.coordinateCarrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : Set (Coord n) := P.simplex.coordinateMap '' standardSimplex n

lemma PositiveSimplex.jacobian_nonneg {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) {u : Coord n} (hu : u ∈ standardSimplex n) :
    0 ≤ coordinateJacobian P.simplex.coordinateMap u := by
  have hc := (continuousOn_coordinateJacobian P.simplex.coordinateMap_c1).mono
    P.simplex.toSurface.domain_subset
  change ContinuousOn (coordinateJacobian P.simplex.coordinateMap) (standardSimplex n) at hc
  have he := closure_interior_standardSimplex n
  exact le_on_closure (fun x hx => (P.positive x hx).le) continuousOn_const
    (by simpa only [he] using hc) (by simpa only [he] using hu)

lemma PositiveSimplex.coordinate_injective {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : InjOn P.simplex.coordinateMap (standardSimplex n) := by
  intro u hu v hv h
  apply P.injective hu hv
  exact (coordEquivEuclidean n).symm.injective h

lemma PositiveSimplex.coordinateCarrier_eq {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) :
    P.coordinateCarrier = (coordEquivEuclidean n).symm '' P.carrier := by
  simp only [coordinateCarrier, carrier, C2Simplex.coordinateMap, image_comp]

lemma PositiveSimplex.isCompact_carrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : IsCompact P.carrier :=
  (isCompact_standardSimplex n).image_of_continuousOn
    (P.simplex.toSurface.regularity.continuousOn.mono P.simplex.toSurface.domain_subset)

/-- The scalar density of a top-degree form in standard target coordinates. -/
def topFormDensity {n : ℕ} (ω : FormField n) (y : Coord n) : ℝ :=
  evaluateForm n (fun j => coordEquivEuclidean n (Pi.single j 1)) (ω (coordEquivEuclidean n y))

lemma C2Simplex.top_integrand {n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex n n E) {ω : FormField n} (hω : IsFormOn E n ω)
    {u : Coord n} (hu : u ∈ standardSimplex n) :
    surfaceIntegrand σ.toSurface ω u =
      coordinateJacobian σ.coordinateMap u * topFormDensity ω (σ.coordinateMap u) := by
  let e := coordEquivEuclidean n
  have hd : HasFDerivAt σ.coordinateMap
      (e.symm.toContinuousLinearMap.comp (fderiv ℝ σ.map u)) u :=
    e.symm.hasFDerivAt.comp u (σ.toSurface.differentiableAt hu).hasFDerivAt
  have hv : (fun j => fderiv ℝ σ.map u (Pi.single j 1)) =
      fun j => e (fderiv ℝ σ.coordinateMap u (Pi.single j 1)) := by
    rw [hd.fderiv]
    funext j
    exact (e.apply_symm_apply _).symm
  change evaluateForm n (fun j => fderiv ℝ σ.map u (Pi.single j 1)) (ω (σ.map u)) = _
  rw [hv]
  have heval := evaluateForm_precompose e.toContinuousLinearMap
    (fderiv ℝ σ.coordinateMap u) (hω.1 _ (σ.mapsTo hu))
  simpa only [coordinateJacobian, topFormDensity, C2Simplex.coordinateMap,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using! heval

/-- The native integral exists on every parameter fiber before the measure
change-of-variables formula is used. -/
lemma PositiveSimplex.integral_eq_image {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) {ω : FormField n} (hω : IsFormOn E n ω) :
    (ParameterDomain.simplex : ParameterDomain n).Integrable
      (surfaceIntegrand P.simplex.toSurface ω) ∧
    surfaceIntegral P.simplex.toSurface ω =
      ∫ y in P.coordinateCarrier, topFormDensity ω y := by
  have hc := P.simplex.toSurface.continuousOn_integrand hω
  refine ⟨ParameterDomain.integrable_of_continuousOn hc, ?_⟩
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral hc]
  have hd : ∀ u ∈ standardSimplex n, HasFDerivWithinAt P.simplex.coordinateMap
      (fderiv ℝ P.simplex.coordinateMap u) (standardSimplex n) u := by
    intro u hu
    exact (P.simplex.coordinateMap_c1.1 u (P.simplex.toSurface.domain_subset hu)).hasFDerivAt.hasFDerivWithinAt
  rw [show P.coordinateCarrier = P.simplex.coordinateMap '' standardSimplex n from rfl,
    integral_image_eq_integral_abs_det_fderiv_smul volume
      (isClosed_standardSimplex n).measurableSet hd P.coordinate_injective]
  apply setIntegral_congr_fun (isClosed_standardSimplex n).measurableSet
  intro u hu
  rw [P.simplex.top_integrand hω hu]
  change _ = |coordinateJacobian P.simplex.coordinateMap u| * _
  rw [abs_of_nonneg (P.jacobian_nonneg hu)]

lemma PositiveSimplex.integral_independent {n : ℕ} {E : Set (Euclidean n)}
    (P Q : PositiveSimplex n E) (hPQ : P.carrier = Q.carrier)
    {ω : FormField n} (hω : IsFormOn E n ω) :
    surfaceIntegral P.simplex.toSurface ω = surfaceIntegral Q.simplex.toSurface ω := by
  rw [(P.integral_eq_image hω).2, (Q.integral_eq_image hω).2,
    P.coordinateCarrier_eq, Q.coordinateCarrier_eq, hPQ]

def PositiveSimplex.openCarrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : Set (Euclidean n) :=
  P.simplex.map '' interior (standardSimplex n)

lemma PositiveSimplex.isOpen_openCarrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : IsOpen P.openCarrier := by
  have hsub : interior (standardSimplex n) ⊆ P.simplex.toSurface.neighborhood :=
    interior_subset.trans P.simplex.toSurface.domain_subset
  have hc : C1On P.simplex.coordinateMap (interior (standardSimplex n)) :=
    ⟨fun u hu => P.simplex.coordinateMap_c1.1 u (hsub hu),
      P.simplex.coordinateMap_c1.2.mono hsub⟩
  have ho := coordinate_open_image hc (fun u hu => ne_of_gt (P.positive u hu))
    isOpen_interior Subset.rfl
  have he : P.openCarrier = coordEquivEuclidean n ''
      (P.simplex.coordinateMap '' interior (standardSimplex n)) := by
    simp only [openCarrier, image_image, C2Simplex.coordinateMap, Function.comp_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [he]
  exact (coordEquivEuclidean n).toHomeomorph.isOpenMap _ ho

lemma PositiveSimplex.closure_openCarrier {n : ℕ} {E : Set (Euclidean n)}
    (P : PositiveSimplex n E) : closure P.openCarrier = P.carrier := by
  apply Subset.antisymm
  · exact closure_minimal (image_mono interior_subset) P.isCompact_carrier.isClosed
  · have hc : ContinuousOn P.simplex.map (closure (interior (standardSimplex n))) := by
      rw [closure_interior_standardSimplex]
      exact P.simplex.toSurface.regularity.continuousOn.mono P.simplex.toSurface.domain_subset
    have hh := hc.image_closure
    rw [closure_interior_standardSimplex] at hh
    exact hh

end Rudin.PMA.Chapter10
