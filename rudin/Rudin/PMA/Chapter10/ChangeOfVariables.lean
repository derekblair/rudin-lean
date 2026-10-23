import Rudin.PMA.Chapter10.IntegrationMeasure
import Rudin.PMA.Chapter10.Primitive
import Rudin.PMA.Chapter10.Partition

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

open Chapter09

/-- The determinant of the derivative in the native coordinate model. The
standard-matrix and Euclidean transport identities below identify this with
the Chapter 9 Jacobian. -/
def coordinateJacobian {n : ℕ} (T : Coord n → Coord n) (x : Coord n) : ℝ :=
  LinearMap.det (fderiv ℝ T x).toLinearMap

/-- The same map in Chapter 9's Euclidean model. -/
def euclideanTransform {n : ℕ} (T : Coord n → Coord n) : Euclidean n → Euclidean n :=
  fun x => coordEquivEuclidean n (T ((coordEquivEuclidean n).symm x))

/-- The change-of-variables integrand, extended by zero off the open domain.
The values of `T` and its derivative outside `E` have no effect on this function. -/
def zeroExtendedPullback {n : ℕ} (E : Set (Coord n)) (T : Coord n → Coord n)
    (f : Coord n → ℝ) : Coord n → ℝ :=
  E.indicator (fun x => f (T x) * |coordinateJacobian T x|)

/-- Rudin 10.9: native iterated integrals, including existence of every slice
integral, and the continuity and support properties needed to define them.
The coordinate model is linked explicitly to the Euclidean Jacobian. -/
def pma10_9_contract : Prop :=
  (∀ (n : ℕ) (T : Coord n → Coord n) (x : Coord n),
    coordinateJacobian T x = Matrix.det (LinearMap.toMatrix' (fderiv ℝ T x).toLinearMap)) ∧
  (∀ (n : ℕ) (T : Coord n → Coord n) (x : Coord n), DifferentiableAt ℝ T x →
    jacobian (euclideanTransform T) (coordEquivEuclidean n x) = coordinateJacobian T x) ∧
  (∀ (n : ℕ) (E : Set (Coord n)) (T : Coord n → Coord n) (f : Coord n → ℝ),
    IsOpen E → C1On T E → InjOn T E →
    (∀ x ∈ E, coordinateJacobian T x ≠ 0) →
    Continuous f → HasCompactSupport f → tsupport f ⊆ T '' E →
    ∃ e : OpenPartialHomeomorph (Coord n) (Coord n),
      (e : Coord n → Coord n) = T ∧ e.source = E ∧ e.target = T '' E ∧
      IsOpen (T '' E) ∧ ContinuousOn e.symm (T '' E) ∧
      Continuous (zeroExtendedPullback E T f) ∧
      HasCompactSupport (zeroExtendedPullback E T f) ∧
      tsupport (zeroExtendedPullback E T f) ⊆ E ∧
      IteratedRIntegrable (supportCell f) f ∧
      IteratedRIntegrable (supportCell (zeroExtendedPullback E T f))
        (zeroExtendedPullback E T f) ∧
      wholeRIntegral f = wholeRIntegral (zeroExtendedPullback E T f))

theorem coordinateJacobian_eq_matrix {n : ℕ} (T : Coord n → Coord n) (x : Coord n) :
    coordinateJacobian T x = Matrix.det (LinearMap.toMatrix' (fderiv ℝ T x).toLinearMap) :=
  (LinearMap.det_toMatrix' _).symm

set_option synthInstance.maxHeartbeats 100000 in
theorem jacobian_euclideanTransform {n : ℕ} {T : Coord n → Coord n} {x : Coord n}
    (hT : DifferentiableAt ℝ T x) :
    jacobian (euclideanTransform T) (coordEquivEuclidean n x) = coordinateJacobian T x := by
  let e := coordEquivEuclidean n
  set_option backward.isDefEq.respectTransparency false in
  have hd : HasFDerivAt (euclideanTransform T)
      ((e : Coord n →L[ℝ] Euclidean n).comp
        ((fderiv ℝ T x).comp (e.symm : Euclidean n →L[ℝ] Coord n))) (e x) := by
    change HasFDerivAt (fun y => e (T (e.symm y))) _ (e x)
    convert! e.hasFDerivAt.comp (e x)
      (hT.hasFDerivAt.comp (e x) e.symm.hasFDerivAt) using 1
  rw [(pma9_38.1 n (euclideanTransform T) (e x) hd.differentiableAt).1, hd.fderiv]
  exact LinearMap.det_conj (fderiv ℝ T x).toLinearMap e.toLinearEquiv

theorem continuousOn_coordinateJacobian {n : ℕ} {T : Coord n → Coord n}
    {E : Set (Coord n)} (hT : C1On T E) : ContinuousOn (coordinateJacobian T) E :=
  ContinuousLinearMap.continuous_det.comp_continuousOn hT.2

theorem coordinateDerivative_isInvertible {n : ℕ} {T : Coord n → Coord n}
    {x : Coord n} (h : coordinateJacobian T x ≠ 0) : (fderiv ℝ T x).IsInvertible :=
  ⟨(fderiv ℝ T x).toContinuousLinearEquivOfDetNeZero h,
    (fderiv ℝ T x).coe_toContinuousLinearEquivOfDetNeZero h⟩

/-- The inverse-function theorem shows that the restriction of `T` is open;
this is proved locally, without any assumptions on its extension off `E`. -/
theorem coordinate_open_image {n : ℕ} {T : Coord n → Coord n} {E W : Set (Coord n)}
    (hT : C1On T E) (hJ : ∀ x ∈ E, coordinateJacobian T x ≠ 0)
    (hW : IsOpen W) (hWE : W ⊆ E) : IsOpen (T '' W) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hTW : C1On T W := ⟨fun y hy => hT.1 y (hWE hy), hT.2.mono hWE⟩
  obtain ⟨e, he, _, _⟩ := inverse_neighborhood_c1 hW hx hTW
    (coordinateDerivative_isInvertible (hJ x (hWE hx)))
  have htarget : e.target ⊆ T '' W := by
    intro y hy
    refine ⟨e.symm y, he.2.2 (e.map_target hy), ?_⟩
    rw [← he.1]
    exact e.right_inv hy
  have hy : T x ∈ e.target := by simpa only [he.1] using e.map_source he.2.1
  exact mem_of_superset (e.open_target.mem_nhds hy) htarget

theorem coordinate_partialHomeomorph {n : ℕ} {T : Coord n → Coord n}
    {E : Set (Coord n)} (hE : IsOpen E) (hT : C1On T E) (hi : InjOn T E)
    (hJ : ∀ x ∈ E, coordinateJacobian T x ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Coord n) (Coord n),
      (e : Coord n → Coord n) = T ∧ e.source = E ∧ e.target = T '' E := by
  have hc : ContinuousOn T E := fun x hx => (hT.1 x hx).continuousAt.continuousWithinAt
  have ho : IsOpenMap (E.domRestrict T) := by
    intro U hU
    have hsub : Subtype.val '' U ⊆ E := by rintro _ ⟨x, _, rfl⟩; exact x.property
    have hopen := coordinate_open_image hT hJ (hE.isOpenMap_subtype_val U hU) hsub
    simpa only [Set.image_image, Set.domRestrict_eq, Function.comp_def] using hopen
  let e := OpenPartialHomeomorph.ofContinuousOpenRestrict (hi.toPartialEquiv T E) hc ho hE
  exact ⟨e, rfl, rfl, rfl⟩

/-- Compactness is transported by the actual inverse on the image. In
particular, a boundary of the open source cannot acquire new support. -/
theorem zeroExtendedPullback_support {n : ℕ} {T : Coord n → Coord n}
    {E : Set (Coord n)} {f : Coord n → ℝ}
    (e : OpenPartialHomeomorph (Coord n) (Coord n)) (he : (e : Coord n → Coord n) = T)
    (hsource : e.source = E) (htarget : e.target = T '' E)
    (hs : HasCompactSupport f) (hsub : tsupport f ⊆ T '' E) :
    HasCompactSupport (zeroExtendedPullback E T f) ∧
      tsupport (zeroExtendedPullback E T f) ⊆ E := by
  have hsub' : tsupport f ⊆ e.target := by simpa only [htarget] using hsub
  have hK : IsCompact (e.symm '' tsupport f) :=
    hs.image_of_continuousOn (e.continuousOn_symm.mono hsub')
  have hKE : e.symm '' tsupport f ⊆ E := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← hsource]
    exact e.map_target (hsub' hy)
  have hsupport : Function.support (zeroExtendedPullback E T f) ⊆ e.symm '' tsupport f := by
    intro x hx
    have hxE : x ∈ E := by
      by_contra h
      exact hx (by simp [zeroExtendedPullback, h])
    have hfx : f (T x) ≠ 0 := by
      intro hz
      exact hx (by simp [zeroExtendedPullback, hxE, hz])
    refine ⟨T x, subset_tsupport f hfx, ?_⟩
    rw [← he]
    exact e.left_inv (by simpa only [hsource] using hxE)
  have hclosure : tsupport (zeroExtendedPullback E T f) ⊆ e.symm '' tsupport f :=
    closure_minimal hsupport hK.isClosed
  exact ⟨hK.of_isClosed_subset isClosed_closure hclosure, hclosure.trans hKE⟩

theorem zeroExtendedPullback_continuous {n : ℕ} {T : Coord n → Coord n}
    {E : Set (Coord n)} {f : Coord n → ℝ} (hE : IsOpen E) (hT : C1On T E)
    (hf : Continuous f) (hsub : tsupport (zeroExtendedPullback E T f) ⊆ E) :
    Continuous (zeroExtendedPullback E T f) := by
  apply continuous_of_tsupport
  intro x hx
  have hxE := hsub hx
  have hc : ContinuousAt (fun y => f (T y) * |coordinateJacobian T y|) x :=
    (hf.continuousAt.comp (hT.1 x hxE).continuousAt).mul
      (((continuousOn_coordinateJacobian hT).continuousAt (hE.mem_nhds hxE)).abs)
  apply hc.congr
  filter_upwards [hE.mem_nhds hxE] with y hy
  simp only [zeroExtendedPullback, indicator_of_mem hy]

theorem native_changeOfVariables {n : ℕ} {T : Coord n → Coord n}
    {E : Set (Coord n)} {f : Coord n → ℝ} (hE : IsOpen E) (hT : C1On T E)
    (hi : InjOn T E) (hf : Continuous f) (hs : HasCompactSupport f)
    (hsub : tsupport f ⊆ T '' E)
    (hp : Continuous (zeroExtendedPullback E T f))
    (hps : HasCompactSupport (zeroExtendedPullback E T f)) :
    wholeRIntegral f = wholeRIntegral (zeroExtendedPullback E T f) := by
  rw [wholeRIntegral_eq_integral hf hs, wholeRIntegral_eq_integral hp hps]
  have hrestrict : (∫ y in T '' E, f y) = ∫ y, f y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_contra hfy
    exact hy (hsub (subset_tsupport f hfy))
  rw [← hrestrict]
  have hchange := integral_image_eq_integral_abs_det_fderiv_smul volume hE.measurableSet
    (fun x hx => (hT.1 x hx).hasFDerivAt.hasFDerivWithinAt) hi f
  rw [zeroExtendedPullback, integral_indicator hE.measurableSet]
  simpa only [coordinateJacobian, ContinuousLinearMap.det, smul_eq_mul, mul_comm] using hchange

theorem pma10_9 : pma10_9_contract := by
  refine ⟨fun _ => coordinateJacobian_eq_matrix, fun _ _ _ => jacobian_euclideanTransform, ?_⟩
  intro n E T f hE hT hi hJ hf hs hsub
  obtain ⟨e, he, hsource, htarget⟩ := coordinate_partialHomeomorph hE hT hi hJ
  obtain ⟨hps, hpsub⟩ := zeroExtendedPullback_support e he hsource htarget hs hsub
  have hp := zeroExtendedPullback_continuous hE hT hf hpsub
  refine ⟨e, he, hsource, htarget, htarget ▸ e.open_target,
    htarget ▸ e.continuousOn_symm, hp, hps, hpsub,
    iteratedRIntegrable_of_continuousOn hf.continuousOn,
    iteratedRIntegrable_of_continuousOn hp.continuousOn, ?_⟩
  exact native_changeOfVariables hE hT hi hf hs hsub hp hps

end Rudin.PMA.Chapter10
