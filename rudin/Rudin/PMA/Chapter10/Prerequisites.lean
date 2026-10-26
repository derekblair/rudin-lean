import Rudin.PMA.Chapter08
import Rudin.PMA.Chapter09.SecondHalf

/-!
# Chapter 10 prerequisites in the merged Chapter 8/9 layout

The recovered Chapter 10 proofs use Euclidean-coordinate helper names from
`bb50a2079f8e189d8e282e2521bbadb64f4f98eb`. The merged Chapter 9 has a different
module/API layout, including a different `Chapter09.coordinatePartial` interface.
This narrow adapter keeps the recovered Euclidean definitions in Chapter 10,
imports the current chapters, and does not replace any of their node proofs.

Provenance: the Euclidean aliases/evaluation lemmas come from recovered
`Chapter09/Linear.lean`; coordinate helpers from `Differentiation.lean`;
determinant helpers from `Determinants.lean`; the native oriented integral bridge
from `ParameterIntegrals.lean`. Those declaration bodies are preserved below.
The C1 predicate/comparison, inverse-neighborhood theorem and uniform-integral
limit are adapters to the corresponding merged Chapter 9 results.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory Module
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

/-! ## Euclidean-coordinate support (recovered declarations) -/

abbrev Euclidean (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The standard coordinate basis of Euclidean space. -/
abbrev standardBasis (n : ℕ) := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis

/-- Continuous representatives of the finite-dimensional linear transformations. -/
abbrev Operator (n m : ℕ) := Euclidean n →L[ℝ] Euclidean m

def operatorMatrix {n m : ℕ} (A : Operator n m) : Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toMatrix (standardBasis n) (standardBasis m) A.toLinearMap

@[simp] theorem standardBasis_repr {n : ℕ} (x : Euclidean n) (i : Fin n) :
    (standardBasis n).repr x i = x i := rfl

@[simp] theorem standardBasis_apply {n : ℕ} (i j : Fin n) :
    standardBasis n i j = if j = i then 1 else 0 := by
  simp [standardBasis, EuclideanSpace.basisFun_apply, eq_comm]

@[simp] theorem operatorMatrix_apply {n m : ℕ} (A : Operator n m)
    (i : Fin m) (j : Fin n) : operatorMatrix A i j = A (standardBasis n j) i := by
  simp [operatorMatrix, LinearMap.toMatrix_apply]

/-! ## Differentiation support -/

section C1
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The recovered predicate is exactly the merged Chapter 9 predicate. -/
abbrev C1On (f : V → W) (E : Set V) : Prop := Chapter09.IsC1On f E

theorem c1On_iff_contDiffOn {f : V → W} {E : Set V} (hE : IsOpen E) :
    C1On f E ↔ ContDiffOn ℝ 1 f E := Chapter09.pma9_20 hE

end C1

def coordinateVector (n : ℕ) (j : Fin n) : Euclidean n :=
  EuclideanSpace.basisFun (Fin n) ℝ j

def HasCoordinatePartial {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (j : Fin n) (d : ℝ) : Prop :=
  HasDerivAt (fun t : ℝ => f (x + t • coordinateVector n j)) d 0

def coordinatePartial {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (j : Fin n) : ℝ :=
  deriv (fun t : ℝ => f (x + t • coordinateVector n j)) 0

theorem hasCoordinatePartial_of_hasFDerivAt {n : ℕ} {f : Euclidean n → ℝ}
    {A : Euclidean n →L[ℝ] ℝ} {x : Euclidean n} (h : HasFDerivAt f A x) (j : Fin n) :
    HasCoordinatePartial f x j (A (coordinateVector n j)) :=
  h.hasLineDerivAt (coordinateVector n j)

theorem coordinatePartial_eq_fderiv {n : ℕ} {f : Euclidean n → ℝ}
    {x : Euclidean n} (h : DifferentiableAt ℝ f x) (j : Fin n) :
    coordinatePartial f x j = fderiv ℝ f x (coordinateVector n j) :=
  (hasCoordinatePartial_of_hasFDerivAt h.hasFDerivAt j).deriv

theorem linear_apply_eq_sum_coordinates {n : ℕ} (A : Euclidean n →L[ℝ] ℝ)
    (h : Euclidean n) :
    A h = ∑ j, A (coordinateVector n j) * h j := by
  nth_rw 1 [← (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr h]
  simp [coordinateVector, map_sum, map_smul, mul_comm]

/-! ## Determinants in the recovered Euclidean coordinates -/

def tupleSign {n : ℕ} (t : Fin n → ℤ) : ℤ :=
  ∏ i, ∏ j ∈ Finset.Ioi i, Int.sign (t j - t i)

/-- The determinant as a function of its ordered column vectors. -/
def columnDet {n : ℕ} (v : Fin n → Euclidean n) : ℝ :=
  Matrix.det (fun i j => v j i)

/-- The Jacobian is the determinant of the total derivative in standard bases. -/
def jacobian {n : ℕ} (f : Euclidean n → Euclidean n) (x : Euclidean n) : ℝ :=
  Matrix.det (operatorMatrix (fderiv ℝ f x))

/-- The partial Jacobian for the first (solved) variable block. -/
def partialJacobian {n m : ℕ} (f : Euclidean n × Euclidean m → Euclidean n)
    (z : Euclidean n × Euclidean m) : ℝ :=
  Matrix.det (operatorMatrix
    ((fderiv ℝ f z).comp (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean m))))

def pma9_38_contract : Prop :=
  (∀ (n : ℕ) (f : Euclidean n → Euclidean n) (x : Euclidean n),
    DifferentiableAt ℝ f x →
      jacobian f x = LinearMap.det (fderiv ℝ f x).toLinearMap ∧
      ((fderiv ℝ f x).IsInvertible ↔ jacobian f x ≠ 0)) ∧
  (∀ (n m : ℕ) (f : Euclidean n × Euclidean m → Euclidean n)
      (z : Euclidean n × Euclidean m), DifferentiableAt ℝ f z →
    (((fderiv ℝ f z).comp
      (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean m))).IsInvertible ↔
        partialJacobian f z ≠ 0))

theorem operator_isUnit_iff_det_ne_zero {n : ℕ} (A : Operator n n) :
    IsUnit A ↔ (operatorMatrix A).det ≠ 0 := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap,
    LinearMap.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rw [operatorMatrix, LinearMap.det_toMatrix]

theorem operator_isInvertible_iff_isUnit {n : ℕ} (A : Operator n n) :
    A.IsInvertible ↔ IsUnit A := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  constructor
  · rintro ⟨e, rfl⟩
    exact e.bijective
  · intro h
    exact ⟨ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr h.1) (LinearMap.range_eq_top.mpr h.2), rfl⟩

theorem pma9_38 : pma9_38_contract := by
  constructor
  · intro n f x _
    refine ⟨LinearMap.det_toMatrix (standardBasis n) _, ?_⟩
    exact (operator_isInvertible_iff_isUnit _).trans (operator_isUnit_iff_det_ne_zero _)
  · intro n m f z _
    exact (operator_isInvertible_iff_isUnit _).trans (operator_isUnit_iff_det_ne_zero _)

/-! ## Local inverse: adapter to the merged Chapter 9 theorem -/

def InverseNeighborhood {V W : Type*} [TopologicalSpace V] [TopologicalSpace W]
    (f : V → W) (E : Set V) (a : V) (e : OpenPartialHomeomorph V W) : Prop :=
  (e : V → W) = f ∧ a ∈ e.source ∧ e.source ⊆ E

section Inverse
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The recovered C1 interface, obtained from the merged local inverse theorem. -/
theorem inverse_neighborhood_c1 {E : Set V} {f : V → W} {a : V}
    (hE : IsOpen E) (ha : a ∈ E) (hf : C1On f E)
    (hinv : (fderiv ℝ f a).IsInvertible) :
    ∃ e : OpenPartialHomeomorph V W,
      InverseNeighborhood f E a e ∧ C1On e.symm e.target ∧
      ∀ y ∈ e.target, HasFDerivAt e.symm (fderiv ℝ f (e.symm y)).inverse y := by
  obtain ⟨A, hA⟩ := hinv
  have hfa : HasFDerivAt f (A : V →L[ℝ] W) a := by
    rw [hA]
    exact (hf.1 a ha).hasFDerivAt
  obtain ⟨e, he, haE, hsub, hgc⟩ :=
    Chapter09.pma9_24 hE ((c1On_iff_contDiffOn hE).mp hf) ha A hfa
  refine ⟨e, ⟨he, haE, hsub⟩, (c1On_iff_contDiffOn e.open_target).mpr hgc, ?_⟩
  intro y hy
  have hx := e.map_target hy
  have hd : HasFDerivAt e (fderiv ℝ f (e.symm y)) (e.symm y) := by
    rw [he]
    exact (hf.1 _ (hsub hx)).hasFDerivAt
  have hg : DifferentiableAt ℝ e.symm y :=
    (hgc.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt (by norm_num)
  have hg' : HasFDerivAt e.symm (fderiv ℝ e.symm y) (e (e.symm y)) := by
    simpa only [e.right_inv hy] using hg.hasFDerivAt
  have hcomp := hg'.comp (e.symm y) hd
  have hleft : (fderiv ℝ e.symm y).comp (fderiv ℝ f (e.symm y)) =
      ContinuousLinearMap.id ℝ V := by
    have hh : e.symm ∘ e =ᶠ[𝓝 (e.symm y)] id :=
      Filter.eventually_of_mem (e.open_source.mem_nhds hx) fun z hz => e.left_inv hz
    simpa only [e.left_inv hx] using (hcomp.congr_of_eventuallyEq hh.symm).unique (hasFDerivAt_id _)
  have hright : (fderiv ℝ f (e.symm y)).comp (fderiv ℝ e.symm y) =
      ContinuousLinearMap.id ℝ W := by
    have hh : e ∘ e.symm =ᶠ[𝓝 y] id :=
      Filter.eventually_of_mem (e.open_target.mem_nhds hy) fun z hz => e.right_inv hz
    exact ((hd.comp y hg.hasFDerivAt).congr_of_eventuallyEq hh.symm).unique (hasFDerivAt_id _)
  let B : V ≃L[ℝ] W := ContinuousLinearEquiv.equivOfInverse'
    (fderiv ℝ f (e.symm y)) (fderiv ℝ e.symm y) hright hleft
  change HasFDerivAt e.symm (B : V →L[ℝ] W).inverse y
  rw [ContinuousLinearMap.inverse_equiv]
  exact e.hasFDerivAt_symm hy
    (show HasFDerivAt e (B : V →L[ℝ] W) (e.symm y) from hd)

end Inverse

/-! ## Native integral adapters -/

open Chapter06

theorem rsIntegral_tendsto_of_uniformFilterLimit {ι : Type*} {L : Filter ι} [L.NeBot]
    {F : ι → ℝ → ℝ} {f α : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ᶠ i in L, RSIntegrable (F i) α a b)
    (hlim : TendstoUniformlyOn F f L (Icc a b)) :
    RSIntegrable f α a b ∧
      Tendsto (fun i => RSIntegral (F i) α a b) L (𝓝 (RSIntegral f α a b)) :=
  Chapter09.rsIntegral_uniformLimit_filter hF hlim

theorem orientedRIntegral_eq_intervalIntegral {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    Chapter08.orientedRIntegral f a b = ∫ x in a..b, f x := by
  have hi : ∀ u v, u ≤ v → RIntegrable f u v :=
    fun u v huv => pma6_8 f id u v huv hf.continuousOn (monotone_id.monotoneOn _)
  have he : ∀ u v, u < v → RIntegral f u v = ∫ x in u..v, f x := by
    intro u v huv
    have hd : ∀ x : ℝ, HasDerivAt (fun y => ∫ t in u..y, f t) (f x) x := by
      intro x
      exact intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable u x)
        (hf.stronglyMeasurableAtFilter volume (𝓝 x)) hf.continuousAt
    have hFTC : RIntegral f u v = (∫ t in u..v, f t) - (∫ t in u..u, f t) :=
      pma6_21 (fun y => ∫ t in u..y, f t) f u v huv
        (fun x _ => (hd x).hasDerivWithinAt) (hi u v huv.le)
    simpa only [intervalIntegral.integral_same, sub_zero] using hFTC
  rcases lt_trichotomy a b with hab | hab | hab
  · simp only [Chapter08.orientedRIntegral, ite_eq_left hab.le, he a b hab]
  · subst b
    simp only [Chapter08.orientedRIntegral, le_refl, ite_true, intervalIntegral.integral_same]
    exact (calculus_singleton_integrals f id a).2
  · rw [Chapter08.orientedRIntegral, ite_eq_right (not_le.mpr hab), he b a hab,
      intervalIntegral.integral_symm]
    simp

end Rudin.PMA.Chapter10
