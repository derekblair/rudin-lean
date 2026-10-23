import Rudin.PMA.Chapter10.ConvexLinearSections
import Rudin.PMA.Chapter10.Integration
import Rudin.PMA.Chapter09.Differentiation

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def prefixIndex {n : ℕ} (p : Fin n) (i : Fin p.val) : Fin n :=
  ⟨i.val, i.isLt.trans p.isLt⟩

lemma prefixIndex_injective {n : ℕ} (p : Fin n) : Injective (prefixIndex p) := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin n => x.val) h)

def coordinatePrefixProjection {n : ℕ} (p : Fin n) : Euclidean n →L[ℝ] Euclidean p.val :=
  (coordEquivEuclidean p.val).toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (prefixIndex p i)))

@[simp] lemma coordinatePrefixProjection_apply {n : ℕ} (p : Fin n) (x : Euclidean n) (i : Fin p.val) :
    coordinatePrefixProjection p x i = x (prefixIndex p i) := rfl

def prefixInsertion {n : ℕ} (p : Fin n) : Euclidean p.val →L[ℝ] Euclidean n :=
  ∑ i : Fin p.val, (EuclideanSpace.proj i).smulRight (coordinateVector n (prefixIndex p i))

@[simp] lemma prefixInsertion_apply {n : ℕ} (p : Fin n) (y : Euclidean p.val) :
    prefixInsertion p y = ∑ i : Fin p.val, y i • coordinateVector n (prefixIndex p i) := by
  simp [prefixInsertion]

lemma coordinatePrefixProjection_rightInverse {n : ℕ} (p : Fin n) :
    Function.RightInverse (prefixInsertion p) (coordinatePrefixProjection p) := by
  intro y
  ext i
  simp [prefixInsertion_apply, coordinateVector, EuclideanSpace.basisFun_apply,
    PiLp.single_apply, (prefixIndex_injective p).eq_iff, eq_comm]

lemma coordinatePrefixProjection_eq_iff {n : ℕ} (p : Fin n) (x y : Euclidean n) :
    coordinatePrefixProjection p x = coordinatePrefixProjection p y ↔ ∀ i : Fin n, i < p → x i = y i := by
  constructor
  · intro h i hi
    have he := congrArg (fun z : Euclidean p.val => z ⟨i.val, hi⟩) h
    simpa only [coordinatePrefixProjection_apply, prefixIndex, Fin.eta] using he
  · intro h
    ext i
    exact h (prefixIndex p i) i.isLt

lemma coordinatePrefixProjection_later_coordinate {n : ℕ} (p j : Fin n) (hj : p ≤ j) :
    coordinatePrefixProjection p (coordinateVector n j) = 0 := by
  ext i
  have hn : prefixIndex p i ≠ j := by
    intro he
    have hv := congrArg Fin.val he
    dsimp only [prefixIndex] at hv
    omega
  simp [coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply, hn, Ne.symm hn]

/-- The smooth choice of a point in each prefix fiber is independent of all
remaining coordinates. This includes the zero-dimensional prefix for p=0. -/
lemma exists_prefix_retraction {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (hc : Convex ℝ E) (p : Fin n) :
    ∃ a : Euclidean n → Euclidean n, ContDiffOn ℝ 1 a E ∧ MapsTo a E E ∧
      (∀ x ∈ E, ∀ j : Fin n, j < p → a x j = x j) ∧
      (∀ x ∈ E, ∀ j : Fin n, p ≤ j → fderiv ℝ a x (coordinateVector n j) = 0) := by
  let P := coordinatePrefixProjection p
  obtain ⟨s, hs, hsection⟩ := exists_contDiffOn_linear_section P (prefixInsertion p)
    (coordinatePrefixProjection_rightInverse p) hE hc
  have hU : IsOpen (P '' E) := P.isOpenMap (coordinatePrefixProjection_rightInverse p).surjective E hE
  let a : Euclidean n → Euclidean n := s ∘ P
  have ha : ContDiffOn ℝ 1 a E := hs.comp P.contDiff.contDiffOn (mapsTo_image _ _)
  refine ⟨a, ha, fun x hx => (hsection (P x) ⟨x, hx, rfl⟩).1, ?_, ?_⟩
  · intro x hx j hj
    exact (coordinatePrefixProjection_eq_iff p (a x) x).mp (hsection (P x) ⟨x, hx, rfl⟩).2 j hj
  · intro x hx j hj
    have hds : DifferentiableAt ℝ s (P x) :=
      hs.differentiableOn_one.differentiableAt (hU.mem_nhds ⟨x, hx, rfl⟩)
    have hd : HasFDerivAt a ((fderiv ℝ s (P x)).comp P) x := hds.hasFDerivAt.comp x P.hasFDerivAt
    rw [hd.fderiv, ContinuousLinearMap.comp_apply, coordinatePrefixProjection_later_coordinate p j hj, map_zero]

end Rudin.PMA.Chapter10
