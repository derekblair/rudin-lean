import Rudin.PMA.Chapter09.ParameterIntegrals
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Topology.TietzeExtension

/-! # PMA 10.1–10.4: native iterated integration.

The recursive value uses Chapter 6's ordinary Riemann integral at every step.
`IteratedRIntegrable` records existence of all one-dimensional integrals; values
of totalized integrals alone never count as existence assertions.
-/

noncomputable section
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10

abbrev Coord (n : ℕ) := Fin n → ℝ

/-- A closed coordinate cell, with degenerate side intervals admitted. -/
structure Cell (n : ℕ) where
  lower : Coord n
  upper : Coord n
  lower_le_upper : lower ≤ upper

namespace Cell

def carrier {n : ℕ} (C : Cell n) : Set (Coord n) := Icc C.lower C.upper

def init {n : ℕ} (C : Cell (n + 1)) : Cell n where
  lower i := C.lower i.castSucc
  upper i := C.upper i.castSucc
  lower_le_upper i := C.lower_le_upper i.castSucc

def permute {n : ℕ} (C : Cell n) (σ : Equiv.Perm (Fin n)) : Cell n where
  lower i := C.lower (σ i)
  upper i := C.upper (σ i)
  lower_le_upper i := C.lower_le_upper (σ i)

def unit (n : ℕ) : Cell n where
  lower := 0
  upper := 1
  lower_le_upper := by intro i; norm_num

end Cell

/-- Integrate the last coordinate, retaining the source's coordinate order. -/
def nativeSliceIntegral {n : ℕ} (C : Cell (n + 1)) (f : Coord (n + 1) → ℝ)
    (x : Coord n) : ℝ :=
  Chapter06.RIntegral (fun t => f (Fin.snoc x t))
    (C.lower (Fin.last n)) (C.upper (Fin.last n))

def iteratedRIntegral : {n : ℕ} → Cell n → (Coord n → ℝ) → ℝ
  | 0, _, f => f 0
  | n + 1, C, f => iteratedRIntegral C.init (nativeSliceIntegral C f)

/-- Existence of every slice integral encountered in the recursion. -/
def IteratedRIntegrable : {n : ℕ} → Cell n → (Coord n → ℝ) → Prop
  | 0, _, _ => True
  | n + 1, C, f =>
      (∀ x ∈ C.init.carrier, Chapter06.RIntegrable (fun t => f (Fin.snoc x t))
        (C.lower (Fin.last n)) (C.upper (Fin.last n))) ∧
      IteratedRIntegrable C.init (nativeSliceIntegral C f)

/-- Convert coordinates in a permuted cell back to the original ordering. -/
def unpermute {n : ℕ} (σ : Equiv.Perm (Fin n)) (x : Coord n) : Coord n :=
  fun i => x (σ.symm i)

/-- A containing cell is chosen only to define the totalized value. The public
contract proves existence and independence whenever the support is compact. -/
def supportCell {n : ℕ} (f : Coord n → ℝ) : Cell n := by
  classical
  exact if h : ∃ C : Cell n, tsupport f ⊆ C.carrier then Classical.choose h else Cell.unit n

def wholeRIntegral {n : ℕ} (f : Coord n → ℝ) : ℝ :=
  iteratedRIntegral (supportCell f) f

def complexIteratedRIntegral {n : ℕ} (C : Cell n) (f : Coord n → ℂ) : ℂ :=
  (iteratedRIntegral C (fun x => (f x).re) : ℂ) +
    (iteratedRIntegral C (fun x => (f x).im) : ℂ) * Complex.I

def ComplexIteratedRIntegrable {n : ℕ} (C : Cell n) (f : Coord n → ℂ) : Prop :=
  IteratedRIntegrable C (fun x => (f x).re) ∧ IteratedRIntegrable C (fun x => (f x).im)

def complexWholeRIntegral {n : ℕ} (f : Coord n → ℂ) : ℂ :=
  (wholeRIntegral (fun x => (f x).re) : ℂ) +
    (wholeRIntegral (fun x => (f x).im) : ℂ) * Complex.I

def coordEquivEuclidean (n : ℕ) : Coord n ≃L[ℝ] Chapter09.Euclidean n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

def standardSimplex (n : ℕ) : Set (Coord n) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def simplexExtension {n : ℕ} (f : Coord n → ℝ) : Coord n → ℝ :=
  (standardSimplex n).indicator f

def simplexRIntegral {n : ℕ} (f : Coord n → ℝ) : ℝ :=
  iteratedRIntegral (Cell.unit n) (simplexExtension f)

/-- Euclidean ambient functions can be integrated using the same coordinate
parameters as the source cells and simplices. -/
def euclideanCellIntegral {n : ℕ} (C : Cell n)
    (f : Chapter09.Euclidean n → ℝ) : ℝ :=
  iteratedRIntegral C (fun x => f (WithLp.toLp 2 x))

def euclideanSimplexIntegral {n : ℕ} (f : Chapter09.Euclidean n → ℝ) : ℝ :=
  simplexRIntegral (fun x => f (WithLp.toLp 2 x))

def pma10_1_contract : Prop :=
  (∀ n (C : Cell n) (f : Coord n → ℝ), ContinuousOn f C.carrier →
    IteratedRIntegrable C f) ∧
  (∀ n (C : Cell (n + 1)) (f : Coord (n + 1) → ℝ), ContinuousOn f C.carrier →
    ContinuousOn (nativeSliceIntegral C f) C.init.carrier) ∧
  (∀ n (C : Cell (n + 1)) (f : Coord (n + 1) → ℝ),
    iteratedRIntegral C f = iteratedRIntegral C.init (nativeSliceIntegral C f)) ∧
  (∀ n (C : Cell n) (f : Coord n → ℝ), ContinuousOn f C.carrier →
    IntegrableOn f C.carrier ∧ iteratedRIntegral C f = ∫ x in C.carrier, f x)

def pma10_2_contract : Prop :=
  ∀ n (C : Cell n) (f : Coord n → ℝ), ContinuousOn f C.carrier →
    ∀ σ : Equiv.Perm (Fin n),
      IteratedRIntegrable (C.permute σ) (fun x => f (unpermute σ x)) ∧
      iteratedRIntegral (C.permute σ) (fun x => f (unpermute σ x)) = iteratedRIntegral C f

def pma10_3_contract : Prop :=
  (∀ n (f : Coord n → ℝ), tsupport f = closure {x | f x ≠ 0}) ∧
  (∀ n (f : Coord n → ℂ), tsupport f = closure {x | f x ≠ 0}) ∧
  (∀ n (f : Coord n → ℝ), Continuous f → HasCompactSupport f →
    (∃ C : Cell n, tsupport f ⊆ C.carrier) ∧ Integrable f ∧
    wholeRIntegral f = ∫ x, f x) ∧
  (∀ n (f : Coord n → ℝ) (C : Cell n), Continuous f → HasCompactSupport f →
    tsupport f ⊆ C.carrier → IteratedRIntegrable C f ∧
      wholeRIntegral f = iteratedRIntegral C f) ∧
  (∀ n (f : Coord n → ℂ), Continuous f → HasCompactSupport f →
    (∃ C : Cell n, tsupport f ⊆ C.carrier) ∧ Integrable f ∧
    complexWholeRIntegral f = ∫ x, f x) ∧
  (∀ n (f : Coord n → ℂ) (C : Cell n), Continuous f → HasCompactSupport f →
    tsupport f ⊆ C.carrier → ComplexIteratedRIntegrable C f ∧
      complexWholeRIntegral f = complexIteratedRIntegral C f)

def pma10_4_contract : Prop :=
  (∀ n (f : Coord n → ℝ), ContinuousOn f (standardSimplex n) →
    IteratedRIntegrable (Cell.unit n) (simplexExtension f) ∧
    IntegrableOn f (standardSimplex n) ∧
    simplexRIntegral f = ∫ x in standardSimplex n, f x) ∧
  (∀ n (f : Coord (n + 1) → ℝ), ContinuousOn f (standardSimplex (n + 1)) →
    ContinuousOn (nativeSliceIntegral (Cell.unit (n + 1)) (simplexExtension f))
      (Cell.unit n).carrier) ∧
  (∀ n (f : Coord n → ℝ), ContinuousOn f (standardSimplex n) →
    ∀ σ : Equiv.Perm (Fin n),
      IteratedRIntegrable (Cell.unit n) (fun x => simplexExtension f (unpermute σ x)) ∧
      iteratedRIntegral (Cell.unit n) (fun x => simplexExtension f (unpermute σ x)) =
        simplexRIntegral f)

end Rudin.PMA.Chapter10
