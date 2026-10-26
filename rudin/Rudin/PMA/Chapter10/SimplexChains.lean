import Rudin.PMA.Chapter10.PullbackEvaluation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- A C² parametrized simplex retains its actual map, with regularity on an
open neighborhood of the standard closed parameter simplex. -/
structure C2Simplex (k n : ℕ) (E : Set (Euclidean n)) where
  map : Coord k → Euclidean n
  regularity : ∃ U : Set (Coord k), IsOpen U ∧ standardSimplex k ⊆ U ∧ ContDiffOn ℝ 2 map U
  mapsTo : MapsTo map (standardSimplex k) E

@[ext] lemma C2Simplex.ext {k n : ℕ} {E : Set (Euclidean n)}
    {σ τ : C2Simplex k n E} (h : σ.map = τ.map) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

/-- Choosing a neighborhood changes neither the map nor its integral. -/
def C2Simplex.toSurface {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : Surface k n E where
  domain := .simplex
  map := σ.map
  neighborhood := σ.regularity.choose
  open_neighborhood := σ.regularity.choose_spec.1
  domain_subset := σ.regularity.choose_spec.2.1
  regularity := σ.regularity.choose_spec.2.2.of_le (by norm_num)
  mapsTo := σ.mapsTo

lemma C2Simplex.toSurface_isC2 {k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) : σ.toSurface.IsC2 := σ.regularity

/-- Precomposition uses an actual map carrying the smaller standard simplex
into the larger one; no immersion or injectivity is assumed. -/
def C2Simplex.precompose {l k n : ℕ} {E : Set (Euclidean n)}
    (σ : C2Simplex k n E) (A : Coord l → Coord k) (hA : ContDiff ℝ 2 A)
    (hAS : MapsTo A (standardSimplex l) (standardSimplex k)) : C2Simplex l n E where
  map := σ.map ∘ A
  regularity := ⟨A ⁻¹' σ.regularity.choose,
    σ.regularity.choose_spec.1.preimage hA.continuous,
    fun u hu => σ.regularity.choose_spec.2.1 (hAS hu),
    σ.regularity.choose_spec.2.2.comp hA.contDiffOn (mapsTo_preimage _ _)⟩
  mapsTo := σ.mapsTo.comp hAS

/-- Postcomposition restricts the parameter neighborhood to the preimage of
its open target before applying the C² chain rule. -/
def C2Simplex.mapBy {k n m : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    (σ : C2Simplex k n E) (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) : C2Simplex k m V where
  map := T ∘ σ.map
  regularity := ⟨σ.regularity.choose ∩ σ.map ⁻¹' E,
    σ.regularity.choose_spec.2.2.continuousOn.isOpen_inter_preimage
      σ.regularity.choose_spec.1 hE,
    fun u hu => ⟨σ.regularity.choose_spec.2.1 hu, σ.mapsTo hu⟩,
    hT.comp (σ.regularity.choose_spec.2.2.mono inter_subset_left) (fun _ hu => hu.2)⟩
  mapsTo := hTV.comp σ.mapsTo

lemma C2Simplex.mapBy_precompose {l k n m : ℕ}
    {E : Set (Euclidean n)} {V : Set (Euclidean m)} (σ : C2Simplex k n E)
    (A : Coord l → Coord k) (hA : ContDiff ℝ 2 A)
    (hAS : MapsTo A (standardSimplex l) (standardSimplex k))
    (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) :
    (σ.precompose A hA hAS).mapBy T hE hT hTV =
      (σ.mapBy T hE hT hTV).precompose A hA hAS := by
  apply C2Simplex.ext
  rfl

/-- Integer multiplicities distinguish chain addition from pointwise addition
of parametrizations. Negative multiplicity reverses integration orientation. -/
abbrev SimplexChain (k n : ℕ) (E : Set (Euclidean n)) := C2Simplex k n E →₀ ℤ

def chainIntegral {k n : ℕ} {E : Set (Euclidean n)} (ω : FormField n) :
    SimplexChain k n E →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ (fun σ => surfaceIntegral σ.toSurface ω)

/-- The source's equality of chains is equality of their integration functionals. -/
def ChainEq {k n : ℕ} {E : Set (Euclidean n)} (Γ Δ : SimplexChain k n E) : Prop :=
  ∀ ω : FormField n, IsFormOn E k ω → chainIntegral ω Γ = chainIntegral ω Δ

@[simp] lemma chainIntegral_single {k n : ℕ} {E : Set (Euclidean n)}
    (ω : FormField n) (σ : C2Simplex k n E) (z : ℤ) :
    chainIntegral ω (Finsupp.single σ z) = (z : ℝ) * surfaceIntegral σ.toSurface ω := by
  simp [chainIntegral, Finsupp.linearCombination_single, zsmul_eq_mul]

def chainMap {k n m : ℕ} {E : Set (Euclidean n)} {V : Set (Euclidean m)}
    (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) :
    SimplexChain k n E →ₗ[ℤ] SimplexChain k m V :=
  Finsupp.lmapDomain ℤ ℤ (fun σ => σ.mapBy T hE hT hTV)

@[simp] lemma chainMap_single {k n m : ℕ} {E : Set (Euclidean n)}
    {V : Set (Euclidean m)} (T : Euclidean n → Euclidean m) (hE : IsOpen E)
    (hT : ContDiffOn ℝ 2 T E) (hTV : MapsTo T E V) (σ : C2Simplex k n E) (z : ℤ) :
    chainMap T hE hT hTV (Finsupp.single σ z) = Finsupp.single (σ.mapBy T hE hT hTV) z := by
  simp [chainMap]

end Rudin.PMA.Chapter10
