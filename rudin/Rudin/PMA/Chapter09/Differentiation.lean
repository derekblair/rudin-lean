import Mathlib
import Rudin.PMA.Chapter09.Linear

/-!
# Chapter 9: differentiation, PMA 9.10–9.21

Source contracts use Euclidean norms and the total derivative. The coordinate
partials in 9.16 and 9.21 are ordinary one-variable derivatives; their existence
does not presuppose total differentiability. The `HasFDerivAt` and `ContDiffOn`
bridges make the explicitly documented Mathlib calculus dependencies reusable.
-/

noncomputable section

set_option autoImplicit false

open Set Filter
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter09

section Definitions

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The source's linear approximation, written with the approaching point `y`. -/
def HasTotalDerivative (f : V → W) (A : V →L[ℝ] W) (x : V) : Prop :=
  Tendsto (fun y => ‖f y - f x - A (y - x)‖ / ‖y - x‖) (𝓝 x) (𝓝 0)

def TotalDifferentiableOn (f : V → W) (E : Set V) : Prop :=
  ∀ x ∈ E, ∃ A, HasTotalDerivative f A x

/-- The source definition: differentiability and continuity of the operator derivative. -/
def C1On (f : V → W) (E : Set V) : Prop :=
  (∀ x ∈ E, DifferentiableAt ℝ f x) ∧ ContinuousOn (fderiv ℝ f) E

end Definitions

def coordinateVector (n : ℕ) (j : Fin n) : Euclidean n :=
  EuclideanSpace.basisFun (Fin n) ℝ j

def HasCoordinatePartial {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (j : Fin n) (d : ℝ) : Prop :=
  HasDerivAt (fun t : ℝ => f (x + t • coordinateVector n j)) d 0

def coordinatePartial {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (j : Fin n) : ℝ :=
  deriv (fun t : ℝ => f (x + t • coordinateVector n j)) 0

def componentPartial {n m : ℕ} (f : Euclidean n → Euclidean m)
    (x : Euclidean n) (i : Fin m) (j : Fin n) : ℝ :=
  coordinatePartial (fun y => f y i) x j

def sourceGradient {n : ℕ} (f : Euclidean n → ℝ) (x : Euclidean n) : Euclidean n :=
  ∑ j, coordinatePartial f x j • coordinateVector n j

def ContinuousPartialsOn {n m : ℕ} (f : Euclidean n → Euclidean m)
    (E : Set (Euclidean n)) : Prop :=
  (∀ x ∈ E, ∀ i j, ∃ d, HasCoordinatePartial (fun y => f y i) x j d) ∧
    ∀ i j, ContinuousOn (fun x => componentPartial f x i j) E

def pma9_10_contract : Prop :=
  (∀ m (f : ℝ → Euclidean m) x y,
    HasDerivAt f y x ↔ HasTotalDerivative f ((1 : ℝ →L[ℝ] ℝ).smulRight y) x) ∧
  (∀ (f : ℝ → ℝ) x y,
    HasDerivAt f y x ↔ HasTotalDerivative f ((1 : ℝ →L[ℝ] ℝ).smulRight y) x) ∧
  (∀ m (A : ℝ →L[ℝ] Euclidean m) h, A h = h • A 1)

def pma9_11_contract : Prop :=
  (∀ n m (f : Euclidean n → Euclidean m) A x,
    HasTotalDerivative f A x ↔ HasFDerivAt f A x) ∧
  (∀ n m (f : Euclidean n → Euclidean m) (E : Set (Euclidean n)),
    IsOpen E → (TotalDifferentiableOn f E ↔ DifferentiableOn ℝ f E))

def pma9_12_contract : Prop :=
  ∀ n m (f : Euclidean n → Euclidean m) A B x,
    HasTotalDerivative f A x → HasTotalDerivative f B x → A = B

def pma9_13_contract : Prop :=
  (∀ n m (f : Euclidean n → Euclidean m) A x,
    HasTotalDerivative f A x ↔
      (fun h => f (x + h) - f x - A h) =o[𝓝 0] (fun h => h)) ∧
  (∀ n m (f : Euclidean n → Euclidean m) A x,
    HasTotalDerivative f A x → ContinuousAt f x) ∧
  (∀ n m (f : Euclidean n → Euclidean m) A x,
    HasTotalDerivative f A x → fderiv ℝ f x = A)

def pma9_14_contract : Prop :=
  ∀ n m (A : Euclidean n →L[ℝ] Euclidean m) x,
    HasTotalDerivative A A x ∧ fderiv ℝ A x = A

def pma9_15_contract : Prop :=
  ∀ n m k (E : Set (Euclidean n)) (U : Set (Euclidean m))
    (f : Euclidean n → Euclidean m) (g : Euclidean m → Euclidean k) x A B,
    IsOpen E → IsOpen U → x ∈ E → f x ∈ U →
    HasTotalDerivative f A x → HasTotalDerivative g B (f x) →
    HasTotalDerivative (g ∘ f) (B.comp A) x

def pma9_16_contract : Prop :=
  (∀ n (f : Euclidean n → ℝ) x j d,
    HasCoordinatePartial f x j d ↔
      Tendsto (fun t : ℝ => (f (x + t • coordinateVector n j) - f x) / t)
        (𝓝[≠] 0) (𝓝 d)) ∧
  (∃ f : Euclidean 2 → ℝ,
    (∀ x j, ∃ d, HasCoordinatePartial f x j d) ∧
    (∀ j, HasCoordinatePartial f 0 j 0) ∧ ¬ ContinuousAt f 0) ∧
  (∃ f : Euclidean 2 → ℝ,
    Continuous f ∧ (∀ x j, ∃ d, HasCoordinatePartial f x j d) ∧
    (∀ j, HasCoordinatePartial f 0 j 0) ∧ ¬ DifferentiableAt ℝ f 0)

def pma9_17_contract : Prop :=
  ∀ n m (f : Euclidean n → Euclidean m) A x,
    HasTotalDerivative f A x →
    (∀ i j, HasCoordinatePartial (fun y => f y i) x j (A (coordinateVector n j) i)) ∧
    (∀ i j, componentPartial f x i j = A (coordinateVector n j) i) ∧
    (∀ h, A h = ∑ i, (∑ j, componentPartial f x i j * h j) • coordinateVector m i)

def pma9_18_contract : Prop :=
  (∀ n (f : Euclidean n → ℝ) (γ : ℝ → Euclidean n) (E : Set (Euclidean n))
    a b t v, IsOpen E → MapsTo γ (Ioo a b) E → t ∈ Ioo a b →
    (∀ x ∈ E, DifferentiableAt ℝ f x) → HasDerivAt γ v t →
    HasDerivAt (f ∘ γ) (∑ j, coordinatePartial f (γ t) j * v j) t ∧
    HasDerivAt (f ∘ γ) (inner ℝ (sourceGradient f (γ t)) v) t) ∧
  (∀ n (f : Euclidean n → ℝ) x, DifferentiableAt ℝ f x →
    (∀ u, HasDerivAt (fun t : ℝ => f (x + t • u))
      (inner ℝ (sourceGradient f x) u) 0) ∧
    (∀ u, ‖u‖ = 1 → inner ℝ (sourceGradient f x) u ≤ ‖sourceGradient f x‖) ∧
    (sourceGradient f x ≠ 0 →
      ‖(‖sourceGradient f x‖⁻¹ : ℝ) • sourceGradient f x‖ = 1 ∧
      inner ℝ (sourceGradient f x)
        ((‖sourceGradient f x‖⁻¹ : ℝ) • sourceGradient f x) = ‖sourceGradient f x‖))

def pma9_19_contract : Prop :=
  (∀ n m (f : Euclidean n → Euclidean m) (E : Set (Euclidean n)) M,
    IsOpen E → Convex ℝ E → (∀ x ∈ E, DifferentiableAt ℝ f x) →
    (∀ x ∈ E, ‖fderiv ℝ f x‖ ≤ M) →
    ∀ a ∈ E, ∀ b ∈ E, ‖f b - f a‖ ≤ M * ‖b - a‖) ∧
  (∀ n m (f : Euclidean n → Euclidean m) (E : Set (Euclidean n)),
    IsOpen E → Convex ℝ E → (∀ x ∈ E, DifferentiableAt ℝ f x) →
    (∀ x ∈ E, fderiv ℝ f x = 0) → ∀ a ∈ E, ∀ b ∈ E, f a = f b)

def pma9_20_contract : Prop :=
  (∀ n m (f : Euclidean n → Euclidean m) (E : Set (Euclidean n)),
    IsOpen E → (C1On f E ↔ ContDiffOn ℝ 1 f E)) ∧
  (∀ n m (f : Euclidean n → Euclidean m) (E : Set (Euclidean n)),
    C1On f E ↔ (∀ x ∈ E, DifferentiableAt ℝ f x) ∧
      ∀ x ∈ E, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ E,
        ‖y - x‖ < δ → ‖fderiv ℝ f y - fderiv ℝ f x‖ < ε)

def pma9_21_contract : Prop :=
  ∀ n m (f : Euclidean n → Euclidean m) (E : Set (Euclidean n)),
    IsOpen E → (C1On f E ↔ ContinuousPartialsOn f E)

section Bridges

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem hasTotalDerivative_iff {f : V → W} {A : V →L[ℝ] W} {x : V} :
    HasTotalDerivative f A x ↔ HasFDerivAt f A x := by
  simpa only [HasTotalDerivative, div_eq_inv_mul] using
    (hasFDerivAt_iff_tendsto (f := f) (f' := A) (x := x)).symm

theorem totalDifferentiableOn_iff {f : V → W} {E : Set V} (hE : IsOpen E) :
    TotalDifferentiableOn f E ↔ DifferentiableOn ℝ f E := by
  constructor
  · intro h x hx
    obtain ⟨A, hA⟩ := h x hx
    exact (hasTotalDerivative_iff.mp hA).differentiableAt.differentiableWithinAt
  · intro h x hx
    exact ⟨fderiv ℝ f x, hasTotalDerivative_iff.mpr
      ((h x hx).differentiableAt (hE.mem_nhds hx)).hasFDerivAt⟩

theorem c1On_iff_contDiffOn {f : V → W} {E : Set V} (hE : IsOpen E) :
    C1On f E ↔ ContDiffOn ℝ 1 f E := by
  have hd : (∀ x ∈ E, DifferentiableAt ℝ f x) ↔ DifferentiableOn ℝ f E := by
    constructor
    · exact fun h x hx => (h x hx).differentiableWithinAt
    · exact fun h x hx => (h x hx).differentiableAt (hE.mem_nhds hx)
  rw [C1On, hd]
  simpa using (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) hE).symm

theorem c1On_iff_epsilon {f : V → W} {E : Set V} :
    C1On f E ↔ (∀ x ∈ E, DifferentiableAt ℝ f x) ∧
      ∀ x ∈ E, ∀ ε > 0, ∃ δ > 0, ∀ y ∈ E,
        ‖y - x‖ < δ → ‖fderiv ℝ f y - fderiv ℝ f x‖ < ε := by
  simp only [C1On, Metric.continuousOn_iff, dist_eq_norm]

end Bridges

theorem pma9_10 : pma9_10_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro m f x y
    rw [hasTotalDerivative_iff]
    exact hasDerivAt_iff_hasFDerivAt
  · intro f x y
    rw [hasTotalDerivative_iff]
    exact hasDerivAt_iff_hasFDerivAt
  · intro m A h
    simpa using A.map_smul h (1 : ℝ)

theorem pma9_11 : pma9_11_contract := by
  exact ⟨fun _ _ _ _ _ => hasTotalDerivative_iff,
    fun _ _ _ _ hE => totalDifferentiableOn_iff hE⟩

theorem pma9_12 : pma9_12_contract := by
  intro n m f A B x hA hB
  exact (hasTotalDerivative_iff.mp hA).unique (hasTotalDerivative_iff.mp hB)

theorem pma9_13 : pma9_13_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro n m f A x
    rw [hasTotalDerivative_iff, hasFDerivAt_iff_isLittleO_nhds_zero]
  · intro n m f A x h
    exact (hasTotalDerivative_iff.mp h).continuousAt
  · intro n m f A x h
    exact (hasTotalDerivative_iff.mp h).fderiv

theorem pma9_14 : pma9_14_contract := by
  intro n m A x
  exact ⟨hasTotalDerivative_iff.mpr A.hasFDerivAt, A.hasFDerivAt.fderiv⟩

theorem pma9_15 : pma9_15_contract := by
  intro n m k E U f g x A B _ _ _ _ hf hg
  exact hasTotalDerivative_iff.mpr
    ((hasTotalDerivative_iff.mp hg).comp x (hasTotalDerivative_iff.mp hf))

theorem hasCoordinatePartial_iff_quotient {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (j : Fin n) (d : ℝ) :
    HasCoordinatePartial f x j d ↔
      Tendsto (fun t : ℝ => (f (x + t • coordinateVector n j) - f x) / t)
        (𝓝[≠] 0) (𝓝 d) := by
  rw [HasCoordinatePartial, hasDerivAt_iff_tendsto_slope]
  have he : slope (fun t : ℝ => f (x + t • coordinateVector n j)) 0 =
      (fun t : ℝ => (f (x + t • coordinateVector n j) - f x) / t) := by
    funext t
    simp only [slope_def_field, zero_smul, add_zero, sub_zero]
  rw [he]

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

theorem sourceGradient_inner {n : ℕ} (f : Euclidean n → ℝ) (x u : Euclidean n) :
    inner ℝ (sourceGradient f x) u = ∑ j, coordinatePartial f x j * u j := by
  simp only [sourceGradient, coordinateVector, sum_inner, real_inner_smul_left,
    EuclideanSpace.basisFun_inner]

theorem sourceGradient_inner_eq_fderiv {n : ℕ} {f : Euclidean n → ℝ}
    {x : Euclidean n} (h : DifferentiableAt ℝ f x) (u : Euclidean n) :
    inner ℝ (sourceGradient f x) u = fderiv ℝ f x u := by
  rw [sourceGradient_inner, linear_apply_eq_sum_coordinates]
  exact Finset.sum_congr rfl fun j _ => by rw [coordinatePartial_eq_fderiv h]

theorem pma9_17 : pma9_17_contract := by
  intro n m f A x h
  have hf := hasTotalDerivative_iff.mp h
  have hp : ∀ i j, HasCoordinatePartial (fun y => f y i) x j
      (A (coordinateVector n j) i) := by
    intro i j
    exact hasCoordinatePartial_of_hasFDerivAt
      ((EuclideanSpace.proj i).hasFDerivAt.comp x hf) j
  have he : ∀ i j, componentPartial f x i j = A (coordinateVector n j) i := by
    intro i j
    exact (hp i j).deriv
  refine ⟨hp, he, ?_⟩
  intro h
  have hcoord : ∀ i, A h i = ∑ j, componentPartial f x i j * h j := by
    intro i
    simpa only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj, he] using
      linear_apply_eq_sum_coordinates ((EuclideanSpace.proj i).comp A) h
  calc
    A h = ∑ i, A h i • coordinateVector m i :=
      ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr (A h)).symm
    _ = _ := by simp_rw [hcoord]

theorem pma9_18 : pma9_18_contract := by
  constructor
  · intro n f γ E a b t v _ hγ ht hf hγ'
    have hd := hf (γ t) (hγ ht)
    have hc := hd.hasFDerivAt.comp_hasDerivAt t hγ'
    have he := sourceGradient_inner_eq_fderiv hd v
    constructor
    · convert hc using 1
      rw [← he, sourceGradient_inner]
    · rwa [← he] at hc
  · intro n f x hf
    refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [sourceGradient_inner_eq_fderiv hf]
      exact hf.hasFDerivAt.hasLineDerivAt u
    · intro u hu
      simpa only [hu, mul_one] using real_inner_le_norm (sourceGradient f x) u
    · intro hg
      have hn : ‖sourceGradient f x‖ ≠ 0 := norm_ne_zero_iff.mpr hg
      constructor
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
          inv_mul_cancel₀ hn]
      · rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp

theorem pma9_19 : pma9_19_contract := by
  constructor
  · intro n m f E M _ hE hd hM a ha b hb
    exact hE.norm_image_sub_le_of_norm_fderiv_le hd hM ha hb
  · intro n m f E _ hE hd hz a ha b hb
    have hbound : ∀ x ∈ E, ‖fderiv ℝ f x‖ ≤ (0 : ℝ) := by
      intro x hx
      simp [hz x hx]
    have h := hE.norm_image_sub_le_of_norm_fderiv_le hd hbound hb ha
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (by simpa using h) (norm_nonneg _)))

theorem pma9_20 : pma9_20_contract := by
  exact ⟨fun _ _ _ _ hE => c1On_iff_contDiffOn hE,
    fun _ _ _ _ => c1On_iff_epsilon⟩

end Rudin.PMA.Chapter09
