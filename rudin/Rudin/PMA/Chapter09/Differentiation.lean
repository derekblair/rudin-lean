import Mathlib

/-!
# PMA 9.10–9.18: differentiation

The finite-dimensional spaces below carry their Euclidean norms. Functions on open
sets are represented by total extensions; every derivative assertion is local, so
the values of an extension away from the open set are immaterial. Continuous
linear maps represent Rudin's linear transformations: in finite dimensions every
linear map is continuous. The statements are pointwise, with no unnecessary
global hypotheses on the extensions. Generalization: natural-number dimensions
also include the harmless zero-dimensional case.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter09

/-- **9.10**, (7), (10): the one-variable derivative is the limit of slopes. -/
theorem pma9_10_slope {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {x : ℝ} {y : EuclideanSpace ℝ (Fin m)} :
    HasDerivAt f y x ↔
      Tendsto (fun h : ℝ => h⁻¹ • (f (x + h) - f x)) (𝓝[≠] 0) (𝓝 y) :=
  hasDerivAt_iff_tendsto_slope_zero

/-- **9.10**, (7): the scalar derivative is the usual difference-quotient limit. -/
theorem pma9_10_scalar_slope {f : ℝ → ℝ} {x y : ℝ} :
    HasDerivAt f y x ↔
      Tendsto (fun h : ℝ => (f (x + h) - f x) / h) (𝓝[≠] 0) (𝓝 y) := by
  simpa [div_eq_inv_mul] using (hasDerivAt_iff_tendsto_slope_zero (f := f) (x := x)
    (f' := y))

/-- **9.10**, (11)–(13): the vector derivative is equivalently a vanishing
normalized remainder. -/
theorem pma9_10_remainder {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {x : ℝ} {y : EuclideanSpace ℝ (Fin m)} :
    HasDerivAt f y x ↔
      Tendsto (fun h : ℝ => ‖f (x + h) - f x - h • y‖ / |h|) (𝓝 0) (𝓝 0) := by
  rw [hasDerivAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero,
    ← isLittleO_norm_left, ← isLittleO_norm_right, isLittleO_iff_tendsto]
  · rfl
  · intro h hh
    have : h = 0 := norm_eq_zero.mp hh
    simp [this]

/-- **9.10**: the vector derivative and the corresponding linear map agree. -/
theorem pma9_10_linear_derivative {m : ℕ} {f : ℝ → EuclideanSpace ℝ (Fin m)}
    {x : ℝ} {y : EuclideanSpace ℝ (Fin m)} :
    HasDerivAt f y x ↔ HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ y) x :=
  hasDerivAt_iff_hasFDerivAt

/-- **9.10**: every linear map from the real line is multiplication by its value at one. -/
theorem pma9_10_linear_map (m : ℕ) (A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin m))
    (h : ℝ) : A h = h • A 1 := by
  simpa using A.map_smul h (1 : ℝ)

/-- **9.10**: the identification of vectors with linear maps from the real line
is onto, and the representing vector is recovered by evaluation at one. -/
theorem pma9_10_linear_map_eq {m : ℕ} (A : ℝ →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    A = ContinuousLinearMap.toSpanSingleton ℝ (A 1) := by
  apply ContinuousLinearMap.ext
  intro h
  exact pma9_10_linear_map m A h

/-- **9.10**, scalar version of the same identification. -/
theorem pma9_10_scalar_linear_map (A : ℝ →L[ℝ] ℝ) (h : ℝ) : A h = A 1 * h := by
  simpa [mul_comm] using A.map_smul h (1 : ℝ)

/-- **9.11**: differentiability with a specified total derivative. -/
def pma9_11 {n m : ℕ} (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Prop := HasFDerivAt f A x

/-- **9.11**: differentiability throughout an open domain. -/
def pma9_11_differentiableOn {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (E : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ E, DifferentiableAt ℝ f x

/-- **9.11**, open-domain convention: changing a total extension outside the
open domain does not change any of its derivatives inside the domain. -/
theorem pma9_11_extension_independent {n m : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {E : Set (EuclideanSpace ℝ (Fin n))} (hE : IsOpen E)
    (hfg : Set.EqOn f g E) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ E)
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    pma9_11 f A x ↔ pma9_11 g A x := by
  have heq : f =ᶠ[𝓝 x] g := by
    filter_upwards [hE.mem_nhds hx] with y hy
    exact hfg hy
  exact heq.hasFDerivAt_iff

/-- **9.11**, (14): the norm of the remainder divided by the increment tends to zero.
Using the full neighborhood is equivalent to the punctured limit here, because
the quotient is zero at the origin under Lean's convention for division by zero. -/
theorem pma9_11_iff_limit {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} :
    pma9_11 f A x ↔
      Tendsto (fun h => ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
  rw [pma9_11, hasFDerivAt_iff_isLittleO_nhds_zero,
    ← isLittleO_norm_left, ← isLittleO_norm_right, isLittleO_iff_tendsto]
  intro h hh
  have : h = 0 := norm_eq_zero.mp hh
  simp [this]

/-- **9.11**, (14), with exactly the punctured-limit convention used in the book. -/
theorem pma9_11_iff_punctured_limit {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} :
    pma9_11 f A x ↔
      Tendsto (fun h => ‖f (x + h) - f x - A h‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0) := by
  rw [pma9_11_iff_limit]
  simpa [ContinuousAt] using
    (continuousAt_iff_punctured_nhds
      (f := fun h => ‖f (x + h) - f x - A h‖ / ‖h‖)
      (a := (0 : EuclideanSpace ℝ (Fin n))))

/-- **9.12**: uniqueness of the derivative. -/
theorem pma9_12 {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hA : pma9_11 f A x) (hB : pma9_11 f B x) :
    A = B := hA.unique hB

/-- **9.13(a)**, (17)–(18): a linear approximation with a negligible remainder. -/
theorem pma9_13_remainder {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} :
    pma9_11 f A x ↔ ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
      (∀ h, f (x + h) - f x = A h + r h) ∧
      Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝 0) (𝓝 0) := by
  rw [pma9_11_iff_limit]
  constructor
  · intro hf
    exact ⟨fun h => f (x + h) - f x - A h,
      fun h => by simp [sub_eq_add_neg, add_left_comm, add_assoc], hf⟩
  · rintro ⟨r, hr, hlim⟩
    simpa only [hr, add_sub_cancel_left] using hlim

/-- **9.13(b,d)**: the differential, as an operator-valued function.
Mathlib totalizes this function with value zero at nondifferentiable points;
on the book's differentiability domain the next theorem identifies its value. -/
def pma9_13_differential {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)) := fderiv ℝ f

theorem pma9_13_differential_eq {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x) :
    pma9_13_differential f x = A := hf.fderiv

/-- **9.13(c)**: differentiability implies continuity. -/
theorem pma9_13_continuous {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x) : ContinuousAt f x :=
  hf.continuousAt

/-- **9.14**, (19): a linear map is its own derivative at every point. -/
theorem pma9_14 {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : pma9_11 A A x := A.hasFDerivAt

/-- **9.14**, (20): the remainder is identically zero. -/
theorem pma9_14_remainder {n m : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (x h : EuclideanSpace ℝ (Fin n)) : A (x + h) - A x = A h := by simp

/-- **9.15**: the chain rule. The local form makes the book's open-domain
hypotheses unnecessary once the two pointwise derivatives are supplied. -/
theorem pma9_15 {n m k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {g : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x)
    (hg : pma9_11 g B (f x)) : pma9_11 (g ∘ f) (B.comp A) x := hg.comp x hf

/-- The standard coordinate vectors used in 9.16–9.18. -/
def pma9_coordinate (n : ℕ) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.basisFun (Fin n) ℝ j

/-- **9.16**, (24): components determine a vector. -/
theorem pma9_16_components {m : ℕ} (y : EuclideanSpace ℝ (Fin m)) :
    y = ∑ i, y i • pma9_coordinate m i := by
  simpa [pma9_coordinate] using ((EuclideanSpace.basisFun (Fin m) ℝ).sum_repr y).symm

/-- **9.16**, (25)–(26): the specified partial derivative is a one-dimensional derivative. -/
def pma9_16_hasPartial {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) (j : Fin n) (d : ℝ) : Prop :=
  HasLineDerivAt ℝ (fun y => f y i) d x (pma9_coordinate n j)

/-- **9.16**: the value of the partial derivative, when it exists. -/
def pma9_16_partial {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin m) (j : Fin n) : ℝ :=
  lineDeriv ℝ (fun y => f y i) x (pma9_coordinate n j)

/-- **9.16**, the defining limit of the partial derivative. -/
theorem pma9_16_iff_limit {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} {i : Fin m} {j : Fin n} {d : ℝ} :
    pma9_16_hasPartial f x i j d ↔
      Tendsto (fun t : ℝ => (f (x + t • pma9_coordinate n j) i - f x i) / t)
        (𝓝[≠] 0) (𝓝 d) := by
  simpa [pma9_16_hasPartial, div_eq_inv_mul] using
    (hasLineDerivAt_iff_tendsto_slope_zero (𝕜 := ℝ) (f := fun y => f y i)
      (x := x) (v := pma9_coordinate n j) (f' := d))

/-- **9.17**: differentiability implies existence of all partial derivatives. -/
theorem pma9_17 {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x) (i : Fin m) (j : Fin n) :
    pma9_16_hasPartial f x i j (A (pma9_coordinate n j) i) := by
  exact ((PiLp.proj 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp x hf).hasLineDerivAt _

/-- **9.17**: the partial derivatives are the entries of the derivative matrix. -/
theorem pma9_17_entries {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x) (i : Fin m) (j : Fin n) :
    pma9_16_partial f x i j = A (pma9_coordinate n j) i :=
  (pma9_17 hf i j).lineDeriv

/-- **9.17**, (27): each derivative column is reconstructed from the partials. -/
theorem pma9_17_column {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x) (j : Fin n) :
    A (pma9_coordinate n j) = ∑ i, pma9_16_partial f x i j • pma9_coordinate m i := by
  simp_rw [pma9_17_entries hf]
  exact pma9_16_components _

/-- **9.17**, (28): the vector-valued directional difference quotient.
Generalization: arbitrary directions include the standard coordinate directions
used in the printed formula. -/
theorem pma9_17_directional_limit {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x)
    (v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ => t⁻¹ • (f (x + t • v) - f x)) (𝓝[≠] 0) (𝓝 (A v)) :=
  (hf.hasLineDerivAt v).tendsto_slope_zero

/-- **9.17**, (30): the derivative applied to an arbitrary increment. -/
theorem pma9_17_apply {n m : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    {x : EuclideanSpace ℝ (Fin n)} (hf : pma9_11 f A x)
    (h : EuclideanSpace ℝ (Fin n)) :
    A h = ∑ i, (∑ j, pma9_16_partial f x i j * h j) • pma9_coordinate m i := by
  calc
    A h = ∑ i, (A h) i • pma9_coordinate m i := pma9_16_components _
    _ = ∑ i, (∑ j, pma9_16_partial f x i j * h j) • pma9_coordinate m i := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg (fun c : ℝ => c • pma9_coordinate m i)
      conv_lhs => rw [pma9_16_components h]
      simp [map_sum, pma9_17_entries hf, mul_comm]

/-- **9.18**, (32): the derivative of a real function along a differentiable curve.
The pointwise version applies at every point of the book's parameter interval. -/
theorem pma9_18_chain {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {t : ℝ} (hf : HasFDerivAt f A (γ t)) (hγ : HasDerivAt γ v t) :
    HasDerivAt (f ∘ γ) (A v) t := hf.comp_hasDerivAt t hγ

/-- **9.18**: scalar-valued partial derivatives. -/
def pma9_18_partial {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) : ℝ :=
  lineDeriv ℝ f x (pma9_coordinate n j)

/-- **9.18**, (34): the gradient vector. -/
def pma9_18_gradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun j => pma9_18_partial f x j)

theorem pma9_18_partial_eq {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f A x) (j : Fin n) :
    pma9_18_partial f x j = A (pma9_coordinate n j) :=
  (hf.hasLineDerivAt _).lineDeriv

/-- The coordinate formula for a scalar-valued differential. -/
theorem pma9_18_apply {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f A x) (v : EuclideanSpace ℝ (Fin n)) :
    A v = ∑ j, pma9_18_partial f x j * v j := by
  conv_lhs => rw [pma9_16_components v]
  simp [map_sum, pma9_18_partial_eq hf, mul_comm]

/-- **9.18**, (33): the coordinate form of the chain rule. -/
theorem pma9_18_chain_coordinates {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {t : ℝ} (hf : HasFDerivAt f A (γ t)) (hγ : HasDerivAt γ v t) :
    HasDerivAt (f ∘ γ) (∑ j, pma9_18_partial f (γ t) j * v j) t := by
  rw [← pma9_18_apply hf v]
  exact pma9_18_chain hf hγ

/-- **9.18**, (35): the coordinates of a curve derivative are the component derivatives. -/
theorem pma9_18_curve_components {n : ℕ} {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin n)} {t : ℝ} (hγ : HasDerivAt γ v t) (j : Fin n) :
    HasDerivAt (fun s => γ s j) (v j) t :=
  (PiLp.proj 2 (fun _ : Fin n => ℝ) j).hasFDerivAt.comp_hasDerivAt t hγ

/-- **9.18**, (34): the gradient in standard basis notation. -/
theorem pma9_18_gradient_sum {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    pma9_18_gradient f x = ∑ j, pma9_18_partial f x j • pma9_coordinate n j :=
  pma9_16_components _

/-- The differential is the inner product with the gradient. -/
theorem pma9_18_gradient_inner {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f A x) (v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (pma9_18_gradient f x) v = A v := by
  rw [pma9_18_apply hf v]
  simp [PiLp.inner_apply, pma9_18_gradient, mul_comm]

/-- **9.18**, (36): differentiation along a curve is the gradient dotted with velocity. -/
theorem pma9_18_chain_gradient {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {γ : ℝ → EuclideanSpace ℝ (Fin n)}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {v : EuclideanSpace ℝ (Fin n)}
    {t : ℝ} (hf : HasFDerivAt f A (γ t)) (hγ : HasDerivAt γ v t) :
    HasDerivAt (f ∘ γ) (inner ℝ (pma9_18_gradient f (γ t)) v) t := by
  rw [pma9_18_gradient_inner hf]
  exact pma9_18_chain hf hγ

/-- **9.18**, (37): the line through `x` with velocity `u` has derivative `u`. -/
theorem pma9_18_line {n : ℕ} (x u : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • u) u t := by
  convert! (hasDerivAt_const t x).add ((hasDerivAt_id' t).smul_const u) using 1
  simp only [zero_add, one_smul]

/-- **9.18**, (38)–(39): the directional derivative is the gradient dotted with direction.
Generalization: the formula holds for arbitrary directions, not only unit vectors. -/
theorem pma9_18_directional {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f A x) (u : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ => (f (x + t • u) - f x) / t) (𝓝[≠] 0)
      (𝓝 (inner ℝ (pma9_18_gradient f x) u)) := by
  rw [pma9_18_gradient_inner hf]
  simpa [div_eq_inv_mul] using (hf.hasLineDerivAt u).tendsto_slope_zero

/-- **9.18**, (40): a directional derivative is the weighted sum of partial derivatives. -/
theorem pma9_18_directional_coordinates {n : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f A x) (u : EuclideanSpace ℝ (Fin n)) :
    lineDeriv ℝ f x u = ∑ j, pma9_18_partial f x j * u j := by
  rw [(hf.hasLineDerivAt u).lineDeriv]
  exact pma9_18_apply hf u

/-- **9.18**: the maximum directional derivative is achieved in the positive
gradient direction when the gradient is nonzero. -/
theorem pma9_18_maximum {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {A : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ} {x : EuclideanSpace ℝ (Fin n)}
    (hf : HasFDerivAt f A x) (hg : pma9_18_gradient f x ≠ 0) :
    let g := pma9_18_gradient f x
    ‖‖g‖⁻¹ • g‖ = 1 ∧
      lineDeriv ℝ f x (‖g‖⁻¹ • g) = ‖g‖ ∧
      ∀ u : EuclideanSpace ℝ (Fin n), ‖u‖ = 1 → lineDeriv ℝ f x u ≤ ‖g‖ := by
  dsimp only
  refine ⟨norm_smul_inv_norm hg, ?_, ?_⟩
  · rw [(hf.hasLineDerivAt _).lineDeriv, ← pma9_18_gradient_inner hf,
      inner_smul_right, real_inner_self_eq_norm_mul_norm]
    have hn : ‖pma9_18_gradient f x‖ ≠ 0 := norm_ne_zero_iff.mpr hg
    simp [hn]
  · intro u hu
    rw [(hf.hasLineDerivAt u).lineDeriv, ← pma9_18_gradient_inner hf]
    simpa [hu] using real_inner_le_norm (pma9_18_gradient f x) u

end Rudin.PMA.Chapter09
