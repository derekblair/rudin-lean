import Rudin.PMA.Chapter09.FirstHalf
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# PMA 9.39–9.41: higher partial derivatives

Coordinate derivatives use one-variable derivatives of coordinate slices. In particular,
no total differentiability hypothesis is substituted for the partial derivative hypotheses
in the rectangle mean value theorem.
-/

noncomputable section
open Set Filter Topology

namespace Rudin.PMA.Chapter09

/-- PMA 9.39: the coordinate partial derivative, defined by a coordinate slice. -/
def coordinatePartial {n : ℕ} (i : Fin n) (f : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  deriv (fun t => f (Function.update x i t)) (x i)

/-- PMA 9.39: `Dᵢⱼ f = Dᵢ (Dⱼ f)`. -/
def pma9_39_secondPartial {n : ℕ} (i j : Fin n) (f : (Fin n → ℝ) → ℝ) :
    (Fin n → ℝ) → ℝ := coordinatePartial i (coordinatePartial j f)

/-- PMA 9.39: twice continuously differentiable scalar functions on an open set.
Existence of the partial derivatives is recorded explicitly since Lean's `deriv` is total. -/
def pma9_39 {n : ℕ} (f : (Fin n → ℝ) → ℝ) (E : Set (Fin n → ℝ)) : Prop :=
  IsOpen E ∧
  (∀ i x, x ∈ E → DifferentiableAt ℝ (fun t => f (Function.update x i t)) (x i)) ∧
  (∀ i, DifferentiableOn ℝ (coordinatePartial i f) E) ∧
  ∀ i j, ContinuousOn (pma9_39_secondPartial i j f) E

/-- PMA 9.39: the componentwise extension to mappings. -/
def pma9_39_mapping {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ))
    (E : Set (Fin n → ℝ)) : Prop := IsOpen E ∧ ∀ j, pma9_39 (fun x => f x j) E

/-- The first-coordinate derivative for a two-variable real function. -/
def partialX (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => f (x, p.2)) p.1

/-- The second-coordinate derivative for a two-variable real function. -/
def partialY (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => f (p.1, y)) p.2

/-- The alternating sum at the corners of the rectangle with opposite corners
`(a,b)` and `(a+h,b+k)`. -/
def rectangleDifference (f : ℝ × ℝ → ℝ) (a b h k : ℝ) : ℝ :=
  f (a + h, b + k) - f (a + h, b) - f (a, b + k) + f (a, b)

/-- The mean value theorem on an unordered nondegenerate interval. -/
theorem exists_deriv_unordered {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hd : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x) :
    ∃ x ∈ uIoo a b, f b - f a = (b - a) * f' x := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hd' : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x := by
      simpa [uIcc_of_le hab.le] using hd
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hab
      (fun x hx => (hd' x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd' x ⟨hx.1.le, hx.2.le⟩)
    refine ⟨x, by simpa [uIoo, min_eq_left hab.le, max_eq_right hab.le] using hx, ?_⟩
    exact (eq_div_iff (sub_ne_zero.mpr hab.ne')).mp he |>.symm.trans (mul_comm _ _)
  · have hd' : ∀ x ∈ Icc b a, HasDerivAt f (f' x) x := by
      simpa [uIcc_of_ge hba.le] using hd
    obtain ⟨x, hx, he⟩ := exists_hasDerivAt_eq_slope f f' hba
      (fun x hx => (hd' x hx).continuousAt.continuousWithinAt)
      (fun x hx => hd' x ⟨hx.1.le, hx.2.le⟩)
    refine ⟨x, by simpa [uIoo, min_eq_right hba.le, max_eq_left hba.le] using hx, ?_⟩
    have he' := (eq_div_iff (sub_ne_zero.mpr hba.ne')).mp he
    nlinarith

/-- PMA 9.40: the rectangle mean value theorem. The open domain is retained in
the statement, and the two derivative assumptions are exactly slice derivatives. -/
theorem pma9_40 (f : ℝ × ℝ → ℝ) (E : Set (ℝ × ℝ)) (_hE : IsOpen E)
    (hX : ∀ p ∈ E, DifferentiableAt ℝ (fun x => f (x, p.2)) p.1)
    (hYX : ∀ p ∈ E, DifferentiableAt ℝ (fun y => partialX f (p.1, y)) p.2)
    (a b h k : ℝ) (hh : h ≠ 0) (hk : k ≠ 0)
    (hQ : uIcc a (a + h) ×ˢ uIcc b (b + k) ⊆ E) :
    ∃ x ∈ uIoo a (a + h), ∃ y ∈ uIoo b (b + k),
      rectangleDifference f a b h k = h * k * partialY (partialX f) (x, y) := by
  have hx0 : a ≠ a + h := by intro he; apply hh; linarith
  have hy0 : b ≠ b + k := by intro he; apply hk; linarith
  have hx (x : ℝ) (hxx : x ∈ uIcc a (a + h)) (y : ℝ)
      (hyy : y ∈ uIcc b (b + k)) :
      HasDerivAt (fun t => f (t, y)) (partialX f (x, y)) x :=
    (hX (x,y) (hQ ⟨hxx, hyy⟩)).hasDerivAt
  obtain ⟨x, hxi, he⟩ := exists_deriv_unordered (f := fun t => f (t, b+k) - f (t,b))
    (f' := fun t => partialX f (t,b+k) - partialX f (t,b)) hx0
    (fun x hxx => (hx x hxx (b+k) right_mem_uIcc).sub (hx x hxx b left_mem_uIcc))
  obtain ⟨y, hyi, he'⟩ := exists_deriv_unordered (f := fun y => partialX f (x,y))
    (f' := fun y => partialY (partialX f) (x,y)) hy0
    (fun y hyy => (hYX (x,y) (hQ ⟨Ioo_subset_Icc_self hxi, hyy⟩)).hasDerivAt)
  refine ⟨x, hxi, y, hyi, ?_⟩
  dsimp [rectangleDifference]
  rw [show a+h-a=h by ring] at he
  rw [show b+k-b=k by ring] at he'
  rw [he'] at he
  convert he using 1 <;> ring

/-- A corner rectangle close to its base point is contained in the corresponding ball. -/
theorem rectangle_subset_ball {a b h k r : ℝ} (hh : |h| < r) (hk : |k| < r) :
    uIcc a (a+h) ×ˢ uIcc b (b+k) ⊆ Metric.ball (a,b) r := by
  rintro ⟨x,y⟩ ⟨hx,hy⟩
  have hx' := abs_sub_left_of_mem_uIcc hx
  have hy' := abs_sub_left_of_mem_uIcc hy
  simp only [add_sub_cancel_left] at hx' hy'
  change max (dist x a) (dist y b) < r
  simpa only [Real.dist_eq] using max_lt (hx'.trans_lt hh) (hy'.trans_lt hk)

/-- PMA 9.41, with its weak hypotheses: only `D₂D₁f` is assumed continuous,
and only at the point in question. Existence of `D₁D₂f` is a conclusion. -/
theorem pma9_41 (f : ℝ × ℝ → ℝ) (E : Set (ℝ × ℝ)) (hE : IsOpen E)
    (hX : ∀ p ∈ E, DifferentiableAt ℝ (fun x => f (x, p.2)) p.1)
    (hYX : ∀ p ∈ E, DifferentiableAt ℝ (fun y => partialX f (p.1, y)) p.2)
    (hY : ∀ p ∈ E, DifferentiableAt ℝ (fun y => f (p.1, y)) p.2)
    (a b : ℝ) (hab : (a,b) ∈ E) (hc : ContinuousAt (partialY (partialX f)) (a,b)) :
    HasDerivAt (fun x => partialY f (x,b)) (partialY (partialX f) (a,b)) a := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨r, hr, hrE⟩ := Metric.isOpen_iff.mp hE (a,b) hab
  obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (by positivity)
  let ρ := min r δ
  have hρ : 0 < ρ := lt_min hr hδ
  have hsmall : ∀ᶠ h : ℝ in 𝓝[≠] 0, |h| < ρ := by
    exact (show ∀ᶠ h : ℝ in 𝓝 0, |h| < ρ from by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with t ht
      simpa [Metric.mem_ball, Real.dist_eq] using ht).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with h hh hh0
  have hne : h ≠ 0 := by simpa using hh0
  have hbase : (a+h,b) ∈ E := by
    apply hrE
    change max (dist (a+h) a) (dist b b) < r
    simp only [Real.dist_eq, add_sub_cancel_left, sub_self, abs_zero, max_eq_left (abs_nonneg h)]
    exact hh.trans_le (min_le_left _ _)
  have ht₁ := (hY (a+h,b) hbase).hasDerivAt.tendsto_slope_zero
  have ht₀ := (hY (a,b) hab).hasDerivAt.tendsto_slope_zero
  have hlim : Tendsto
      (fun k : ℝ => ((f (a+h,b+k)-f (a+h,b))/k - (f (a,b+k)-f (a,b))/k)/h)
      (𝓝[≠] 0) (𝓝 ((partialY f (a+h,b)-partialY f (a,b))/h)) := by
    simpa only [partialY, smul_eq_mul, div_eq_mul_inv, mul_comm] using (ht₁.sub ht₀).div_const h
  have hbnd : ∀ᶠ k : ℝ in 𝓝[≠] 0,
      |((f (a+h,b+k)-f (a+h,b))/k - (f (a,b+k)-f (a,b))/k)/h -
        partialY (partialX f) (a,b)| ≤ ε/2 := by
    filter_upwards [hsmall, self_mem_nhdsWithin] with k hk hk0
    have kne : k ≠ 0 := by simpa using hk0
    have hQ : uIcc a (a+h) ×ˢ uIcc b (b+k) ⊆ E :=
      (rectangle_subset_ball (hh.trans_le (min_le_left _ _))
        (hk.trans_le (min_le_left _ _))).trans hrE
    obtain ⟨x,hxi,y,hyi,he⟩ := pma9_40 f E hE hX hYX a b h k hne kne hQ
    have hxy := rectangle_subset_ball (a := a) (b := b) (hh.trans_le (min_le_right _ _))
      (hk.trans_le (min_le_right _ _)) (show (x,y) ∈ uIcc a (a+h) ×ˢ uIcc b (b+k) from
        ⟨Ioo_subset_Icc_self hxi, Ioo_subset_Icc_self hyi⟩)
    have hbound := hδc (show dist (x,y) (a,b) < δ from hxy)
    have heq : ((f (a+h,b+k)-f (a+h,b))/k - (f (a,b+k)-f (a,b))/k)/h =
        partialY (partialX f) (x,y) := by
      field_simp [hne, kne]
      dsimp [rectangleDifference] at he
      nlinarith [he]
    rw [heq]
    exact (by simpa only [Real.dist_eq] using hbound.le)
  have hb := le_of_tendsto (hlim.sub_const (partialY (partialX f) (a,b))).abs hbnd
  simpa only [Real.dist_eq, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    hb.trans_lt (half_lt_self hε)

/-- PMA 9.41 corollary: the two mixed partials agree on the open domain when
`D₂D₁ f` is continuous there. This includes the printed `C²` corollary. -/
theorem pma9_41_corollary (f : ℝ × ℝ → ℝ) (E : Set (ℝ × ℝ)) (hE : IsOpen E)
    (hX : ∀ p ∈ E, DifferentiableAt ℝ (fun x => f (x, p.2)) p.1)
    (hYX : ∀ p ∈ E, DifferentiableAt ℝ (fun y => partialX f (p.1, y)) p.2)
    (hY : ∀ p ∈ E, DifferentiableAt ℝ (fun y => f (p.1, y)) p.2)
    (hc : ContinuousOn (partialY (partialX f)) E) (p : ℝ × ℝ) (hp : p ∈ E) :
    partialX (partialY f) p = partialY (partialX f) p :=
  (pma9_41 f E hE hX hYX hY p.1 p.2 hp (hc.continuousAt (hE.mem_nhds hp))).deriv

end Rudin.PMA.Chapter09

namespace Rudin.PMA.Chapter09

/-- The coordinate identification used to compare 9.39 with the two-variable
statements 9.40–9.41. -/
def pairCoordinates (p : ℝ × ℝ) : Fin 2 → ℝ := ![p.1, p.2]

lemma pairCoordinates_update_first (p : ℝ × ℝ) (t : ℝ) :
    Function.update (pairCoordinates p) 0 t = pairCoordinates (t, p.2) := by
  ext i
  fin_cases i <;> simp [pairCoordinates]

lemma pairCoordinates_update_second (p : ℝ × ℝ) (t : ℝ) :
    Function.update (pairCoordinates p) 1 t = pairCoordinates (p.1, t) := by
  ext i
  fin_cases i <;> simp [pairCoordinates]

lemma partialX_pairCoordinates (f : (Fin 2 → ℝ) → ℝ) :
    partialX (fun p => f (pairCoordinates p)) =
      fun p => coordinatePartial 0 f (pairCoordinates p) := by
  funext p
  simp only [partialX, coordinatePartial, pairCoordinates_update_first]
  rfl

lemma partialY_pairCoordinates (f : (Fin 2 → ℝ) → ℝ) :
    partialY (fun p => f (pairCoordinates p)) =
      fun p => coordinatePartial 1 f (pairCoordinates p) := by
  funext p
  simp only [partialY, coordinatePartial, pairCoordinates_update_second]
  rfl

/-- The printed C² corollary of 9.41 with the exact native definition 9.39 as
hypothesis, using the equivalence of pair and two-coordinate representations. -/
theorem pma9_41_of_pma9_39 {f : (Fin 2 → ℝ) → ℝ} {E : Set (Fin 2 → ℝ)}
    (hf : pma9_39 f E) (x : Fin 2 → ℝ) (hx : x ∈ E) :
    pma9_39_secondPartial 0 1 f x = pma9_39_secondPartial 1 0 f x := by
  let g : ℝ × ℝ → ℝ := fun p => f (pairCoordinates p)
  let U : Set (ℝ × ℝ) := pairCoordinates ⁻¹' E
  have hcont : Continuous pairCoordinates := by unfold pairCoordinates; fun_prop
  have hU : IsOpen U := hf.1.preimage hcont
  have hX : ∀ p ∈ U, DifferentiableAt ℝ (fun t => g (t, p.2)) p.1 := by
    intro p hp
    have hd := hf.2.1 0 (pairCoordinates p) hp
    simp only [pairCoordinates_update_first] at hd
    exact hd
  have hY : ∀ p ∈ U, DifferentiableAt ℝ (fun t => g (p.1, t)) p.2 := by
    intro p hp
    have hd := hf.2.1 1 (pairCoordinates p) hp
    simp only [pairCoordinates_update_second] at hd
    exact hd
  have hYX : ∀ p ∈ U,
      DifferentiableAt ℝ (fun t => partialX g (p.1, t)) p.2 := by
    intro p hp
    have hd := (hf.2.2.1 0 (pairCoordinates p) hp).differentiableAt
      (hf.1.mem_nhds hp)
    have hp' : DifferentiableAt ℝ (fun t => pairCoordinates (p.1, t)) p.2 := by
      apply differentiableAt_pi.mpr
      intro i
      fin_cases i <;> simp only [pairCoordinates, Matrix.cons_val_zero, Matrix.cons_val_one]
      · exact differentiableAt_const _
      · exact differentiableAt_id
    rw [show partialX g = fun p => coordinatePartial 0 f (pairCoordinates p) from
      partialX_pairCoordinates f]
    convert! hd.comp p.2 hp' using 1
  have heqYX : partialY (partialX g) =
      fun p => pma9_39_secondPartial 1 0 f (pairCoordinates p) := by
    rw [show partialX g = fun p => coordinatePartial 0 f (pairCoordinates p) from
      partialX_pairCoordinates f]
    exact partialY_pairCoordinates (coordinatePartial 0 f)
  have heqXY : partialX (partialY g) =
      fun p => pma9_39_secondPartial 0 1 f (pairCoordinates p) := by
    rw [show partialY g = fun p => coordinatePartial 1 f (pairCoordinates p) from
      partialY_pairCoordinates f]
    exact partialX_pairCoordinates (coordinatePartial 1 f)
  have hc : ContinuousOn (partialY (partialX g)) U := by
    rw [heqYX]
    exact (hf.2.2.2 1 0).comp hcont.continuousOn (fun _ hp => hp)
  have hpc : pairCoordinates (x 0, x 1) = x := by
    ext i
    fin_cases i <;> simp [pairCoordinates]
  have hp : (x 0, x 1) ∈ U := by change pairCoordinates (x 0, x 1) ∈ E; rwa [hpc]
  have h := pma9_41_corollary g U hU hX hYX hY hc (x 0, x 1) hp
  simpa only [heqXY, heqYX, hpc] using h

end Rudin.PMA.Chapter09
