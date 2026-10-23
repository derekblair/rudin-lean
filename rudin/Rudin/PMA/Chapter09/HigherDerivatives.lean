import Rudin.PMA.Chapter09.PartialExamples

/-! # PMA 9.39–9.41: second partials and the source's weak Schwarz theorem.

The principal symmetry theorem assumes continuity of just `D₂(D₁ f)` at
the one point and derives the missing opposite mixed partial there.
-/

noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter09

/-- The order is `Dᵢ(Dⱼ f)`, matching the source's subscript order. -/
def secondCoordinatePartial {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i j : Fin n) : ℝ :=
  coordinatePartial (fun y => coordinatePartial f y j) x i

def ScalarC2On {n : ℕ} (f : Euclidean n → ℝ) (E : Set (Euclidean n)) : Prop :=
  (∀ x ∈ E, ∀ j, ∃ d, HasCoordinatePartial f x j d) ∧
  (∀ x ∈ E, ∀ i j, ∃ d,
    HasCoordinatePartial (fun y => coordinatePartial f y j) x i d) ∧
  ∀ i j, ContinuousOn (fun x => secondCoordinatePartial f x i j) E

def ComponentC2On {n m : ℕ} (f : Euclidean n → Euclidean m)
    (E : Set (Euclidean n)) : Prop :=
  ∀ i, ScalarC2On (fun x => f x i) E

def planePoint (a b : ℝ) : Euclidean 2 :=
  a • coordinateVector 2 0 + b • coordinateVector 2 1

def coordinateRectangle (a b h k : ℝ) : Set (Euclidean 2) :=
  {p | p 0 ∈ uIcc a (a + h) ∧ p 1 ∈ uIcc b (b + k)}

def pma9_39_contract : Prop :=
  (∀ n (f : Euclidean n → ℝ) x i j,
    secondCoordinatePartial f x i j =
      coordinatePartial (fun y => coordinatePartial f y j) x i) ∧
  (∀ n m (f : Euclidean n → Euclidean m) E,
    ComponentC2On f E ↔ ∀ i, ScalarC2On (fun x => f x i) E) ∧
  (∃ (f : Euclidean 2 → ℝ) (a b : ℝ),
    (∀ x j, ∃ d, HasCoordinatePartial f x j d) ∧
    HasCoordinatePartial (fun y => coordinatePartial f y 0) 0 1 a ∧
    HasCoordinatePartial (fun y => coordinatePartial f y 1) 0 0 b ∧ a ≠ b)

def pma9_40_contract : Prop :=
  ∀ (f : Euclidean 2 → ℝ) (E : Set (Euclidean 2)) a b h k,
    IsOpen E → h ≠ 0 → k ≠ 0 → coordinateRectangle a b h k ⊆ E →
    (∀ p ∈ E, ∃ d, HasCoordinatePartial f p 0 d) →
    (∀ p ∈ E, ∃ d, HasCoordinatePartial (fun q => coordinatePartial f q 0) p 1 d) →
    ∃ x ∈ uIoo a (a + h), ∃ y ∈ uIoo b (b + k),
      f (planePoint (a + h) (b + k)) - f (planePoint (a + h) b) -
        f (planePoint a (b + k)) + f (planePoint a b) =
          h * k * secondCoordinatePartial f (planePoint x y) 1 0

def pma9_41_contract : Prop :=
  (∀ (f : Euclidean 2 → ℝ) (E : Set (Euclidean 2)) (p : Euclidean 2),
    IsOpen E → p ∈ E →
    (∀ q ∈ E, ∃ d, HasCoordinatePartial f q 0 d) →
    (∀ q ∈ E, ∃ d, HasCoordinatePartial (fun z => coordinatePartial f z 0) q 1 d) →
    (∀ q ∈ E, ∃ d, HasCoordinatePartial f q 1 d) →
    ContinuousAt (fun q => secondCoordinatePartial f q 1 0) p →
    HasCoordinatePartial (fun q => coordinatePartial f q 1) p 0
      (secondCoordinatePartial f p 1 0)) ∧
  (∀ n (f : Euclidean n → ℝ) (E : Set (Euclidean n)), IsOpen E → ScalarC2On f E →
    ∀ p ∈ E, ∀ i j, secondCoordinatePartial f p i j = secondCoordinatePartial f p j i)

@[simp] theorem planePoint_zero (a b : ℝ) : planePoint a b 0 = a := by
  simp [planePoint, coordinateVector, EuclideanSpace.basisFun_apply]

@[simp] theorem planePoint_one (a b : ℝ) : planePoint a b 1 = b := by
  simp [planePoint, coordinateVector, EuclideanSpace.basisFun_apply]

theorem planePoint_add_first (a b t : ℝ) :
    planePoint (a + t) b = planePoint a b + t • coordinateVector 2 0 := by
  simp only [planePoint, add_smul]
  abel

theorem planePoint_add_second (a b t : ℝ) :
    planePoint a (b + t) = planePoint a b + t • coordinateVector 2 1 := by
  simp only [planePoint, add_smul]
  abel

theorem hasCoordinatePartial_first_iff (f : Euclidean 2 → ℝ) (a b d : ℝ) :
    HasCoordinatePartial f (planePoint a b) 0 d ↔
      HasDerivAt (fun t => f (planePoint t b)) d a := by
  simp only [HasCoordinatePartial, hasDerivAt_iff_tendsto_slope_zero,
    zero_add, zero_smul, add_zero, planePoint_add_first]

theorem hasCoordinatePartial_second_iff (f : Euclidean 2 → ℝ) (a b d : ℝ) :
    HasCoordinatePartial f (planePoint a b) 1 d ↔
      HasDerivAt (fun t => f (planePoint a t)) d b := by
  simp only [HasCoordinatePartial, hasDerivAt_iff_tendsto_slope_zero,
    zero_add, zero_smul, add_zero, planePoint_add_second]

def unequalMixedExample (x : Euclidean 2) : ℝ :=
  discontinuousPartialsExample x * ((x 0) ^ 2 - (x 1) ^ 2)

theorem unequalMixedExample_partials_zero (j : Fin 2) :
    HasCoordinatePartial unequalMixedExample 0 j 0 := by
  have he : (fun t : ℝ => unequalMixedExample (t • coordinateVector 2 j)) = (fun _ => 0) := by
    funext t
    have h := congrFun (partialExamples_axis_zero j).1 t
    simp only [unequalMixedExample, h, zero_mul]
  simpa only [HasCoordinatePartial, zero_add, he] using (hasDerivAt_const 0 (0 : ℝ))

theorem unequalMixedExample_partials_everywhere (x : Euclidean 2) (j : Fin 2) :
    ∃ d, HasCoordinatePartial unequalMixedExample x j d := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0, unequalMixedExample_partials_zero j⟩
  · have h0 : DifferentiableAt ℝ (fun y : Euclidean 2 => y 0) x :=
      (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).differentiableAt
    have h1 : DifferentiableAt ℝ (fun y : Euclidean 2 => y 1) x :=
      (EuclideanSpace.proj 1 : Euclidean 2 →L[ℝ] ℝ).differentiableAt
    have hd : DifferentiableAt ℝ unequalMixedExample x :=
      (partialExamples_differentiable_off_zero hx).1.mul ((h0.pow 2).sub (h1.pow 2))
    exact ⟨_, hasCoordinatePartial_of_hasFDerivAt hd.hasFDerivAt j⟩

theorem unequalMixedExample_plane (a b : ℝ) :
    unequalMixedExample (planePoint a b) = a * b * (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) := by
  have hn : ‖planePoint a b‖ ^ 2 = a ^ 2 + b ^ 2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  simp only [unequalMixedExample, discontinuousPartialsExample, planePoint_zero, planePoint_one, hn]
  ring

theorem unequalMixedExample_first_axis (t : ℝ) :
    coordinatePartial unequalMixedExample (planePoint 0 t) 0 = -t := by
  by_cases ht : t = 0
  · subst t
    simpa [planePoint, coordinatePartial] using (unequalMixedExample_partials_zero 0).deriv
  · have hnum : HasDerivAt (fun u : ℝ => u * t * (u ^ 2 - t ^ 2)) (-(t ^ 3)) 0 := by
      convert ((hasDerivAt_id 0).mul_const t).mul ((hasDerivAt_pow 2 0).sub_const (t ^ 2)) using 1
      · ext u
        simp only [Pi.mul_apply, id_eq]
      · simp only [id_eq]
        ring
    have hden : HasDerivAt (fun u : ℝ => u ^ 2 + t ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).add_const (t ^ 2)
    have hd : HasDerivAt (fun u => unequalMixedExample (planePoint u t)) (-t) 0 := by
      simp_rw [unequalMixedExample_plane]
      convert hnum.div hden (by simpa using pow_ne_zero 2 ht) using 1
      field_simp
      ring
    exact ((hasCoordinatePartial_first_iff _ 0 t (-t)).mpr hd).deriv

theorem unequalMixedExample_second_axis (t : ℝ) :
    coordinatePartial unequalMixedExample (planePoint t 0) 1 = t := by
  by_cases ht : t = 0
  · subst t
    simpa [planePoint, coordinatePartial] using (unequalMixedExample_partials_zero 1).deriv
  · have hnum : HasDerivAt (fun u : ℝ => t * u * (t ^ 2 - u ^ 2)) (t ^ 3) 0 := by
      convert ((hasDerivAt_id 0).const_mul t).mul ((hasDerivAt_pow 2 0).const_sub (t ^ 2)) using 1
      · ext u
        simp only [Pi.mul_apply, id_eq]
      · simp only [id_eq]
        ring
    have hden : HasDerivAt (fun u : ℝ => t ^ 2 + u ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℝ)).const_add (t ^ 2)
    have hd : HasDerivAt (fun u => unequalMixedExample (planePoint t u)) t 0 := by
      simp_rw [unequalMixedExample_plane]
      convert hnum.div hden (by simpa using pow_ne_zero 2 ht) using 1
      field_simp
      ring
    exact ((hasCoordinatePartial_second_iff _ t 0 t).mpr hd).deriv

theorem pma9_39 : pma9_39_contract := by
  refine ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ => Iff.rfl,
    unequalMixedExample, -1, 1, unequalMixedExample_partials_everywhere, ?_, ?_, by norm_num⟩
  · change HasDerivAt (fun t : ℝ => coordinatePartial unequalMixedExample
      (0 + t • coordinateVector 2 1) 0) (-1) 0
    have he : (fun t : ℝ => coordinatePartial unequalMixedExample
        (0 + t • coordinateVector 2 1) 0) = fun t => -t := by
      funext t
      simpa [planePoint] using unequalMixedExample_first_axis t
    rw [he]
    exact (hasDerivAt_id 0).neg
  · change HasDerivAt (fun t : ℝ => coordinatePartial unequalMixedExample
      (0 + t • coordinateVector 2 0) 1) 1 0
    have he : (fun t : ℝ => coordinatePartial unequalMixedExample
        (0 + t • coordinateVector 2 0) 1) = fun t => t := by
      funext t
      simpa [planePoint] using unequalMixedExample_second_axis t
    rw [he]
    exact hasDerivAt_id 0

theorem exists_increment_eq_deriv_mul {g g' : ℝ → ℝ} {a b : ℝ} (hab : a ≠ b)
    (hg : ∀ t ∈ uIcc a b, HasDerivAt g (g' t) t) :
    ∃ t ∈ uIoo a b, g b - g a = (b - a) * g' t := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hc : ContinuousOn g (Icc a b) := by
      intro t ht
      exact (hg t (by simpa [uIcc_of_le hab.le] using ht)).continuousAt.continuousWithinAt
    obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope g g' hab hc
      (fun t ht => hg t (by simpa [uIcc_of_le hab.le] using Ioo_subset_Icc_self ht))
    refine ⟨t, by simpa [uIoo_of_le hab.le] using ht, ?_⟩
    have hn : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    exact ((eq_div_iff hn).mp he).symm.trans (mul_comm _ _)
  · have hc : ContinuousOn g (Icc b a) := by
      intro t ht
      exact (hg t (by simpa [uIcc_of_ge hba.le] using ht)).continuousAt.continuousWithinAt
    obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope g g' hba hc
      (fun t ht => hg t (by simpa [uIcc_of_ge hba.le] using Ioo_subset_Icc_self ht))
    refine ⟨t, by simpa [uIoo_of_ge hba.le] using ht, ?_⟩
    have hn : a - b ≠ 0 := sub_ne_zero.mpr hba.ne'
    have he' := (eq_div_iff hn).mp he
    nlinarith

theorem pma9_40 : pma9_40_contract := by
  intro f E a b h k _ hh hk hrect h1 h21
  have hmem : ∀ x ∈ uIcc a (a + h), ∀ y ∈ uIcc b (b + k), planePoint x y ∈ E := by
    intro x hx y hy
    exact hrect (by simpa [coordinateRectangle] using And.intro hx hy)
  have hd1 : ∀ x ∈ uIcc a (a + h), ∀ y ∈ uIcc b (b + k),
      HasDerivAt (fun t => f (planePoint t y)) (coordinatePartial f (planePoint x y) 0) x := by
    intro x hx y hy
    obtain ⟨d, hd⟩ := h1 (planePoint x y) (hmem x hx y hy)
    have he : coordinatePartial f (planePoint x y) 0 = d := hd.deriv
    rw [he]
    exact (hasCoordinatePartial_first_iff f x y d).mp hd
  have hd21 : ∀ x ∈ uIcc a (a + h), ∀ y ∈ uIcc b (b + k),
      HasDerivAt (fun t => coordinatePartial f (planePoint x t) 0)
        (secondCoordinatePartial f (planePoint x y) 1 0) y := by
    intro x hx y hy
    obtain ⟨d, hd⟩ := h21 (planePoint x y) (hmem x hx y hy)
    have he : secondCoordinatePartial f (planePoint x y) 1 0 = d := hd.deriv
    rw [he]
    exact (hasCoordinatePartial_second_iff _ x y d).mp hd
  obtain ⟨x, hx, he⟩ := exists_increment_eq_deriv_mul
    (g := fun x => f (planePoint x (b + k)) - f (planePoint x b))
    (g' := fun x => coordinatePartial f (planePoint x (b + k)) 0 -
      coordinatePartial f (planePoint x b) 0)
    (show a ≠ a + h by intro he; apply hh; linarith)
    (fun x hx => (hd1 x hx (b + k) right_mem_uIcc).sub (hd1 x hx b left_mem_uIcc))
  obtain ⟨y, hy, he'⟩ := exists_increment_eq_deriv_mul
    (show b ≠ b + k by intro he; apply hk; linarith)
    (hd21 x (uIoo_subset_uIcc_self hx))
  refine ⟨x, hx, y, hy, ?_⟩
  have hxinc : a + h - a = h := by ring
  have hyinc : b + k - b = k := by ring
  rw [hxinc, he', hyinc] at he
  nlinarith [he]

theorem planePoint_coordinates (p : Euclidean 2) : planePoint (p 0) (p 1) = p := by
  ext j
  fin_cases j <;> simp

theorem continuous_planePoint : Continuous (fun q : ℝ × ℝ => planePoint q.1 q.2) := by
  unfold planePoint
  fun_prop

theorem weak_mixed_partial_at_planePoint {f : Euclidean 2 → ℝ} {E : Set (Euclidean 2)}
    {a b : ℝ} (hE : IsOpen E) (hp : planePoint a b ∈ E)
    (h1 : ∀ q ∈ E, ∃ d, HasCoordinatePartial f q 0 d)
    (h21 : ∀ q ∈ E, ∃ d, HasCoordinatePartial (fun z => coordinatePartial f z 0) q 1 d)
    (h2 : ∀ q ∈ E, ∃ d, HasCoordinatePartial f q 1 d)
    (hc : ContinuousAt (fun q => secondCoordinatePartial f q 1 0) (planePoint a b)) :
    HasCoordinatePartial (fun q => coordinatePartial f q 1) (planePoint a b) 0
      (secondCoordinatePartial f (planePoint a b) 1 0) := by
  apply (hasCoordinatePartial_first_iff _ a b _).mpr
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  let L := secondCoordinatePartial f (planePoint a b) 1 0
  have hgood : ∀ᶠ q : ℝ × ℝ in 𝓝 (a, b),
      planePoint q.1 q.2 ∈ E ∧ |secondCoordinatePartial f (planePoint q.1 q.2) 1 0 - L| < ε := by
    have hm : ∀ᶠ q : ℝ × ℝ in 𝓝 (a, b), planePoint q.1 q.2 ∈ E :=
      (continuous_planePoint.continuousAt (x := (a, b))).preimage_mem_nhds (hE.mem_nhds hp)
    have hcomp : ContinuousAt (fun q : ℝ × ℝ =>
        secondCoordinatePartial f (planePoint q.1 q.2) 1 0) (a, b) :=
      ContinuousAt.comp (f := fun q : ℝ × ℝ => planePoint q.1 q.2)
        (g := fun p : Euclidean 2 => secondCoordinatePartial f p 1 0) hc
        (continuous_planePoint.continuousAt (x := (a, b)))
    have hb := (hcomp.sub_const L).abs.eventually
      (gt_mem_nhds (show |L - L| < ε by simpa using hε))
    exact hm.and hb
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hgood
  have hnear : ∀ x y : ℝ, |x - a| < δ → |y - b| < δ →
      planePoint x y ∈ E ∧ |secondCoordinatePartial f (planePoint x y) 1 0 - L| < ε := by
    intro x y hx hy
    apply hball (a := (x, y))
    simpa only [Metric.mem_ball, Prod.dist_eq, Real.dist_eq] using max_lt hx hy
  have hd2 : ∀ x, |x - a| < δ →
      HasDerivAt (fun y => f (planePoint x y)) (coordinatePartial f (planePoint x b) 1) b := by
    intro x hx
    obtain ⟨d, hd⟩ := h2 (planePoint x b) (hnear x b hx (by simpa using hδ)).1
    have he : coordinatePartial f (planePoint x b) 1 = d := hd.deriv
    rw [he]
    exact (hasCoordinatePartial_second_iff _ x b d).mp hd
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
  have hh' : |h| < δ := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh
  by_cases hh0 : h = 0
  · simp [hh0]
  · let g : ℝ → ℝ := fun y => f (planePoint (a + h) y) - f (planePoint a y) - h * L * (y - b)
    have hg : HasDerivAt g
        (coordinatePartial f (planePoint (a + h) b) 1 - coordinatePartial f (planePoint a b) 1 - h * L) b := by
      simpa only [g, Pi.sub_def, id_eq, mul_one] using
        ((hd2 (a + h) (by simpa using hh')).sub
          (hd2 a (by simpa using hδ))).sub (((hasDerivAt_id b).sub_const b).const_mul (h * L))
    have hlip : ∀ᶠ y in 𝓝 b, ‖g y - g b‖ ≤ (ε * ‖h‖) * ‖y - b‖ := by
      filter_upwards [Metric.ball_mem_nhds b hδ] with y hy
      have hy' : |y - b| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hy
      by_cases hy0 : y = b
      · simp [hy0]
      · have hrect : coordinateRectangle a b h (y - b) ⊆ E := by
          intro q hq
          have hxq : |q 0 - a| ≤ |h| := by
            have hz := Real.dist_left_le_of_mem_uIcc hq.1
            simpa only [Real.dist_eq, abs_sub_comm a (q 0),
              show a - (a + h) = -h by ring, abs_neg] using hz
          have hyq : |q 1 - b| ≤ |y - b| := by
            have hz := Real.dist_left_le_of_mem_uIcc hq.2
            simpa only [Real.dist_eq, show b + (y - b) = y by ring,
              abs_sub_comm b (q 1), abs_sub_comm b y] using hz
          have ht := (hnear (q 0) (q 1) (hxq.trans_lt hh') (hyq.trans_lt hy')).1
          simpa only [planePoint_coordinates] using ht
        obtain ⟨x', hx', y', hy'', he⟩ := pma9_40 f E a b h (y - b) hE hh0
          (sub_ne_zero.mpr hy0) hrect h1 h21
        have hxx : |x' - a| < δ := by
          have hz := Real.dist_left_le_of_mem_uIcc (uIoo_subset_uIcc_self hx')
          have hz' : |x' - a| ≤ |h| := by
            simpa only [Real.dist_eq, abs_sub_comm a x',
              show a - (a + h) = -h by ring, abs_neg] using hz
          exact hz'.trans_lt hh'
        have hyy : |y' - b| < δ := by
          have hz := Real.dist_left_le_of_mem_uIcc (uIoo_subset_uIcc_self hy'')
          have hz' : |y' - b| ≤ |y - b| := by
            simpa only [Real.dist_eq, show b + (y - b) = y by ring,
              abs_sub_comm b y', abs_sub_comm b y] using hz
          exact hz'.trans_lt hy'
        have hm := (hnear x' y' hxx hyy).2
        have heq : g y - g b = h * (y - b) *
            (secondCoordinatePartial f (planePoint x' y') 1 0 - L) := by
          dsimp only [g]
          rw [show b + (y - b) = y by ring] at he
          nlinarith [he]
        rw [heq, norm_mul, norm_mul, Real.norm_eq_abs]
        calc
          ‖h‖ * ‖y - b‖ * |secondCoordinatePartial f (planePoint x' y') 1 0 - L|
              ≤ ‖h‖ * ‖y - b‖ * ε :=
            mul_le_mul_of_nonneg_left hm.le (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = (ε * ‖h‖) * ‖y - b‖ := by ring
    have hbnd := norm_deriv_le_of_lip' (mul_nonneg hε.le (norm_nonneg h)) hlip
    rw [hg.deriv] at hbnd
    simpa only [smul_eq_mul] using hbnd

theorem weak_mixed_partial {f : Euclidean 2 → ℝ} {E : Set (Euclidean 2)}
    {p : Euclidean 2} (hE : IsOpen E) (hp : p ∈ E)
    (h1 : ∀ q ∈ E, ∃ d, HasCoordinatePartial f q 0 d)
    (h21 : ∀ q ∈ E, ∃ d, HasCoordinatePartial (fun z => coordinatePartial f z 0) q 1 d)
    (h2 : ∀ q ∈ E, ∃ d, HasCoordinatePartial f q 1 d)
    (hc : ContinuousAt (fun q => secondCoordinatePartial f q 1 0) p) :
    HasCoordinatePartial (fun q => coordinatePartial f q 1) p 0
      (secondCoordinatePartial f p 1 0) := by
  have he := planePoint_coordinates p
  simpa only [he] using weak_mixed_partial_at_planePoint (a := p 0) (b := p 1) hE
    (by simpa only [he] using hp) h1 h21 h2 (by simpa only [he] using hc)

def coordinatePlane {n : ℕ} (x : Euclidean n) (i j : Fin n) (q : Euclidean 2) : Euclidean n :=
  x + q 0 • coordinateVector n i + q 1 • coordinateVector n j

@[simp] theorem coordinatePlane_zero {n : ℕ} (x : Euclidean n) (i j : Fin n) :
    coordinatePlane x i j 0 = x := by simp [coordinatePlane]

theorem continuous_coordinatePlane {n : ℕ} (x : Euclidean n) (i j : Fin n) :
    Continuous (coordinatePlane x i j) := by
  unfold coordinatePlane
  fun_prop

theorem coordinatePlane_add_first {n : ℕ} (x : Euclidean n) (i j : Fin n)
    (q : Euclidean 2) (t : ℝ) :
    coordinatePlane x i j (q + t • coordinateVector 2 0) =
      coordinatePlane x i j q + t • coordinateVector n i := by
  simp [coordinatePlane, coordinateVector, EuclideanSpace.basisFun_apply, add_smul]
  abel

theorem coordinatePlane_add_second {n : ℕ} (x : Euclidean n) (i j : Fin n)
    (q : Euclidean 2) (t : ℝ) :
    coordinatePlane x i j (q + t • coordinateVector 2 1) =
      coordinatePlane x i j q + t • coordinateVector n j := by
  simp [coordinatePlane, coordinateVector, EuclideanSpace.basisFun_apply, add_smul]
  abel

theorem hasCoordinatePartial_comp_plane_first {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i j : Fin n) (q : Euclidean 2) (d : ℝ) :
    HasCoordinatePartial (fun z => f (coordinatePlane x i j z)) q 0 d ↔
      HasCoordinatePartial f (coordinatePlane x i j q) i d := by
  simp only [HasCoordinatePartial, coordinatePlane_add_first]

theorem hasCoordinatePartial_comp_plane_second {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i j : Fin n) (q : Euclidean 2) (d : ℝ) :
    HasCoordinatePartial (fun z => f (coordinatePlane x i j z)) q 1 d ↔
      HasCoordinatePartial f (coordinatePlane x i j q) j d := by
  simp only [HasCoordinatePartial, coordinatePlane_add_second]

theorem coordinatePartial_comp_plane_first {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i j : Fin n) (q : Euclidean 2) :
    coordinatePartial (fun z => f (coordinatePlane x i j z)) q 0 =
      coordinatePartial f (coordinatePlane x i j q) i := by
  simp only [coordinatePartial, coordinatePlane_add_first]

theorem coordinatePartial_comp_plane_second {n : ℕ} (f : Euclidean n → ℝ)
    (x : Euclidean n) (i j : Fin n) (q : Euclidean 2) :
    coordinatePartial (fun z => f (coordinatePlane x i j z)) q 1 =
      coordinatePartial f (coordinatePlane x i j q) j := by
  simp only [coordinatePartial, coordinatePlane_add_second]

theorem scalarC2On_mixed_eq {n : ℕ} {f : Euclidean n → ℝ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (hC : ScalarC2On f E) {x : Euclidean n} (hx : x ∈ E) (i j : Fin n) :
    secondCoordinatePartial f x i j = secondCoordinatePartial f x j i := by
  let g : Euclidean 2 → ℝ := fun q => f (coordinatePlane x i j q)
  let U : Set (Euclidean 2) := coordinatePlane x i j ⁻¹' E
  have hU : IsOpen U := hE.preimage (continuous_coordinatePlane x i j)
  have hz : (0 : Euclidean 2) ∈ U := by simpa [U] using hx
  have hfirst : ∀ q ∈ U, ∃ d, HasCoordinatePartial g q 0 d := by
    intro q hq
    obtain ⟨d, hd⟩ := hC.1 (coordinatePlane x i j q) hq i
    exact ⟨d, (hasCoordinatePartial_comp_plane_first f x i j q d).mpr hd⟩
  have hsecond : ∀ q ∈ U, ∃ d, HasCoordinatePartial g q 1 d := by
    intro q hq
    obtain ⟨d, hd⟩ := hC.1 (coordinatePlane x i j q) hq j
    exact ⟨d, (hasCoordinatePartial_comp_plane_second f x i j q d).mpr hd⟩
  have h21 : ∀ q ∈ U, ∃ d, HasCoordinatePartial (fun z => coordinatePartial g z 0) q 1 d := by
    intro q hq
    obtain ⟨d, hd⟩ := hC.2.1 (coordinatePlane x i j q) hq j i
    refine ⟨d, ?_⟩
    simpa only [g, coordinatePartial_comp_plane_first] using
      (hasCoordinatePartial_comp_plane_second (fun y => coordinatePartial f y i) x i j q d).mpr hd
  have he21 : (fun q => secondCoordinatePartial g q 1 0) =
      (fun q => secondCoordinatePartial f (coordinatePlane x i j q) j i) := by
    funext q
    simp only [secondCoordinatePartial, g, coordinatePartial_comp_plane_first]
    exact coordinatePartial_comp_plane_second (fun y => coordinatePartial f y i) x i j q
  have hc : ContinuousAt (fun q => secondCoordinatePartial g q 1 0) 0 := by
    rw [he21]
    have hcx : ContinuousAt (fun y => secondCoordinatePartial f y j i)
        (coordinatePlane x i j 0) := by
      simpa only [coordinatePlane_zero] using
        ((hC.2.2 j i x hx).continuousAt (hE.mem_nhds hx))
    exact hcx.comp ((continuous_coordinatePlane x i j).continuousAt (x := 0))
  have hh := weak_mixed_partial hU hz hfirst h21 hsecond hc
  have hv := hh.deriv
  change secondCoordinatePartial g 0 0 1 = secondCoordinatePartial g 0 1 0 at hv
  simp only [secondCoordinatePartial, g, coordinatePartial_comp_plane_first,
    coordinatePartial_comp_plane_second] at hv
  rw [coordinatePartial_comp_plane_first (fun y => coordinatePartial f y j),
    coordinatePartial_comp_plane_second (fun y => coordinatePartial f y i),
    coordinatePlane_zero] at hv
  exact hv

theorem pma9_41 : pma9_41_contract := by
  exact ⟨fun _ _ _ hE hp h1 h21 h2 hc => weak_mixed_partial hE hp h1 h21 h2 hc,
    fun _ _ _ hE hC _ hx i j => scalarC2On_mixed_eq hE hC hx i j⟩

end Rudin.PMA.Chapter09
