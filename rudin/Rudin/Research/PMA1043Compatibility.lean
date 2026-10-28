import Rudin.Research.PMA1043Planar
import Rudin.Research.PMA1043Gauge

/-!
# A first-derivative compatibility criterion for planar endpoint solvability

This module proves that a C² divergence primitive exists exactly when the datum
is the trace of a C¹ matrix whose rows are closed. The compatibility condition
is an additional unknown, not a claim that every C¹ datum satisfies it.
-/

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The two coordinate partials of a planar scalar. -/
def planarGradient (f : Euclidean 2 → ℝ) : PlanarVectorField := fun x =>
  coordEquivEuclidean 2 (fun i => coordinatePartial f x i)

@[simp] lemma planarGradient_apply (f : Euclidean 2 → ℝ) (x : Euclidean 2) (i : Fin 2) :
    planarGradient f x i = coordinatePartial f x i := rfl

/-- Row integrability, with the derivative indices spelled out. -/
def PlanarClosed (v : PlanarVectorField) : Prop :=
  ∀ x, coordinatePartial (fun y => v y 0) x 1 =
    coordinatePartial (fun y => v y 1) x 0

lemma contDiff_planarGradient {f : Euclidean 2 → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (planarGradient f) := by
  apply (coordEquivEuclidean 2).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  exact contDiffOn_univ.mp (contDiffOn_coordinatePartial (r := 1) isOpen_univ hf.contDiffOn i)

lemma planarClosed_planarGradient {f : Euclidean 2 → ℝ} (hf : ContDiff ℝ 2 f) :
    PlanarClosed (planarGradient f) := by
  intro x
  exact coordinatePartial_commute isOpen_univ hf.contDiffOn (mem_univ x) 0 1

/-- Embed a closed planar row as a horizontal, z-independent field. -/
def horizontalField (v : PlanarVectorField) : VectorField := fun x =>
  coordEquivEuclidean 3 ![v (planeProjection x) 0, v (planeProjection x) 1, 0]

lemma contDiff_horizontalField {v : PlanarVectorField} (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (horizontalField v) := by
  apply (coordEquivEuclidean 3).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact ((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hv).comp planeProjection.contDiff
  · exact ((EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hv).comp planeProjection.contDiff
  · exact contDiff_const

lemma curl_horizontalField_eq_zero {v : PlanarVectorField} (hv : PlanarClosed v) :
    curl (horizontalField v) = 0 := by
  funext x
  ext i
  fin_cases i
  · change coordinatePartial (fun _ => (0 : ℝ)) x 1 -
      coordinatePartial (fun y => v (planeProjection y) 1) x 2 = 0
    rw [coordinatePartial_const,
      coordinatePartial_planeProjection_two (fun y => v y 1)]
    ring
  · change coordinatePartial (fun y => v (planeProjection y) 0) x 2 -
      coordinatePartial (fun _ => (0 : ℝ)) x 0 = 0
    rw [coordinatePartial_const,
      coordinatePartial_planeProjection_two (fun y => v y 0)]
    ring
  · change coordinatePartial (fun y => v (planeProjection y) 1) x 0 -
      coordinatePartial (fun y => v (planeProjection y) 0) x 1 = 0
    have hp0 := coordinatePartial_planeProjection (fun y => v y 1) x 0
    have hp1 := coordinatePartial_planeProjection (fun y => v y 0) x 1
    norm_num at hp0 hp1
    rw [hp0, hp1, hv (planeProjection x), sub_self]

/-- The already-proved scalar converse integrates each C¹ closed planar row.
This uses no vector-potential endpoint assumption. -/
theorem planarClosed_has_c2_scalarPotential {v : PlanarVectorField}
    (hv : ContDiff ℝ 1 v) (hc : PlanarClosed v) :
    ∃ f : Euclidean 2 → ℝ, ContDiff ℝ 2 f ∧ planarGradient f = v := by
  let e : C2DomainEquivalence (univ : Set (Euclidean 3)) univ :=
    { forward := id
      inverse := id
      forward_mapsTo := fun _ _ => mem_univ _
      inverse_mapsTo := fun _ _ => mem_univ _
      left_inverse := fun _ _ => rfl
      right_inverse := fun _ _ => rfl
      forward_c2 := contDiff_id.contDiffOn
      inverse_c2 := contDiff_id.contDiffOn }
  have hz : EqOn (curl (horizontalField v)) 0 univ := by
    rw [curl_horizontalField_eq_zero hc]
    exact fun _ _ => rfl
  obtain ⟨f, hf, he⟩ := scalarPotential_c2_of_equivalent_convex e isOpen_univ
    isOpen_univ convex_univ (contDiff_horizontalField hv).contDiffOn hz
  refine ⟨f ∘ planeInclusion, (contDiffOn_univ.mp hf).comp planeInclusion.contDiff, ?_⟩
  funext x
  ext i
  rw [planarGradient_apply]
  change coordinatePartial (fun y => f (planeInclusion y)) x i = v x i
  rw [coordinatePartial_planeInclusion]
  have h := congrArg (fun z => z i.castSucc) (he (mem_univ (planeInclusion x)))
  fin_cases i <;> simpa [gradient, horizontalField] using h

/-- A C¹ matrix represented by its two rows, with exactly prescribed trace and
closed rows. No existence of this matrix is asserted here. -/
def PlanarCompatibleTrace (h : Euclidean 2 → ℝ) : Prop :=
  ∃ a b : PlanarVectorField,
    ContDiff ℝ 1 a ∧ ContDiff ℝ 1 b ∧ PlanarClosed a ∧ PlanarClosed b ∧
      ∀ x, a x 0 + b x 1 = h x

/-- Exact endpoint reduction to first-order compatibility. This is an iff for
one datum on the whole plane, not an equivalence with Rudin's full contract. -/
theorem c2_planarDivergence_iff_compatibleTrace (h : Euclidean 2 → ℝ) :
    (∃ u : PlanarVectorField, ContDiff ℝ 2 u ∧ planarDivergence u = h) ↔
      PlanarCompatibleTrace h := by
  constructor
  · rintro ⟨u, hu, hd⟩
    have h0 := (EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hu
    have h1 := (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hu
    refine ⟨planarGradient (fun x => u x 0), planarGradient (fun x => u x 1),
      contDiff_planarGradient h0, contDiff_planarGradient h1,
      planarClosed_planarGradient h0, planarClosed_planarGradient h1, ?_⟩
    intro x
    exact congrFun hd x
  · rintro ⟨a, b, ha, hb, hca, hcb, ht⟩
    obtain ⟨f, hf, hfa⟩ := planarClosed_has_c2_scalarPotential ha hca
    obtain ⟨g, hg, hgb⟩ := planarClosed_has_c2_scalarPotential hb hcb
    let u : PlanarVectorField := fun x => coordEquivEuclidean 2 ![f x, g x]
    have hu : ContDiff ℝ 2 u := by
      apply (coordEquivEuclidean 2).contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact hf
      · exact hg
    refine ⟨u, hu, ?_⟩
    funext x
    have h0 := congrArg (fun v : PlanarVectorField => v x 0) hfa
    have h1 := congrArg (fun v : PlanarVectorField => v x 1) hgb
    simpa [planarDivergence, u, ← h0, ← h1] using ht x

/-- The vertical family also admits exactly this compatibility criterion. -/
theorem c2_verticalPotential_iff_compatibleTrace (h : Euclidean 2 → ℝ) :
    (∃ G : VectorField, ContDiff ℝ 2 G ∧ curl G = verticalField h) ↔
      PlanarCompatibleTrace h :=
  (c2_verticalPotential_iff_planarDivergence h).trans
    (c2_planarDivergence_iff_compatibleTrace h)

/-- Columns of a matrix represented by its row fields. -/
def planarMatrixColumn (a b : PlanarVectorField) (j : Fin 2) : PlanarVectorField :=
  fun x => coordEquivEuclidean 2 ![a x j, b x j]

/-- The trace of the same matrix. -/
def planarMatrixTrace (a b : PlanarVectorField) : Euclidean 2 → ℝ :=
  fun x => a x 0 + b x 1

lemma contDiff_planarMatrixTrace {a b : PlanarVectorField}
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b) :
    ContDiff ℝ 1 (planarMatrixTrace a b) :=
  ((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp ha).add
    ((EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hb)

lemma planarDivergence_column_eq_partial_trace {a b : PlanarVectorField}
    (ha : ContDiff ℝ 1 a) (hb : ContDiff ℝ 1 b)
    (hca : PlanarClosed a) (hcb : PlanarClosed b) (j : Fin 2) (x : Euclidean 2) :
    planarDivergence (planarMatrixColumn a b j) x =
      coordinatePartial (planarMatrixTrace a b) x j := by
  have ha0 : DifferentiableAt ℝ (fun y => a y 0) x :=
    ((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp ha).differentiable (by norm_num) x
  have hb1 : DifferentiableAt ℝ (fun y => b y 1) x :=
    ((EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp hb).differentiable (by norm_num) x
  change _ = coordinatePartial (fun y => a y 0 + b y 1) x j
  rw [coordinatePartial_add ha0 hb1]
  fin_cases j <;> simp [planarDivergence, planarMatrixColumn, hca x, hcb x]

/-- Simultaneous solutions of the differentiated divergence equations, whose
rows also satisfy the integrability conditions needed to be a Jacobian. -/
def PlanarCompatibleColumns (h : Euclidean 2 → ℝ) : Prop :=
  ∃ a b : PlanarVectorField,
    ContDiff ℝ 1 a ∧ ContDiff ℝ 1 b ∧ PlanarClosed a ∧ PlanarClosed b ∧
      ∀ j : Fin 2, planarDivergence (planarMatrixColumn a b j) =
        fun x => coordinatePartial h x j

/-- A C¹ scalar with all coordinate partials zero is constant on the plane. -/
lemma planar_constant_of_partials_zero {f : Euclidean 2 → ℝ}
    (hf : ContDiff ℝ 1 f) (hz : ∀ x i, coordinatePartial f x i = 0) :
    ∀ x, f x = f 0 := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfd : ∀ x, fderiv ℝ f x = 0 := by
    intro x
    ext v
    rw [linear_apply_eq_sum_coordinates]
    simp_rw [← coordinatePartial_eq_fderiv (hd x)]
    simp [hz]
  exact fun x => is_const_of_fderiv_eq_zero hd hfd x 0

/-- The differentiated equations determine the trace up to one constant;
a constant change of one diagonal entry removes it without changing closure. -/
theorem compatibleColumns_iff_compatibleTrace {h : Euclidean 2 → ℝ}
    (hh : ContDiff ℝ 1 h) :
    PlanarCompatibleColumns h ↔ PlanarCompatibleTrace h := by
  constructor
  · rintro ⟨a, b, ha, hb, hca, hcb, he⟩
    let s := planarMatrixTrace a b
    have hs : ContDiff ℝ 1 s := contDiff_planarMatrixTrace ha hb
    have hder : ∀ x j, coordinatePartial s x j = coordinatePartial h x j := by
      intro x j
      rw [← planarDivergence_column_eq_partial_trace ha hb hca hcb]
      exact congrFun (he j) x
    have hc : ∀ x, s x - h x = s 0 - h 0 := by
      apply planar_constant_of_partials_zero (hs.sub hh)
      intro x i
      rw [coordinatePartial_sub_gauge (hs.differentiable (by norm_num) x)
        (hh.differentiable (by norm_num) x), hder, sub_self]
    let c : ℝ := s 0 - h 0
    let a' : PlanarVectorField := fun x =>
      coordEquivEuclidean 2 ![a x 0 - c, a x 1]
    have ha' : ContDiff ℝ 1 a' := by
      apply (coordEquivEuclidean 2).contDiff.comp
      apply contDiff_pi.mpr
      intro i
      fin_cases i
      · exact ((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp ha).sub contDiff_const
      · exact (EuclideanSpace.proj (1 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp ha
    have hca' : PlanarClosed a' := by
      intro x
      change coordinatePartial (fun y => a y 0 - c) x 1 =
        coordinatePartial (fun y => a y 1) x 0
      have ha0 : DifferentiableAt ℝ (fun y => a y 0) x :=
        ((EuclideanSpace.proj (0 : Fin 2) : Euclidean 2 →L[ℝ] ℝ).contDiff.comp ha).differentiable
          (by norm_num) x
      rw [coordinatePartial_sub_gauge ha0 (differentiableAt_const c)]
      simpa using hca x
    refine ⟨a', b, ha', hb, hca', hcb, ?_⟩
    intro x
    have hvalue := hc x
    change a x 0 - c + b x 1 = _
    change a x 0 + b x 1 - h x = c at hvalue
    linarith
  · rintro ⟨a, b, ha, hb, hca, hcb, ht⟩
    refine ⟨a, b, ha, hb, hca, hcb, ?_⟩
    intro j
    funext x
    rw [planarDivergence_column_eq_partial_trace ha hb hca hcb]
    have he : planarMatrixTrace a b = h := funext ht
    rw [he]

/-- Exact reformulation of the unsolved planar endpoint in terms of C¹
solutions of both differentiated equations with simultaneous compatibility.
Separate solvability of those equations is insufficient for this hypothesis. -/
theorem c2_planarDivergence_iff_compatibleColumns {h : Euclidean 2 → ℝ}
    (hh : ContDiff ℝ 1 h) :
    (∃ u : PlanarVectorField, ContDiff ℝ 2 u ∧ planarDivergence u = h) ↔
      PlanarCompatibleColumns h :=
  (c2_planarDivergence_iff_compatibleTrace h).trans
    (compatibleColumns_iff_compatibleTrace hh).symm

/-- The elementary separate solutions `h e₀` and `h e₁` of the differentiated
divergence equations form a compatible Jacobian only for constant data.
Other choices of solutions remain unrestricted. -/
theorem canonical_columns_compatible_iff_constant {h : Euclidean 2 → ℝ}
    (hh : ContDiff ℝ 1 h) :
    (PlanarClosed (planarCoordinateField 0 h) ∧
      PlanarClosed (planarCoordinateField 1 h)) ↔ ∀ x, h x = h 0 := by
  constructor
  · rintro ⟨ha, hb⟩
    apply planar_constant_of_partials_zero hh
    intro x i
    fin_cases i
    · simpa [planarCoordinateField, coordinateVector, EuclideanSpace.basisFun_apply]
        using (hb x).symm
    · simpa [planarCoordinateField, coordinateVector, EuclideanSpace.basisFun_apply]
        using ha x
  · intro hc
    have he : h = fun _ => h 0 := funext hc
    rw [he]
    constructor <;> intro x <;>
      simp [planarCoordinateField, coordinateVector, EuclideanSpace.basisFun_apply]

end Rudin.PMA.Chapter10
