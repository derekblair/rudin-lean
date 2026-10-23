import Rudin.PMA.Chapter10.PuncturedExamples

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma puncturedSpace_isOpen (n : ℕ) : IsOpen (puncturedSpace n) := isClosed_singleton.isOpen_compl

def planeRadiusSq (x : Euclidean 2) : ℝ := x 0 ^ 2 + x 1 ^ 2

lemma planeRadiusSq_eq_norm_sq (x : Euclidean 2) : planeRadiusSq x = ‖x‖ ^ 2 := by
  simpa only [planeRadiusSq, Fin.sum_univ_two] using (EuclideanSpace.real_norm_sq_eq x).symm

lemma planeRadiusSq_pos {x : Euclidean 2} (hx : x ∈ puncturedSpace 2) : 0 < planeRadiusSq x := by
  rw [planeRadiusSq_eq_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr hx)

def angularCoefficient (i : Fin 2) (x : Euclidean 2) : ℝ :=
  ![-(x 1 / planeRadiusSq x), x 0 / planeRadiusSq x] i

lemma angularForm_eq_sum : angularForm = fun x => ∑ i : Fin 2, angularCoefficient i x • dx i := by
  funext x
  simp only [angularForm, angularCoefficient, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, planeRadiusSq, smul_sub, smul_smul, div_eq_mul_inv, neg_smul]
  module

lemma contDiffOn_angularCoefficient (i : Fin 2) :
    ContDiffOn ℝ 1 (angularCoefficient i) (puncturedSpace 2) := by
  have hc (j : Fin 2) : ContDiffOn ℝ 1 (fun x : Euclidean 2 => x j) (puncturedSpace 2) :=
    (EuclideanSpace.proj j : Euclidean 2 →L[ℝ] ℝ).contDiff.contDiffOn
  have hs : ContDiffOn ℝ 1 planeRadiusSq (puncturedSpace 2) := (hc 0).pow 2 |>.add ((hc 1).pow 2)
  fin_cases i
  · exact ((hc 1).div hs (fun x hx => (planeRadiusSq_pos hx).ne')).neg
  · exact (hc 0).div hs (fun x hx => (planeRadiusSq_pos hx).ne')

lemma isCFormOn_constant {n k r : ℕ} (E : Set (Euclidean n))
    (a : CotangentExterior n) (ha : a ∈ (⋀[ℝ]^k (Coord n))) :
    IsCFormOn r E k (fun _ => a) :=
  ⟨fun _ _ => ha, fun _ => contDiffOn_const⟩

lemma isCFormOn_angularForm : IsCFormOn 1 (puncturedSpace 2) 1 angularForm := by
  rw [angularForm_eq_sum]
  apply isCFormOn_sum
  intro i
  apply (isCFormOn_constant (puncturedSpace 2) (dx i) ?_).smul_function
    (contDiffOn_angularCoefficient i)
  rw [dx_eq_coordinateWedge]
  exact coordinateWedge_mem _

lemma coordinateLine_hasDerivAt {n : ℕ} (x : Euclidean n) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (x + t • coordinateVector n i) j)
      (if j = i then 1 else 0) 0 := by
  have h : HasDerivAt (fun t : ℝ => x j + t * (if j = i then 1 else 0))
      (if j = i then 1 else 0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (if j = i then 1 else 0)).const_add (x j)
  simpa [coordinateVector, EuclideanSpace.basisFun_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul, eq_comm] using h

set_option backward.isDefEq.respectTransparency false in
lemma plane_quotient_coordinatePartial {x : Euclidean 2} (hx : x ∈ puncturedSpace 2)
    (i j : Fin 2) :
    coordinatePartial (fun y : Euclidean 2 => y j / planeRadiusSq y) x i =
      ((if j = i then 1 else 0) * planeRadiusSq x - x j * (2 * x i)) / planeRadiusSq x ^ 2 := by
  have hd : HasDerivAt (fun t : ℝ => planeRadiusSq (x + t • coordinateVector 2 i)) (2 * x i) 0 := by
    have h := ((coordinateLine_hasDerivAt x i 0).fun_pow 2).fun_add
      ((coordinateLine_hasDerivAt x i 1).fun_pow 2)
    fin_cases i <;> simpa! [planeRadiusSq, mul_comm] using h
  have h := (coordinateLine_hasDerivAt x i j).fun_div hd (by simpa using (planeRadiusSq_pos hx).ne')
  simpa! only [coordinatePartial, zero_smul, add_zero] using h.deriv

lemma angularCoefficient_cross_partials {x : Euclidean 2} (hx : x ∈ puncturedSpace 2) :
    coordinatePartial (angularCoefficient 1) x 0 = coordinatePartial (angularCoefficient 0) x 1 := by
  have hdiff : DifferentiableAt ℝ (fun y : Euclidean 2 => y 1 / planeRadiusSq y) x := by
    have h := ((contDiffOn_angularCoefficient 0).differentiableOn (by norm_num)).differentiableAt
      ((puncturedSpace_isOpen 2).mem_nhds hx)
    have he : (-angularCoefficient 0) = (fun y : Euclidean 2 => y 1 / planeRadiusSq y) := by
      funext y
      simp only [Pi.neg_apply, angularCoefficient, Matrix.cons_val_zero, neg_neg]
    rw [← he]
    exact h.neg
  change coordinatePartial (fun y : Euclidean 2 => y 0 / planeRadiusSq y) x 0 =
    coordinatePartial (fun y : Euclidean 2 => -(y 1 / planeRadiusSq y)) x 1
  have he : (fun y : Euclidean 2 => -(y 1 / planeRadiusSq y)) =
      (fun y => (-1 : ℝ) * (y 1 / planeRadiusSq y)) := by funext y; ring
  rw [he, coordinatePartial_const_mul hdiff,
    plane_quotient_coordinatePartial hx, plane_quotient_coordinatePartial hx]
  simp only [ite_true]
  unfold planeRadiusSq
  ring

lemma exteriorDerivative_sum_smul {n : ℕ} {ι : Type*} [Fintype ι]
    (a : ι → Euclidean n → ℝ) (v : ι → CotangentExterior n) {x : Euclidean n}
    (ha : ∀ j, DifferentiableAt ℝ (a j) x) :
    exteriorDerivative (fun y => ∑ j, a j y • v j) x =
      ∑ i : Fin n, ∑ j : ι, coordinatePartial (a j) x i • (dx i * v j) := by
  rw [exteriorDerivative_eq_sum]
  simp_rw [coefficientDerivative_sum_smul a v ha, Finset.mul_sum, mul_smul_comm]

lemma angularForm_closed : IsClosedOn (puncturedSpace 2) 1 angularForm := by
  refine ⟨isCFormOn_angularForm, ?_⟩
  intro x hx
  have hd (i : Fin 2) : DifferentiableAt ℝ (angularCoefficient i) x :=
    ((contDiffOn_angularCoefficient i).differentiableOn (by norm_num)).differentiableAt
      ((puncturedSpace_isOpen 2).mem_nhds hx)
  rw [angularForm_eq_sum, exteriorDerivative_sum_smul angularCoefficient dx hd]
  simp only [Fin.sum_univ_two, dx_mul_dx, smul_zero, zero_add, add_zero, Pi.zero_apply]
  rw [dx_mul_swap (1 : Fin 2) 0, angularCoefficient_cross_partials hx, smul_neg, add_neg_cancel]

end Rudin.PMA.Chapter10
