import Rudin.PMA.Chapter10.AngularForm

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma radial_denominator_eq_rpow (x : Euclidean 3) :
    ‖x‖ ^ 3 = Real.rpow (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) (3 / 2 : ℝ) := by
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
    simpa [Fin.sum_univ_three, add_assoc] using (EuclideanSpace.real_norm_sq_eq x).symm
  rw [hs]
  change ‖x‖ ^ 3 = (‖x‖ ^ (2 : ℕ)) ^ (3 / 2 : ℝ)
  rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg x)]
  norm_num

def radialCoefficient (i : Fin 3) (x : Euclidean 3) : ℝ := x i / ‖x‖ ^ 3

def radialBasis : Fin 3 → CotangentExterior 3 :=
  ![dx 1 * dx 2, dx 2 * dx 0, dx 0 * dx 1]

lemma radialForm_eq_sum : radialForm = fun x => ∑ i : Fin 3, radialCoefficient i x • radialBasis i := by
  funext x
  simp [radialForm, radialCoefficient, radialBasis, Fin.sum_univ_three,
    smul_add, smul_smul, div_eq_mul_inv, mul_comm, add_assoc]

lemma contDiffOn_radialCoefficient (i : Fin 3) :
    ContDiffOn ℝ 1 (radialCoefficient i) (puncturedSpace 3) := by
  have hn : ContDiffOn ℝ 1 (fun x : Euclidean 3 => ‖x‖) (puncturedSpace 3) :=
    contDiffOn_id.norm ℝ (fun x hx => hx)
  exact (EuclideanSpace.proj i : Euclidean 3 →L[ℝ] ℝ).contDiff.contDiffOn.div
    (hn.pow 3) (fun x hx => pow_ne_zero _ (norm_ne_zero_iff.mpr hx))

lemma radialBasis_mem (i : Fin 3) : radialBasis i ∈ (⋀[ℝ]^2 (Coord 3)) := by
  have hd (j : Fin 3) : dx j ∈ (⋀[ℝ]^1 (Coord 3)) := by
    rw [dx_eq_coordinateWedge]
    exact coordinateWedge_mem _
  fin_cases i
  · exact homogeneous_mul_mem (hd 1) (hd 2)
  · exact homogeneous_mul_mem (hd 2) (hd 0)
  · exact homogeneous_mul_mem (hd 0) (hd 1)

lemma isCFormOn_radialForm : IsCFormOn 1 (puncturedSpace 3) 2 radialForm := by
  rw [radialForm_eq_sum]
  exact isCFormOn_sum fun i =>
    (isCFormOn_constant (puncturedSpace 3) (radialBasis i) (radialBasis_mem i)).smul_function
      (contDiffOn_radialCoefficient i)

set_option backward.isDefEq.respectTransparency false in
lemma coordinateLine_norm_hasDerivAt {x : Euclidean 3} (hx : x ∈ puncturedSpace 3) (i : Fin 3) :
    HasDerivAt (fun t : ℝ => ‖x + t • coordinateVector 3 i‖) (x i / ‖x‖) 0 := by
  have hs : HasDerivAt (fun t : ℝ => ‖x + t • coordinateVector 3 i‖ ^ 2) (2 * x i) 0 := by
    have h := (((coordinateLine_hasDerivAt x i 0).fun_pow 2).fun_add
      ((coordinateLine_hasDerivAt x i 1).fun_pow 2)).fun_add ((coordinateLine_hasDerivAt x i 2).fun_pow 2)
    have he : (fun t : ℝ => (x + t • coordinateVector 3 i) 0 ^ 2 +
        (x + t • coordinateVector 3 i) 1 ^ 2 + (x + t • coordinateVector 3 i) 2 ^ 2) =
        (fun t => ‖x + t • coordinateVector 3 i‖ ^ 2) := by
      funext t
      simpa [Fin.sum_univ_three, add_assoc] using
        (EuclideanSpace.real_norm_sq_eq (x + t • coordinateVector 3 i)).symm
    rw [he] at h
    fin_cases i <;> simpa using h
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have h := hs.sqrt (by simpa using pow_ne_zero 2 hn)
  have he : (fun t : ℝ => Real.sqrt (‖x + t • coordinateVector 3 i‖ ^ 2)) =
      (fun t => ‖x + t • coordinateVector 3 i‖) := by
    funext t
    exact Real.sqrt_sq (norm_nonneg _)
  rw [he] at h
  convert h using 1
  simp only [zero_smul, add_zero, Real.sqrt_sq (norm_nonneg x)]
  field_simp

set_option backward.isDefEq.respectTransparency false in
lemma radialCoefficient_coordinatePartial {x : Euclidean 3} (hx : x ∈ puncturedSpace 3)
    (i j : Fin 3) :
    coordinatePartial (radialCoefficient j) x i =
      ((if j = i then 1 else 0) * ‖x‖ ^ 3 -
        x j * (3 * ‖x‖ ^ 2 * (x i / ‖x‖))) / (‖x‖ ^ 3) ^ 2 := by
  have h := (coordinateLine_hasDerivAt x i j).fun_div
    ((coordinateLine_norm_hasDerivAt hx i).fun_pow 3)
    (by simpa using pow_ne_zero 3 (norm_ne_zero_iff.mpr hx))
  simpa [coordinatePartial, radialCoefficient] using h.deriv

lemma radialCoefficient_divergence {x : Euclidean 3} (hx : x ∈ puncturedSpace 3) :
    (∑ i : Fin 3, coordinatePartial (radialCoefficient i) x i) = 0 := by
  simp_rw [radialCoefficient_coordinatePartial hx, ite_true, one_mul]
  rw [Fin.sum_univ_three]
  have hs : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = ‖x‖ ^ 2 := by
    simpa [Fin.sum_univ_three, add_assoc] using (EuclideanSpace.real_norm_sq_eq x).symm
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp
  nlinarith [hs]

lemma dx_mul_radialBasis (i j : Fin 3) :
    dx i * radialBasis j = if i = j then dx 0 * (dx 1 * dx 2) else 0 := by
  fin_cases i <;> fin_cases j
  · rfl
  · change dx (0 : Fin 3) * (dx 2 * dx 0) = 0
    rw [← mul_assoc, dx_mul_swap (0 : Fin 3) 2, neg_mul, mul_assoc, dx_mul_dx, mul_zero, neg_zero]
  · change dx (0 : Fin 3) * (dx 0 * dx 1) = 0
    rw [← mul_assoc, dx_mul_dx, zero_mul]
  · change dx (1 : Fin 3) * (dx 1 * dx 2) = 0
    rw [← mul_assoc, dx_mul_dx, zero_mul]
  · change dx (1 : Fin 3) * (dx 2 * dx 0) = dx 0 * (dx 1 * dx 2)
    rw [dx_mul_swap (2 : Fin 3) 0, mul_neg, ← mul_assoc,
      dx_mul_swap (1 : Fin 3) 0, neg_mul, neg_neg, mul_assoc]
  · change dx (1 : Fin 3) * (dx 0 * dx 1) = 0
    rw [dx_mul_swap (0 : Fin 3) 1, mul_neg, ← mul_assoc, dx_mul_dx, zero_mul, neg_zero]
  · change dx (2 : Fin 3) * (dx 1 * dx 2) = 0
    rw [dx_mul_swap (1 : Fin 3) 2, mul_neg, ← mul_assoc, dx_mul_dx, zero_mul, neg_zero]
  · change dx (2 : Fin 3) * (dx 2 * dx 0) = 0
    rw [← mul_assoc, dx_mul_dx, zero_mul]
  · change dx (2 : Fin 3) * (dx 0 * dx 1) = dx 0 * (dx 1 * dx 2)
    rw [← mul_assoc, dx_mul_swap (2 : Fin 3) 0, neg_mul, mul_assoc,
      dx_mul_swap (2 : Fin 3) 1, mul_neg, neg_neg]

lemma radialForm_closed : IsClosedOn (puncturedSpace 3) 2 radialForm := by
  refine ⟨isCFormOn_radialForm, ?_⟩
  intro x hx
  have hd (i : Fin 3) : DifferentiableAt ℝ (radialCoefficient i) x :=
    ((contDiffOn_radialCoefficient i).differentiableOn (by norm_num)).differentiableAt
      ((puncturedSpace_isOpen 3).mem_nhds hx)
  rw [radialForm_eq_sum, exteriorDerivative_sum_smul radialCoefficient radialBasis hd]
  simp only [dx_mul_radialBasis, smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]
  rw [← Finset.sum_smul, radialCoefficient_divergence hx, zero_smul]
  rfl

end Rudin.PMA.Chapter10
