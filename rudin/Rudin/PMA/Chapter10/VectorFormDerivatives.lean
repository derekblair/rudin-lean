import Rudin.PMA.Chapter10.VectorFields

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

lemma vectorOneForm_gradient (f : Euclidean 3 → ℝ) :
    vectorOneForm (gradient f) = scalarDifferential f := by
  funext x
  simp only [vectorOneForm, gradient, coordEquivEuclidean_apply_coordinate, scalarDifferential]

lemma exteriorDerivative_scalarForm_gradient (f : Euclidean 3 → ℝ) :
    exteriorDerivative (scalarForm f) = vectorOneForm (gradient f) := by
  rw [exteriorDerivative_scalarForm, vectorOneForm_gradient]

lemma exteriorDerivative_vectorOneForm {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    EqOn (exteriorDerivative (vectorOneForm F)) (vectorTwoForm (curl F)) E := by
  intro x hx
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (contDiffOn_map_coordinate hF i).differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  change exteriorDerivative (fun y => ∑ i : Fin 3, F y i • dx i) x = _
  rw [exteriorDerivative_sum_smul (fun i y => F y i) dx hd]
  simp [Fin.sum_univ_three, dx_mul_dx, smul_zero, zero_add, add_zero,
    vectorTwoForm, curl, radialBasis, coordEquivEuclidean_apply_coordinate,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [dx_mul_swap (0 : Fin 3) 2, dx_mul_swap (1 : Fin 3) 0, dx_mul_swap (2 : Fin 3) 1]
  module

lemma volumeForm_eq_cyclic (x : Euclidean 3) :
    volumeForm x = dx 0 * (dx 1 * dx 2) := by
  simp [volumeForm, coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply,
    Matrix.vecTail, Function.comp_def]

lemma exteriorDerivative_vectorTwoForm {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    EqOn (exteriorDerivative (vectorTwoForm F))
      (fun x => divergence F x • volumeForm x) E := by
  intro x hx
  have hd (i : Fin 3) : DifferentiableAt ℝ (fun y => F y i) x :=
    (contDiffOn_map_coordinate hF i).differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  change exteriorDerivative (fun y => ∑ i : Fin 3, F y i • radialBasis i) x = _
  rw [exteriorDerivative_sum_smul (fun i y => F y i) radialBasis hd]
  simp only [dx_mul_radialBasis, smul_ite, smul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [← Finset.sum_smul, volumeForm_eq_cyclic]
  rfl

lemma vectorOneForm_zero : vectorOneForm 0 = 0 := by
  funext x
  simp [vectorOneForm]

lemma vectorTwoForm_zero : vectorTwoForm 0 = 0 := by
  funext x
  simp [vectorTwoForm]

lemma vectorOneForm_closed_iff {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    IsClosedOn E 1 (vectorOneForm F) ↔ EqOn (curl F) 0 E := by
  have he := exteriorDerivative_vectorOneForm hE hF
  constructor
  · intro h
    apply (vectorTwoForm_eqOn_iff (curl F) 0).mp
    intro x hx
    rw [← he hx, h.2 hx, vectorTwoForm_zero]
  · intro h
    refine ⟨isCFormOn_vectorOneForm hF, ?_⟩
    intro x hx
    rw [he hx]
    simp [vectorTwoForm, h hx]

lemma volumeForm_ne_zero (x : Euclidean 3) : volumeForm x ≠ 0 := by
  intro hz
  have he := congrArg (evaluateForm 3 (fun i => coordinateVector 3 i)) hz
  change evaluateForm 3 (fun i => coordinateVector 3 i) (coordinateWedge id) = _ at he
  rw [evaluateForm_coordinateWedge, map_zero] at he
  have hm : (fun i j : Fin 3 => coordinateVector 3 j (id i)) = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    simp [coordinateVector, EuclideanSpace.basisFun_apply, PiLp.single_apply, Matrix.one_apply, eq_comm]
  rw [hm, Matrix.det_one] at he
  exact one_ne_zero he

lemma vectorTwoForm_closed_iff {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) :
    IsClosedOn E 2 (vectorTwoForm F) ↔ EqOn (divergence F) 0 E := by
  have he := exteriorDerivative_vectorTwoForm hE hF
  constructor
  · intro h x hx
    have hz : divergence F x • volumeForm x = 0 := (he hx).symm.trans (h.2 hx)
    exact (smul_eq_zero.mp hz).resolve_right (volumeForm_ne_zero x)
  · intro h
    refine ⟨isCFormOn_vectorTwoForm hF, ?_⟩
    intro x hx
    rw [he hx]
    change divergence F x • volumeForm x = 0
    rw [h hx]
    exact zero_smul _ _

end Rudin.PMA.Chapter10
