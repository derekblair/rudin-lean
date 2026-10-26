import Rudin.PMA.Chapter10.VolumeElements
import Rudin.PMA.Chapter10.PositiveBoundaries
import Rudin.PMA.Chapter10.OneFormCoordinates
import Rudin.PMA.Chapter10.ClosedExact

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def regionIntegral {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E)
    (f : Euclidean n → ℝ) : ℝ := ∫ x in R.carrier, f x

lemma regionIntegral_eq_chain {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E)
    {f : Euclidean n → ℝ} (hf : ContinuousOn f E) :
    regionIntegral R f = chainIntegral (densityForm f) R.chain := by
  rw [R.integral_eq_image (isFormOn_densityForm hf)]
  simp_rw [topFormDensity_densityForm]
  rw [R.coordinateCarrier_preimage]
  exact ((coordEquivEuclidean_measurePreserving n).setIntegral_preimage_emb
    (coordEquivEuclidean n).toHomeomorph.measurableEmbedding f R.carrier).symm

lemma regionIntegral_const {n : ℕ} {E : Set (Euclidean n)} (R : PositiveRegion n E) (c : ℝ) :
    regionIntegral R (fun _ => c) = (volume R.carrier).toReal * c := by
  simp [regionIntegral, measureReal_def, smul_eq_mul]

/-- The actual two-dimensional one-form α dx + β dy. -/
def planarOneForm (α β : Euclidean 2 → ℝ) : FormField 2 := fun x =>
  ∑ i : Fin 2, (![α, β] i) x • dx i

lemma planarOneForm_apply (α β : Euclidean 2 → ℝ) (x : Euclidean 2) :
    planarOneForm α β x = α x • dx 0 + β x • dx 1 := by
  simp [planarOneForm, Fin.sum_univ_two]

lemma isCFormOn_planarOneForm {r : ℕ} {E : Set (Euclidean 2)}
    {α β : Euclidean 2 → ℝ} (hα : ContDiffOn ℝ r α E) (hβ : ContDiffOn ℝ r β E) :
    IsCFormOn r E 1 (planarOneForm α β) := by
  refine ⟨fun x hx => ?_, fun S => ?_⟩
  · apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem
    rw [dx_eq_coordinateWedge]
    exact coordinateWedge_mem _
  · have he : formCoefficient (planarOneForm α β) S = fun x =>
        α x * (exteriorBasis 2).repr (dx 0) S + β x * (exteriorBasis 2).repr (dx 1) S := by
      funext x
      simp [formCoefficient, planarOneForm_apply, map_add, map_smul]
    rw [he]
    exact (hα.mul contDiffOn_const).add (hβ.mul contDiffOn_const)

lemma standardVolume_two : standardVolume 2 = dx (0 : Fin 2) * dx 1 := by
  simp [standardVolume, coordinateWedge, ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, dx]

lemma exteriorDerivative_planarOneForm {E : Set (Euclidean 2)} (hE : IsOpen E)
    {α β : Euclidean 2 → ℝ} (hα : ContDiffOn ℝ 1 α E) (hβ : ContDiffOn ℝ 1 β E) :
    EqOn (exteriorDerivative (planarOneForm α β))
      (densityForm (fun x => coordinatePartial β x 0 - coordinatePartial α x 1)) E := by
  intro x hx
  have hd (i : Fin 2) : DifferentiableAt ℝ (![α, β] i) x := by
    fin_cases i
    · exact hα.differentiableOn_one.differentiableAt (hE.mem_nhds hx)
    · exact hβ.differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  rw [exteriorDerivative_eq_sum]
  have he (j : Fin 2) : coefficientDerivative (planarOneForm α β) j x =
      ∑ i : Fin 2, coordinatePartial (![α, β] i) x j • dx i :=
    coefficientDerivative_sum_smul (![α, β]) (fun i => dx i) hd j
  simp only [he, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_add, mul_smul_comm, dx_mul_dx, smul_zero, zero_add, add_zero,
    densityForm, standardVolume_two]
  rw [dx_mul_swap 1 0]
  module

lemma green_native {E : Set (Euclidean 2)} (hE : IsOpen E) (R : PositiveRegion 2 E)
    {α β : Euclidean 2 → ℝ} (hα : ContDiffOn ℝ 1 α E) (hβ : ContDiffOn ℝ 1 β E) :
    chainIntegral (planarOneForm α β) R.boundary =
      regionIntegral R (fun x => coordinatePartial β x 0 - coordinatePartial α x 1) := by
  have hω := isCFormOn_planarOneForm hα hβ
  have hf : ContinuousOn (fun x => coordinatePartial β x 0 - coordinatePartial α x 1) E :=
    ((contDiffOn_coordinatePartial hE hβ 0).continuousOn).sub
      ((contDiffOn_coordinatePartial hE hα 1).continuousOn)
  rw [PositiveRegion.boundary, ← pma10_33 1 2 E (planarOneForm α β) R.chain hE hω,
    regionIntegral_eq_chain R hf]
  exact chainIntegral_congr_eqOn (pma10_18.1 2 1 E _ hE hω).1
    (isFormOn_densityForm hf) (exteriorDerivative_planarOneForm hE hα hβ) R.chain

lemma coordinatePartial_coordinate {n : ℕ} (i j : Fin n) (x : Euclidean n) :
    coordinatePartial (fun y : Euclidean n => y i) x j = if i = j then 1 else 0 := by
  have h := (hasCoordinatePartial_of_hasFDerivAt (x := x)
    (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt j).deriv
  simpa! [coordinatePartial, EuclideanSpace.coe_proj, coordinateVector,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm] using h

lemma green_area_xdy {E : Set (Euclidean 2)} (hE : IsOpen E) (R : PositiveRegion 2 E) :
    chainIntegral (planarOneForm (fun _ => 0) (fun x => x 0)) R.boundary =
      (volume R.carrier).toReal := by
  have hβ : ContDiffOn ℝ 1 (fun x : Euclidean 2 => x 0) E :=
    (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).contDiff.contDiffOn
  have h := green_native hE R (α := fun _ => 0) contDiffOn_const hβ
  simpa only [coordinatePartial_coordinate, coordinatePartial_const, ite_true, sub_zero,
    regionIntegral_const, mul_one] using h

lemma green_area_symmetric {E : Set (Euclidean 2)} (hE : IsOpen E) (R : PositiveRegion 2 E) :
    (1 / 2 : ℝ) * chainIntegral (planarOneForm (fun x => -x 1) (fun x => x 0)) R.boundary =
      (volume R.carrier).toReal := by
  have hα : ContDiffOn ℝ 1 (fun x : Euclidean 2 => -x 1) E :=
    (EuclideanSpace.proj 1 : Euclidean 2 →L[ℝ] ℝ).contDiff.contDiffOn.neg
  have hβ : ContDiffOn ℝ 1 (fun x : Euclidean 2 => x 0) E :=
    (EuclideanSpace.proj 0 : Euclidean 2 →L[ℝ] ℝ).contDiff.contDiffOn
  have h := green_native hE R hα hβ
  have hneg (x : Euclidean 2) : coordinatePartial (fun y : Euclidean 2 => -y 1) x 1 = -1 := by
    have hd : DifferentiableAt ℝ (fun y : Euclidean 2 => y 1) x :=
      (EuclideanSpace.proj 1 : Euclidean 2 →L[ℝ] ℝ).differentiableAt
    have he : (fun y : Euclidean 2 => -y 1) = fun y => (-1 : ℝ) * y 1 := by
      funext y
      ring
    rw [he]
    rw [coordinatePartial_const_mul hd, coordinatePartial_coordinate]
    norm_num
  simp only [coordinatePartial_coordinate, hneg, ite_true] at h
  have hc : (fun _ : Euclidean 2 => (1 : ℝ) - -1) = fun _ => (2 : ℝ) := by ext; norm_num
  rw [hc, regionIntegral_const] at h
  rw [h]
  ring

/-- Green's theorem and both source area formulas, with the actual positive
boundary and ordinary region integral. -/
def pma10_45_contract : Prop :=
  ∀ (E : Set (Euclidean 2)) (R : PositiveRegion 2 E), IsOpen E →
    (∀ (α β : Euclidean 2 → ℝ), ContDiffOn ℝ 1 α E → ContDiffOn ℝ 1 β E →
      chainIntegral (planarOneForm α β) R.boundary =
        regionIntegral R (fun x => coordinatePartial β x 0 - coordinatePartial α x 1) ∧
      (∀ i : Fin R.size, (ParameterDomain.simplex : ParameterDomain 2).Integrable
        (surfaceIntegrand (R.piece i).simplex.toSurface
          (densityForm (fun x => coordinatePartial β x 0 - coordinatePartial α x 1)))) ∧
      (∀ (i : Fin R.size) (j : Fin 3), (ParameterDomain.simplex : ParameterDomain 1).Integrable
        (surfaceIntegrand ((R.piece i).simplex.face j).toSurface (planarOneForm α β)))) ∧
    (1 / 2 : ℝ) * chainIntegral (planarOneForm (fun x => -x 1) (fun x => x 0)) R.boundary =
      (volume R.carrier).toReal ∧
    chainIntegral (planarOneForm (fun _ => 0) (fun x => x 0)) R.boundary =
      (volume R.carrier).toReal

theorem pma10_45 : pma10_45_contract := by
  intro E R hE
  refine ⟨?_, green_area_symmetric hE R, green_area_xdy hE R⟩
  intro α β hα hβ
  have hω := (isCFormOn_planarOneForm hα hβ).isFormOn
  have hf := ((contDiffOn_coordinatePartial hE hβ 0).continuousOn).sub
    ((contDiffOn_coordinatePartial hE hα 1).continuousOn)
  exact ⟨green_native hE R hα hβ,
    fun i => ParameterDomain.integrable_of_continuousOn
      ((R.piece i).simplex.toSurface.continuousOn_integrand (isFormOn_densityForm hf)),
    fun i j => ParameterDomain.integrable_of_continuousOn
      (((R.piece i).simplex.face j).toSurface.continuousOn_integrand hω)⟩

end Rudin.PMA.Chapter10
