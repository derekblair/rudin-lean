import Rudin.PMA.Chapter10.ParametricC1
import Rudin.PMA.Chapter10.StokesCoefficients

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory Module
open scoped BigOperators Interval

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Integration in the finite exterior basis, with the ordinary scalar integral
in each coefficient. -/
def coefficientIntegral {n : ℕ} (H : ℝ × Euclidean n → CotangentExterior n) : FormField n :=
  fun x => ∑ S : Finset (Fin n),
    (∫ t in (0 : ℝ)..1, (exteriorBasis n).repr (H (t, x)) S) • exteriorBasis n S

@[simp] lemma formCoefficient_coefficientIntegral {n : ℕ}
    (H : ℝ × Euclidean n → CotangentExterior n) (S : Finset (Fin n)) (x : Euclidean n) :
    formCoefficient (coefficientIntegral H) S x =
      ∫ t in (0 : ℝ)..1, (exteriorBasis n).repr (H (t, x)) S := by
  classical
  simp [coefficientIntegral, formCoefficient, map_sum, map_smul, Finsupp.single_apply]

lemma isCFormOn_coefficientIntegral {n k : ℕ} {U : Set (Euclidean n)}
    {W : Set (ℝ × Euclidean n)} (hW : IsOpen W) (hU : IsOpen U)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W)
    {H : ℝ × Euclidean n → CotangentExterior n}
    (hH : ∀ S : Finset (Fin n), ContDiffOn ℝ 1 (fun q => (exteriorBasis n).repr (H q) S) W)
    (hg : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ U, H (t, x) ∈ (⋀[ℝ]^k (Coord n))) :
    IsCFormOn 1 U k (coefficientIntegral H) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x hx
    apply Submodule.sum_mem
    intro S hS
    by_cases hSk : S.card = k
    · have hm : exteriorBasis n S ∈ (⋀[ℝ]^k (Coord n)) := by
        subst k
        exact standardWedge_mem (⟨S, rfl⟩ : StandardIndex n S.card)
      exact Submodule.smul_mem _ _ hm
    · have hz : (∫ t in (0 : ℝ)..1, (exteriorBasis n).repr (H (t, x)) S) = 0 := by
        calc
          _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            exact exteriorBasis_repr_eq_zero_of_degree (hg t
              (by simpa only [uIcc_of_le zero_le_one] using ht) x hx) S hSk
          _ = 0 := intervalIntegral.integral_zero
      rw [hz, zero_smul]
      exact Submodule.zero_mem _
  · intro S
    simp only [funext (formCoefficient_coefficientIntegral H S)]
    exact contDiffOn_parameter_integral hW hU hUW (hH S)

lemma coordinatePartial_parameter_integral {n : ℕ} {U : Set (Euclidean n)}
    {W : Set (ℝ × Euclidean n)} (hW : IsOpen W) (hU : IsOpen U)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W) {H : ℝ × Euclidean n → ℝ}
    (hH : ContDiffOn ℝ 1 H W) {x : Euclidean n} (hx : x ∈ U) (j : Fin n) :
    coordinatePartial (fun y => ∫ t in (0 : ℝ)..1, H (t, y)) x j =
      ∫ t in (0 : ℝ)..1, coordinatePartial (fun y => H (t, y)) x j := by
  have hd := hasFDerivAt_parameter_integral hW hU hUW hH hx
  rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv,
    ContinuousLinearMap.intervalIntegral_apply
      (parameter_slice_intervalIntegrable ((continuousOn_parameterDerivative hW hH).mono hUW) hx)]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hs := hasFDerivAt_parameter_slice hW hH (hUW ⟨ht', hx⟩)
  change parameterDerivative H (t, x) (coordinateVector n j) =
    coordinatePartial (fun y => H (t, y)) x j
  rw [coordinatePartial_eq_fderiv hs.differentiableAt, hs.fderiv]

lemma intervalIntegrable_parameter_partial {n : ℕ} {U : Set (Euclidean n)}
    {W : Set (ℝ × Euclidean n)} (hW : IsOpen W)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W) {H : ℝ × Euclidean n → ℝ}
    (hH : ContDiffOn ℝ 1 H W) {x : Euclidean n} (hx : x ∈ U) (j : Fin n) :
    IntervalIntegrable (fun t => coordinatePartial (fun y => H (t, y)) x j) volume 0 1 := by
  have hd := (parameter_slice_continuous
    ((continuousOn_parameterDerivative hW hH).mono hUW) hx).clm_apply
      (continuousOn_const (c := coordinateVector n j))
  apply ContinuousOn.intervalIntegrable
  apply (hd.congr ?_).mono
    (by simp only [uIcc_of_le zero_le_one]; exact Subset.rfl)
  intro t ht
  have hs := hasFDerivAt_parameter_slice hW hH (hUW ⟨ht, hx⟩)
  change coordinatePartial (fun y => H (t, y)) x j =
    parameterDerivative H (t, x) (coordinateVector n j)
  rw [coordinatePartial_eq_fderiv hs.differentiableAt, hs.fderiv]

/-- Exterior differentiation passes through compact parameter integration when
the joint coefficients are C¹. No second derivatives are involved. -/
lemma linear_exteriorDerivative_coefficientIntegral {n : ℕ} {U : Set (Euclidean n)}
    {W : Set (ℝ × Euclidean n)} (hW : IsOpen W) (hU : IsOpen U)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W)
    {H : ℝ × Euclidean n → CotangentExterior n}
    (hH : ∀ S : Finset (Fin n), ContDiffOn ℝ 1 (fun q => (exteriorBasis n).repr (H q) S) W)
    (L : CotangentExterior n →ₗ[ℝ] ℝ) {x : Euclidean n} (hx : x ∈ U) :
    L (exteriorDerivative (coefficientIntegral H) x) =
      ∫ t in (0 : ℝ)..1, L (exteriorDerivative (fun y => H (t, y)) x) := by
  classical
  have hi (j : Fin n) (S : Finset (Fin n)) :
      IntervalIntegrable (fun t =>
        coordinatePartial (fun y => (exteriorBasis n).repr (H (t, y)) S) x j *
          L (dx j * exteriorBasis n S)) volume 0 1 :=
    (intervalIntegrable_parameter_partial hW hUW (hH S) hx j).mul_const _
  simp only [exteriorDerivative, map_sum, map_smul, smul_eq_mul]
  simp only [funext (formCoefficient_coefficientIntegral H _)]
  simp_rw [coordinatePartial_parameter_integral hW hU hUW (hH _) hx]
  simp_rw [← intervalIntegral.integral_mul_const]
  let A (j : Fin n) (S : Finset (Fin n)) (t : ℝ) :=
    coordinatePartial (fun y => (exteriorBasis n).repr (H (t, y)) S) x j *
      L (dx j * exteriorBasis n S)
  change (∑ j : Fin n, ∑ S : Finset (Fin n), ∫ t in (0 : ℝ)..1, A j S t) =
    ∫ t in (0 : ℝ)..1, ∑ j : Fin n, ∑ S : Finset (Fin n), A j S t
  rw [intervalIntegral.integral_finsetSum
    (f := fun j t => ∑ S : Finset (Fin n), A j S t)
    (fun j _ => by
      convert! IntervalIntegrable.sum Finset.univ (fun S _ => hi j S) using 1
      funext t
      simp only [A, Finset.sum_apply])]
  apply Finset.sum_congr rfl
  intro j hj
  exact (intervalIntegral.integral_finsetSum (f := fun S t => A j S t)
    (fun S _ => hi j S)).symm

end Rudin.PMA.Chapter10
