import Rudin.PMA.Chapter10.RadialHomotopy

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators Topology Interval

namespace Rudin.PMA.Chapter10
open Chapter09

lemma intervalIntegrable_linear_exteriorDerivative {n : ℕ} {U : Set (Euclidean n)}
    {W : Set (ℝ × Euclidean n)} (hW : IsOpen W)
    (hUW : Icc (0 : ℝ) 1 ×ˢ U ⊆ W)
    {H : ℝ × Euclidean n → CotangentExterior n}
    (hH : ∀ S : Finset (Fin n), ContDiffOn ℝ 1 (fun q => (exteriorBasis n).repr (H q) S) W)
    (L : CotangentExterior n →ₗ[ℝ] ℝ) {x : Euclidean n} (hx : x ∈ U) :
    IntervalIntegrable (fun t => L (exteriorDerivative (fun y => H (t,y)) x)) volume 0 1 := by
  classical
  let A (j : Fin n) (S : Finset (Fin n)) (t : ℝ) :=
    coordinatePartial (fun y => (exteriorBasis n).repr (H (t,y)) S) x j *
      L (dx j * exteriorBasis n S)
  have hi (j : Fin n) (S : Finset (Fin n)) : IntervalIntegrable (A j S) volume 0 1 :=
    (intervalIntegrable_parameter_partial hW hUW (hH S) hx j).mul_const _
  have hj (j : Fin n) :
      IntervalIntegrable (fun t => ∑ S : Finset (Fin n), A j S t) volume 0 1 := by
    convert! IntervalIntegrable.sum Finset.univ (fun S _ => hi j S) using 1
    funext t
    simp only [Finset.sum_apply]
  simp only [exteriorDerivative, map_sum, map_smul, smul_eq_mul]
  convert! IntervalIntegrable.sum Finset.univ (fun j _ => hj j) using 1
  funext t
  simp only [A, Finset.sum_apply]
  rfl

lemma hasDerivAt_radial_homotopy_coefficient {n k : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) {ω : FormField n} (hω : IsClosedOn E (k+1) ω)
    (a x : Euclidean n) (t : ℝ) (hy : radialPoint a (t,x) ∈ E)
    (L : CotangentExterior n →ₗ[ℝ] ℝ) :
    HasDerivAt (fun s : ℝ => s^(k+1) * L (ω (radialPoint a (s,x))))
      (L (exteriorDerivative (fun y => radialHomotopyIntegrand k a ω (t,y)) x)) t := by
  have hcoeff := hω.1.coefficientsDifferentiableAt hE hy
  have hL := (contDiffOn_linear_formEvaluation hω.1 L).differentiableOn_one.differentiableAt
    (hE.mem_nhds hy)
  have hline : HasDerivAt (fun s : ℝ => radialPoint a (s,x)) (x-a) t := by
    simpa only [radialPoint, id_eq, one_smul] using!
      ((hasDerivAt_id t).smul_const (x-a)).const_add a
  have hdir : fderiv ℝ (fun z => L (ω z)) (radialPoint a (t,x)) (x-a) =
      ∑ i : Fin n, (x i-a i) * L (coefficientDerivative ω i (radialPoint a (t,x))) := by
    rw [linear_apply_eq_sum_coordinates]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← coordinatePartial_eq_fderiv hL,
      coordinatePartial_linear_formEvaluation hcoeff L]
    change L (coefficientDerivative ω i (radialPoint a (t,x))) * (x i-a i) = _
    ring
  have hh := ((hasDerivAt_id t).pow (k+1)).mul (hL.hasFDerivAt.comp_hasDerivAt t hline)
  convert! hh using 1
  rw [exteriorDerivative_radialHomotopyIntegrand a x t hcoeff (hω.1.1 _ hy) (hω.2 hy),
    map_add, map_smul, map_smul, map_sum, hdir]
  simp only [map_smul, smul_eq_mul, Nat.add_sub_cancel, Pi.pow_apply, id_eq,
    Function.comp_apply]
  ring

/-- A radial homotopy supplies a global C¹ primitive of a closed C¹ positive
degree form on a convex open set. -/
lemma radial_primitive {n k : ℕ} {E : Set (Euclidean n)} (hE : IsOpen E)
    (hc : Convex ℝ E) {a : Euclidean n} (ha : a ∈ E) {ω : FormField n}
    (hω : IsClosedOn E (k+1) ω) : IsExactOn E (k+1) ω := by
  classical
  let W : Set (ℝ × Euclidean n) := radialPoint a ⁻¹' E
  let H := radialHomotopyIntegrand k a ω
  have hW : IsOpen W := hE.preimage (contDiff_radialPoint a).continuous
  have hEW : Icc (0 : ℝ) 1 ×ˢ E ⊆ W := by
    intro q hq
    exact hc.add_smul_sub_mem ha hq.2 hq.1
  have hH (S : Finset (Fin n)) :
      ContDiffOn ℝ 1 (fun q => (exteriorBasis n).repr (H q) S) W :=
    radialHomotopyIntegrand_coeff_regular hω.1 a S
  refine ⟨coefficientIntegral H, isCFormOn_coefficientIntegral hW hE hEW hH ?_, ?_⟩
  · intro t ht x hx
    exact radialHomotopyIntegrand_mem (hω.1.1 _ (hEW ⟨ht,hx⟩))
  · intro x hx
    apply (exteriorBasis n).repr.injective
    ext S
    let L : CotangentExterior n →ₗ[ℝ] ℝ := (exteriorBasis n).coord S
    change L (exteriorDerivative (coefficientIntegral H) x) = L (ω x)
    rw [linear_exteriorDerivative_coefficientIntegral hW hE hEW hH L hx]
    have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ => s^(k+1) * L (ω (radialPoint a (s,x))))
          (L (exteriorDerivative (fun y => H (t,y)) x)) t :=
      hasDerivAt_radial_homotopy_coefficient hE hω a x t
        (hEW ⟨by simpa only [uIcc_of_le zero_le_one] using ht, hx⟩) L
    have hi := intervalIntegrable_linear_exteriorDerivative hW hEW hH L hx
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    simpa [radialPoint] using he

lemma closed_exact_on_convex {n k : ℕ} {E : Set (Euclidean n)} (hE : IsOpen E)
    (hc : Convex ℝ E) {ω : FormField n} (hω : IsClosedOn E (k+1) ω) :
    IsExactOn E (k+1) ω := by
  classical
  by_cases hne : E.Nonempty
  · obtain ⟨a, ha⟩ := hne
    exact radial_primitive hE hc ha hω
  · have hzero : IsCFormOn 1 E k (0 : FormField n) := by
      refine ⟨fun x hx => False.elim (hne ⟨x,hx⟩), fun S => ?_⟩
      intro x hx
      exact False.elim (hne ⟨x,hx⟩)
    exact ⟨0, hzero, fun x hx => False.elim (hne ⟨x,hx⟩)⟩

end Rudin.PMA.Chapter10
