import Rudin.PMA.Chapter10.Prerequisites

noncomputable section
set_option autoImplicit false
open Set Filter Function
open scoped Topology BigOperators ContDiff

namespace Rudin.PMA.Chapter10
open Chapter09

@[simp] theorem coordinatePartial_const {n : ℕ} (c : ℝ) (x : Euclidean n) (i : Fin n) :
    coordinatePartial (fun _ => c) x i = 0 := by
  simp [coordinatePartial]

theorem coordinatePartial_congr_of_eqOn {n : ℕ} {E : Set (Euclidean n)}
    {f g : Euclidean n → ℝ} (hE : IsOpen E) (he : EqOn f g E)
    {x : Euclidean n} (hx : x ∈ E) (i : Fin n) :
    coordinatePartial f x i = coordinatePartial g x i := by
  have hnear : f =ᶠ[𝓝 x] g := Filter.eventually_of_mem (hE.mem_nhds hx) (fun _ hy => he hy)
  have ht : Tendsto (fun t : ℝ => x + t • coordinateVector n i) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • coordinateVector n i) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto (0 : ℝ)
  exact (hnear.comp_tendsto ht).deriv_eq

theorem coordinatePartial_add {n : ℕ} {f g : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinatePartial (fun y => f y + g y) x i = coordinatePartial f x i + coordinatePartial g x i := by
  change coordinatePartial (f + g) x i = _
  rw [coordinatePartial_eq_fderiv (hf.add hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [ContinuousLinearMap.add_apply] using
    congrArg (fun A : Euclidean n →L[ℝ] ℝ => A (coordinateVector n i)) (fderiv_add hf hg)

theorem coordinatePartial_mul {n : ℕ} {f g : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinatePartial (fun y => f y * g y) x i =
      coordinatePartial f x i * g x + f x * coordinatePartial g x i := by
  change coordinatePartial (f * g) x i = _
  rw [coordinatePartial_eq_fderiv (hf.mul hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  have h := congrArg (fun A : Euclidean n →L[ℝ] ℝ => A (coordinateVector n i)) (fderiv_mul hf hg)
  simpa only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    mul_comm, add_comm] using h

theorem coordinatePartial_const_mul {n : ℕ} {f : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin n) :
    coordinatePartial (fun y => c * f y) x i = c * coordinatePartial f x i := by
  simpa only [coordinatePartial_const, zero_mul, zero_add] using
    coordinatePartial_mul (differentiableAt_const c) hf i

theorem coordinatePartial_mul_const {n : ℕ} {f : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (c : ℝ) (i : Fin n) :
    coordinatePartial (fun y => f y * c) x i = coordinatePartial f x i * c := by
  simpa only [coordinatePartial_const, mul_zero, add_zero] using
    coordinatePartial_mul hf (differentiableAt_const c) i

theorem coordinatePartial_sum {n : ℕ} {ι : Type*} [Fintype ι]
    {f : ι → Euclidean n → ℝ} {x : Euclidean n}
    (hf : ∀ a, DifferentiableAt ℝ (f a) x) (i : Fin n) :
    coordinatePartial (fun y => ∑ a, f a y) x i = ∑ a, coordinatePartial (f a) x i := by
  rw [coordinatePartial_eq_fderiv (DifferentiableAt.fun_sum fun a _ => hf a)]
  simp_rw [coordinatePartial_eq_fderiv (hf _)]
  simpa only [sum_apply] using
    congrArg (fun A : Euclidean n →L[ℝ] ℝ => A (coordinateVector n i))
      (fderiv_fun_sum (u := Finset.univ) (fun a _ => hf a))

theorem contDiffOn_coordinatePartial {n r : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → ℝ} (hE : IsOpen E) (hf : ContDiffOn ℝ (r + 1) f E) (i : Fin n) :
    ContDiffOn ℝ r (fun x => coordinatePartial f x i) E := by
  have hd : ∀ x ∈ E, DifferentiableAt ℝ f x := fun x hx =>
    (hf.differentiableOn (by exact_mod_cast Nat.succ_ne_zero r)).differentiableAt (hE.mem_nhds hx)
  have hc : ContDiffOn ℝ r (fun x => fderiv ℝ f x (coordinateVector n i)) E :=
    (hf.fderiv_of_isOpen hE (by simp)).clm_apply contDiffOn_const
  exact hc.congr (fun x hx => coordinatePartial_eq_fderiv (hd x hx) i)

theorem continuousOn_coordinatePartial {n : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → ℝ} (hE : IsOpen E) (hf : ContDiffOn ℝ 1 f E) (i : Fin n) :
    ContinuousOn (fun x => coordinatePartial f x i) E :=
  (contDiffOn_coordinatePartial (r := 0) hE hf i).continuousOn

/-- Classical symmetry of mixed coordinate derivatives, under exactly C²
regularity on an open domain. -/
theorem coordinatePartial_commute {n : ℕ} {E : Set (Euclidean n)} {f : Euclidean n → ℝ}
    (hE : IsOpen E) (hf : ContDiffOn ℝ 2 f E) {x : Euclidean n} (hx : x ∈ E) (i j : Fin n) :
    coordinatePartial (fun y => coordinatePartial f y i) x j =
      coordinatePartial (fun y => coordinatePartial f y j) x i := by
  have hd : ∀ y ∈ E, DifferentiableAt ℝ f y := fun y hy =>
    (hf.differentiableOn (by norm_num)).differentiableAt (hE.mem_nhds hy)
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hE (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).differentiableOn
      (by norm_num)).differentiableAt (hE.mem_nhds hx)
  have he (a b : Fin n) : coordinatePartial (fun y => coordinatePartial f y a) x b =
      fderiv ℝ (fderiv ℝ f) x (coordinateVector n b) (coordinateVector n a) := by
    rw [coordinatePartial_congr_of_eqOn hE (fun y hy => coordinatePartial_eq_fderiv (hd y hy) a) hx b]
    have hh := (ContinuousLinearMap.apply ℝ ℝ (coordinateVector n a)).hasFDerivAt.comp x hdf.hasFDerivAt
    have hh' : HasFDerivAt (fun y => fderiv ℝ f y (coordinateVector n a))
        ((ContinuousLinearMap.apply ℝ ℝ (coordinateVector n a)).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
      hh
    rw [coordinatePartial_eq_fderiv hh'.differentiableAt, hh'.fderiv]
    rfl
  rw [he i j, he j i]
  exact ((hf x hx).contDiffAt (hE.mem_nhds hx)).isSymmSndFDerivAt
    (by norm_num) (coordinateVector n j) (coordinateVector n i)

end Rudin.PMA.Chapter10
