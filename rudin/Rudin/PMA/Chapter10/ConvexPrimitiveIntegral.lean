import Rudin.PMA.Chapter10.ParametricC1

noncomputable section
set_option autoImplicit false
open Set Function Filter MeasureTheory
open scoped Topology BigOperators Interval

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The straight segment from a smoothly chosen point in a prefix fiber. -/
def sectionSegment {n : ℕ} (a : Euclidean n → Euclidean n)
    (q : ℝ × Euclidean n) : Euclidean n := a q.2 + q.1 • (q.2 - a q.2)

def sectionPrimitiveIntegrand {n : ℕ} (a : Euclidean n → Euclidean n)
    (f : Euclidean n → ℝ) (p : Fin n) (q : ℝ × Euclidean n) : ℝ :=
  (q.2 p - a q.2 p) * f (sectionSegment a q)

lemma contDiffOn_sectionSegment {n : ℕ} {E : Set (Euclidean n)}
    {a : Euclidean n → Euclidean n} (ha : ContDiffOn ℝ 1 a E) :
    ContDiffOn ℝ 1 (sectionSegment a) (univ ×ˢ E) := by
  have ha' : ContDiffOn ℝ 1 (fun q : ℝ × Euclidean n => a q.2) (univ ×ˢ E) :=
    ha.comp contDiffOn_snd (fun _ h => h.2)
  exact ha'.add (contDiffOn_fst.smul (contDiffOn_snd.sub ha'))

lemma sectionSegment_mem {n : ℕ} {E : Set (Euclidean n)} (hc : Convex ℝ E)
    {a : Euclidean n → Euclidean n} (ha : MapsTo a E E)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {x : Euclidean n} (hx : x ∈ E) :
    sectionSegment a (t, x) ∈ E := hc.add_smul_sub_mem (ha hx) hx ht

lemma sectionPrimitive_joint_regular {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (hc : Convex ℝ E) {a : Euclidean n → Euclidean n}
    (ha : ContDiffOn ℝ 1 a E) (ham : MapsTo a E E)
    {f : Euclidean n → ℝ} (hf : ContDiffOn ℝ 1 f E) (p : Fin n) :
    ∃ W : Set (ℝ × Euclidean n), IsOpen W ∧ Icc (0 : ℝ) 1 ×ˢ E ⊆ W ∧
      ContDiffOn ℝ 1 (sectionPrimitiveIntegrand a f p) W := by
  let V : Set (ℝ × Euclidean n) := univ ×ˢ E
  let W := V ∩ sectionSegment a ⁻¹' E
  have hA := contDiffOn_sectionSegment ha
  have hW : IsOpen W := hA.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hE) hE
  refine ⟨W, hW, ?_, ?_⟩
  · intro q hq
    exact ⟨⟨mem_univ _, hq.2⟩, sectionSegment_mem hc ham hq.1 hq.2⟩
  · have has : ContDiffOn ℝ 1 (fun q : ℝ × Euclidean n => a q.2) W :=
      ha.comp (contDiffOn_snd.mono inter_subset_left) (fun _ h => h.1.2)
    have hc1 : ContDiffOn ℝ 1 (fun q : ℝ × Euclidean n => q.2 p) W :=
      (EuclideanSpace.proj p : Euclidean n →L[ℝ] ℝ).contDiff.comp_contDiffOn contDiffOn_snd
    have hc2 : ContDiffOn ℝ 1 (fun q : ℝ × Euclidean n => a q.2 p) W :=
      (EuclideanSpace.proj p : Euclidean n →L[ℝ] ℝ).contDiff.comp_contDiffOn has
    exact (hc1.sub hc2).mul (hf.comp (hA.mono inter_subset_left) (fun _ h => h.2))

lemma sectionPrimitive_parameterDerivative {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) {a : Euclidean n → Euclidean n} (ha : ContDiffOn ℝ 1 a E)
    {f : Euclidean n → ℝ} (hf : ContDiffOn ℝ 1 f E) (p j : Fin n)
    {W : Set (ℝ × Euclidean n)} (hW : IsOpen W)
    (hH : ContDiffOn ℝ 1 (sectionPrimitiveIntegrand a f p) W)
    {t : ℝ} {x : Euclidean n} (hx : x ∈ E) (htx : (t, x) ∈ W)
    (hAx : sectionSegment a (t, x) ∈ E)
    (haz : fderiv ℝ a x (coordinateVector n j) = 0) :
    parameterDerivative (sectionPrimitiveIntegrand a f p) (t, x) (coordinateVector n j) =
      (if j = p then 1 else 0) * f (sectionSegment a (t, x)) +
        (x p - a x p) * t * coordinatePartial f (sectionSegment a (t, x)) j := by
  classical
  have hda := (ha.differentiableOn_one.differentiableAt (hE.mem_nhds hx)).hasFDerivAt
  have hdf := (hf.differentiableOn_one.differentiableAt (hE.mem_nhds hAx)).hasFDerivAt
  have hA : HasFDerivAt (fun y : Euclidean n => sectionSegment a (t, y))
      (fderiv ℝ a x + t • (ContinuousLinearMap.id ℝ (Euclidean n) - fderiv ℝ a x)) x :=
    hda.add (((hasFDerivAt_id x).sub hda).const_smul t)
  have hd := ((EuclideanSpace.proj p).hasFDerivAt.sub
    ((EuclideanSpace.proj p).hasFDerivAt.comp x hda)).mul (hdf.comp x hA)
  have hde := (hasFDerivAt_parameter_slice hW hH htx).unique hd
  have hv := congrArg (fun L : Euclidean n →L[ℝ] ℝ => L (coordinateVector n j)) hde
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, haz, sub_zero, zero_add, map_smul, map_zero] at hv
  rw [coordinatePartial_eq_fderiv hdf.differentiableAt]
  simpa [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, haz, sub_zero, zero_add, map_smul, map_zero,
    smul_eq_mul, EuclideanSpace.coe_proj, coordinateVector,
    EuclideanSpace.basisFun_apply, PiLp.single_apply, eq_comm, mul_assoc, add_comm] using hv

lemma section_fderiv_direction {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) {f : Euclidean n → ℝ} (hf : ContDiffOn ℝ 1 f E) (p : Fin n)
    (hz : ∀ y ∈ E, ∀ j : Fin n, p < j → coordinatePartial f y j = 0)
    {a : Euclidean n → Euclidean n} {x y : Euclidean n} (hy : y ∈ E)
    (hap : ∀ j : Fin n, j < p → a x j = x j) :
    fderiv ℝ f y (x - a x) = coordinatePartial f y p * (x p - a x p) := by
  classical
  have hdf := hf.differentiableOn_one.differentiableAt (hE.mem_nhds hy)
  rw [linear_apply_eq_sum_coordinates]
  simp_rw [← coordinatePartial_eq_fderiv hdf]
  apply Finset.sum_eq_single p
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hjp | hpj
    · simp [hap j hjp]
    · simp [hz y hy j hpj]
  · simp

/-- Integrating from a smooth prefix section produces the prescribed coordinate
primitive and preserves all vanishing later partial derivatives. -/
lemma exists_coordinate_primitive_of_retraction {n : ℕ} {E : Set (Euclidean n)}
    (hE : IsOpen E) (hc : Convex ℝ E) {f : Euclidean n → ℝ}
    (hf : ContDiffOn ℝ 1 f E) (p : Fin n)
    (hz : ∀ x ∈ E, ∀ j : Fin n, p < j → coordinatePartial f x j = 0)
    {a : Euclidean n → Euclidean n} (ha : ContDiffOn ℝ 1 a E) (ham : MapsTo a E E)
    (hap : ∀ x ∈ E, ∀ j : Fin n, j < p → a x j = x j)
    (haz : ∀ x ∈ E, ∀ j : Fin n, p ≤ j → fderiv ℝ a x (coordinateVector n j) = 0) :
    ∃ F : Euclidean n → ℝ, ContDiffOn ℝ 1 F E ∧
      (∀ x ∈ E, coordinatePartial F x p = f x) ∧
      (∀ x ∈ E, ∀ j : Fin n, p < j → coordinatePartial F x j = 0) := by
  obtain ⟨W, hW, hEW, hH⟩ := sectionPrimitive_joint_regular hE hc ha ham hf p
  let H := sectionPrimitiveIntegrand a f p
  let F : Euclidean n → ℝ := fun x => ∫ t in (0 : ℝ)..1, H (t, x)
  have hFC : ContDiffOn ℝ 1 F E := contDiffOn_parameter_integral hW hE hEW hH
  have hDI := (continuousOn_parameterDerivative hW hH).mono hEW
  have hpart (x : Euclidean n) (hx : x ∈ E) (j : Fin n) :
      coordinatePartial F x j =
        ∫ t in (0 : ℝ)..1, parameterDerivative H (t, x) (coordinateVector n j) := by
    have hd := hasFDerivAt_parameter_integral hW hE hEW hH hx
    rw [coordinatePartial_eq_fderiv hd.differentiableAt, hd.fderiv]
    exact ContinuousLinearMap.intervalIntegral_apply (parameter_slice_intervalIntegrable hDI hx) _
  refine ⟨F, hFC, ?_, ?_⟩
  · intro x hx
    rw [hpart x hx p]
    have hd (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) 1) :
        HasDerivAt (fun s : ℝ => s * f (sectionSegment a (s, x)))
          (parameterDerivative H (t, x) (coordinateVector n p)) t := by
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      have hAx := sectionSegment_mem hc ham ht' hx
      have hdf := (hf.differentiableOn_one.differentiableAt (hE.mem_nhds hAx)).hasFDerivAt
      have hline : HasDerivAt (fun s : ℝ => sectionSegment a (s, x)) (x - a x) t := by
        simpa only [sectionSegment, id_eq, one_smul] using!
          ((hasDerivAt_id t).smul_const (x - a x)).const_add (a x)
      have hh := (hasDerivAt_id t).mul (hdf.comp_hasDerivAt t hline)
      convert! hh using 1
      rw [sectionPrimitive_parameterDerivative hE ha hf p p hW hH hx (hEW ⟨ht', hx⟩)
        hAx (haz x hx p le_rfl), if_pos rfl,
        section_fderiv_direction hE hf p hz hAx (hap x hx)]
      simp only [id_eq, Function.comp_apply]
      ring
    have hi : IntervalIntegrable
        (fun t => parameterDerivative H (t, x) (coordinateVector n p)) volume 0 1 :=
      ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le zero_le_one] using
        (parameter_slice_continuous hDI hx).clm_apply continuousOn_const)
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
    simpa only [sectionSegment, one_smul, add_sub_cancel, one_mul, zero_mul, sub_zero] using he
  · intro x hx j hj
    rw [hpart x hx j]
    have he : (∫ t in (0 : ℝ)..1, parameterDerivative H (t, x) (coordinateVector n j)) =
        ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
      have hAx := sectionSegment_mem hc ham ht' hx
      change parameterDerivative (sectionPrimitiveIntegrand a f p) (t, x)
        (coordinateVector n j) = 0
      rw [sectionPrimitive_parameterDerivative hE ha hf p j hW hH hx (hEW ⟨ht', hx⟩)
        hAx (haz x hx j hj.le), if_neg (ne_of_gt hj), hz _ hAx j hj]
      ring
    rw [he, intervalIntegral.integral_zero]

end Rudin.PMA.Chapter10
