import Rudin.PMA.Chapter10.FormSeparation
import Rudin.PMA.Chapter10.SimplexChains
import Rudin.PMA.Chapter10.Simplex

noncomputable section
set_option autoImplicit false
open Set Function Filter MeasureTheory Module
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Actual native integrals over C² simplices separate continuous forms, including
zero-forms and degrees larger than the ambient dimension. -/
def simplexSeparation_contract : Prop :=
  ∀ (k n : ℕ) (E : Set (Euclidean n)) (ω : FormField n),
    IsOpen E → IsFormOn E k ω →
      ((∀ σ : C2Simplex k n E, surfaceIntegral σ.toSurface ω = 0) ↔ EqOn ω 0 E)


/-- The simplex has positive measure in every dimension, including dimension zero.
A small positive-side cell is enough; its exact volume is not needed. -/
lemma volume_standardSimplex_pos (k : ℕ) : 0 < volume (standardSimplex k) := by
  let c : ℝ := 1 / ((k : ℝ) + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  let C : Cell k := ⟨0, fun _ => c, fun _ => hc.le⟩
  have hC : C.carrier ⊆ standardSimplex k := by
    intro u hu
    refine ⟨fun i => (Cell.mem_carrier.mp hu i).1, ?_⟩
    have hs : (∑ i, u i) ≤ (k : ℝ) * c := by
      simpa only [C, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => (Cell.mem_carrier.mp hu i).2)
    apply hs.trans
    dsimp [c]
    rw [mul_one_div]
    exact (div_le_one (by positivity : (0 : ℝ) < (k : ℝ) + 1)).mpr (by linarith)
  have hpos : 0 < volume C.carrier := by
    change 0 < volume (Icc (0 : Coord k) (fun _ => c))
    rw [Real.volume_Icc_pi]
    apply pos_iff_ne_zero.mpr
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by
      simpa only [Pi.zero_apply, sub_zero] using (ENNReal.ofReal_pos.mpr hc).ne'
  exact hpos.trans_le (measure_mono hC)

lemma simplexRIntegral_pos {k : ℕ} {f : Coord k → ℝ}
    (hf : ContinuousOn f (standardSimplex k))
    (hp : ∀ u ∈ standardSimplex k, 0 < f u) : 0 < simplexRIntegral f := by
  rw [simplexRIntegral_eq_integral hf]
  have hae : 0 ≤ᵐ[volume.restrict (standardSimplex k)] f :=
    (ae_restrict_mem (isClosed_standardSimplex k).measurableSet).mono fun u hu => (hp u hu).le
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae
    (hf.integrableOn_compact (isCompact_standardSimplex k))]
  have hs : Function.support f ∩ standardSimplex k = standardSimplex k :=
    inter_eq_right.mpr fun u hu => (hp u hu).ne'
  rw [hs]
  exact volume_standardSimplex_pos k

lemma norm_le_one_of_mem_standardSimplex {k : ℕ} {u : Coord k}
    (hu : u ∈ standardSimplex k) : ‖u‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro i
  have hi := Cell.mem_carrier.mp (standardSimplex_subset_unit k hu) i
  exact abs_le.mpr ⟨(by norm_num : (-1 : ℝ) ≤ 0).trans hi.1, hi.2⟩

lemma exists_positive_scaled_simplex {k : ℕ} {U : Set (Coord k)} {f : Coord k → ℝ}
    (hU : IsOpen U) (h0 : (0 : Coord k) ∈ U) (hf : ContinuousOn f U) (hf0 : 0 < f 0) :
    ∃ r : ℝ, 0 < r ∧ MapsTo (fun u => r • u) (standardSimplex k) U ∧
      ContinuousOn (fun u => f (r • u)) (standardSimplex k) ∧
      0 < simplexRIntegral (fun u => f (r • u)) := by
  have hfc : ContinuousAt f 0 := (hf 0 h0).continuousAt (hU.mem_nhds h0)
  have hmem : ∀ᶠ u in 𝓝 (0 : Coord k), u ∈ U := hU.mem_nhds h0
  have hnear : ∀ᶠ u in 𝓝 (0 : Coord k), u ∈ U ∧ 0 < f u :=
    hmem.and (hfc.eventually (isOpen_Ioi.mem_nhds hf0))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  have hsmall (u : Coord k) (hu : u ∈ standardSimplex k) : r • u ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    calc
      r * ‖u‖ ≤ r * 1 := mul_le_mul_of_nonneg_left (norm_le_one_of_mem_standardSimplex hu) hr.le
      _ < ε := by simpa only [mul_one] using half_lt_self hε
  have hm : MapsTo (fun u => r • u) (standardSimplex k) U :=
    fun u hu => (hball (hsmall u hu)).1
  have hc : ContinuousOn (fun u => f (r • u)) (standardSimplex k) :=
    hf.comp (show Continuous (fun u : Coord k => r • u) by fun_prop).continuousOn hm
  exact ⟨r, hr, hm, hc, simplexRIntegral_pos hc (fun u hu => (hball (hsmall u hu)).2)⟩

lemma exists_nonzero_scaled_simplex {k : ℕ} {U : Set (Coord k)} {f : Coord k → ℝ}
    (hU : IsOpen U) (h0 : (0 : Coord k) ∈ U) (hf : ContinuousOn f U) (hf0 : f 0 ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ MapsTo (fun u => r • u) (standardSimplex k) U ∧
      ContinuousOn (fun u => f (r • u)) (standardSimplex k) ∧
      simplexRIntegral (fun u => f (r • u)) ≠ 0 := by
  rcases lt_or_gt_of_ne hf0 with hneg | hpos
  · obtain ⟨r, hr, hm, hc, hp⟩ := exists_positive_scaled_simplex hU h0 hf.neg (neg_pos.mpr hneg)
    have hc' : ContinuousOn (fun u => f (r • u)) (standardSimplex k) :=
      hf.comp (show Continuous (fun u : Coord k => r • u) by fun_prop).continuousOn hm
    have he : simplexRIntegral (fun u => (-f) (r • u)) =
        -simplexRIntegral (fun u => f (r • u)) := by
      rw [simplexRIntegral_eq_integral hc, simplexRIntegral_eq_integral hc']
      simp only [Pi.neg_apply, integral_neg]
    rw [he] at hp
    exact ⟨r, hr, hm, hc', (neg_pos.mp hp).ne⟩
  · obtain ⟨r, hr, hm, hc, hp⟩ := exists_positive_scaled_simplex hU h0 hf hpos
    exact ⟨r, hr, hm, hc, hp.ne'⟩

lemma evaluateForm_smul_tangents {k n : ℕ} {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^k (Coord n))) (r : ℝ) (v : Fin k → Euclidean n) :
    evaluateForm k (fun j => r • v j) a = r^k * evaluateForm k v a := by
  classical
  rw [standard_expansion a ha, map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [map_smul, smul_eq_mul, standardWedge_eq_coordinateWedge,
    evaluateForm_coordinateWedge]
  let M : Matrix (Fin k) (Fin k) ℝ := fun i j => v j (Set.powersetCard.ofFinEmbEquiv.symm S i)
  have hd : Matrix.det (fun i j => (r • v j) (Set.powersetCard.ofFinEmbEquiv.symm S i)) =
      r^k * Matrix.det M := by
    change Matrix.det (r • M) = r^k * Matrix.det M
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [hd]
  change _ = r^k * (((exteriorBasis n).repr a) S.val * Matrix.det M)
  ring

/-- A small affine coordinate simplex, whose image stays in the prescribed domain. -/
def scaledAxisSimplex {k n : ℕ} {E : Set (Euclidean n)} (x : Euclidean n)
    (I : Fin k → Fin n) (r : ℝ)
    (hm : MapsTo (fun u => axisParameterization x I (r • u)) (standardSimplex k) E) :
    C2Simplex k n E where
  map := fun u => axisParameterization x I (r • u)
  regularity := by
    refine ⟨univ, isOpen_univ, subset_univ _, ?_⟩
    have hs : ContDiff ℝ 2 (fun u : Coord k => r • u) := by fun_prop
    exact ((axisParameterization_contDiff x I 2).comp hs).contDiffOn
  mapsTo := hm

lemma scaledAxisSimplex_integrand {k n : ℕ} {E : Set (Euclidean n)} {ω : FormField n}
    (hω : IsFormOn E k ω) (S : StandardIndex n k) (x : Euclidean n) (r : ℝ)
    (hm : MapsTo (fun u => axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S) (r • u))
      (standardSimplex k) E) {u : Coord k} (hu : u ∈ standardSimplex k) :
    surfaceIntegrand (scaledAxisSimplex x (Set.powersetCard.ofFinEmbEquiv.symm S) r hm).toSurface ω u =
      r^k * formCoefficient ω S.val
        (axisParameterization x (Set.powersetCard.ofFinEmbEquiv.symm S) (r • u)) := by
  let I := Set.powersetCard.ofFinEmbEquiv.symm S
  have hs : HasFDerivAt (fun v : Coord k => r • v)
      (r • ContinuousLinearMap.id ℝ (Coord k)) u := by
    simpa only [id_eq] using! (hasFDerivAt_id u).const_smul r
  have hd : HasFDerivAt (fun v : Coord k => axisParameterization x I (r • v))
      ((axisDifferential I).comp (r • ContinuousLinearMap.id ℝ (Coord k))) u := by
    simpa only [Function.comp_def] using!
      (axisParameterization_hasFDerivAt x I (r • u)).comp u hs
  change evaluateForm k (fun j => fderiv ℝ (fun u => axisParameterization x I (r • u)) u
    (Pi.single j 1)) (ω (axisParameterization x I (r • u))) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, axisDifferential_single]
  rw [evaluateForm_smul_tangents (hω.1 _ (hm hu)), evaluateForm_axis_coefficient hω S (hm hu)]

/-- If one standard coefficient is nonzero, an actual affine simplex has a
nonzero native form integral. -/
lemma exists_nonzero_simplex_integral {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E k ω)
    (S : StandardIndex n k) {x : Euclidean n} (hx : x ∈ E)
    (hne : formCoefficient ω S.val x ≠ 0) :
    ∃ σ : C2Simplex k n E, surfaceIntegral σ.toSurface ω ≠ 0 := by
  let I := Set.powersetCard.ofFinEmbEquiv.symm S
  let φ := axisParameterization x I
  let U := φ ⁻¹' E
  let f : Coord k → ℝ := fun u => formCoefficient ω S.val (φ u)
  have hφ : Continuous φ := (axisParameterization_contDiff x I 0).continuous
  have hU : IsOpen U := hE.preimage hφ
  have h0 : (0 : Coord k) ∈ U := by simpa only [U, φ, mem_preimage, axisParameterization_zero] using hx
  have hf : ContinuousOn f U := (hω.2 S.val).comp hφ.continuousOn (mapsTo_preimage _ _)
  have hf0 : f 0 ≠ 0 := by simpa only [f, φ, axisParameterization_zero] using hne
  obtain ⟨r, hr, hm, hc, hi⟩ := exists_nonzero_scaled_simplex hU h0 hf hf0
  let σ := scaledAxisSimplex x I r hm
  have he : surfaceIntegral σ.toSurface ω = r^k * simplexRIntegral (fun u => f (r • u)) := by
    change simplexRIntegral (surfaceIntegrand σ.toSurface ω) = _
    rw [simplexRIntegral_eq_integral (σ.toSurface.continuousOn_integrand hω),
      simplexRIntegral_eq_integral hc, ← integral_const_mul]
    apply setIntegral_congr_fun (isClosed_standardSimplex k).measurableSet
    intro u hu
    exact scaledAxisSimplex_integrand hω S x r hm hu
  refine ⟨σ, ?_⟩
  rw [he]
  exact mul_ne_zero (pow_ne_zero _ hr.ne') hi

lemma eqOn_zero_of_simplex_integrals_zero {k n : ℕ} {E : Set (Euclidean n)}
    {ω : FormField n} (hE : IsOpen E) (hω : IsFormOn E k ω)
    (hz : ∀ σ : C2Simplex k n E, surfaceIntegral σ.toSurface ω = 0) : EqOn ω 0 E := by
  apply eqOn_zero_of_standard_coefficients_zero hω
  intro S x hx
  by_contra hne
  obtain ⟨σ, hσ⟩ := exists_nonzero_simplex_integral hE hω S hx hne
  exact hσ (hz σ)

theorem simplexSeparation : simplexSeparation_contract := by
  intro k n E ω hE hω
  refine ⟨eqOn_zero_of_simplex_integrals_zero hE hω, ?_⟩
  intro he σ
  exact (FormEqOn.of_eqOn hω (isFormOn_zero E) he σ.toSurface).trans (surfaceIntegral_zero σ.toSurface)

end Rudin.PMA.Chapter10
