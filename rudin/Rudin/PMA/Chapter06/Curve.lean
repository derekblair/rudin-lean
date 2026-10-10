import Mathlib
import Rudin.PMA.Chapter05
import Rudin.PMA.Chapter06.Basic
import Rudin.PMA.Chapter06.Definitions
import Rudin.PMA.Chapter06.Integrability

noncomputable section
open Set Filter Topology
open scoped BigOperators ENNReal

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.26: Curves, arcs, closed curves, and polygonal length -/

def CurveOn {E : Type*} [TopologicalSpace E] (γ : ℝ → E) (a b : ℝ) : Prop :=
  a ≤ b ∧ ContinuousOn γ (Icc a b)

def ArcOn {E : Type*} [TopologicalSpace E] (γ : ℝ → E) (a b : ℝ) : Prop :=
  CurveOn γ a b ∧ InjOn γ (Icc a b)

def ClosedCurveOn {E : Type*} [TopologicalSpace E] (γ : ℝ → E) (a b : ℝ) : Prop :=
  CurveOn γ a b ∧ γ a = γ b

def PolygonalLength {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) {a b : ℝ} (P : Partition a b) : ℝ :=
  ∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖

def CurveLength {E : Type*} [NormedAddCommGroup E] (γ : ℝ → E) (a b : ℝ) : ℝ≥0∞ :=
  ⨆ P : Partition a b, ENNReal.ofReal (PolygonalLength γ P)

def RectifiableCurveOn {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) (a b : ℝ) : Prop :=
  CurveOn γ a b ∧ CurveLength γ a b < ⊤

def pma6_26_contract : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] (γ : ℝ → E) (a b : ℝ),
    (CurveOn γ a b ↔ a ≤ b ∧ ContinuousOn γ (Icc a b)) ∧
    (ArcOn γ a b ↔ CurveOn γ a b ∧ InjOn γ (Icc a b)) ∧
    (ClosedCurveOn γ a b ↔ CurveOn γ a b ∧ γ a = γ b) ∧
    (∀ P : Partition a b, PolygonalLength γ P =
      ∑ i : Fin P.n, ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖) ∧
    (CurveLength γ a b = ⨆ P : Partition a b, ENNReal.ofReal (PolygonalLength γ P)) ∧
    (RectifiableCurveOn γ a b ↔ CurveOn γ a b ∧ CurveLength γ a b < ⊤) ∧
    (a ≤ b → CurveLength γ a b = eVariationOn γ (Icc a b)) ∧
    (RectifiableCurveOn γ a b ↔ CurveOn γ a b ∧ BoundedVariationOn γ (Icc a b))

/-! ### PMA-6.27: Continuous speed and the native Riemann integral for length -/

def pma6_27_contract : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (γ v : ℝ → E) (a b : ℝ), a ≤ b →
    (∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t) →
    ContinuousOn v (Icc a b) →
    RectifiableCurveOn γ a b ∧ RIntegrable (fun t => ‖v t‖) a b ∧
      CurveLength γ a b = ENNReal.ofReal (RIntegral (fun t => ‖v t‖) a b)

/-! Independent variation helpers; these do not define a Riemann integral. -/

theorem continuouslyDifferentiable_curveOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t) :
    CurveOn γ a b :=
  ⟨hab, fun t ht => (hd t ht).continuousWithinAt⟩

theorem continuouslyDifferentiable_boundedVariation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hv : ContinuousOn v (Icc a b)) : BoundedVariationOn γ (Icc a b) := by
  obtain ⟨C, hC, hbound⟩ := (isCompact_Icc.image_of_continuousOn hv).isBounded.exists_pos_norm_le
  have hlip : LipschitzOnWith ⟨C, hC.le⟩ γ (Icc a b) :=
    (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd
      (fun t ht => hbound _ ⟨t, ht, rfl⟩)
  exact hlip.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc a b)

def curvePartitionExtend {a b : ℝ} (P : Partition a b) (i : ℕ) : ℝ :=
  P.point ⟨min i P.n, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

@[simp] theorem curvePartitionExtend_fin {a b : ℝ} (P : Partition a b)
    (i : Fin (P.n + 1)) : curvePartitionExtend P i = P.point i := by
  unfold curvePartitionExtend
  congr 1
  exact Fin.ext (Nat.min_eq_left (Nat.le_of_lt_succ i.isLt))

theorem curvePartitionExtend_monotone {a b : ℝ} (P : Partition a b) :
    Monotone (curvePartitionExtend P) := by
  intro i j hij
  exact P.mono (min_le_min_right P.n hij)

theorem curvePartitionPoint_mem {a b : ℝ} (P : Partition a b) (i : Fin (P.n + 1)) :
    P.point i ∈ Icc a b := by
  constructor
  · simpa only [P.left] using P.mono (Fin.zero_le i)
  · simpa only [P.right] using P.mono (Fin.le_last i)

theorem polygonalLength_le_variation {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) {a b : ℝ} (P : Partition a b) :
    ENNReal.ofReal (PolygonalLength γ P) ≤ eVariationOn γ (Icc a b) := by
  rw [PolygonalLength, ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
  have hsum : (∑ i : Fin P.n,
      ENNReal.ofReal ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖) =
      ∑ i ∈ Finset.range P.n,
        edist (γ (curvePartitionExtend P (i + 1))) (γ (curvePartitionExtend P i)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi : curvePartitionExtend P i = P.point i.castSucc := curvePartitionExtend_fin P i.castSucc
    have his : curvePartitionExtend P (i + 1) = P.point i.succ := curvePartitionExtend_fin P i.succ
    rw [hi, his, edist_dist, dist_eq_norm]
  rw [hsum]
  exact eVariationOn.sum_le (curvePartitionExtend_monotone P)
    (fun i => curvePartitionPoint_mem P _)

def curvePartitionPad {a b : ℝ} (u : ℕ → ℝ) (hu : Monotone u)
    (us : ∀ i, u i ∈ Icc a b) (n : ℕ) : Partition a b where
  n := n + 2
  point := fun i => if i.val = 0 then a else if i.val = n + 2 then b else u (i.val - 1)
  mono := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    have hi := i.isLt
    have hj := j.isLt
    have hai := (us (i.val - 1)).1
    have hbi := (us (i.val - 1)).2
    have haj := (us (j.val - 1)).1
    have hbj := (us (j.val - 1)).2
    have hab := (us 0).1.trans (us 0).2
    dsimp only
    split_ifs <;> grind [Monotone]
  left := by simp
  right := by simp

theorem curveLength_eq_variation {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) {a b : ℝ} (_hab : a ≤ b) :
    CurveLength γ a b = eVariationOn γ (Icc a b) := by
  apply le_antisymm
  · exact iSup_le (polygonalLength_le_variation γ)
  · unfold eVariationOn
    apply iSup_le
    rintro ⟨n, u, hu, us⟩
    let P := curvePartitionPad u hu us n
    apply le_trans (b := ENNReal.ofReal (PolygonalLength γ P))
    · rw [PolygonalLength, ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _),
        ← Fin.sum_univ_eq_sum_range]
      let e : Fin n → Fin P.n := fun i => ⟨i.val + 1, by dsimp [P, curvePartitionPad]; omega⟩
      apply Finset.sum_le_sum_of_injOn e
      · intro i _ j _ hij
        apply Fin.ext
        have he := congrArg Fin.val hij
        dsimp [e] at he
        omega
      · simp
      · intro i _
        have hi := i.isLt
        have hnext : i.val ≠ n + 1 := by omega
        simp [P, curvePartitionPad, e, ne_of_lt hi, hnext, edist_dist, dist_eq_norm]
      · intro i _ _
        exact bot_le
    · exact le_iSup (fun P : Partition a b => ENNReal.ofReal (PolygonalLength γ P)) P

theorem rectifiableCurveOn_iff_variation {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) (a b : ℝ) :
    RectifiableCurveOn γ a b ↔ CurveOn γ a b ∧ BoundedVariationOn γ (Icc a b) := by
  constructor
  · rintro ⟨hc, hl⟩
    refine ⟨hc, ?_⟩
    rw [curveLength_eq_variation γ hc.1] at hl
    exact ne_of_lt hl
  · rintro ⟨hc, hv⟩
    refine ⟨hc, ?_⟩
    rw [curveLength_eq_variation γ hc.1]
    exact lt_top_iff_ne_top.mpr hv

theorem pma6_26 : pma6_26_contract := by
  intro E _ γ a b
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl, rfl, Iff.rfl,
    curveLength_eq_variation γ, rectifiableCurveOn_iff_variation γ a b⟩

theorem continuouslyDifferentiable_rectifiable {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hv : ContinuousOn v (Icc a b)) : RectifiableCurveOn γ a b :=
  (rectifiableCurveOn_iff_variation γ a b).mpr
    ⟨continuouslyDifferentiable_curveOn hab hd, continuouslyDifferentiable_boundedVariation hd hv⟩

theorem curveIncrement_norm_estimate {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {c d ε : ℝ} (w : E)
    (hcd : c ≤ d) (hd : ∀ t ∈ Icc c d, HasDerivWithinAt γ (v t) (Icc c d) t)
    (hv : ∀ t ∈ Icc c d, ‖v t - w‖ ≤ ε) :
    |‖γ d - γ c‖ - (d - c) * ‖w‖| ≤ ε * (d - c) := by
  have hder : ∀ t ∈ Icc c d,
      HasDerivWithinAt (fun x => γ x - x • w) (v t - w) (Icc c d) t := by
    intro t ht
    simpa using (hd t ht).fun_sub ((hasDerivWithinAt_id t (Icc c d)).smul_const w)
  have h := (convex_Icc c d).norm_image_sub_le_of_norm_hasDerivWithin_le hder hv
    (left_mem_Icc.mpr hcd) (right_mem_Icc.mpr hcd)
  have he : (γ d - d • w) - (γ c - c • w) = (γ d - γ c) - (d - c) • w := by
    rw [sub_smul]
    abel
  rw [he, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcd)] at h
  have hh := abs_norm_sub_norm_le (γ d - γ c) ((d - c) • w)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hcd)] at hh
  exact hh.trans h

theorem curve_variation_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {c d C : ℝ}
    (hC : 0 ≤ C) (hd : ∀ t ∈ Icc c d, HasDerivWithinAt γ (v t) (Icc c d) t)
    (hv : ∀ t ∈ Icc c d, ‖v t‖ ≤ C) :
    eVariationOn γ (Icc c d) ≤ ENNReal.ofReal (C * (d - c)) := by
  have hlip : LipschitzOnWith ⟨C, hC⟩ γ (Icc c d) :=
    (convex_Icc c d).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hd hv
  have hh := hlip.comp_eVariationOn_le (mapsTo_id (Icc c d))
  rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_eq_coe_nnreal hC]
  simpa only [Function.comp_id, eVariationOn_id_Icc, NNReal.mk] using hh

theorem curve_variation_partition {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) {a b : ℝ} (P : Partition a b) :
    (∑ i : Fin P.n, eVariationOn γ (P.cell i)) = eVariationOn γ (Icc a b) := by
  have he0 : curvePartitionExtend P 0 = a := by
    simpa only [P.left, Fin.val_zero] using curvePartitionExtend_fin P 0
  have hen : curvePartitionExtend P P.n = b := by
    simpa only [P.right, Fin.val_last] using curvePartitionExtend_fin P (Fin.last P.n)
  have hsum := eVariationOn.sum' γ (curvePartitionExtend_monotone P) (n := P.n)
  rw [he0, hen, ← Fin.sum_univ_eq_sum_range] at hsum
  convert hsum using 1
  apply Finset.sum_congr rfl
  intro i _
  have hi : curvePartitionExtend P i = P.point i.castSucc := curvePartitionExtend_fin P i.castSucc
  have his : curvePartitionExtend P (i + 1) = P.point i.succ := curvePartitionExtend_fin P i.succ
  rw [hi, his]
  rfl

theorem curveLength_le_upperSum {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hb : BoundedOn (fun t => ‖v t‖) a b) (P : Partition a b) :
    CurveLength γ a b ≤ ENNReal.ofReal (upperSum (fun t => ‖v t‖) id P) := by
  have hu (i : Fin P.n) : 0 ≤ cellUpper (fun t => ‖v t‖) P i :=
    (norm_nonneg _).trans (value_le_cellUpper hb P i (P.cell_nonempty i).choose_spec)
  rw [curveLength_eq_variation γ hab, ← curve_variation_partition γ P, upperSum,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hu i)
      (P.weight_nonneg id (fun _ _ _ _ h => h) i))]
  apply Finset.sum_le_sum
  intro i _
  exact curve_variation_le (hu i)
    (fun t ht => (hd t (P.cell_subset i ht)).mono (P.cell_subset i))
    (fun t ht => value_le_cellUpper hb P i ht)

theorem curveLength_toReal_le_upperIntegral {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hb : BoundedOn (fun t => ‖v t‖) a b) :
    (CurveLength γ a b).toReal ≤ upperIntegral (fun t => ‖v t‖) id a b := by
  unfold upperIntegral
  refine le_csInf (s := Set.range (upperSum (fun t => ‖v t‖) id : Partition a b → ℝ))
    ⟨_, Partition.single hab, rfl⟩ ?_
  rintro _ ⟨P, rfl⟩
  have hnonneg : 0 ≤ upperSum (fun t => ‖v t‖) id P := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg ((norm_nonneg _).trans
      (value_le_cellUpper hb P i (P.cell_nonempty i).choose_spec))
      (P.weight_nonneg id (fun _ _ _ _ h => h) i)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (curveLength_le_upperSum hab hd hb P)
  simpa only [ENNReal.toReal_ofReal hnonneg] using h

theorem curve_upperSum_le_polygonal_of_oscillation {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b η : ℝ}
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (P : Partition a b)
    (hosc : ∀ i : Fin P.n, ∀ t ∈ P.cell i, ‖v t - v (P.point i.castSucc)‖ ≤ η) :
    upperSum (fun t => ‖v t‖) id P ≤ PolygonalLength γ P + (2 * η) * (b - a) := by
  have hcell (i : Fin P.n) :
      cellUpper (fun t => ‖v t‖) P i * P.weight id i ≤
        ‖γ (P.point i.succ) - γ (P.point i.castSucc)‖ + (2 * η) * P.weight id i := by
    have hupper : cellUpper (fun t => ‖v t‖) P i ≤ ‖v (P.point i.castSucc)‖ + η := by
      apply csSup_le ((P.cell_nonempty i).image _)
      rintro _ ⟨t, ht, rfl⟩
      have hnorm := norm_sub_norm_le (v t) (v (P.point i.castSucc))
      linarith [hosc i t ht]
    have hinc := curveIncrement_norm_estimate (v (P.point i.castSucc)) (P.cell_order i)
      (fun t ht => (hd t (P.cell_subset i ht)).mono (P.cell_subset i)) (hosc i)
    have hinc' := (abs_le.mp hinc).1
    have hmul := mul_le_mul_of_nonneg_right hupper
      (P.weight_nonneg id (fun _ _ _ _ h => h) i)
    dsimp only [Partition.weight, id_eq] at hmul ⊢
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin P.n))) => hcell i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, P.sum_weights id, id_eq,
    upperSum, PolygonalLength] using hsum

theorem upperIntegral_le_curveLength_toReal {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ v : ℝ → E} {a b : ℝ}
    (hab : a < b) (hd : ∀ t ∈ Icc a b, HasDerivWithinAt γ (v t) (Icc a b) t)
    (hv : ContinuousOn v (Icc a b)) :
    upperIntegral (fun t => ‖v t‖) id a b ≤ (CurveLength γ a b).toReal := by
  have hfinite := (continuouslyDifferentiable_rectifiable hab.le hd hv).2.ne
  have hb := continuousOn_boundedOn hv.norm
  apply le_of_forall_pos_le_add
  intro ε hε
  let η := ε / (2 * (b - a))
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) (sub_pos.mpr hab))
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hv) η hη
  obtain ⟨P, hP⟩ := exists_partition_width_lt hab.le hδ
  have hosc (i : Fin P.n) (t : ℝ) (ht : t ∈ P.cell i) :
      ‖v t - v (P.point i.castSucc)‖ ≤ η := by
    have hdist : dist t (P.point i.castSucc) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)]
      exact (sub_le_sub_right ht.2 _).trans_lt (hP i)
    simpa only [dist_eq_norm] using
      (huc t (P.cell_subset i ht) (P.point i.castSucc) (P.point_mem _) hdist).le
  have hupper := curve_upperSum_le_polygonal_of_oscillation hd P hosc
  have hpoly : PolygonalLength γ P ≤ (CurveLength γ a b).toReal := by
    have h := ENNReal.toReal_mono hfinite
      (le_iSup (fun P : Partition a b => ENNReal.ofReal (PolygonalLength γ P)) P)
    have hnonneg : 0 ≤ PolygonalLength γ P := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    simpa only [ENNReal.toReal_ofReal hnonneg] using h
  have hηeq : (2 * η) * (b - a) = ε := by
    dsimp [η]
    field_simp [(sub_pos.mpr hab).ne']
  rw [hηeq] at hupper
  exact (upperIntegral_le_upperSum hb (fun _ _ _ _ h => h) P).trans
    (hupper.trans (add_le_add_left hpoly ε))

theorem pma6_27 : pma6_27_contract := by
  intro E _ _ γ v a b hab hd hv
  have hrect := continuouslyDifferentiable_rectifiable hab hd hv
  have hint : RIntegrable (fun t => ‖v t‖) a b :=
    rsIntegrable_of_continuousOn hab hv.norm (fun _ _ _ _ h => h)
  refine ⟨hrect, hint, ?_⟩
  rcases lt_or_eq_of_le hab with hlt | heq
  swap
  · subst b
    change CurveLength γ a a = ENNReal.ofReal (RSIntegral (fun t => ‖v t‖) id a a)
    rw [(rsIntegral_same_endpoint (fun t => ‖v t‖) id a).2,
      curveLength_eq_variation γ le_rfl]
    simp
  have heq : (CurveLength γ a b).toReal = upperIntegral (fun t => ‖v t‖) id a b :=
    le_antisymm (curveLength_toReal_le_upperIntegral hab hd hint.2.1)
      (upperIntegral_le_curveLength_toReal hlt hd hv)
  rw [← hint.2.2.2] at heq
  change CurveLength γ a b = ENNReal.ofReal (lowerIntegral (fun t => ‖v t‖) id a b)
  rw [← heq, ENNReal.ofReal_toReal hrect.2.ne]

theorem curveLength_singleton_probe {E : Type*} [NormedAddCommGroup E]
    (γ : ℝ → E) (a : ℝ) : CurveLength γ a a = 0 := by
  rw [curveLength_eq_variation γ le_rfl]
  simp

theorem curveLength_line_probe {a b : ℝ} (hab : a ≤ b) :
    CurveLength (fun t : ℝ => t) a b = ENNReal.ofReal (b - a) := by
  rw [curveLength_eq_variation _ hab]
  exact eVariationOn_id_Icc a b

theorem constant_curve_closed_not_arc_probe (c : ℝ) :
    ClosedCurveOn (fun _ : ℝ => c) 0 1 ∧ ¬ ArcOn (fun _ : ℝ => c) 0 1 := by
  refine ⟨⟨⟨zero_le_one, continuousOn_const⟩, rfl⟩, ?_⟩
  intro h
  have hh := h.2 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) rfl
  norm_num at hh

#print axioms pma6_26
#print axioms pma6_27
#print axioms continuouslyDifferentiable_rectifiable
#print axioms curveIncrement_norm_estimate
#print axioms curveLength_singleton_probe
#print axioms curveLength_line_probe
#print axioms constant_curve_closed_not_arc_probe

end Rudin.PMA.Chapter06
