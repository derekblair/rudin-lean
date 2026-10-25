import Mathlib
import Rudin.PMA.Chapter05
import Rudin.PMA.Chapter06.Basic
import Rudin.PMA.Chapter06.Integrability

noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.14: The source unit step, with its value at zero retained. -/

def UnitStep (x : ℝ) : ℝ := if x ≤ 0 then 0 else 1

def TranslatedStep (s x : ℝ) : ℝ := UnitStep (x - s)

def AtomicStepSum {ι : Type*} (s c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑' i, c i * UnitStep (x - s i)

def pma6_14_contract : Prop :=
  (∀ x : ℝ, x ≤ 0 → UnitStep x = 0) ∧
  (∀ x : ℝ, 0 < x → UnitStep x = 1) ∧
  Monotone UnitStep

/-! ### PMA-6.15: A single strictly interior jump. -/

def pma6_15_contract : Prop :=
  ∀ (a b s : ℝ) (f : ℝ → ℝ), a < s → s < b →
    BoundedOn f a b → ContinuousAt f s →
    RSIntegrable f (TranslatedStep s) a b ∧
      RSIntegral f (TranslatedStep s) a b = f s

/-! ### PMA-6.16: Nonnegative summable weights at distinct interior points. -/

def pma6_16_contract : Prop :=
  ∀ (a b : ℝ) (s c : ℕ → ℝ) (f : ℝ → ℝ),
    (∀ i, s i ∈ Ioo a b) → Function.Injective s →
    (∀ i, 0 ≤ c i) → Summable c → ContinuousOn f (Icc a b) →
    (∀ x : ℝ, Summable (fun i => c i * UnitStep (x - s i))) ∧
    Monotone (AtomicStepSum s c) ∧
    AtomicStepSum s c a = 0 ∧ AtomicStepSum s c b = ∑' i, c i ∧
    Summable (fun i => c i * f (s i)) ∧
    RSIntegrable f (AtomicStepSum s c) a b ∧
    RSIntegral f (AtomicStepSum s c) a b = ∑' i, c i * f (s i)

/-! ### PMA-6.18: Quadratic moment for mass in the closed interval `[0, x]`.

The cumulative mass uses `s i ≤ x`, separately from the strict step in 6.14–6.16.
Atoms at both endpoints are allowed: an atom at `1` contributes its full mass to
the moment, and an atom at `0` is included in `m 0` but has zero moment. -/

/-- Cumulative atomic mass, including the atom at the observation point.
For support in `[0, 1]`, this is the mass in `[0, x]` for `0 ≤ x ≤ 1`. -/
def AtomicMass {ι : Type*} (s c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑' i, if s i ≤ x then c i else 0

def QuadraticPosition (x : ℝ) : ℝ := x ^ 2

def pma6_18_contract : Prop :=
  (∀ m : ℝ → ℝ, MonotoneOn m (Icc (0 : ℝ) 1) →
    RSIntegrable QuadraticPosition m 0 1) ∧
  (∀ m ρ : ℝ → ℝ, MonotoneOn m (Icc (0 : ℝ) 1) →
    (∀ x ∈ Icc (0 : ℝ) 1, HasDerivWithinAt m (ρ x) (Icc (0 : ℝ) 1) x) →
    RIntegrable ρ 0 1 →
    RIntegrable (fun x => x ^ 2 * ρ x) 0 1 ∧
    RSIntegral QuadraticPosition m 0 1 = RIntegral (fun x => x ^ 2 * ρ x) 0 1) ∧
  (∀ s c : ℕ → ℝ, (∀ i, s i ∈ Icc (0 : ℝ) 1) → Function.Injective s →
    (∀ i, 0 ≤ c i) → Summable c →
    Summable (fun i => c i * s i ^ 2) ∧
    RSIntegrable QuadraticPosition (AtomicMass s c) 0 1 ∧
    RSIntegral QuadraticPosition (AtomicMass s c) 0 1 = ∑' i, c i * s i ^ 2) ∧
  (∀ (n : ℕ) (s c : Fin n → ℝ),
    (∀ i, s i ∈ Icc (0 : ℝ) 1) → Function.Injective s → (∀ i, 0 ≤ c i) →
    RSIntegrable QuadraticPosition (AtomicMass s c) 0 1 ∧
    RSIntegral QuadraticPosition (AtomicMass s c) 0 1 = ∑ i, c i * s i ^ 2)

theorem pma6_14 : pma6_14_contract := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp [UnitStep, hx]
  · intro x hx
    simp [UnitStep, not_le.mpr hx]
  · intro x y hxy
    by_cases hx : x ≤ 0
    · by_cases hy : y ≤ 0 <;> simp [UnitStep, hx, hy]
    · have hy : ¬ y ≤ 0 := fun hy => hx (hxy.trans hy)
      simp [UnitStep, hx, hy]

theorem translatedStep_monotone (s : ℝ) : Monotone (TranslatedStep s) := by
  intro x y hxy
  exact pma6_14.2.2 (sub_le_sub_right hxy s)

theorem atomicStepSum_eq_jumpSumLeft {ι : Type*} (s c : ι → ℝ) :
    AtomicStepSum s c = Chapter04.JumpSumLeft s c := by
  funext x
  apply tsum_congr
  intro i
  by_cases hx : x ≤ s i
  · simp [UnitStep, hx, not_lt.mpr hx]
  · simp [UnitStep, hx, lt_of_not_ge hx]

theorem atomicStepSum_summable {ι : Type*} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (x : ℝ) :
    Summable (fun i => c i * UnitStep (x - s i)) := by
  have heq : (fun i => c i * UnitStep (x - s i)) =
      (fun i => if s i < x then c i else 0) := by
    funext i
    by_cases hx : x ≤ s i
    · simp [UnitStep, hx, not_lt.mpr hx]
    · simp [UnitStep, hx, lt_of_not_ge hx]
  rw [heq]
  exact Chapter04.jumpSumLeft_summable hc hnonneg x

theorem atomicStepSum_monotone {ι : Type*} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) : Monotone (AtomicStepSum s c) := by
  rw [atomicStepSum_eq_jumpSumLeft]
  exact Chapter04.jumpSumLeft_monotone hc hnonneg

theorem atomicStepSum_endpoints {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hs : ∀ i, s i ∈ Ioo a b) :
    AtomicStepSum s c a = 0 ∧ AtomicStepSum s c b = ∑' i, c i := by
  constructor
  · unfold AtomicStepSum
    convert tsum_zero using 1
    congr 1
    funext i
    simp [UnitStep, (hs i).1.le]
  · apply tsum_congr
    intro i
    simp [UnitStep, not_le.mpr (hs i).2]

theorem atomic_weighted_samples_summable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    {f : ℝ → ℝ} (hs : ∀ i, s i ∈ Icc a b)
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (hf : ContinuousOn f (Icc a b)) :
    Summable (fun i => c i * f (s i)) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.abs
  apply (hc.mul_left M).of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hnonneg i), Real.norm_eq_abs]
  calc
    c i * |f (s i)| ≤ c i * M := mul_le_mul_of_nonneg_left
      (hM ⟨s i, hs i, rfl⟩) (hnonneg i)
    _ = M * c i := mul_comm _ _

theorem translatedStep_cell_of_weight_ne_zero {a b s : ℝ} (P : Partition a b)
    (i : Fin P.n) (hw : P.weight (TranslatedStep s) i ≠ 0) : s ∈ P.cell i := by
  by_cases hl : P.point i.castSucc ≤ s
  · refine ⟨hl, ?_⟩
    by_contra hr
    have hr' : P.point i.succ ≤ s := (lt_of_not_ge hr).le
    exact hw (by simp [Partition.weight, TranslatedStep, UnitStep, hl, hr'])
  · have hr : ¬ P.point i.succ ≤ s := fun h => hl ((P.cell_order i).trans h)
    exact (hw (by simp [Partition.weight, TranslatedStep, UnitStep, hl, hr])).elim

theorem translatedStep_sum_bounds {a b s : ℝ} {f : ℝ → ℝ}
    (has : a < s) (hsb : s < b) (hf : BoundedOn f a b) (P : Partition a b) :
    lowerSum f (TranslatedStep s) P ≤ f s ∧ f s ≤ upperSum f (TranslatedStep s) P := by
  have hsum : (∑ i : Fin P.n, f s * P.weight (TranslatedStep s) i) = f s := by
    rw [← Finset.mul_sum, P.sum_weights]
    simp [TranslatedStep, UnitStep, has.le, not_le.mpr hsb]
  have hn := P.weight_nonneg (TranslatedStep s) ((translatedStep_monotone s).monotoneOn (Icc a b))
  constructor
  · calc
      lowerSum f (TranslatedStep s) P ≤ ∑ i : Fin P.n, f s * P.weight (TranslatedStep s) i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hw : P.weight (TranslatedStep s) i = 0
        · simp [hw]
        · exact mul_le_mul_of_nonneg_right
            (cellLower_le_value hf P i (translatedStep_cell_of_weight_ne_zero P i hw)) (hn i)
      _ = f s := hsum
  · rw [← hsum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hw : P.weight (TranslatedStep s) i = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_right
        (value_le_cellUpper hf P i (translatedStep_cell_of_weight_ne_zero P i hw)) (hn i)

def jumpPartition {a s t b : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
    Partition a b where
  n := 3
  point := ![a, s, t, b]
  mono := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    fin_cases i <;> simp_all
  left := rfl
  right := rfl

theorem jumpPartition_sums {a s t b : ℝ} (has : a < s) (hst : s < t) (htb : t < b)
    (f : ℝ → ℝ) :
    lowerSum f (TranslatedStep s) (jumpPartition has.le hst.le htb.le) = sInf (f '' Icc s t) ∧
    upperSum f (TranslatedStep s) (jumpPartition has.le hst.le htb.le) = sSup (f '' Icc s t) := by
  dsimp only [lowerSum, upperSum, jumpPartition]
  simp [cellLower, cellUpper, Partition.cell,
    Partition.weight, TranslatedStep, UnitStep, Fin.sum_univ_succ,
    has.le, not_le.mpr hst, not_le.mpr (hst.trans htb)]

theorem translatedStep_close_partition {a b s : ℝ} {f : ℝ → ℝ}
    (has : a < s) (hsb : s < b) (hc : ContinuousAt f s) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Partition a b, f s - ε < lowerSum f (TranslatedStep s) P ∧
      upperSum f (TranslatedStep s) P < f s + ε := by
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hc (ε / 2) (half_pos hε)
  let t := s + min δ (b - s) / 2
  have hm : 0 < min δ (b - s) := lt_min hδ (sub_pos.mpr hsb)
  have hst : s < t := by dsimp [t]; linarith
  have htb : t < b := by dsimp [t]; linarith [min_le_right δ (b - s)]
  have htδ : t - s < δ := by dsimp [t]; linarith [min_le_left δ (b - s)]
  have hvalues : ∀ x ∈ Icc s t, f s - ε / 2 ≤ f x ∧ f x ≤ f s + ε / 2 := by
    intro x hx
    have hd : dist x s < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      linarith [hx.2]
    have hv := hclose hd
    rw [Real.dist_eq] at hv
    constructor <;> linarith [(abs_lt.mp hv).1, (abs_lt.mp hv).2]
  have hne : (f '' Icc s t).Nonempty := ⟨f s, s, ⟨le_rfl, hst.le⟩, rfl⟩
  have hl : f s - ε / 2 ≤ sInf (f '' Icc s t) := by
    apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    exact (hvalues x hx).1
  have hu : sSup (f '' Icc s t) ≤ f s + ε / 2 := by
    apply csSup_le hne
    rintro _ ⟨x, hx, rfl⟩
    exact (hvalues x hx).2
  refine ⟨jumpPartition has.le hst.le htb.le, ?_, ?_⟩
  · rw [(jumpPartition_sums has hst htb f).1]
    linarith
  · rw [(jumpPartition_sums has hst htb f).2]
    linarith

theorem pma6_15 : pma6_15_contract := by
  intro a b s f has hsb hf hc
  have hab : a ≤ b := (has.trans hsb).le
  have hl : lowerIntegral f (TranslatedStep s) a b = f s := by
    apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
    · exact ⟨_, ⟨Partition.single hab, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (translatedStep_sum_bounds has hsb hf P).1
    · intro w hw
      obtain ⟨P, hP, _⟩ := translatedStep_close_partition has hsb hc
        (half_pos (sub_pos.mpr hw))
      exact ⟨_, ⟨P, rfl⟩, by linarith⟩
  have hu : upperIntegral f (TranslatedStep s) a b = f s := by
    apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · exact ⟨_, ⟨Partition.single hab, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (translatedStep_sum_bounds has hsb hf P).2
    · intro w hw
      obtain ⟨P, _, hP⟩ := translatedStep_close_partition has hsb hc
        (half_pos (sub_pos.mpr hw))
      exact ⟨_, ⟨P, rfl⟩, by linarith⟩
  exact ⟨⟨hab, hf, (translatedStep_monotone s).monotoneOn (Icc a b), hl.trans hu.symm⟩, hl⟩

theorem atomicStepSum_weight_summable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (i : Fin P.n) :
    Summable (fun j => c j * P.weight (TranslatedStep (s j)) i) := by
  simpa only [Partition.weight, TranslatedStep, mul_sub] using
    (atomicStepSum_summable (s := s) hc hnonneg (P.point i.succ)).sub
      (atomicStepSum_summable (s := s) hc hnonneg (P.point i.castSucc))

theorem atomicStepSum_weight_eq_tsum {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (i : Fin P.n) :
    P.weight (AtomicStepSum s c) i = ∑' j, c j * P.weight (TranslatedStep (s j)) i := by
  unfold Partition.weight AtomicStepSum
  rw [← (atomicStepSum_summable (s := s) hc hnonneg (P.point i.succ)).tsum_sub
    (atomicStepSum_summable (s := s) hc hnonneg (P.point i.castSucc))]
  apply tsum_congr
  intro j
  simp [TranslatedStep, mul_sub]

theorem atomicStepSum_cells_summable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (v : Fin P.n → ℝ) :
    Summable (fun j => c j * ∑ i : Fin P.n, v i * P.weight (TranslatedStep (s j)) i) := by
  have h := summable_sum (s := (Finset.univ : Finset (Fin P.n)))
    (fun i _ => (atomicStepSum_weight_summable (s := s) hc hnonneg P i).mul_left (v i))
  simpa only [Finset.mul_sum, mul_left_comm] using h

theorem atomicStepSum_cells_eq_tsum {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (v : Fin P.n → ℝ) :
    (∑ i : Fin P.n, v i * P.weight (AtomicStepSum s c) i) =
      ∑' j, c j * ∑ i : Fin P.n, v i * P.weight (TranslatedStep (s j)) i := by
  simp_rw [Finset.mul_sum, mul_left_comm (c _) (v _)]
  rw [Summable.tsum_finsetSum (fun i _ =>
    (atomicStepSum_weight_summable hc hnonneg P i).mul_left (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, atomicStepSum_weight_eq_tsum hc hnonneg P i]

theorem atomicStepSum_partition_bounds {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    {f : ℝ → ℝ} (hs : ∀ i, s i ∈ Ioo a b) (hc : Summable c)
    (hnonneg : ∀ i, 0 ≤ c i) (hf : ContinuousOn f (Icc a b))
    (hbdd : BoundedOn f a b) (P : Partition a b) :
    lowerSum f (AtomicStepSum s c) P ≤ ∑' j, c j * f (s j) ∧
      (∑' j, c j * f (s j)) ≤ upperSum f (AtomicStepSum s c) P := by
  have hsample := atomic_weighted_samples_summable (fun i => Ioo_subset_Icc_self (hs i)) hc hnonneg hf
  constructor
  · rw [lowerSum, atomicStepSum_cells_eq_tsum hc hnonneg P (cellLower f P)]
    apply Summable.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left
        (translatedStep_sum_bounds (hs j).1 (hs j).2 hbdd P).1 (hnonneg j))
      (atomicStepSum_cells_summable hc hnonneg P (cellLower f P)) hsample
  · rw [upperSum, atomicStepSum_cells_eq_tsum hc hnonneg P (cellUpper f P)]
    apply Summable.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left
        (translatedStep_sum_bounds (hs j).1 (hs j).2 hbdd P).2 (hnonneg j))
      hsample (atomicStepSum_cells_summable hc hnonneg P (cellUpper f P))

theorem atomicStepSum_integral_of_integrable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    {f : ℝ → ℝ} (hs : ∀ i, s i ∈ Ioo a b) (hc : Summable c)
    (hnonneg : ∀ i, 0 ≤ c i) (hf : ContinuousOn f (Icc a b))
    (hi : RSIntegrable f (AtomicStepSum s c) a b) :
    RSIntegral f (AtomicStepSum s c) a b = ∑' j, c j * f (s j) := by
  have hlow : lowerIntegral f (AtomicStepSum s c) a b ≤ ∑' j, c j * f (s j) := by
    apply csSup_le
    · exact ⟨_, ⟨Partition.single hi.1, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (atomicStepSum_partition_bounds hs hc hnonneg hf hi.2.1 P).1
  have hupp : (∑' j, c j * f (s j)) ≤ upperIntegral f (AtomicStepSum s c) a b := by
    apply le_csInf
    · exact ⟨_, ⟨Partition.single hi.1, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (atomicStepSum_partition_bounds hs hc hnonneg hf hi.2.1 P).2
  change lowerIntegral f (AtomicStepSum s c) a b = ∑' j, c j * f (s j)
  exact le_antisymm hlow (hi.2.2.2.symm ▸ hupp)

theorem atomicStepSum_integrable {ι : Type*} {a b : ℝ} {s c : ι → ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i)
    (hf : ContinuousOn f (Icc a b)) : RSIntegrable f (AtomicStepSum s c) a b :=
  rsIntegrable_of_continuousOn hab hf ((atomicStepSum_monotone hc hnonneg).monotoneOn (Icc a b))

theorem pma6_16 : pma6_16_contract := by
  intro a b s c f hs _hinj hnonneg hc hf
  have hab : a ≤ b := ((hs 0).1.trans (hs 0).2).le
  have hi := atomicStepSum_integrable (s := s) hab hc hnonneg hf
  exact ⟨atomicStepSum_summable hc hnonneg,
    atomicStepSum_monotone hc hnonneg,
    (atomicStepSum_endpoints hs).1, (atomicStepSum_endpoints hs).2,
    atomic_weighted_samples_summable (fun i => Ioo_subset_Icc_self (hs i)) hc hnonneg hf, hi,
    atomicStepSum_integral_of_integrable hs hc hnonneg hf hi⟩

/-- The closed cumulative contribution of one unit atom. -/
def ClosedAtomicStep (s x : ℝ) : ℝ := if s ≤ x then 1 else 0

theorem closedAtomicStep_monotone (s : ℝ) : Monotone (ClosedAtomicStep s) := by
  intro x y hxy
  by_cases hx : s ≤ x
  · simp [ClosedAtomicStep, hx, hx.trans hxy]
  · by_cases hy : s ≤ y <;> simp [ClosedAtomicStep, hx, hy]

/-- With nonnegative locations, the cumulative mass is exactly the sum over `[0, x]`. -/
theorem atomicMass_eq_closed_interval {ι : Type*} {s c : ι → ℝ}
    (hs : ∀ i, 0 ≤ s i) (x : ℝ) :
    AtomicMass s c x = ∑' i, if s i ∈ Icc 0 x then c i else 0 := by
  apply tsum_congr
  intro i
  simp only [mem_Icc, hs i, true_and]

theorem atomicMass_summable {ι : Type*} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (x : ℝ) :
    Summable (fun i => c i * ClosedAtomicStep (s i) x) := by
  simpa only [ClosedAtomicStep, mul_ite, mul_one, mul_zero] using
    Chapter04.jumpSumRight_summable (p := s) hc hnonneg x

theorem atomicMass_monotone {ι : Type*} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) : Monotone (AtomicMass s c) :=
  Chapter04.jumpSumRight_monotone hc hnonneg

/-- The initial mass includes the left endpoint, and the final mass includes the right endpoint. -/
theorem atomicMass_endpoints {ι : Type*} {s c : ι → ℝ}
    (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) :
    AtomicMass s c 0 = (∑' i, if s i = 0 then c i else 0) ∧
    AtomicMass s c 1 = ∑' i, c i := by
  constructor
  · apply tsum_congr
    intro i
    have h : s i ≤ 0 ↔ s i = 0 := ⟨fun hi => le_antisymm hi (hs i).1, fun hi => hi.le⟩
    simp only [h]
  · apply tsum_congr
    intro i
    simp [(hs i).2]

theorem closedAtomicStep_cell_of_weight_ne_zero {a b s : ℝ} (P : Partition a b)
    (i : Fin P.n) (hw : P.weight (ClosedAtomicStep s) i ≠ 0) : s ∈ P.cell i := by
  by_cases hl : s ≤ P.point i.castSucc
  · have hr : s ≤ P.point i.succ := hl.trans (P.cell_order i)
    exact (hw (by simp [Partition.weight, ClosedAtomicStep, hl, hr])).elim
  · refine ⟨(lt_of_not_ge hl).le, ?_⟩
    by_contra hr
    exact hw (by simp [Partition.weight, ClosedAtomicStep, hl, hr])

/-- An atom at the left endpoint is already in the initial cumulative mass;
its contribution to these bounds vanishes when `f a = 0`. -/
theorem closedAtomicStep_sum_bounds {a b s : ℝ} {f : ℝ → ℝ}
    (hs : s ∈ Icc a b) (ha : f a = 0) (hf : BoundedOn f a b) (P : Partition a b) :
    lowerSum f (ClosedAtomicStep s) P ≤ f s ∧ f s ≤ upperSum f (ClosedAtomicStep s) P := by
  have hsum : (∑ i : Fin P.n, f s * P.weight (ClosedAtomicStep s) i) = f s := by
    rw [← Finset.mul_sum, P.sum_weights]
    by_cases hsa : s = a
    · simp [hsa, ha]
    · have has : ¬ s ≤ a := fun h => hsa (le_antisymm h hs.1)
      simp [ClosedAtomicStep, hs.2, has]
  have hn := P.weight_nonneg (ClosedAtomicStep s)
    ((closedAtomicStep_monotone s).monotoneOn (Icc a b))
  constructor
  · calc
      lowerSum f (ClosedAtomicStep s) P ≤ ∑ i : Fin P.n, f s * P.weight (ClosedAtomicStep s) i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hw : P.weight (ClosedAtomicStep s) i = 0
        · simp [hw]
        · exact mul_le_mul_of_nonneg_right
            (cellLower_le_value hf P i (closedAtomicStep_cell_of_weight_ne_zero P i hw)) (hn i)
      _ = f s := hsum
  · rw [← hsum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hw : P.weight (ClosedAtomicStep s) i = 0
    · simp [hw]
    · exact mul_le_mul_of_nonneg_right
        (value_le_cellUpper hf P i (closedAtomicStep_cell_of_weight_ne_zero P i hw)) (hn i)

theorem atomicMass_weight_summable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (i : Fin P.n) :
    Summable (fun j => c j * P.weight (ClosedAtomicStep (s j)) i) := by
  simpa only [Partition.weight, mul_sub] using
    (atomicMass_summable (s := s) hc hnonneg (P.point i.succ)).sub
      (atomicMass_summable (s := s) hc hnonneg (P.point i.castSucc))

theorem atomicMass_weight_eq_tsum {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (i : Fin P.n) :
    P.weight (AtomicMass s c) i = ∑' j, c j * P.weight (ClosedAtomicStep (s j)) i := by
  have heq : AtomicMass s c = fun x => ∑' j, c j * ClosedAtomicStep (s j) x := by
    funext x
    simp only [AtomicMass, ClosedAtomicStep, mul_ite, mul_one, mul_zero]
  rw [Partition.weight, heq,
    ← (atomicMass_summable (s := s) hc hnonneg (P.point i.succ)).tsum_sub
      (atomicMass_summable (s := s) hc hnonneg (P.point i.castSucc))]
  apply tsum_congr
  intro j
  simp [Partition.weight, mul_sub]

theorem atomicMass_cells_summable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (v : Fin P.n → ℝ) :
    Summable (fun j => c j * ∑ i : Fin P.n, v i * P.weight (ClosedAtomicStep (s j)) i) := by
  have h := summable_sum (s := (Finset.univ : Finset (Fin P.n)))
    (fun i _ => (atomicMass_weight_summable (s := s) hc hnonneg P i).mul_left (v i))
  simpa only [Finset.mul_sum, mul_left_comm] using h

theorem atomicMass_cells_eq_tsum {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) (P : Partition a b) (v : Fin P.n → ℝ) :
    (∑ i : Fin P.n, v i * P.weight (AtomicMass s c) i) =
      ∑' j, c j * ∑ i : Fin P.n, v i * P.weight (ClosedAtomicStep (s j)) i := by
  simp_rw [Finset.mul_sum, mul_left_comm (c _) (v _)]
  rw [Summable.tsum_finsetSum (fun i _ =>
    (atomicMass_weight_summable hc hnonneg P i).mul_left (v i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [tsum_mul_left, atomicMass_weight_eq_tsum hc hnonneg P i]

theorem atomicMass_partition_bounds {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    {f : ℝ → ℝ} (hs : ∀ i, s i ∈ Icc a b) (hc : Summable c)
    (hnonneg : ∀ i, 0 ≤ c i) (hf : ContinuousOn f (Icc a b)) (ha : f a = 0)
    (hbdd : BoundedOn f a b) (P : Partition a b) :
    lowerSum f (AtomicMass s c) P ≤ ∑' j, c j * f (s j) ∧
      (∑' j, c j * f (s j)) ≤ upperSum f (AtomicMass s c) P := by
  have hsample := atomic_weighted_samples_summable hs hc hnonneg hf
  constructor
  · rw [lowerSum, atomicMass_cells_eq_tsum hc hnonneg P (cellLower f P)]
    apply Summable.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left
        (closedAtomicStep_sum_bounds (hs j) ha hbdd P).1 (hnonneg j))
      (atomicMass_cells_summable hc hnonneg P (cellLower f P)) hsample
  · rw [upperSum, atomicMass_cells_eq_tsum hc hnonneg P (cellUpper f P)]
    apply Summable.tsum_le_tsum
      (fun j => mul_le_mul_of_nonneg_left
        (closedAtomicStep_sum_bounds (hs j) ha hbdd P).2 (hnonneg j))
      hsample (atomicMass_cells_summable hc hnonneg P (cellUpper f P))

theorem atomicMass_integral_of_integrable {ι : Type*} {a b : ℝ} {s c : ι → ℝ}
    {f : ℝ → ℝ} (hs : ∀ i, s i ∈ Icc a b) (hc : Summable c)
    (hnonneg : ∀ i, 0 ≤ c i) (hf : ContinuousOn f (Icc a b)) (ha : f a = 0)
    (hi : RSIntegrable f (AtomicMass s c) a b) :
    RSIntegral f (AtomicMass s c) a b = ∑' j, c j * f (s j) := by
  have hlow : lowerIntegral f (AtomicMass s c) a b ≤ ∑' j, c j * f (s j) := by
    apply csSup_le
    · exact ⟨_, ⟨Partition.single hi.1, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (atomicMass_partition_bounds hs hc hnonneg hf ha hi.2.1 P).1
  have hupp : (∑' j, c j * f (s j)) ≤ upperIntegral f (AtomicMass s c) a b := by
    apply le_csInf
    · exact ⟨_, ⟨Partition.single hi.1, rfl⟩⟩
    · rintro _ ⟨P, rfl⟩
      exact (atomicMass_partition_bounds hs hc hnonneg hf ha hi.2.1 P).2
  change lowerIntegral f (AtomicMass s c) a b = ∑' j, c j * f (s j)
  exact le_antisymm hlow (hi.2.2.2.symm ▸ hupp)

theorem atomicMass_integrable {ι : Type*} {a b : ℝ} {s c : ι → ℝ} {f : ℝ → ℝ}
    (hab : a ≤ b) (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i)
    (hf : ContinuousOn f (Icc a b)) : RSIntegrable f (AtomicMass s c) a b :=
  rsIntegrable_of_continuousOn hab hf ((atomicMass_monotone hc hnonneg).monotoneOn (Icc a b))

theorem quadraticPosition_continuous : Continuous QuadraticPosition := continuous_id.pow 2

theorem quadraticMoment_integrable {m : ℝ → ℝ} (hm : MonotoneOn m (Icc (0 : ℝ) 1)) :
    RSIntegrable QuadraticPosition m 0 1 :=
  rsIntegrable_of_continuousOn (by norm_num) quadraticPosition_continuous.continuousOn hm

theorem atomicQuadraticMoment {ι : Type*} {s c : ι → ℝ}
    (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) (hc : Summable c) (hnonneg : ∀ i, 0 ≤ c i) :
    Summable (fun i => c i * s i ^ 2) ∧
    RSIntegrable QuadraticPosition (AtomicMass s c) 0 1 ∧
    RSIntegral QuadraticPosition (AtomicMass s c) 0 1 = ∑' i, c i * s i ^ 2 := by
  have hf : ContinuousOn QuadraticPosition (Icc (0 : ℝ) 1) :=
    quadraticPosition_continuous.continuousOn
  have hi : RSIntegrable QuadraticPosition (AtomicMass s c) 0 1 :=
    atomicMass_integrable (s := s) (by norm_num : (0 : ℝ) ≤ 1) hc hnonneg hf
  refine ⟨?_, hi, ?_⟩
  · simpa only [QuadraticPosition] using
      atomic_weighted_samples_summable (f := QuadraticPosition) hs hc hnonneg hf
  · simpa only [QuadraticPosition] using
      atomicMass_integral_of_integrable (f := QuadraticPosition) hs hc hnonneg hf
        (by norm_num [QuadraticPosition]) hi

theorem finiteAtomicQuadraticMoment {n : ℕ} {s c : Fin n → ℝ}
    (hs : ∀ i, s i ∈ Icc (0 : ℝ) 1) (hnonneg : ∀ i, 0 ≤ c i) :
    RSIntegrable QuadraticPosition (AtomicMass s c) 0 1 ∧
    RSIntegral QuadraticPosition (AtomicMass s c) 0 1 = ∑ i, c i * s i ^ 2 := by
  simpa only [tsum_fintype] using (atomicQuadraticMoment hs (hasSum_fintype c).summable hnonneg).2

theorem translatedStep_mem_unit_interval (s x : ℝ) :
    0 ≤ TranslatedStep s x ∧ TranslatedStep s x ≤ 1 := by
  by_cases hx : x ≤ s <;> simp [TranslatedStep, UnitStep, hx]

theorem translatedStep_bounded (s a b : ℝ) : BoundedOn (TranslatedStep s) a b := by
  refine ⟨1, ?_⟩
  intro x _
  rw [abs_of_nonneg (translatedStep_mem_unit_interval s x).1]
  exact (translatedStep_mem_unit_interval s x).2

/-- Shared jumps need not be Darboux-integrable: the source caution after 6.10. -/
theorem translatedStep_self_sums {a b s : ℝ} (has : a < s) (hsb : s < b)
    (P : Partition a b) :
    lowerSum (TranslatedStep s) (TranslatedStep s) P = 0 ∧
    upperSum (TranslatedStep s) (TranslatedStep s) P = 1 := by
  have hmono := (translatedStep_monotone s).monotoneOn (Icc a b)
  have hbound := translatedStep_bounded s a b
  have hdiff : TranslatedStep s b - TranslatedStep s a = 1 := by
    simp [TranslatedStep, UnitStep, has.le, not_le.mpr hsb]
  constructor
  · apply le_antisymm
    · simpa [TranslatedStep, UnitStep] using (translatedStep_sum_bounds has hsb hbound P).1
    · simpa only [zero_mul] using lowerSum_lower_bound hmono
        (fun x _ => (translatedStep_mem_unit_interval s x).1) P
  · apply le_antisymm
    · simpa only [hdiff, one_mul] using upperSum_upper_bound hmono
        (fun x _ => (translatedStep_mem_unit_interval s x).2) P
    · calc
        1 = ∑ i : Fin P.n, P.weight (TranslatedStep s) i := (P.sum_weights _).trans hdiff |>.symm
        _ ≤ upperSum (TranslatedStep s) (TranslatedStep s) P := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hr : P.point i.succ ≤ s
          · have hl : P.point i.castSucc ≤ s := (P.cell_order i).trans hr
            simp [Partition.weight, TranslatedStep, UnitStep, hr, hl]
          · have hv : 1 ≤ cellUpper (TranslatedStep s) P i := by
              simpa [TranslatedStep, UnitStep, hr] using
                value_le_cellUpper hbound P i ⟨P.cell_order i, le_rfl⟩
            simpa only [one_mul] using mul_le_mul_of_nonneg_right hv
              (P.weight_nonneg _ hmono i)

theorem translatedStep_not_RSIntegrable_self {a b s : ℝ} (has : a < s) (hsb : s < b) :
    ¬ RSIntegrable (TranslatedStep s) (TranslatedStep s) a b := by
  have : Nonempty (Partition a b) := Partition.nonempty (has.trans hsb).le
  have hl : (lowerSum (TranslatedStep s) (TranslatedStep s) : Partition a b → ℝ) =
      fun _ => 0 := funext fun P => (translatedStep_self_sums has hsb P).1
  have hu : (upperSum (TranslatedStep s) (TranslatedStep s) : Partition a b → ℝ) =
      fun _ => 1 := funext fun P => (translatedStep_self_sums has hsb P).2
  intro h
  have heq := h.2.2.2
  simp [lowerIntegral, upperIntegral, hl, hu] at heq

theorem translatedStep_continuousAt_of_ne {s x : ℝ} (hx : x ≠ s) :
    ContinuousAt (TranslatedStep s) x := by
  rcases lt_or_gt_of_ne hx with hxs | hsx
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hxs] with y hy
    simp [TranslatedStep, UnitStep, (show y ≤ s from le_of_lt hy)]
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hsx] with y hy
    simp [TranslatedStep, UnitStep, not_le.mpr (show s < y from hy)]

theorem translatedStep_not_continuousWithinAt {a b s : ℝ} (has : a < s) (hsb : s < b) :
    ¬ ContinuousWithinAt (TranslatedStep s) (Icc a b) s := by
  intro hc
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousWithinAt_iff.mp hc (1 / 2) (by norm_num)
  let x := s + min δ (b - s) / 2
  have hm : 0 < min δ (b - s) := lt_min hδ (sub_pos.mpr hsb)
  have hsx : s < x := by dsimp [x]; linarith
  have hxb : x < b := by dsimp [x]; linarith [min_le_right δ (b - s)]
  have hxd : dist x s < δ := by
    rw [Real.dist_eq, abs_of_pos (sub_pos.mpr hsx)]
    dsimp [x]
    linarith [min_le_left δ (b - s)]
  have hbad := hclose ⟨(has.trans hsx).le, hxb.le⟩ hxd
  norm_num [TranslatedStep, UnitStep, not_le.mpr hsx, Real.dist_eq] at hbad

theorem unitStep_source_caution :
    ¬ ContinuousWithinAt UnitStep (Icc (-1 : ℝ) 1) 0 ∧
    ¬ RSIntegrable UnitStep UnitStep (-1) 1 := by
  have heq : TranslatedStep 0 = UnitStep := by funext x; simp [TranslatedStep]
  exact ⟨heq ▸ translatedStep_not_continuousWithinAt (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1),
    heq ▸ translatedStep_not_RSIntegrable_self (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1)⟩

#print axioms pma6_14
#print axioms pma6_15
#print axioms pma6_16
#print axioms atomicQuadraticMoment
#print axioms finiteAtomicQuadraticMoment
#print axioms atomicStepSum_integral_of_integrable
#print axioms translatedStep_not_RSIntegrable_self
#print axioms unitStep_source_caution

end Rudin.PMA.Chapter06
