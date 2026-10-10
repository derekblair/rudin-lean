import Rudin.PMA.Chapter06.Criterion

noncomputable section
open Set Filter Topology
open scoped BigOperators

namespace Rudin.PMA.Chapter06

/-! ### PMA-6.8: Continuous integrands. -/

def pma6_8_contract : Prop :=
  ∀ (f α : ℝ → ℝ) (a b : ℝ), a ≤ b →
    ContinuousOn f (Icc a b) → MonotoneOn α (Icc a b) → RSIntegrable f α a b

/-! ### PMA-6.9: Monotone integrands and continuous integrators. -/

def pma6_9_contract : Prop :=
  ∀ (f α : ℝ → ℝ) (a b : ℝ), a ≤ b →
    (MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) →
    MonotoneOn α (Icc a b) → ContinuousOn α (Icc a b) → RSIntegrable f α a b

/-! ### PMA-6.10: Finitely many discontinuities and the shared-jump caution. -/

def pma6_10_contract : Prop :=
  (∀ (f α : ℝ → ℝ) (a b : ℝ), a ≤ b → BoundedOn f a b →
    MonotoneOn α (Icc a b) →
    {x | x ∈ Icc a b ∧ ¬ ContinuousWithinAt f (Icc a b) x}.Finite →
    (∀ x ∈ Icc a b, ¬ ContinuousWithinAt f (Icc a b) x →
      ContinuousWithinAt α (Icc a b) x) → RSIntegrable f α a b) ∧
  ¬ RSIntegrable (fun x : ℝ => if x ≤ 0 then 0 else 1)
    (fun x : ℝ => if x ≤ 0 then 0 else 1) (-1) 1

/-! ### PMA-6.11: Continuous composition. -/

def pma6_11_contract : Prop :=
  ∀ (f α φ : ℝ → ℝ) (a b m M : ℝ), RSIntegrable f α a b →
    (∀ x ∈ Icc a b, f x ∈ Icc m M) → ContinuousOn φ (Icc m M) →
    RSIntegrable (φ ∘ f) α a b

/-! ### PMA-6.12: All five algebraic and order properties. -/

def pma6_12_contract : Prop :=
  (∀ (f g α : ℝ → ℝ) (a b c : ℝ), RSIntegrable f α a b →
    RSIntegrable g α a b →
    RSIntegrable (fun x => f x + g x) α a b ∧
    RSIntegral (fun x => f x + g x) α a b = RSIntegral f α a b + RSIntegral g α a b ∧
    RSIntegrable (fun x => c * f x) α a b ∧
    RSIntegral (fun x => c * f x) α a b = c * RSIntegral f α a b) ∧
  (∀ (f g α : ℝ → ℝ) (a b : ℝ), RSIntegrable f α a b →
    RSIntegrable g α a b → (∀ x ∈ Icc a b, f x ≤ g x) →
    RSIntegral f α a b ≤ RSIntegral g α a b) ∧
  (∀ (f α : ℝ → ℝ) (a b c : ℝ), a < c → c < b → RSIntegrable f α a b →
    RSIntegrable f α a c ∧ RSIntegrable f α c b ∧
    RSIntegral f α a b = RSIntegral f α a c + RSIntegral f α c b) ∧
  (∀ (f α : ℝ → ℝ) (a b M : ℝ), RSIntegrable f α a b →
    (∀ x ∈ Icc a b, |f x| ≤ M) →
    |RSIntegral f α a b| ≤ M * (α b - α a)) ∧
  (∀ (f α β : ℝ → ℝ) (a b c : ℝ), RSIntegrable f α a b →
    RSIntegrable f β a b → 0 < c →
    RSIntegrable f (fun x => α x + β x) a b ∧
    RSIntegral f (fun x => α x + β x) a b = RSIntegral f α a b + RSIntegral f β a b ∧
    RSIntegrable f (fun x => c * α x) a b ∧
    RSIntegral f (fun x => c * α x) a b = c * RSIntegral f α a b)

/-! ### PMA-6.13: Products and absolute values. -/

def pma6_13_contract : Prop :=
  (∀ (f g α : ℝ → ℝ) (a b : ℝ), RSIntegrable f α a b →
    RSIntegrable g α a b → RSIntegrable (fun x => f x * g x) α a b) ∧
  (∀ (f α : ℝ → ℝ) (a b : ℝ), RSIntegrable f α a b →
    RSIntegrable (fun x => |f x|) α a b ∧
    |RSIntegral f α a b| ≤ RSIntegral (fun x => |f x|) α a b)

/-! Continuous integrands: uniform partitions and native Darboux oscillations. -/

def Partition.uniform {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Partition a b where
  n := n + 1
  point := fun i => a + (i.val : ℝ) * ((b - a) / (n + 1 : ℝ))
  mono := by
    intro i j hij
    apply add_le_add (le_refl a)
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hij
    · exact div_nonneg (sub_nonneg.mpr hab) (by positivity)
  left := by simp
  right := by
    simp only [Fin.val_last, Nat.cast_add, Nat.cast_one]
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem Partition.uniform_width {a b : ℝ} (hab : a ≤ b) (n : ℕ)
    (i : Fin (Partition.uniform hab n).n) :
    (Partition.uniform hab n).point i.succ - (Partition.uniform hab n).point i.castSucc =
      (b - a) / (n + 1 : ℝ) := by
  change a + ((i.val + 1 : ℕ) : ℝ) * ((b - a) / (n + 1 : ℝ)) -
    (a + (i.val : ℝ) * ((b - a) / (n + 1 : ℝ))) = (b - a) / (n + 1 : ℝ)
  push_cast
  ring

theorem exists_partition_width_lt {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    ∃ P : Partition a b, ∀ i : Fin P.n, P.point i.succ - P.point i.castSucc < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b - a) / δ)
  refine ⟨Partition.uniform hab n, fun i => ?_⟩
  rw [Partition.uniform_width]
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 1)).mpr
  have h := (div_lt_iff₀ hδ).mp hn
  nlinarith

theorem continuousOn_boundedOn {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) : BoundedOn f a b := by
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hf.abs
  exact ⟨M, fun x hx => hM ⟨x, hx, rfl⟩⟩

theorem cell_gap_le_of_oscillation {f : ℝ → ℝ} {a b η : ℝ}
    (P : Partition a b) (i : Fin P.n)
    (h : ∀ x ∈ P.cell i, ∀ y ∈ P.cell i, |f x - f y| ≤ η) :
    cellUpper f P i - cellLower f P i ≤ η := by
  have hu : cellUpper f P i ≤ cellLower f P i + η := by
    apply csSup_le ((P.cell_nonempty i).image f)
    rintro _ ⟨x, hx, rfl⟩
    have hl : f x - η ≤ cellLower f P i := by
      apply le_csInf ((P.cell_nonempty i).image f)
      rintro _ ⟨y, hy, rfl⟩
      have hxy := (abs_le.mp (h x hx y hy)).2
      linarith
    linarith
  linarith

theorem gap_le_of_cell_gaps {f α : ℝ → ℝ} {a b η : ℝ}
    (hα : MonotoneOn α (Icc a b)) (P : Partition a b)
    (h : ∀ i : Fin P.n, cellUpper f P i - cellLower f P i ≤ η) :
    upperSum f α P - lowerSum f α P ≤ η * (α b - α a) := by
  calc
    upperSum f α P - lowerSum f α P =
        ∑ i : Fin P.n, (cellUpper f P i - cellLower f P i) * P.weight α i := by
      rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i : Fin P.n, η * P.weight α i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (h i) (P.weight_nonneg α hα i))
    _ = η * (α b - α a) := by rw [← Finset.mul_sum, P.sum_weights]

theorem continuousOn_exists_gap_lt {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hα : MonotoneOn α (Icc a b))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Partition a b, upperSum f α P - lowerSum f α P < ε := by
  have hmass : 0 ≤ α b - α a := sub_nonneg.mpr (hα ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  let η := ε / (α b - α a + 1)
  have hden : 0 < α b - α a + 1 := by linarith
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hf) η hη
  obtain ⟨P, hP⟩ := exists_partition_width_lt hab hδ
  refine ⟨P, (gap_le_of_cell_gaps (η := η) hα P ?_).trans_lt ?_⟩
  · intro i
    apply cell_gap_le_of_oscillation P i
    intro x hx y hy
    have hd : dist x y < δ := by
      rw [Real.dist_eq]
      have hh : |x - y| ≤ P.point i.succ - P.point i.castSucc := by
        apply abs_le.mpr
        rcases hx with ⟨hx₁, hx₂⟩
        rcases hy with ⟨hy₁, hy₂⟩
        constructor <;> linarith
      exact hh.trans_lt (hP i)
    simpa only [Real.dist_eq] using (huc x (P.cell_subset i hx) y (P.cell_subset i hy) hd).le
  · have heq : η * (α b - α a + 1) = ε := div_mul_cancel₀ ε hden.ne'
    nlinarith

theorem rsIntegrable_of_continuousOn {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) (hα : MonotoneOn α (Icc a b)) :
    RSIntegrable f α a b :=
  (rsIntegrable_iff_gap hab (continuousOn_boundedOn hf) hα).mpr
    (fun _ hε => continuousOn_exists_gap_lt hab hf hα hε)

theorem pma6_8 : pma6_8_contract := by
  intro f α a b hab hf hα
  exact rsIntegrable_of_continuousOn hab hf hα

/-! Elementary order and absolute bounds do not need an auxiliary integral theory. -/

theorem rsIntegral_mono {f g α : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b)
    (hfg : ∀ x ∈ Icc a b, f x ≤ g x) : RSIntegral f α a b ≤ RSIntegral g α a b := by
  change lowerIntegral f α a b ≤ lowerIntegral g α a b
  apply csSup_le (s := range (lowerSum f α : Partition a b → ℝ))
    ⟨lowerSum f α (Partition.single hf.1), Partition.single hf.1, rfl⟩
  rintro _ ⟨P, rfl⟩
  apply le_trans _ (lowerSum_le_lowerIntegral hg.2.1 hg.2.2.1 P)
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_right _ (P.weight_nonneg α hf.2.2.1 i)
  apply le_csInf ((P.cell_nonempty i).image g)
  rintro _ ⟨x, hx, rfl⟩
  exact (cellLower_le_value hf.2.1 P i hx).trans (hfg x (P.cell_subset i hx))

theorem rsIntegral_abs_le_bound {f α : ℝ → ℝ} {a b M : ℝ}
    (hf : RSIntegrable f α a b) (hM : ∀ x ∈ Icc a b, |f x| ≤ M) :
    |RSIntegral f α a b| ≤ M * (α b - α a) := by
  have hb := darboux_integrals_bounds hf.1 hf.2.1 hf.2.2.1
    (fun x hx => (abs_le.mp (hM x hx)).1) (fun x hx => (abs_le.mp (hM x hx)).2)
  apply abs_le.mpr
  constructor
  · simpa only [RSIntegral, neg_mul] using hb.1
  · exact hb.2.1

theorem BoundedOn.add {f g : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b) :
    BoundedOn (fun x => f x + g x) a b := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  exact ⟨M + N, fun x hx => (abs_add_le _ _).trans (add_le_add (hM x hx) (hN x hx))⟩

theorem cellLower_add_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b) (P : Partition a b) (i : Fin P.n) :
    cellLower f P i + cellLower g P i ≤ cellLower (fun x => f x + g x) P i := by
  apply le_csInf ((P.cell_nonempty i).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact add_le_add (cellLower_le_value hf P i hx) (cellLower_le_value hg P i hx)

theorem cellUpper_add_le {f g : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b) (P : Partition a b) (i : Fin P.n) :
    cellUpper (fun x => f x + g x) P i ≤ cellUpper f P i + cellUpper g P i := by
  apply csSup_le ((P.cell_nonempty i).image _)
  rintro _ ⟨x, hx, rfl⟩
  exact add_le_add (value_le_cellUpper hf P i hx) (value_le_cellUpper hg P i hx)

theorem lowerSum_add_le {f g α : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b) (hα : MonotoneOn α (Icc a b))
    (P : Partition a b) : lowerSum f α P + lowerSum g α P ≤ lowerSum (fun x => f x + g x) α P := by
  rw [lowerSum, lowerSum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (cellLower_add_le hf hg P i) (P.weight_nonneg α hα i)

theorem upperSum_add_le {f g α : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b) (hα : MonotoneOn α (Icc a b))
    (P : Partition a b) : upperSum (fun x => f x + g x) α P ≤ upperSum f α P + upperSum g α P := by
  rw [upperSum, upperSum, upperSum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (cellUpper_add_le hf hg P i) (P.weight_nonneg α hα i)

theorem exists_common_gap_lt {f g α β : ℝ → ℝ} {a b ε : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g β a b) (hε : 0 < ε) :
    ∃ P : Partition a b, upperSum f α P - lowerSum f α P < ε ∧
      upperSum g β P - lowerSum g β P < ε := by
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf ε hε
  obtain ⟨Q, hQ⟩ := (rsIntegrable_iff_gap hg.1 hg.2.1 hg.2.2.1).mp hg ε hε
  obtain ⟨R, _, hRP, hRQ⟩ := pma6_3_common_refinement P Q
  exact ⟨R, pma6_7_refinement_gap P R hRP hf.2.1 hf.2.2.1 hP,
    pma6_7_refinement_gap Q R hRQ hg.2.1 hg.2.2.1 hQ⟩

theorem rsIntegrable_add_sandwich {f g h α β γ : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g β a b)
    (hh : BoundedOn h a b) (hγ : MonotoneOn γ (Icc a b))
    (hL : ∀ P : Partition a b, lowerSum f α P + lowerSum g β P ≤ lowerSum h γ P)
    (hU : ∀ P : Partition a b, upperSum h γ P ≤ upperSum f α P + upperSum g β P) :
    RSIntegrable h γ a b ∧ RSIntegral h γ a b = RSIntegral f α a b + RSIntegral g β a b := by
  have hnew : RSIntegrable h γ a b := by
    apply (rsIntegrable_iff_gap hf.1 hh hγ).mpr
    intro ε hε
    obtain ⟨P, hPf, hPg⟩ := exists_common_gap_lt hf hg (half_pos hε)
    exact ⟨P, by linarith [hL P, hU P]⟩
  refine ⟨hnew, ?_⟩
  have hc (ε : ℝ) (hε : 0 < ε) :
      RSIntegral h γ a b ≤ RSIntegral f α a b + RSIntegral g β a b + ε ∧
      RSIntegral f α a b + RSIntegral g β a b ≤ RSIntegral h γ a b + ε := by
    obtain ⟨P, hPf, hPg⟩ := exists_common_gap_lt hf hg (half_pos hε)
    have hIf := rsIntegral_bounds hf P
    have hIg := rsIntegral_bounds hg P
    have hIh := rsIntegral_bounds hnew P
    constructor <;> linarith [hL P, hU P, hIf.1, hIf.2, hIg.1, hIg.2, hIh.1, hIh.2]
  exact le_antisymm (le_of_forall_pos_le_add (fun ε hε => (hc ε hε).1))
    (le_of_forall_pos_le_add (fun ε hε => (hc ε hε).2))

theorem rsIntegrable_add {f g α : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b) :
    RSIntegrable (fun x => f x + g x) α a b ∧
      RSIntegral (fun x => f x + g x) α a b = RSIntegral f α a b + RSIntegral g α a b :=
  rsIntegrable_add_sandwich hf hg (hf.2.1.add hg.2.1) hf.2.2.1
    (lowerSum_add_le hf.2.1 hg.2.1 hf.2.2.1) (upperSum_add_le hf.2.1 hg.2.1 hf.2.2.1)

theorem lowerSum_integrator_add {f α β : ℝ → ℝ} {a b : ℝ} (P : Partition a b) :
    lowerSum f (fun x => α x + β x) P = lowerSum f α P + lowerSum f β P := by
  simp only [lowerSum, Partition.weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem upperSum_integrator_add {f α β : ℝ → ℝ} {a b : ℝ} (P : Partition a b) :
    upperSum f (fun x => α x + β x) P = upperSum f α P + upperSum f β P := by
  simp only [upperSum, Partition.weight, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rsIntegrable_integrator_add {f α β : ℝ → ℝ} {a b : ℝ}
    (hα : RSIntegrable f α a b) (hβ : RSIntegrable f β a b) :
    RSIntegrable f (fun x => α x + β x) a b ∧
      RSIntegral f (fun x => α x + β x) a b = RSIntegral f α a b + RSIntegral f β a b := by
  apply rsIntegrable_add_sandwich hα hβ hα.2.1
    (fun _ hx _ hy hxy => add_le_add (hα.2.2.1 hx hy hxy) (hβ.2.2.1 hx hy hxy))
  · intro P
    exact (lowerSum_integrator_add P).ge
  · intro P
    exact (upperSum_integrator_add P).le

theorem rsIntegrable_of_scaled_tagged_sums {f h α γ : ℝ → ℝ} {a b c K : ℝ}
    (hf : RSIntegrable f α a b) (hh : BoundedOn h a b) (hγ : MonotoneOn γ (Icc a b))
    (hK : 0 ≤ K)
    (hgap : ∀ P : Partition a b, upperSum h γ P - lowerSum h γ P ≤
      K * (upperSum f α P - lowerSum f α P))
    (htag : ∀ (P : Partition a b) (tag : Fin P.n → ℝ),
      taggedSum h γ P tag = c * taggedSum f α P tag) :
    RSIntegrable h γ a b ∧ RSIntegral h γ a b = c * RSIntegral f α a b := by
  have hnew : RSIntegrable h γ a b := by
    apply (rsIntegrable_iff_gap hf.1 hh hγ).mpr
    intro ε hε
    have hd : 0 < K + 1 := by linarith
    obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf
      (ε / (K + 1)) (div_pos hε hd)
    refine ⟨P, (hgap P).trans_lt ?_⟩
    have hm := mul_le_mul_of_nonneg_left hP.le hK
    have heq := div_mul_cancel₀ ε hd.ne'
    have hp : 0 < ε / (K + 1) := div_pos hε hd
    nlinarith
  refine ⟨hnew, ?_⟩
  have heps (ε : ℝ) (hε : 0 < ε) : |RSIntegral h γ a b - c * RSIntegral f α a b| ≤ ε := by
    have hd : 0 < K + |c| + 1 := by positivity
    let δ := ε / (K + |c| + 1)
    have hδ : 0 < δ := div_pos hε hd
    obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf δ hδ
    let tag : Fin P.n → ℝ := fun i => P.point i.castSucc
    have htags : TaggedBy P tag := fun i => ⟨le_rfl, P.cell_order i⟩
    have he : RSIntegral h γ a b - c * RSIntegral f α a b =
        -(taggedSum h γ P tag - RSIntegral h γ a b) +
          c * (taggedSum f α P tag - RSIntegral f α a b) := by
      rw [htag P tag]
      ring
    have herr : |RSIntegral h γ a b - c * RSIntegral f α a b| ≤
        (K + |c|) * (upperSum f α P - lowerSum f α P) := by
      rw [he]
      calc
        _ ≤ |-(taggedSum h γ P tag - RSIntegral h γ a b)| +
            |c * (taggedSum f α P tag - RSIntegral f α a b)| := abs_add_le _ _
        _ = |taggedSum h γ P tag - RSIntegral h γ a b| +
            |c| * |taggedSum f α P tag - RSIntegral f α a b| := by rw [abs_neg, abs_mul]
        _ ≤ upperSum h γ P - lowerSum h γ P +
            |c| * (upperSum f α P - lowerSum f α P) :=
          add_le_add (taggedSum_sub_integral_le_gap hnew P htags)
            (mul_le_mul_of_nonneg_left (taggedSum_sub_integral_le_gap hf P htags) (abs_nonneg c))
        _ ≤ (K + |c|) * (upperSum f α P - lowerSum f α P) := by nlinarith [hgap P]
    have hm := mul_le_mul_of_nonneg_left hP.le (show 0 ≤ K + |c| by positivity)
    have heq : δ * (K + |c| + 1) = ε := div_mul_cancel₀ ε hd.ne'
    nlinarith
  have hz : |RSIntegral h γ a b - c * RSIntegral f α a b| ≤ 0 :=
    le_of_forall_pos_le_add (fun ε hε => by simpa only [zero_add] using heps ε hε)
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))

theorem BoundedOn.const_mul {f : ℝ → ℝ} {a b : ℝ} (hf : BoundedOn f a b) (c : ℝ) :
    BoundedOn (fun x => c * f x) a b := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨|c| * M, fun x hx => ?_⟩
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM x hx) (abs_nonneg c)

theorem scalar_gap_le {f α : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hα : MonotoneOn α (Icc a b)) (c : ℝ) (P : Partition a b) :
    upperSum (fun x => c * f x) α P - lowerSum (fun x => c * f x) α P ≤
      |c| * (upperSum f α P - lowerSum f α P) := by
  have hc (i : Fin P.n) :
      cellUpper (fun x => c * f x) P i - cellLower (fun x => c * f x) P i ≤
        |c| * (cellUpper f P i - cellLower f P i) := by
    apply cell_gap_le_of_oscillation P i
    intro x hx y hy
    rw [← mul_sub, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
    apply abs_le.mpr
    have hxL := cellLower_le_value hf P i hx
    have hxU := value_le_cellUpper hf P i hx
    have hyL := cellLower_le_value hf P i hy
    have hyU := value_le_cellUpper hf P i hy
    constructor <;> linarith
  simp only [upperSum, lowerSum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hm := mul_le_mul_of_nonneg_right (hc i) (P.weight_nonneg α hα i)
  nlinarith

theorem rsIntegrable_const_mul {f α : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f α a b) (c : ℝ) :
    RSIntegrable (fun x => c * f x) α a b ∧
      RSIntegral (fun x => c * f x) α a b = c * RSIntegral f α a b := by
  apply rsIntegrable_of_scaled_tagged_sums hf (hf.2.1.const_mul c) hf.2.2.1 (abs_nonneg c)
    (scalar_gap_le hf.2.1 hf.2.2.1 c)
  intro P tag
  simp only [taggedSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem rsIntegrable_integrator_const_mul {f α : ℝ → ℝ} {a b c : ℝ}
    (hf : RSIntegrable f α a b) (hc : 0 < c) :
    RSIntegrable f (fun x => c * α x) a b ∧
      RSIntegral f (fun x => c * α x) a b = c * RSIntegral f α a b := by
  have hmono : MonotoneOn (fun x => c * α x) (Icc a b) :=
    fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (hf.2.2.1 hx hy hxy) hc.le
  apply rsIntegrable_of_scaled_tagged_sums hf hf.2.1 hmono hc.le
  · intro P
    have hL : lowerSum f (fun x => c * α x) P = c * lowerSum f α P := by
      simp only [lowerSum, Partition.weight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hU : upperSum f (fun x => c * α x) P = c * upperSum f α P := by
      simp only [upperSum, Partition.weight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hL, hU]
    exact le_of_eq (by ring)
  · intro P tag
    simp only [taggedSum, Partition.weight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem gap_eq_sum {f α : ℝ → ℝ} {a b : ℝ} (P : Partition a b) :
    upperSum f α P - lowerSum f α P =
      ∑ i : Fin P.n, (cellUpper f P i - cellLower f P i) * P.weight α i := by
  rw [upperSum, lowerSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gap_le_of_cell_affine_gaps {f h α : ℝ → ℝ} {a b η C : ℝ}
    (hα : MonotoneOn α (Icc a b)) (P : Partition a b)
    (hgap : ∀ i : Fin P.n, cellUpper h P i - cellLower h P i ≤
      η + C * (cellUpper f P i - cellLower f P i)) :
    upperSum h α P - lowerSum h α P ≤
      η * (α b - α a) + C * (upperSum f α P - lowerSum f α P) := by
  rw [gap_eq_sum, gap_eq_sum]
  calc
    _ ≤ ∑ i : Fin P.n, (η + C * (cellUpper f P i - cellLower f P i)) * P.weight α i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hgap i) (P.weight_nonneg α hα i))
    _ = _ := by
      simp only [add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum, P.sum_weights]

theorem rsIntegrable_comp {f α φ : ℝ → ℝ} {a b m M : ℝ}
    (hf : RSIntegrable f α a b) (hrange : ∀ x ∈ Icc a b, f x ∈ Icc m M)
    (hφ : ContinuousOn φ (Icc m M)) : RSIntegrable (φ ∘ f) α a b := by
  obtain ⟨N, hN⟩ := continuousOn_boundedOn hφ
  have hb : BoundedOn (φ ∘ f) a b := ⟨N, fun x hx => hN (f x) (hrange x hx)⟩
  apply (rsIntegrable_iff_gap hf.1 hb hf.2.2.1).mpr
  intro ε hε
  have hmass : 0 ≤ α b - α a :=
    sub_nonneg.mpr (hf.2.2.1 ⟨le_rfl, hf.1⟩ ⟨hf.1, le_rfl⟩ hf.1)
  let η := ε / (2 * (α b - α a + 1))
  have hden : 0 < 2 * (α b - α a + 1) := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, huc⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hφ) η hη
  let C := 2 * |N| / δ
  have hC : 0 ≤ C := div_nonneg (by positivity) hδ.le
  have hpoint (u : ℝ) (hu : u ∈ Icc m M) (v : ℝ) (hv : v ∈ Icc m M) :
      |φ u - φ v| ≤ η + C * |u - v| := by
    by_cases huv : |u - v| < δ
    · have huvc : |φ u - φ v| < η := by
        simpa only [Real.dist_eq] using huc u hu v hv (by simpa only [Real.dist_eq] using huv)
      exact huvc.le.trans (le_add_of_nonneg_right (mul_nonneg hC (abs_nonneg _)))
    · have huv' : δ ≤ |u - v| := le_of_not_gt huv
      have hbound : |φ u - φ v| ≤ 2 * |N| := by
        have ht := abs_sub_le (φ u) 0 (φ v)
        simp only [sub_zero, zero_sub, abs_neg] at ht
        have huN := (hN u hu).trans (le_abs_self N)
        have hvN := (hN v hv).trans (le_abs_self N)
        linarith
      have hmul := mul_le_mul_of_nonneg_left huv' hC
      have heq : C * δ = 2 * |N| := div_mul_cancel₀ _ hδ.ne'
      linarith
  have hCD : 0 < 2 * (C + 1) := by positivity
  let ζ := ε / (2 * (C + 1))
  have hζ : 0 < ζ := div_pos hε hCD
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf ζ hζ
  refine ⟨P, (gap_le_of_cell_affine_gaps (f := f) (η := η) (C := C) hf.2.2.1 P ?_).trans_lt ?_⟩
  · intro i
    apply cell_gap_le_of_oscillation P i
    intro x hx y hy
    have hxy : |f x - f y| ≤ cellUpper f P i - cellLower f P i := by
      apply abs_le.mpr
      have hxL := cellLower_le_value hf.2.1 P i hx
      have hxU := value_le_cellUpper hf.2.1 P i hx
      have hyL := cellLower_le_value hf.2.1 P i hy
      have hyU := value_le_cellUpper hf.2.1 P i hy
      constructor <;> linarith
    exact (hpoint (f x) (hrange x (P.cell_subset i hx)) (f y) (hrange y (P.cell_subset i hy))).trans
      (add_le_add (le_refl η) (mul_le_mul_of_nonneg_left hxy hC))
  · have hηeq : η * (2 * (α b - α a + 1)) = ε := div_mul_cancel₀ ε hden.ne'
    have hζeq : ζ * (2 * (C + 1)) = ε := div_mul_cancel₀ ε hCD.ne'
    have hm := mul_le_mul_of_nonneg_left hP.le hC
    nlinarith

theorem pma6_11 : pma6_11_contract := by
  intro f α φ a b m M hf hrange hφ
  exact rsIntegrable_comp hf hrange hφ

theorem rsIntegrable_square {f α : ℝ → ℝ} {a b : ℝ} (hf : RSIntegrable f α a b) :
    RSIntegrable (fun x => f x ^ 2) α a b := by
  obtain ⟨M, hM⟩ := hf.2.1
  exact rsIntegrable_comp hf (fun x hx => abs_le.mp (hM x hx))
    (show ContinuousOn (fun x : ℝ => x ^ 2) (Icc (-M) M) from (continuous_id.pow 2).continuousOn)

theorem rsIntegrable_mul {f g α : ℝ → ℝ} {a b : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g α a b) :
    RSIntegrable (fun x => f x * g x) α a b := by
  have hs := rsIntegrable_square (rsIntegrable_add hf hg).1
  have hf2 := (rsIntegrable_const_mul (rsIntegrable_square hf) (-1)).1
  have hg2 := (rsIntegrable_const_mul (rsIntegrable_square hg) (-1)).1
  have hh := (rsIntegrable_const_mul (rsIntegrable_add (rsIntegrable_add hs hf2).1 hg2).1 (1 / 2)).1
  convert hh using 1
  funext x
  ring

theorem rsIntegrable_abs {f α : ℝ → ℝ} {a b : ℝ} (hf : RSIntegrable f α a b) :
    RSIntegrable (fun x => |f x|) α a b ∧
      |RSIntegral f α a b| ≤ RSIntegral (fun x => |f x|) α a b := by
  obtain ⟨M, hM⟩ := hf.2.1
  have habs : RSIntegrable (fun x => |f x|) α a b :=
    rsIntegrable_comp hf (fun x hx => abs_le.mp (hM x hx))
      (show ContinuousOn (fun x : ℝ => |x|) (Icc (-M) M) from continuous_id.abs.continuousOn)
  refine ⟨habs, abs_le.mpr ⟨?_, ?_⟩⟩
  · have hneg := rsIntegrable_const_mul hf (-1)
    have hm := rsIntegral_mono hneg.1 habs (fun x _ => by simpa only [neg_one_mul] using neg_le_abs (f x))
    rw [hneg.2, neg_one_mul] at hm
    simpa only [neg_neg] using neg_le_neg hm
  · exact rsIntegral_mono hf habs (fun x _ => le_abs_self (f x))

theorem pma6_13 : pma6_13_contract := by
  constructor
  · intro f g α a b hf hg
    exact rsIntegrable_mul hf hg
  · intro f α a b hf
    exact rsIntegrable_abs hf

#print axioms pma6_8
#print axioms pma6_11
#print axioms pma6_13
#print axioms rsIntegrable_add
#print axioms rsIntegrable_const_mul
#print axioms rsIntegrable_integrator_add
#print axioms rsIntegrable_integrator_const_mul

end Rudin.PMA.Chapter06
