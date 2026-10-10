import Rudin.PMA.Chapter06.Split
import Rudin.PMA.Chapter06.Integrability

open Set
open scoped Topology

noncomputable section

namespace Rudin.PMA.Chapter06

/-!
Concrete contracts over the native closed-cell Darboux definitions in Chapter06.Basic.
The ordinary Riemann case uses the identity integrator. No integral or integrability predicate
is redefined here, and no measure representation is imposed on a Stieltjes integrator.
-/

/-! ### PMA-6.17: An integrator with an integrable derivative. -/

def pma6_17_contract : Prop :=
  ∀ (f α α' : ℝ → ℝ) (a b : ℝ), a < b →
    MonotoneOn α (Icc a b) →
    (∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x) →
    RSIntegrable α' (fun x => x) a b →
    BoundedOn f a b →
    (RSIntegrable f α a b ↔ RSIntegrable (fun x => f x * α' x) (fun x => x) a b) ∧
    (RSIntegrable f α a b →
      RSIntegral f α a b = RSIntegral (fun x => f x * α' x) (fun x => x) a b)

/-! ### PMA-6.19: Strictly increasing continuous substitution and its weighted consequence. -/

def pma6_19_contract : Prop :=
  (∀ (f α φ : ℝ → ℝ) (a b A B : ℝ), a ≤ b → A ≤ B →
    StrictMonoOn φ (Icc A B) → ContinuousOn φ (Icc A B) →
    φ '' Icc A B = Icc a b → MonotoneOn α (Icc a b) →
    RSIntegrable f α a b →
    RSIntegrable (f ∘ φ) (α ∘ φ) A B ∧
    RSIntegral (f ∘ φ) (α ∘ φ) A B = RSIntegral f α a b) ∧
  (∀ (f φ φ' : ℝ → ℝ) (a b A B : ℝ), a < b → A < B →
    StrictMonoOn φ (Icc A B) → ContinuousOn φ (Icc A B) →
    φ '' Icc A B = Icc a b →
    (∀ y ∈ Icc A B, HasDerivWithinAt φ (φ' y) (Icc A B) y) →
    RSIntegrable φ' (fun y => y) A B → RSIntegrable f (fun x => x) a b →
    RSIntegrable (fun y => f (φ y) * φ' y) (fun y => y) A B ∧
    RSIntegral f (fun x => x) a b =
      RSIntegral (fun y => f (φ y) * φ' y) (fun y => y) A B)

/-! ### PMA-6.20: Continuity and differentiation of the indefinite Riemann integral. -/

def pma6_20_contract : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a < b → RSIntegrable f (fun x => x) a b →
    ContinuousOn (fun x => RSIntegral f (fun t => t) a x) (Icc a b) ∧
    UniformContinuousOn (fun x => RSIntegral f (fun t => t) a x) (Icc a b) ∧
    (∀ x ∈ Icc a b, ContinuousWithinAt f (Icc a b) x →
      HasDerivWithinAt (fun u => RSIntegral f (fun t => t) a u) (f x) (Icc a b) x)

/-! ### PMA-6.21: Fundamental theorem of calculus. -/

def pma6_21_contract : Prop :=
  ∀ (F f : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x) →
    RSIntegrable f (fun x => x) a b →
    RSIntegral f (fun x => x) a b = F b - F a

/-! ### PMA-6.22: Integration by parts. -/

def pma6_22_contract : Prop :=
  ∀ (F G f g : ℝ → ℝ) (a b : ℝ), a < b →
    (∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x) →
    (∀ x ∈ Icc a b, HasDerivWithinAt G (g x) (Icc a b) x) →
    RSIntegrable f (fun x => x) a b → RSIntegrable g (fun x => x) a b →
    RSIntegrable (fun x => F x * g x) (fun x => x) a b ∧
    RSIntegrable (fun x => f x * G x) (fun x => x) a b ∧
    RSIntegral (fun x => F x * g x) (fun x => x) a b =
      F b * G b - F a * G a - RSIntegral (fun x => f x * G x) (fun x => x) a b

/-! Native FTC proof: no auxiliary integral theory or unproved integral criterion. -/

theorem calculus_ftc_cell_squeeze {F f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b)
    (hder : ∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x)
    (P : Partition a b) (i : Fin P.n) :
    cellLower f P i * P.weight id i ≤ P.weight F i ∧
      P.weight F i ≤ cellUpper f P i * P.weight id i := by
  rcases lt_or_eq_of_le (P.cell_order i) with hlt | heq
  · have hc : ContinuousOn F (P.cell i) := by
      intro x hx
      exact (hder x (P.cell_subset i hx)).continuousWithinAt.mono (P.cell_subset i)
    have hd : ∀ x ∈ Ioo (P.point i.castSucc) (P.point i.succ), HasDerivAt F (f x) x := by
      intro x hx
      exact (hder x (P.cell_subset i (Ioo_subset_Icc_self hx))).hasDerivAt
        (Icc_mem_nhds ((P.point_mem i.castSucc).1.trans_lt hx.1)
          (hx.2.trans_le (P.point_mem i.succ).2))
    obtain ⟨x, hx, hval⟩ := exists_hasDerivAt_eq_slope F f hlt hc hd
    have hinc : P.weight F i = f x * P.weight id i := by
      dsimp only [Partition.weight, id_eq]
      exact ((eq_div_iff (sub_ne_zero.mpr hlt.ne')).mp hval).symm
    rw [hinc]
    have hnonneg : 0 ≤ P.weight id i := sub_nonneg.mpr (P.cell_order i)
    exact ⟨mul_le_mul_of_nonneg_right
        (cellLower_le_value hf P i (Ioo_subset_Icc_self hx)) hnonneg,
      mul_le_mul_of_nonneg_right
        (value_le_cellUpper hf P i (Ioo_subset_Icc_self hx)) hnonneg⟩
  · simp only [Partition.weight, heq, sub_self, mul_zero, le_refl, and_self]

theorem calculus_ftc_sum_squeeze {F f : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b)
    (hder : ∀ x ∈ Icc a b, HasDerivWithinAt F (f x) (Icc a b) x)
    (P : Partition a b) :
    lowerSum f id P ≤ F b - F a ∧ F b - F a ≤ upperSum f id P := by
  constructor
  · calc
      lowerSum f id P ≤ ∑ i : Fin P.n, P.weight F i :=
        Finset.sum_le_sum (fun i _ => (calculus_ftc_cell_squeeze hf hder P i).1)
      _ = F b - F a := P.sum_weights F
  · calc
      F b - F a = ∑ i : Fin P.n, P.weight F i := (P.sum_weights F).symm
      _ ≤ upperSum f id P :=
        Finset.sum_le_sum (fun i _ => (calculus_ftc_cell_squeeze hf hder P i).2)

theorem pma6_21 : pma6_21_contract := by
  intro F f a b hab hder hf
  have : Nonempty (Partition a b) := Partition.nonempty hab.le
  have hl : lowerIntegral f id a b ≤ F b - F a := by
    apply csSup_le (Set.range_nonempty (f := lowerSum f id))
    rintro y ⟨P, rfl⟩
    exact (calculus_ftc_sum_squeeze hf.2.1 hder P).1
  have hu : F b - F a ≤ upperIntegral f id a b := by
    apply le_csInf (Set.range_nonempty (f := upperSum f id))
    rintro y ⟨P, rfl⟩
    exact (calculus_ftc_sum_squeeze hf.2.1 hder P).2
  change lowerIntegral f id a b = F b - F a
  exact le_antisymm hl (hu.trans_eq hf.2.2.2.symm)

/-! Native substitution: cell images and partition ranges, including degenerate intervals. -/

theorem calculus_substitution_endpoints {φ : ℝ → ℝ} {a b A B : ℝ}
    (hab : a ≤ b) (hAB : A ≤ B) (hφ : MonotoneOn φ (Icc A B))
    (him : φ '' Icc A B = Icc a b) : φ A = a ∧ φ B = b := by
  have hmaps : MapsTo φ (Icc A B) (Icc a b) := by
    intro x hx
    rw [← him]
    exact ⟨x, hx, rfl⟩
  obtain ⟨x, hx, hxa⟩ : a ∈ φ '' Icc A B := by rw [him]; exact left_mem_Icc.mpr hab
  obtain ⟨y, hy, hyb⟩ : b ∈ φ '' Icc A B := by rw [him]; exact right_mem_Icc.mpr hab
  constructor
  · exact le_antisymm ((hφ (left_mem_Icc.mpr hAB) hx hx.1).trans_eq hxa)
      (hmaps (left_mem_Icc.mpr hAB)).1
  · exact le_antisymm (hmaps (right_mem_Icc.mpr hAB)).2
      (hyb ▸ hφ hy (right_mem_Icc.mpr hAB) hy.2)

def calculus_mapPartition {φ : ℝ → ℝ} {a b A B : ℝ}
    (hφ : MonotoneOn φ (Icc A B)) (hleft : φ A = a) (hright : φ B = b)
    (P : Partition A B) : Partition a b where
  n := P.n
  point := fun i => φ (P.point i)
  mono := fun i j hij => hφ (P.point_mem i) (P.point_mem j) (P.mono hij)
  left := by simp only [P.left, hleft]
  right := by simp only [P.right, hright]

theorem calculus_mapPartition_cell_image {φ : ℝ → ℝ} {a b A B : ℝ}
    (hφ : MonotoneOn φ (Icc A B)) (hcont : ContinuousOn φ (Icc A B))
    (hleft : φ A = a) (hright : φ B = b) (P : Partition A B) (i : Fin P.n) :
    φ '' P.cell i = (calculus_mapPartition hφ hleft hright P).cell i :=
  ContinuousOn.image_Icc_of_monotoneOn (P.cell_order i)
    (hcont.mono (P.cell_subset i)) (hφ.mono (P.cell_subset i))

theorem calculus_mapPartition_sums {f α φ : ℝ → ℝ} {a b A B : ℝ}
    (hφ : MonotoneOn φ (Icc A B)) (hcont : ContinuousOn φ (Icc A B))
    (hleft : φ A = a) (hright : φ B = b) (P : Partition A B) :
    lowerSum (f ∘ φ) (α ∘ φ) P = lowerSum f α (calculus_mapPartition hφ hleft hright P) ∧
    upperSum (f ∘ φ) (α ∘ φ) P = upperSum f α (calculus_mapPartition hφ hleft hright P) := by
  have hcells : ∀ i : Fin P.n,
      (f ∘ φ) '' P.cell i = f '' (calculus_mapPartition hφ hleft hright P).cell i := by
    intro i
    rw [← calculus_mapPartition_cell_image hφ hcont hleft hright P i, Set.image_image]
    rfl
  constructor
  · unfold lowerSum
    apply Finset.sum_congr rfl
    intro i _
    have heq : cellLower (f ∘ φ) P i =
        cellLower f (calculus_mapPartition hφ hleft hright P) i := congrArg sInf (hcells i)
    rw [heq]
    rfl
  · unfold upperSum
    apply Finset.sum_congr rfl
    intro i _
    have heq : cellUpper (f ∘ φ) P i =
        cellUpper f (calculus_mapPartition hφ hleft hright P) i := congrArg sSup (hcells i)
    rw [heq]
    rfl

theorem calculus_mapPartition_surjective {φ : ℝ → ℝ} {a b A B : ℝ}
    (hAB : A ≤ B) (hφ : StrictMonoOn φ (Icc A B))
    (him : φ '' Icc A B = Icc a b) (hleft : φ A = a) (hright : φ B = b) :
    Function.Surjective (calculus_mapPartition hφ.monotoneOn hleft hright) := by
  classical
  intro P
  have hpre : ∀ i : Fin (P.n + 1), ∃ x ∈ Icc A B, φ x = P.point i := by
    intro i
    have hi := P.point_mem i
    rw [← him] at hi
    exact hi
  choose q hq hval using hpre
  have hmono : Monotone q := by
    intro i j hij
    by_contra h
    have hh := hφ (hq j) (hq i) (lt_of_not_ge h)
    rw [hval j, hval i] at hh
    exact (not_lt_of_ge (P.mono hij)) hh
  have hqleft : q 0 = A := hφ.injOn (hq 0) (left_mem_Icc.mpr hAB)
    (by rw [hval, P.left, hleft])
  have hqright : q (Fin.last P.n) = B := hφ.injOn (hq _) (right_mem_Icc.mpr hAB)
    (by rw [hval, P.right, hright])
  let Q : Partition A B := ⟨P.n, q, hmono, hqleft, hqright⟩
  refine ⟨Q, ?_⟩
  cases P
  dsimp only [calculus_mapPartition, Q]
  congr
  exact funext hval

theorem calculus_substitution_integrals {f α φ : ℝ → ℝ} {a b A B : ℝ}
    (hab : a ≤ b) (hAB : A ≤ B) (hφ : StrictMonoOn φ (Icc A B))
    (hcont : ContinuousOn φ (Icc A B)) (him : φ '' Icc A B = Icc a b) :
    lowerIntegral (f ∘ φ) (α ∘ φ) A B = lowerIntegral f α a b ∧
    upperIntegral (f ∘ φ) (α ∘ φ) A B = upperIntegral f α a b := by
  obtain ⟨hleft, hright⟩ := calculus_substitution_endpoints hab hAB hφ.monotoneOn him
  let T := calculus_mapPartition hφ.monotoneOn hleft hright
  have hsurj : Function.Surjective T :=
    calculus_mapPartition_surjective hAB hφ him hleft hright
  have hl : (lowerSum (f ∘ φ) (α ∘ φ) : Partition A B → ℝ) = (lowerSum f α) ∘ T := by
    funext P
    exact (calculus_mapPartition_sums hφ.monotoneOn hcont hleft hright P).1
  have hu : (upperSum (f ∘ φ) (α ∘ φ) : Partition A B → ℝ) = (upperSum f α) ∘ T := by
    funext P
    exact (calculus_mapPartition_sums hφ.monotoneOn hcont hleft hright P).2
  constructor
  · unfold lowerIntegral
    rw [hl, hsurj.range_comp]
  · unfold upperIntegral
    rw [hu, hsurj.range_comp]

theorem pma6_19_transport {f α φ : ℝ → ℝ} {a b A B : ℝ}
    (hab : a ≤ b) (hAB : A ≤ B) (hφ : StrictMonoOn φ (Icc A B))
    (hcont : ContinuousOn φ (Icc A B)) (him : φ '' Icc A B = Icc a b)
    (hα : MonotoneOn α (Icc a b)) (hf : RSIntegrable f α a b) :
    RSIntegrable (f ∘ φ) (α ∘ φ) A B ∧
      RSIntegral (f ∘ φ) (α ∘ φ) A B = RSIntegral f α a b := by
  have hmaps : MapsTo φ (Icc A B) (Icc a b) := by
    intro x hx
    rw [← him]
    exact ⟨x, hx, rfl⟩
  have hbound : BoundedOn (f ∘ φ) A B := by
    obtain ⟨M, hM⟩ := hf.2.1
    exact ⟨M, fun x hx => hM (φ x) (hmaps hx)⟩
  have hmono : MonotoneOn (α ∘ φ) (Icc A B) := by
    intro x hx y hy hxy
    exact hα (hmaps hx) (hmaps hy) (hφ.monotoneOn hx hy hxy)
  have hi := calculus_substitution_integrals (f := f) (α := α) hab hAB hφ hcont him
  exact ⟨⟨hAB, hbound, hmono, hi.1.trans (hf.2.2.2.trans hi.2.symm)⟩, hi.1⟩

/-! Quantitative native comparison for the integrable-derivative integrator theorem. -/

theorem calculus_integrator_increment_error {α α' : ℝ → ℝ} {a b : ℝ}
    (hbound : BoundedOn α' a b)
    (hder : ∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x)
    (P : Partition a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ P.cell i) :
    |P.weight α i - α' x * P.weight id i| ≤
      (cellUpper α' P i - cellLower α' P i) * P.weight id i := by
  have hinc := calculus_ftc_cell_squeeze hbound hder P i
  have hnonneg : 0 ≤ P.weight id i := sub_nonneg.mpr (P.cell_order i)
  have hlo := mul_le_mul_of_nonneg_right (cellLower_le_value hbound P i hx) hnonneg
  have hup := mul_le_mul_of_nonneg_right (value_le_cellUpper hbound P i hx) hnonneg
  exact abs_le.mpr ⟨by nlinarith [hinc.1, hinc.2], by nlinarith [hinc.1, hinc.2]⟩

theorem calculus_weighted_cell_error {f α α' : ℝ → ℝ} {a b M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hbound : BoundedOn α' a b)
    (hder : ∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x)
    (P : Partition a b) (i : Fin P.n) {x : ℝ} (hx : x ∈ P.cell i) :
    |f x * P.weight α i - (f x * α' x) * P.weight id i| ≤
      M * ((cellUpper α' P i - cellLower α' P i) * P.weight id i) := by
  have heq : f x * P.weight α i - (f x * α' x) * P.weight id i =
      f x * (P.weight α i - α' x * P.weight id i) := by ring
  rw [heq, abs_mul]
  exact mul_le_mul (hM x (P.cell_subset i hx))
    (calculus_integrator_increment_error hbound hder P i hx) (abs_nonneg _) hM0

theorem calculus_weighted_taggedSum_error {f α α' : ℝ → ℝ} {a b M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hbound : BoundedOn α' a b)
    (hder : ∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x)
    (P : Partition a b) (tag : Fin P.n → ℝ) (htag : TaggedBy P tag) :
    |taggedSum f α P tag - taggedSum (fun x => f x * α' x) id P tag| ≤
      M * (upperSum α' id P - lowerSum α' id P) := by
  unfold taggedSum
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin P.n, (f (tag i) * P.weight α i -
        (f (tag i) * α' (tag i)) * P.weight id i)| ≤
        ∑ i : Fin P.n, |f (tag i) * P.weight α i -
          (f (tag i) * α' (tag i)) * P.weight id i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin P.n, M * ((cellUpper α' P i - cellLower α' P i) * P.weight id i) :=
      Finset.sum_le_sum (fun i _ => calculus_weighted_cell_error hM hM0 hbound hder P i (htag i))
    _ = M * (upperSum α' id P - lowerSum α' id P) := by
      unfold upperSum lowerSum
      simp only [← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]

theorem calculus_bounded_mul {f g : ℝ → ℝ} {a b : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b) :
    BoundedOn (fun x => f x * g x) a b := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨|M| * |N|, ?_⟩
  intro x hx
  rw [abs_mul]
  exact mul_le_mul ((hM x hx).trans (le_abs_self _))
    ((hN x hx).trans (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

theorem calculus_cellUpper_weight_le {f : ℝ → ℝ} {a b w z : ℝ}
    (P : Partition a b) (i : Fin P.n) (hw : 0 ≤ w)
    (h : ∀ x ∈ P.cell i, f x * w ≤ z) : cellUpper f P i * w ≤ z := by
  rcases eq_or_lt_of_le hw with rfl | hw
  · obtain ⟨x, hx⟩ := P.cell_nonempty i
    simpa using h x hx
  · apply (le_div_iff₀ hw).mp
    apply csSup_le ((P.cell_nonempty i).image f)
    rintro y ⟨x, hx, rfl⟩
    exact (le_div_iff₀ hw).mpr (h x hx)

theorem calculus_le_cellLower_weight {f : ℝ → ℝ} {a b w z : ℝ}
    (P : Partition a b) (i : Fin P.n) (hw : 0 ≤ w)
    (h : ∀ x ∈ P.cell i, z ≤ f x * w) : z ≤ cellLower f P i * w := by
  rcases eq_or_lt_of_le hw with rfl | hw
  · obtain ⟨x, hx⟩ := P.cell_nonempty i
    simpa using h x hx
  · apply (div_le_iff₀ hw).mp
    apply le_csInf ((P.cell_nonempty i).image f)
    rintro y ⟨x, hx, rfl⟩
    exact (div_le_iff₀ hw).mpr (h x hx)

theorem calculus_cellUpper_weight_error {f g : ℝ → ℝ} {a b w v E : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b)
    (P : Partition a b) (i : Fin P.n) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (herror : ∀ x ∈ P.cell i, |f x * w - g x * v| ≤ E) :
    |cellUpper f P i * w - cellUpper g P i * v| ≤ E := by
  have hfg : cellUpper f P i * w ≤ cellUpper g P i * v + E := by
    apply calculus_cellUpper_weight_le P i hw
    intro x hx
    have hh := (abs_le.mp (herror x hx)).2
    have hgx := mul_le_mul_of_nonneg_right (value_le_cellUpper hg P i hx) hv
    linarith
  have hgf : cellUpper g P i * v ≤ cellUpper f P i * w + E := by
    apply calculus_cellUpper_weight_le P i hv
    intro x hx
    have hh := (abs_le.mp (herror x hx)).1
    have hfx := mul_le_mul_of_nonneg_right (value_le_cellUpper hf P i hx) hw
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem calculus_cellLower_weight_error {f g : ℝ → ℝ} {a b w v E : ℝ}
    (hf : BoundedOn f a b) (hg : BoundedOn g a b)
    (P : Partition a b) (i : Fin P.n) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (herror : ∀ x ∈ P.cell i, |f x * w - g x * v| ≤ E) :
    |cellLower f P i * w - cellLower g P i * v| ≤ E := by
  have hfg : cellLower g P i * v - E ≤ cellLower f P i * w := by
    apply calculus_le_cellLower_weight P i hw
    intro x hx
    have hh := (abs_le.mp (herror x hx)).1
    have hgx := mul_le_mul_of_nonneg_right (cellLower_le_value hg P i hx) hv
    linarith
  have hgf : cellLower f P i * w - E ≤ cellLower g P i * v := by
    apply calculus_le_cellLower_weight P i hv
    intro x hx
    have hh := (abs_le.mp (herror x hx)).2
    have hfx := mul_le_mul_of_nonneg_right (cellLower_le_value hf P i hx) hw
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem calculus_weighted_darbouxSum_error {f α α' : ℝ → ℝ} {a b M : ℝ}
    (hM : ∀ x ∈ Icc a b, |f x| ≤ M) (hM0 : 0 ≤ M)
    (hα : MonotoneOn α (Icc a b)) (hbound : BoundedOn α' a b)
    (hder : ∀ x ∈ Icc a b, HasDerivWithinAt α (α' x) (Icc a b) x)
    (P : Partition a b) :
    |upperSum f α P - upperSum (fun x => f x * α' x) id P| ≤
        M * (upperSum α' id P - lowerSum α' id P) ∧
    |lowerSum f α P - lowerSum (fun x => f x * α' x) id P| ≤
        M * (upperSum α' id P - lowerSum α' id P) := by
  have hf : BoundedOn f a b := ⟨M, hM⟩
  have hg := calculus_bounded_mul hf hbound
  have hsum (c d : Fin P.n → ℝ)
      (he : ∀ i, |c i - d i| ≤
        M * ((cellUpper α' P i - cellLower α' P i) * P.weight id i)) :
      |∑ i, c i - ∑ i, d i| ≤ M * (upperSum α' id P - lowerSum α' id P) := by
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ i, (c i - d i)| ≤ ∑ i, |c i - d i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin P.n, M * ((cellUpper α' P i - cellLower α' P i) * P.weight id i) :=
        Finset.sum_le_sum (fun i _ => he i)
      _ = M * (upperSum α' id P - lowerSum α' id P) := by
        unfold upperSum lowerSum
        simp only [← Finset.mul_sum, sub_mul, Finset.sum_sub_distrib]
  constructor
  · apply hsum
    intro i
    exact calculus_cellUpper_weight_error hf hg P i (P.weight_nonneg α hα i)
      (sub_nonneg.mpr (P.cell_order i))
      (fun x hx => calculus_weighted_cell_error hM hM0 hbound hder P i hx)
  · apply hsum
    intro i
    exact calculus_cellLower_weight_error hf hg P i (P.weight_nonneg α hα i)
      (sub_nonneg.mpr (P.cell_order i))
      (fun x hx => calculus_weighted_cell_error hM hM0 hbound hder P i hx)

theorem calculus_integrable_of_sum_error {f g α β q : ℝ → ℝ} {a b M : ℝ}
    (hf : RSIntegrable f α a b) (hg : BoundedOn g a b)
    (hβ : MonotoneOn β (Icc a b)) (hq : RIntegrable q a b) (hM : 0 ≤ M)
    (he : ∀ P : Partition a b,
      |upperSum f α P - upperSum g β P| ≤ M * (upperSum q id P - lowerSum q id P) ∧
      |lowerSum f α P - lowerSum g β P| ≤ M * (upperSum q id P - lowerSum q id P)) :
    RSIntegrable g β a b := by
  apply (rsIntegrable_iff_gap hf.1 hg hβ).mpr
  intro ε hε
  have hden : 0 < 4 * (M + 1) := by positivity
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hq.1 hq.2.1 hq.2.2.1).mp hq
    (ε / (4 * (M + 1))) (div_pos hε hden)
  obtain ⟨Q, hQ⟩ := (rsIntegrable_iff_gap hf.1 hf.2.1 hf.2.2.1).mp hf
    (ε / 2) (by positivity)
  obtain ⟨R, _, hRP, hRQ⟩ := pma6_3_common_refinement P Q
  refine ⟨R, ?_⟩
  have hqgap := pma6_7_refinement_gap P R hRP hq.2.1 hq.2.2.1 hP
  have hfgap := pma6_7_refinement_gap Q R hRQ hf.2.1 hf.2.2.1 hQ
  have hscaled := (lt_div_iff₀ hden).mp hqgap
  have hqnonneg := sub_nonneg.mpr (lowerSum_le_upperSum hq.2.1 hq.2.2.1 R)
  have hU := (abs_le.mp (he R).1).1
  have hL := (abs_le.mp (he R).2).2
  nlinarith

theorem calculus_integral_le_of_sum_error {f g α β q : ℝ → ℝ} {a b M : ℝ}
    (hf : RSIntegrable f α a b) (hg : RSIntegrable g β a b)
    (hq : RIntegrable q a b) (hM : 0 ≤ M)
    (he : ∀ P : Partition a b,
      upperSum f α P - upperSum g β P ≤ M * (upperSum q id P - lowerSum q id P)) :
    RSIntegral f α a b ≤ RSIntegral g β a b := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hden : 0 < 2 * (M + 1) := by positivity
  obtain ⟨P, hP⟩ := (rsIntegrable_iff_gap hq.1 hq.2.1 hq.2.2.1).mp hq
    (ε / (2 * (M + 1))) (div_pos hε hden)
  obtain ⟨Q, hQ⟩ := (rsIntegrable_iff_gap hg.1 hg.2.1 hg.2.2.1).mp hg
    (ε / 2) (by positivity)
  obtain ⟨R, _, hRP, hRQ⟩ := pma6_3_common_refinement P Q
  have hqgap := pma6_7_refinement_gap P R hRP hq.2.1 hq.2.2.1 hP
  have hggap := pma6_7_refinement_gap Q R hRQ hg.2.1 hg.2.2.1 hQ
  have hscaled := (lt_div_iff₀ hden).mp hqgap
  have hqnonneg := sub_nonneg.mpr (lowerSum_le_upperSum hq.2.1 hq.2.2.1 R)
  have hIf := (rsIntegral_bounds hf R).2
  have hIg := (rsIntegral_bounds hg R).1
  have herror := he R
  nlinarith

theorem pma6_17 : pma6_17_contract := by
  intro f α α' a b hab hα hder hα' hfbound
  obtain ⟨M, hM⟩ := hfbound
  have hM0 : 0 ≤ M := (abs_nonneg (f a)).trans (hM a (left_mem_Icc.mpr hab.le))
  have hfbound : BoundedOn f a b := ⟨M, hM⟩
  have hg := calculus_bounded_mul hfbound hα'.2.1
  have hid : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
  have he := calculus_weighted_darbouxSum_error hM hM0 hα hα'.2.1 hder
  have he' : ∀ P : Partition a b,
      |upperSum (fun x => f x * α' x) id P - upperSum f α P| ≤
        M * (upperSum α' id P - lowerSum α' id P) ∧
      |lowerSum (fun x => f x * α' x) id P - lowerSum f α P| ≤
        M * (upperSum α' id P - lowerSum α' id P) := by
    intro P
    simpa only [abs_sub_comm] using he P
  have hiff : RSIntegrable f α a b ↔ RSIntegrable (fun x => f x * α' x) id a b := by
    constructor
    · intro hf
      exact calculus_integrable_of_sum_error hf hg hid hα' hM0 he
    · intro hh
      exact calculus_integrable_of_sum_error hh hfbound hα hα' hM0 he'
  refine ⟨hiff, ?_⟩
  intro hf
  exact le_antisymm
    (calculus_integral_le_of_sum_error hf (hiff.mp hf) hα' hM0
      (fun P => (abs_le.mp (he P).1).2))
    (calculus_integral_le_of_sum_error (hiff.mp hf) hf hα' hM0
      (fun P => (abs_le.mp (he' P).1).2))

theorem pma6_19 : pma6_19_contract := by
  constructor
  · intro f α φ a b A B hab hAB hφ hcont him hα hf
    exact pma6_19_transport hab hAB hφ hcont him hα hf
  · intro f φ φ' a b A B hab hAB hφ hcont him hder hφ' hf
    have hid : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
    have ht := pma6_19_transport hab.le hAB.le hφ hcont him hid hf
    have ht' : RSIntegrable (f ∘ φ) φ A B := by
      simpa only [Function.id_comp] using ht.1
    have hc := pma6_17 (f ∘ φ) φ φ' A B hAB hφ.monotoneOn hder hφ' ht'.2.1
    refine ⟨hc.1.mp ht', ?_⟩
    have hi : RSIntegral (f ∘ φ) φ A B = RSIntegral f id a b := by
      simpa only [Function.id_comp] using ht.2
    exact hi.symm.trans (hc.2 ht')

/-! Primitive estimates on closed intervals, including zero-length restrictions. -/

theorem calculus_singleton_integrals (f α : ℝ → ℝ) (a : ℝ) :
    RSIntegrable f α a a ∧ RSIntegral f α a a = 0 := by
  have hb : BoundedOn f a a := ⟨|f a|, by simp⟩
  have hm : MonotoneOn α (Icc a a) := by
    intro x hx y hy hxy
    have hx' : x = a := le_antisymm hx.2 hx.1
    have hy' : y = a := le_antisymm hy.2 hy.1
    subst x; subst y
    exact le_rfl
  have hbounds := darboux_integrals_bounds (le_refl a) hb hm
    (m := -|f a|) (M := |f a|)
    (by intro x hx; have : x = a := le_antisymm hx.2 hx.1; subst x; exact neg_abs_le _)
    (by intro x hx; have : x = a := le_antisymm hx.2 hx.1; subst x; exact le_abs_self _)
  simp only [sub_self, mul_zero] at hbounds
  have hl : lowerIntegral f α a a = 0 := le_antisymm hbounds.2.1 hbounds.1
  have hu : upperIntegral f α a a = 0 := le_antisymm hbounds.2.2.2 hbounds.2.2.1
  exact ⟨⟨le_rfl, hb, hm, hl.trans hu.symm⟩, hl⟩

theorem calculus_primitive_increment {f : ℝ → ℝ} {a b x y : ℝ}
    (hf : RSIntegrable f id a b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x ≤ y) :
    RSIntegrable f id x y ∧
      RSIntegral f id a y - RSIntegral f id a x = RSIntegral f id x y := by
  have hay := (split_ordered hy.1 hy.2 hf).1
  have h := split_ordered hx.1 hxy hay
  exact ⟨h.2.1, by linarith [h.2.2]⟩

theorem calculus_primitive_lipschitz {f : ℝ → ℝ} {a b M : ℝ}
    (hf : RSIntegrable f id a b) (hM : ∀ x ∈ Icc a b, |f x| ≤ M)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |RSIntegral f id a y - RSIntegral f id a x| ≤ M * |y - x| := by
  rcases le_total x y with hxy | hyx
  · have h := calculus_primitive_increment hf hx hy hxy
    rw [h.2, abs_of_nonneg (sub_nonneg.mpr hxy)]
    exact rsIntegral_abs_le_bound h.1 (fun t ht => hM t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩)
  · have h := calculus_primitive_increment hf hy hx hyx
    rw [abs_sub_comm, h.2, abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub]
    exact rsIntegral_abs_le_bound h.1 (fun t ht => hM t ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩)

theorem calculus_primitive_error_ordered {f : ℝ → ℝ} {a b x y c ε : ℝ}
    (hf : RSIntegrable f id a b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (hxy : x ≤ y) (he : ∀ t ∈ Icc x y, |f t - c| ≤ ε) :
    |RSIntegral f id a y - RSIntegral f id a x - c * (y - x)| ≤ ε * (y - x) := by
  have h := calculus_primitive_increment hf hx hy hxy
  have hb := darboux_integrals_bounds hxy h.1.2.1 h.1.2.2.1
    (m := c - ε) (M := c + ε)
    (fun t ht => by have := (abs_le.mp (he t ht)).1; linarith)
    (fun t ht => by have := (abs_le.mp (he t ht)).2; linarith)
  rw [h.2]
  change |lowerIntegral f id x y - c * (y - x)| ≤ ε * (y - x)
  simp only [id_eq] at hb
  apply abs_le.mpr
  constructor <;> nlinarith [hb.1, hb.2.1]

theorem calculus_primitive_error {f : ℝ → ℝ} {a b x y ε : ℝ}
    (hf : RSIntegrable f id a b) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b)
    (he : ∀ t ∈ Icc a b, |t - x| ≤ |y - x| → |f t - f x| ≤ ε) :
    |RSIntegral f id a y - RSIntegral f id a x - (y - x) * f x| ≤ ε * |y - x| := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (sub_nonneg.mpr hxy), mul_comm (y - x)]
    apply calculus_primitive_error_ordered hf hx hy hxy
    intro t ht
    apply he t ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1), abs_of_nonneg (sub_nonneg.mpr hxy)]
    linarith [ht.2]
  · have hh := calculus_primitive_error_ordered hf hy hx hyx (c := f x) (ε := ε)
      (fun t ht => he t ⟨hy.1.trans ht.1, ht.2.trans hx.2⟩ (by
        rw [abs_of_nonpos (sub_nonpos.mpr ht.2), abs_of_nonpos (sub_nonpos.mpr hyx)]
        linarith [ht.1]))
    have heq : RSIntegral f id a y - RSIntegral f id a x - (y - x) * f x =
        -(RSIntegral f id a x - RSIntegral f id a y - f x * (x - y)) := by ring
    rw [heq, abs_neg, abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub]
    exact hh

theorem pma6_20 : pma6_20_contract := by
  intro f a b hab hf
  obtain ⟨M, hM⟩ := hf.2.1
  have hM0 : 0 ≤ M := (abs_nonneg (f a)).trans (hM a (left_mem_Icc.mpr hab.le))
  have hlip : LipschitzOnWith ⟨M, hM0⟩ (fun x => RSIntegral f id a x) (Icc a b) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    change |RSIntegral f id a x - RSIntegral f id a y| ≤ M * |x - y|
    exact calculus_primitive_lipschitz hf hM hy hx
  refine ⟨hlip.continuousOn, hlip.uniformContinuousOn, ?_⟩
  intro x hx hc
  apply HasDerivWithinAt.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousWithinAt_iff.mp hc ε hε
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hdist : |y - x| < δ := by simpa only [Metric.mem_ball, Real.dist_eq] using hy.1
  change |RSIntegral f id a y - RSIntegral f id a x - (y - x) * f x| ≤ ε * |y - x|
  exact calculus_primitive_error hf hx hy.2 (fun t ht htx => by
      exact (hd ht (by simpa only [Real.dist_eq] using htx.trans_lt hdist)).le)

/-! The native product rule and integral algebra give the full parts conclusion. -/

theorem pma6_22 : pma6_22_contract := by
  intro F G f g a b hab hF hG hf hg
  have hid : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
  have hFI : RSIntegrable F id a b := rsIntegrable_of_continuousOn hab.le
    (fun x hx => (hF x hx).continuousWithinAt) hid
  have hGI : RSIntegrable G id a b := rsIntegrable_of_continuousOn hab.le
    (fun x hx => (hG x hx).continuousWithinAt) hid
  have hFg := rsIntegrable_mul hFI hg
  have hfG := rsIntegrable_mul hf hGI
  have hadd := rsIntegrable_add hfG hFg
  have hprod := pma6_21 (fun x => F x * G x) (fun x => f x * G x + F x * g x)
    a b hab (fun x hx => (hF x hx).mul (hG x hx)) hadd.1
  exact ⟨hFg, hfG, by linarith [hadd.2, hprod]⟩

/-! Boundary probes: constant integrators, singleton transport, and relative endpoints. -/

theorem calculus_probe_constant_integrator {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (hf : BoundedOn f a b) :
    RSIntegrable f (fun _ => c) a b ∧ RSIntegral f (fun _ => c) a b = 0 := by
  have hid : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
  have hz : RSIntegrable (fun _ : ℝ => (0 : ℝ)) id a b :=
    rsIntegrable_of_continuousOn hab.le continuousOn_const hid
  have h := pma6_17 f (fun _ => c) (fun _ => 0) a b hab (fun _ _ _ _ _ => le_rfl)
    (fun _ _ => hasDerivWithinAt_const _ _ _) hz hf
  have hprod : RSIntegrable (fun x => f x * 0) id a b := by simpa using hz
  have hs := h.1.mpr hprod
  have hi := pma6_21 (fun _ => 0) (fun _ => 0) a b hab
    (fun _ _ => hasDerivWithinAt_const _ _ _) hz
  exact ⟨hs, by simpa using (h.2 hs).trans (by simpa using hi)⟩

theorem calculus_probe_singleton_substitution (f α : ℝ → ℝ) (a A : ℝ) :
    RSIntegrable (f ∘ (fun _ => a)) (α ∘ (fun _ => a)) A A ∧
      RSIntegral (f ∘ (fun _ => a)) (α ∘ (fun _ => a)) A A = RSIntegral f α a a := by
  apply pma6_19.1 f α (fun _ => a) a a A A le_rfl le_rfl
  · intro x hx y hy hxy
    have hx' : x = A := le_antisymm hx.2 hx.1
    have hy' : y = A := le_antisymm hy.2 hy.1
    exact False.elim (hxy.ne (hx'.trans hy'.symm))
  · exact continuousOn_const
  · simp
  · exact (calculus_singleton_integrals f α a).1.2.2.1
  · exact (calculus_singleton_integrals f α a).1

theorem calculus_probe_relative_primitive_endpoints {f : ℝ → ℝ} {a b c : ℝ}
    (hab : a < b) (heq : ∀ x ∈ Icc a b, f x = c) :
    HasDerivWithinAt (fun u => RSIntegral f (fun t => t) a u) c (Icc a b) a ∧
      HasDerivWithinAt (fun u => RSIntegral f (fun t => t) a u) c (Icc a b) b := by
  have hc : ContinuousOn f (Icc a b) := continuousOn_const.congr heq
  have hid : MonotoneOn (id : ℝ → ℝ) (Icc a b) := fun _ _ _ _ h => h
  have hf := rsIntegrable_of_continuousOn hab.le hc hid
  have h := (pma6_20 f a b hab hf).2.2
  have ha := left_mem_Icc.mpr hab.le
  have hb := right_mem_Icc.mpr hab.le
  exact ⟨by simpa only [heq a ha] using h a ha (hc a ha),
    by simpa only [heq b hb] using h b hb (hc b hb)⟩

#print axioms calculus_probe_constant_integrator
#print axioms calculus_probe_singleton_substitution
#print axioms calculus_probe_relative_primitive_endpoints
#print axioms pma6_22
#print axioms pma6_20

#print axioms pma6_17
#print axioms pma6_19
#print axioms pma6_21

end Rudin.PMA.Chapter06
