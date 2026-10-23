import Rudin.PMA.Chapter09.Inverse

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Rudin.PMA.Chapter09

def blockX {n m k : ℕ} (A : Euclidean n × Euclidean m →L[ℝ] Euclidean k) :=
  A.comp (ContinuousLinearMap.inl ℝ (Euclidean n) (Euclidean m))
def blockY {n m k : ℕ} (A : Euclidean n × Euclidean m →L[ℝ] Euclidean k) :=
  A.comp (ContinuousLinearMap.inr ℝ (Euclidean n) (Euclidean m))

def pma9_26_contract : Prop :=
  ∀ n m k (A : Euclidean n × Euclidean m →L[ℝ] Euclidean k),
    (∀ h, blockX A h = A (h, 0)) ∧ (∀ k, blockY A k = A (0, k)) ∧
    ∀ h k, A (h, k) = blockX A h + blockY A k

def pma9_27_contract : Prop :=
  ∀ n m (A : Euclidean n × Euclidean m →L[ℝ] Euclidean n),
    (blockX A).IsInvertible → ∀ k,
      (∃! h, A (h, k) = 0) ∧
      ∀ h, A (h,k) = 0 ↔ h = -(blockX A).inverse (blockY A k)

def ImplicitNeighborhood {n m : ℕ}
    (f : Euclidean n × Euclidean m → Euclidean n)
    (E : Set (Euclidean n × Euclidean m)) (a : Euclidean n) (b : Euclidean m)
    (g : Euclidean m → Euclidean n) (U : Set (Euclidean n × Euclidean m))
    (W : Set (Euclidean m)) : Prop :=
  IsOpen U ∧ (a,b) ∈ U ∧ U ⊆ E ∧ IsOpen W ∧ b ∈ W ∧ C1On g W ∧ g b = a ∧
    (∀ y ∈ W, (g y,y) ∈ U ∧ f (g y,y) = 0) ∧
    ∀ x y, (x,y) ∈ U → y ∈ W → f (x,y) = 0 → x = g y

def pma9_28_contract : Prop :=
  ∀ n m (E : Set (Euclidean n × Euclidean m))
    (f : Euclidean n × Euclidean m → Euclidean n) a b,
    IsOpen E → (a,b) ∈ E → C1On f E → f (a,b) = 0 →
    (blockX (fderiv ℝ f (a,b))).IsInvertible →
    ∃ g U W, ImplicitNeighborhood f E a b g U W ∧
      HasFDerivAt g (-(blockX (fderiv ℝ f (a,b))).inverse.comp
        (blockY (fderiv ℝ f (a,b)))) b ∧
      ∀ i j, (∑ k : Fin n,
        blockX (fderiv ℝ f (a,b)) (coordinateVector n k) i *
          componentPartial g b k j) +
        blockY (fderiv ℝ f (a,b)) (coordinateVector m j) i = 0

theorem pma9_26 : pma9_26_contract := by
  intro n m k A
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro h k
  change A (h,k) = A (h,0) + A (0,k)
  rw [← A.map_add]
  simp

theorem pma9_27 : pma9_27_contract := by
  intro n m A hA k
  obtain ⟨B, hB⟩ := hA
  have he : (blockX A).inverse = (B.symm : Euclidean n →L[ℝ] Euclidean n) := by
    rw [← hB, ContinuousLinearMap.inverse_equiv]
  have heq (h : Euclidean n) : A (h,k) = 0 ↔
      h = -(blockX A).inverse (blockY A k) := by
    rw [(pma9_26 n m n A).2.2, he, ← hB]
    constructor
    · intro hh
      apply B.injective
      simp only [map_neg, ContinuousLinearEquiv.coe_coe, B.apply_symm_apply]
      exact eq_neg_of_add_eq_zero_left hh
    · intro hh
      rw [hh]
      simp
  refine ⟨⟨-(blockX A).inverse (blockY A k), (heq _).mpr rfl,
    fun h hh => (heq h).mp hh⟩, heq⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem pma9_28 : pma9_28_contract := by
  intro n m E f a b hE hab hf hf0 hi
  let A := fderiv ℝ f (a,b)
  let s : (Euclidean m × Euclidean n) ≃L[ℝ] (Euclidean n × Euclidean m) :=
    ContinuousLinearEquiv.prodComm ℝ (Euclidean m) (Euclidean n)
  let F := f ∘ s
  have hdF : HasFDerivAt F (A.comp s) (b,a) :=
    (hf.1 (a,b) hab).hasFDerivAt.comp (b,a) s.hasFDerivAt
  have hcF : ContDiffAt ℝ 1 F (b,a) :=
    (((c1On_iff_contDiffOn hE).mp hf) (a,b) hab).contDiffAt (hE.mem_nhds hab) |>.comp (b,a) s.contDiff.contDiffAt
  have hsX : (A.comp s.toContinuousLinearMap).comp (ContinuousLinearMap.inr ℝ (Euclidean m) (Euclidean n)) = blockX A := by
    ext x i
    rfl
  have hsY : (A.comp s.toContinuousLinearMap).comp (ContinuousLinearMap.inl ℝ (Euclidean m) (Euclidean n)) = blockY A := by
    ext x i
    rfl
  have hiF : (fderiv ℝ F (b,a) ∘L ContinuousLinearMap.inr ℝ (Euclidean m) (Euclidean n)).IsInvertible := by
    rw [hdF.fderiv, hsX]
    exact hi
  let g := hcF.implicitFunction (by norm_num) hiF
  have hgb : g b = a := hcF.implicitFunction_apply_self (by norm_num) hiF
  have hcg : ContDiffAt ℝ 1 g b := hcF.contDiffAt_implicitFunction (by norm_num) hiF
  have hder : HasFDerivAt g (-(blockX A).inverse.comp (blockY A)) b := by
    have h := (hcF.hasStrictFDerivAt_implicitFunction (by norm_num) hiF).hasFDerivAt
    rw [hdF.fderiv, hsX, hsY] at h
    exact h
  have hevent : ∀ᶠ p in 𝓝 (a,b), f p = 0 ↔ g p.2 = p.1 := by
    have h := hcF.eventually_apply_eq_iff_implicitFunction (by norm_num) hiF
    have hs := (s.symm.continuousAt (x := (a,b))).tendsto.eventually h
    simpa [F, s, hf0] using hs
  obtain ⟨U, hUsub, hUopen, habU⟩ := mem_nhds_iff.mp
    (inter_mem (hE.mem_nhds hab) hevent)
  have hgraph : ContinuousAt (fun y => (g y,y)) b := hcg.continuousAt.prodMk continuousAt_id
  have hgraphU : ∀ᶠ y in 𝓝 b, (g y,y) ∈ U := by
    exact hgraph (by simpa only [hgb] using hUopen.mem_nhds habU)
  obtain ⟨W, hWsub, hWopen, hbW⟩ := mem_nhds_iff.mp
    (inter_mem (hcg.eventually (by norm_num)) hgraphU)
  have hCW : C1On g W := (c1On_iff_contDiffOn hWopen).mpr
    (fun y hy => (show ContDiffAt ℝ 1 g y from (hWsub hy).1).contDiffWithinAt)
  refine ⟨g, U, W, ⟨hUopen, habU, fun p hp => (hUsub hp).1,
    hWopen, hbW, hCW, hgb, ?_, ?_⟩, hder, ?_⟩
  · intro y hy
    have hgy := (hWsub hy).2
    exact ⟨hgy, ((hUsub hgy).2).mpr rfl⟩
  · intro x y hxy _ hzero
    exact (((hUsub hxy).2).mp hzero).symm
  · intro i j
    let v := coordinateVector m j
    let G := -(blockX A).inverse.comp (blockY A)
    have hp (k : Fin n) : componentPartial g b k j = G v k := by
      exact (hasCoordinatePartial_of_hasFDerivAt
        (((EuclideanSpace.proj k : Euclidean n →L[ℝ] ℝ)).hasFDerivAt.comp b hder) j).deriv
    have hlin := linear_apply_eq_sum_coordinates
      ((EuclideanSpace.proj i).comp (blockX A)) (G v)
    have hzero : blockX A (G v) + blockY A v = 0 := by
      obtain ⟨B,hB⟩ := hi
      change (B : Euclidean n →L[ℝ] Euclidean n) = blockX A at hB
      simp [G, ← hB, ContinuousLinearMap.inverse_equiv]
    have hz := congrArg (fun z : Euclidean n => z i) hzero
    simp only [ContinuousLinearMap.comp_apply, EuclideanSpace.coe_proj] at hlin
    simp only [PiLp.add_apply, PiLp.zero_apply] at hz
    rw [hlin] at hz
    simpa only [A, v, hp] using hz

end Rudin.PMA.Chapter09
