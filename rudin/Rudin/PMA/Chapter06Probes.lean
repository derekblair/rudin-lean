import Rudin.PMA.Chapter06.Definitions
import Rudin.PMA.Chapter06.Refinement
import Rudin.PMA.Chapter06.Jump
import Rudin.PMA.Chapter06.Monotone
import Rudin.PMA.Chapter06.Calculus

noncomputable section
open Set
open scoped Topology

namespace Rudin.PMA.Chapter06.FidelityProbes

/-- A constant integrator cannot impose continuity on an arbitrary bounded integrand. -/
theorem zero_mass_arbitrary_bounded (f : ℝ → ℝ) (hf : BoundedOn f (-2) 3) :
    RSIntegrable f (fun _ => 11) (-2) 3 ∧ RSIntegral f (fun _ => 11) (-2) 3 = 0 :=
  rsIntegral_const_integrator (by norm_num) hf

/-- A concrete discontinuous integrand still has integral zero against zero mass. -/
theorem discontinuous_zero_mass :
    ¬ ContinuousWithinAt UnitStep (Icc (-1 : ℝ) 1) 0 ∧
    RSIntegrable UnitStep (fun _ => 7) (-1) 1 ∧
      RSIntegral UnitStep (fun _ => 7) (-1) 1 = 0 := by
  have hb : BoundedOn UnitStep (-1) 1 := by
    refine ⟨1, ?_⟩
    intro x _
    by_cases hx : x ≤ 0 <;> simp [UnitStep, hx]
  exact ⟨unitStep_source_caution.1, rsIntegral_const_integrator (by norm_num) hb⟩

/-- The shared-jump obstruction vanishes on an actual zero-length interval. -/
theorem singleton_at_shared_jump :
    RSIntegrable UnitStep UnitStep 0 0 ∧ RSIntegral UnitStep UnitStep 0 0 = 0 :=
  rsIntegral_same_endpoint UnitStep UnitStep 0

/-- Empty partition families on reversed intervals must not manufacture integrability. -/
theorem reversed_interval_rejected (f α : ℝ → ℝ) : ¬ RSIntegrable f α 1 (-1) := by
  intro h
  linarith [h.1]

/-- The actual value at the discontinuity belongs to the left branch. -/
theorem step_value_orientation :
    UnitStep (-1 / 2) = 0 ∧ UnitStep 0 = 0 ∧ UnitStep (1 / 2) = 1 := by
  norm_num [UnitStep]

/-- Refinement never removes the closed-cell gap caused by this shared jump. -/
theorem shared_jump_gap_persists :
    ¬ RSIntegrable UnitStep UnitStep (-1) 1 ∧
      ∀ P : Partition (-1) 1, lowerSum UnitStep UnitStep P = 0 ∧
        upperSum UnitStep UnitStep P = 1 := by
  refine ⟨unitStep_source_caution.2, ?_⟩
  intro P
  have hz : TranslatedStep 0 = UnitStep := by funext x; simp [TranslatedStep]
  simpa only [hz] using translatedStep_self_sums
    (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1) P

/-- The same discontinuous step is ordinarily Riemann integrable. -/
theorem monotone_discontinuous_ordinary :
    ¬ ContinuousWithinAt UnitStep (Icc (-1 : ℝ) 1) 0 ∧ RIntegrable UnitStep (-1) 1 := by
  refine ⟨unitStep_source_caution.1, ?_⟩
  exact rsIntegrable_monotone (by norm_num) (pma6_14.2.2.monotoneOn _)
    (fun _ _ _ _ h => h) continuousOn_id

/-- Antitone discontinuous integrands are included as well. -/
theorem antitone_discontinuous_ordinary :
    ¬ ContinuousWithinAt (fun x => -UnitStep x) (Icc (-1 : ℝ) 1) 0 ∧
      RIntegrable (fun x => -UnitStep x) (-1) 1 := by
  constructor
  · intro hc
    apply unitStep_source_caution.1
    convert hc.neg using 1
    funext x
    simp
  · apply rsIntegrable_antitone (by norm_num)
      (fun x _ y _ hxy => neg_le_neg (pma6_14.2.2 hxy))
      (fun _ _ _ _ h => h) continuousOn_id

def repeatedEndpoints : Partition (-1) 1 where
  n := 3
  point := ![-1, -1, 1, 1]
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  left := rfl
  right := rfl

/-- Two extra endpoint cells contribute zero even for discontinuous bounded functions. -/
theorem repeated_partition_harmless (f α : ℝ → ℝ)
    (hf : BoundedOn f (-1) 1) (hα : MonotoneOn α (Icc (-1 : ℝ) 1)) :
    lowerSum f α repeatedEndpoints = lowerSum f α (Partition.single (by norm_num : (-1 : ℝ) ≤ 1)) ∧
      upperSum f α repeatedEndpoints = upperSum f α (Partition.single (by norm_num : (-1 : ℝ) ≤ 1)) := by
  apply pma6_3_repetition_invariant repeatedEndpoints
    (Partition.single (by norm_num : (-1 : ℝ) ≤ 1)) _ hf hα
  ext x
  simp [repeatedEndpoints, Partition.single]

/-- A jump immediately to the right of the left endpoint retains its full raw mass. -/
theorem boundary_jump_mass_retained :
    RSIntegrable (fun _ => 1) UnitStep 0 1 ∧
      RSIntegral (fun _ => 1) UnitStep 0 1 = 1 := by
  have h := rsIntegral_const (c := 1) (by norm_num : (0 : ℝ) ≤ 1)
    (pma6_14.2.2.monotoneOn (Icc (0 : ℝ) 1))
  norm_num [UnitStep] at h
  exact h

/-- Splitting at the jump assigns zero mass to the left piece and one to the right. -/
theorem split_at_jump_mass :
    RSIntegral (fun _ => 1) UnitStep (-1) 0 = 0 ∧
    RSIntegral (fun _ => 1) UnitStep 0 1 = 1 ∧
    RSIntegral (fun _ => 1) UnitStep (-1) 1 =
      RSIntegral (fun _ => 1) UnitStep (-1) 0 + RSIntegral (fun _ => 1) UnitStep 0 1 := by
  have hL := rsIntegral_const (c := 1) (by norm_num : (-1 : ℝ) ≤ 0)
    (pma6_14.2.2.monotoneOn (Icc (-1 : ℝ) 0))
  have hR := boundary_jump_mass_retained
  refine ⟨by simpa [UnitStep] using hL.2, hR.2, ?_⟩
  exact (split_append hL.1 hR.1).2

/-- An exterior jump does not alter either within-interval primitive derivative. -/
theorem primitive_ignores_exterior_jump :
    HasDerivWithinAt
      (fun u => RIntegral (fun x => if x < 0 then 99 else 1) 0 u) 1 (Icc (0 : ℝ) 1) 0 ∧
    HasDerivWithinAt
      (fun u => RIntegral (fun x => if x < 0 then 99 else 1) 0 u) 1 (Icc (0 : ℝ) 1) 1 := by
  apply calculus_probe_relative_primitive_endpoints (by norm_num : (0 : ℝ) < 1)
  intro x hx
  simp [not_lt.mpr hx.1]

def cutAtZero : Partition (-1) 1 where
  n := 2
  point := ![-1, 0, 1]
  mono := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  left := rfl
  right := rfl

/-- Opposite choices of the value at a shared jump can make the Darboux integral exist.
This example would be lost by replacing refinement convergence with a uniform mesh limit. -/
theorem right_value_jump_is_integrable :
    RSIntegrable (fun x => if x < 0 then 0 else 1) UnitStep (-1) 1 ∧
      RSIntegral (fun x => if x < 0 then 0 else 1) UnitStep (-1) 1 = 1 := by
  let f : ℝ → ℝ := fun x => if x < 0 then 0 else 1
  change RSIntegrable f UnitStep (-1) 1 ∧ RSIntegral f UnitStep (-1) 1 = 1
  have hm : MonotoneOn f (Icc (-1 : ℝ) 1) := by
    intro x _ y _ hxy
    by_cases hx : x < 0
    · by_cases hy : y < 0 <;> simp [f, hx, hy]
    · have hy : ¬ y < 0 := fun hy => hx (hxy.trans_lt hy)
      simp [f, hx, hy]
  have hb := monotoneOn_boundedOn (by norm_num : (-1 : ℝ) ≤ 1) hm
  have hα := pma6_14.2.2.monotoneOn (Icc (-1 : ℝ) 1)
  have hsums : lowerSum f UnitStep cutAtZero = 1 ∧ upperSum f UnitStep cutAtZero = 1 := by
    simp only [lowerSum, upperSum, cellLower_of_monotone hm, cellUpper_of_monotone hm]
    change (∑ i : Fin 2, f (cutAtZero.point i.castSucc) *
      (UnitStep (cutAtZero.point i.succ) - UnitStep (cutAtZero.point i.castSucc))) = 1 ∧
      (∑ i : Fin 2, f (cutAtZero.point i.succ) *
      (UnitStep (cutAtZero.point i.succ) - UnitStep (cutAtZero.point i.castSucc))) = 1
    dsimp only [cutAtZero]
    norm_num [cutAtZero, Partition.weight, Fin.sum_univ_succ, f, UnitStep]
  have hi : RSIntegrable f UnitStep (-1) 1 := by
    apply (rsIntegrable_iff_gap (by norm_num) hb hα).mpr
    intro ε hε
    refine ⟨cutAtZero, ?_⟩
    rw [hsums.1, hsums.2]
    simpa using hε
  refine ⟨hi, ?_⟩
  have hbounds := rsIntegral_bounds hi cutAtZero
  rw [hsums.1, hsums.2] at hbounds
  exact le_antisymm hbounds.2 hbounds.1

/-- Closed cumulative mass includes both endpoint atoms; only the right one contributes
 to the quadratic moment. This directly exercises the endpoint scope of 6.18. -/
theorem endpoint_atomic_moment (c₀ c₁ : ℝ) (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) :
    AtomicMass ![0, 1] ![c₀, c₁] 0 = c₀ ∧
    AtomicMass ![0, 1] ![c₀, c₁] 1 = c₀ + c₁ ∧
    RSIntegrable QuadraticPosition (AtomicMass ![0, 1] ![c₀, c₁]) 0 1 ∧
    RSIntegral QuadraticPosition (AtomicMass ![0, 1] ![c₀, c₁]) 0 1 = c₁ := by
  refine ⟨?_, ?_, ?_⟩
  · norm_num [AtomicMass, tsum_fintype, Fin.sum_univ_succ]
  · norm_num [AtomicMass, tsum_fintype, Fin.sum_univ_succ]
  · have hs : ∀ i : Fin 2, (![0, 1] : Fin 2 → ℝ) i ∈ Icc (0 : ℝ) 1 := by
      intro i
      fin_cases i <;> norm_num
    have hc : ∀ i : Fin 2, 0 ≤ (![c₀, c₁] : Fin 2 → ℝ) i := by
      intro i
      fin_cases i
      · exact h₀
      · exact h₁
    simpa [Fin.sum_univ_succ] using finiteAtomicQuadraticMoment hs hc

end Rudin.PMA.Chapter06.FidelityProbes
