import Rudin.PMA.Chapter11.Regularity
import Rudin.PMA.Chapter11.Geometry

open Set Filter Topology TopologicalSpace MeasureTheory

namespace Rudin.PMA.Chapter11

/-- 11.11(c): the Borel sets form a sigma-ring. -/
theorem pma11_11c_borel_sigmaRing (X : Type*) [TopologicalSpace X] :
    SigmaRing {A : Set X | MeasurableSet[borel X] A} := by
  let : MeasurableSpace X := borel X
  exact {
    union_mem := fun A B hA hB => @MeasurableSet.union X (borel X) A B hA hB
    sdiff_mem := fun A B hA hB => @MeasurableSet.diff X (borel X) A B hA hB
    iUnion_mem := fun A hA => @MeasurableSet.iUnion X ℕ (borel X) _ A hA }

/-- 11.11(c): every sigma-ring containing all open sets contains the Borel sets.
Since the universe is open, no sigma-algebra assumption has been added. -/
theorem pma11_11c_borel_minimal {X : Type*} [TopologicalSpace X]
    {R : Set (Set X)} (hR : SigmaRing R) (hopen : ∀ A, IsOpen A → A ∈ R)
    {A : Set X} (hA : MeasurableSet[borel X] A) : A ∈ R := by
  induction A, hA using MeasurableSpace.generateFrom_induction with
  | hC A hA _ => exact hopen A hA
  | empty => exact hR.toSetRing.empty_mem ⟨univ, hopen univ isOpen_univ⟩
  | compl A _ hA =>
    convert hR.sdiff_mem (hopen univ isOpen_univ) hA using 1
    ext x
    simp only [mem_compl_iff, Set.mem_sdiff, mem_univ, true_and]
  | iUnion A _ hA => exact hR.iUnion_mem A hA

/-- Open elementary sets form a basis in the finite Cartesian coordinate model
of Euclidean space, since every positive-radius supremum-norm ball is an interval. -/
theorem isTopologicalBasis_openElementary (p : ℕ) :
    IsTopologicalBasis {A : Set (Fin p → ℝ) | IsElementary A ∧ IsOpen A} := by
  apply isTopologicalBasis_of_isOpen_of_nhds (fun _ h => h.2)
  intro x U hx hU
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
  exact ⟨Metric.ball x r, ⟨isElementary_ball x hr, Metric.isOpen_ball⟩,
    Metric.mem_ball_self hr, hsub⟩

/-- 11.11(c): every Borel set is measurable for every regular elementary content.
Thus Borel measurability is independent of the particular content. -/
theorem pma11_11c {p : ℕ} (μ : RegularContent (Fin p → ℝ) {A | IsElementary A})
    {A : Set (Fin p → ℝ)} (hA : MeasurableSet A) : μ.RudinMeasurable A := by
  apply (μ.rudinMeasurable_iff (elementaryCube p) (elementaryCube_isElementary p)
    (iUnion_elementaryCube p)).mpr
  have hle : borel (Fin p → ℝ) ≤ μ.outer.caratheodory := by
    rw [(isTopologicalBasis_openElementary p).borel_eq_generateFrom]
    exact MeasurableSpace.generateFrom_le fun A hA => μ.elementary_caratheodory hA.1
  rw [← BorelSpace.measurable_eq (α := Fin p → ℝ)] at hle
  exact hle A hA

/-- 11.11(a): open and closed sets are measurable. -/
theorem pma11_11a {p : ℕ} (μ : RegularContent (Fin p → ℝ) {A | IsElementary A})
    {A : Set (Fin p → ℝ)} (hA : IsOpen A ∨ IsClosed A) : μ.RudinMeasurable A := by
  apply pma11_11c μ
  rcases hA with hA | hA
  · exact hA.measurableSet
  · exact hA.measurableSet

end Rudin.PMA.Chapter11
