import Rudin.PMA.Chapter10.Simplex

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10

lemma mem_standardSimplex_insertNth {d : ℕ} (i : Fin (d + 1)) (u : Coord d) (t : ℝ) :
    i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u ∈ standardSimplex (d + 1) ↔
      (∀ j, 0 ≤ u j) ∧ 0 ≤ t ∧ (∑ j, u j) + t ≤ 1 := by
  change ((∀ j, 0 ≤ i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u j) ∧ (∑ j, i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u j) ≤ 1) ↔ _
  rw [Fin.forall_iff_succAbove i, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp only [and_assoc, and_left_comm, add_comm]

lemma continuous_simplex_upper_face {d : ℕ} (i : Fin (d + 1)) :
    Continuous (fun u : Coord d => i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u) :=
  Continuous.finInsertNth (A := fun _ : Fin (d + 1) => ℝ) i
    (continuous_const.sub (continuous_finsetSum _ (fun j _ => continuous_apply j))) continuous_id

lemma continuous_simplex_lower_face {d : ℕ} (i : Fin (d + 1)) :
    Continuous (fun u : Coord d => i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u) :=
  Continuous.finInsertNth (A := fun _ : Fin (d + 1) => ℝ) i continuous_const continuous_id

lemma simplex_upper_face_mem {d : ℕ} (i : Fin (d + 1)) {u : Coord d}
    (hu : u ∈ standardSimplex d) : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u ∈ standardSimplex (d + 1) := by
  apply (mem_standardSimplex_insertNth i u _).mpr
  exact ⟨hu.1, sub_nonneg.mpr hu.2, by linarith⟩

lemma simplex_lower_face_mem {d : ℕ} (i : Fin (d + 1)) {u : Coord d}
    (hu : u ∈ standardSimplex d) : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u ∈ standardSimplex (d + 1) := by
  apply (mem_standardSimplex_insertNth i u _).mpr
  exact ⟨hu.1, le_rfl, by simpa only [add_zero] using hu.2⟩

/-- Product disintegration at any chosen coordinate, preserving the order of
all remaining coordinates. -/
lemma integral_unit_insertNth {d : ℕ} (i : Fin (d + 1)) (f : Coord (d + 1) → ℝ)
    (hf : Integrable f (Cell.unit (d + 1)).measure) :
    (∫ x, f x ∂(Cell.unit (d + 1)).measure) =
      ∫ u, (∫ t in Icc (0 : ℝ) 1, f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)) ∂(Cell.unit d).measure := by
  let μ : Fin (d + 1) → Measure ℝ := fun _ => volume.restrict (Icc (0 : ℝ) 1)
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i
  have hm := (measurePreserving_piFinSuccAbove μ i).symm
  have hμall : Measure.pi μ = (Cell.unit (d + 1)).measure := by
    rw [Cell.measure_eq_pi]
    rfl
  have hμrest : Measure.pi (fun j => μ (i.succAbove j)) = (Cell.unit d).measure := by
    rw [Cell.measure_eq_pi]
    rfl
  have hi : Integrable f (Measure.pi μ) := by rw [hμall]; exact hf
  have hi' := (hm.integrable_comp_emb e.symm.measurableEmbedding).mpr hi
  have hsplit := (hm.integral_comp' f).symm
  have he : (fun p : ℝ × Coord d => f (e.symm p)) =
      (fun p : ℝ × Coord d => f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) p.1 p.2)) := by
    funext p
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
    rfl
  change Integrable (fun p : ℝ × Coord d => f (e.symm p))
    ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) at hi'
  rw [he, hμrest] at hi'
  change (∫ x, f x ∂Measure.pi μ) = ∫ p : ℝ × Coord d, f (e.symm p)
    ∂((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) at hsplit
  rw [he, hμrest, integral_prod_symm _ hi', hμall] at hsplit
  exact hsplit

/-- Fubini over the simplex with its actual variable endpoint. Native slice
existence is supplied by the already proved simplex integration theorem. -/
lemma simplexRIntegral_eq_fiberIntegral {d : ℕ} {f : Coord (d + 1) → ℝ}
    (hf : ContinuousOn f (standardSimplex (d + 1))) (i : Fin (d + 1)) :
    simplexRIntegral f =
      ∫ u in standardSimplex d, ∫ t in (0 : ℝ)..(1 - ∑ j, u j), f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u) := by
  have hi : Integrable (simplexExtension f) :=
    (hf.integrableOn_compact (isCompact_standardSimplex (d + 1))).integrable_indicator
      (isClosed_standardSimplex (d + 1)).measurableSet
  rw [simplexRIntegral_eq_cubeIntegral hf]
  change (∫ x, simplexExtension f x ∂(Cell.unit (d + 1)).measure) = _
  rw [integral_unit_insertNth i _ hi.restrict]
  let G : Coord d → ℝ := fun u => ∫ t in (0 : ℝ)..(1 - ∑ j, u j), f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)
  calc
    (∫ u, (∫ t in Icc (0 : ℝ) 1, simplexExtension f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)) ∂(Cell.unit d).measure) =
        ∫ u in (Cell.unit d).carrier, simplexExtension G u := by
      apply setIntegral_congr_fun (Cell.unit d).isClosed_carrier.measurableSet
      intro u hu
      dsimp only
      have hu0 : ∀ j, 0 ≤ u j := fun j => (Cell.mem_carrier.mp hu j).1
      have hsum0 : 0 ≤ ∑ j, u j := Finset.sum_nonneg (fun j _ => hu0 j)
      by_cases hsum : (∑ j, u j) ≤ 1
      · have hus : u ∈ standardSimplex d := ⟨hu0, hsum⟩
        have hc0 : 0 ≤ 1 - ∑ j, u j := sub_nonneg.mpr hsum
        have hc1 : 1 - (∑ j, u j) ≤ 1 := by linarith
        have he : EqOn (fun t => simplexExtension f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u))
            (stoppedSlice (fun t => f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)) (1 - ∑ j, u j)) (Icc 0 1) := by
          intro t ht
          by_cases htc : t ≤ 1 - ∑ j, u j
          · have hm : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u ∈ standardSimplex (d + 1) :=
              (mem_standardSimplex_insertNth i u t).mpr ⟨hu0, ht.1, by linarith⟩
            simp only [simplexExtension, Set.indicator_of_mem hm, stoppedSlice, ite_eq_left htc]
          · have hm : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u ∉ standardSimplex (d + 1) := by
              intro hm
              exact htc (by linarith [((mem_standardSimplex_insertNth i u t).mp hm).2.2])
            simp only [simplexExtension, Set.indicator_of_notMem hm, stoppedSlice, ite_eq_right htc]
        rw [setIntegral_congr_fun measurableSet_Icc he, stoppedSlice_setIntegral hc0 hc1]
        exact (Set.indicator_of_mem hus G).symm
      · have hus : u ∉ standardSimplex d := fun hus => hsum hus.2
        have he : EqOn (fun t => simplexExtension f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)) (fun _ => 0) (Icc 0 1) := by
          intro t ht
          have hm : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u ∉ standardSimplex (d + 1) := by
            intro hm
            exact hsum (by linarith [((mem_standardSimplex_insertNth i u t).mp hm).2.2, ht.1])
          exact Set.indicator_of_notMem hm f
        rw [setIntegral_congr_fun measurableSet_Icc he, integral_zero]
        exact (Set.indicator_of_notMem hus G).symm
    _ = ∫ u in standardSimplex d, G u := by
      rw [simplexExtension, setIntegral_indicator (isClosed_standardSimplex d).measurableSet,
        inter_eq_right.mpr (standardSimplex_subset_unit d)]

/-- The coordinate derivative appropriate to the fixed product-coordinate
native integral. -/
def simplexCoordinateDerivative {d : ℕ} (f : Coord d → ℝ) (i : Fin d) : Coord d → ℝ :=
  fun x => fderiv ℝ f x (Pi.single i 1)

def simplexFaceDifference {d : ℕ} (f : Coord (d + 1) → ℝ) (i : Fin (d + 1)) : Coord d → ℝ :=
  fun u => f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u) - f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u)

lemma continuousOn_simplexCoordinateDerivative {d : ℕ} {U : Set (Coord d)}
    {f : Coord d → ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (i : Fin d) :
    ContinuousOn (simplexCoordinateDerivative f i) U :=
  (hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).clm_apply continuousOn_const

lemma continuousOn_simplexFaceDifference {d : ℕ} {f : Coord (d + 1) → ℝ}
    (hf : ContinuousOn f (standardSimplex (d + 1))) (i : Fin (d + 1)) :
    ContinuousOn (simplexFaceDifference f i) (standardSimplex d) :=
  (hf.comp (continuous_simplex_upper_face i).continuousOn (fun _ hu => simplex_upper_face_mem i hu)).sub
    (hf.comp (continuous_simplex_lower_face i).continuousOn (fun _ hu => simplex_lower_face_mem i hu))

lemma hasDerivAt_insertNth {d : ℕ} (i : Fin (d + 1)) (u : Coord d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => i.insertNth (α := fun _ : Fin (d + 1) => ℝ) s u) (Pi.single i 1) t := by
  have he : (fun s : ℝ => i.insertNth (α := fun _ : Fin (d + 1) => ℝ) s u) = fun s => i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u + s • Pi.single i 1 := by
    funext s
    ext j
    refine Fin.succAboveCases i ?_ (fun l => ?_) j
    · simp
    · simp [Fin.succAbove_ne]
  rw [he]
  simpa only [one_smul] using!
    (((hasDerivAt_id t).smul_const (Pi.single i (1 : ℝ))).const_add (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u))

/-- Scalar native simplex FTC, including all coordinate choices, zero-dimensional
faces, and fibers whose upper endpoint is zero. -/
theorem simplex_coordinate_ftc {d : ℕ} {U : Set (Coord (d + 1))} {f : Coord (d + 1) → ℝ}
    (hU : IsOpen U) (hSU : standardSimplex (d + 1) ⊆ U) (hf : ContDiffOn ℝ 1 f U)
    (i : Fin (d + 1)) :
    IteratedRIntegrable (Cell.unit (d + 1)) (simplexExtension (simplexCoordinateDerivative f i)) ∧
    IteratedRIntegrable (Cell.unit d) (simplexExtension (simplexFaceDifference f i)) ∧
      simplexRIntegral (simplexCoordinateDerivative f i) = simplexRIntegral (simplexFaceDifference f i) := by
  have hfc : ContinuousOn f (standardSimplex (d + 1)) := hf.continuousOn.mono hSU
  have hdc : ContinuousOn (simplexCoordinateDerivative f i) (standardSimplex (d + 1)) :=
    (continuousOn_simplexCoordinateDerivative hU hf i).mono hSU
  have hbc := continuousOn_simplexFaceDifference hfc i
  refine ⟨simplex_iteratedRIntegrable hdc, simplex_iteratedRIntegrable hbc, ?_⟩
  rw [simplexRIntegral_eq_fiberIntegral hdc i, simplexRIntegral_eq_integral hbc]
  apply setIntegral_congr_fun (isClosed_standardSimplex d).measurableSet
  intro u hu
  have hc0 : 0 ≤ 1 - ∑ j, u j := sub_nonneg.mpr hu.2
  have hline : MapsTo (fun t : ℝ => i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u) (Icc 0 (1 - ∑ j, u j))
      (standardSimplex (d + 1)) := by
    intro t ht
    exact (mem_standardSimplex_insertNth i u t).mpr ⟨hu.1, ht.1, by linarith [ht.2]⟩
  have hc : ContinuousOn (fun t => simplexCoordinateDerivative f i (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u))
      (Icc 0 (1 - ∑ j, u j)) :=
    hdc.comp (Continuous.finInsertNth (A := fun _ : Fin (d + 1) => ℝ) i
      (f := fun t : ℝ => t) (g := fun _ : ℝ => u) continuous_id continuous_const).continuousOn hline
  have hint : IntervalIntegrable (fun t => simplexCoordinateDerivative f i (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u))
      volume 0 (1 - ∑ j, u j) :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le hc0] using hc)
  change (∫ t in (0 : ℝ)..(1 - ∑ j, u j), simplexCoordinateDerivative f i (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)) =
    f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) (1 - ∑ j, u j) u) - f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) 0 u)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => f (i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u)) _ hint
  intro t ht
  have hts : i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u ∈ standardSimplex (d + 1) :=
    hline (by simpa only [uIcc_of_le hc0] using ht)
  have hfd := hf.differentiableOn_one.differentiableAt (hU.mem_nhds (hSU hts))
  simpa only [simplexCoordinateDerivative] using!
    hfd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i u t)

end Rudin.PMA.Chapter10
