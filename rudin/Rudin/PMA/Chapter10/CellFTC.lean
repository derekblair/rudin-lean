import Rudin.PMA.Chapter10.SimplexFTC

noncomputable section
set_option autoImplicit false
open Set Function MeasureTheory
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10

/-- Remove one coordinate without changing the order of the remaining ones. -/
def Cell.delete {d : ℕ} (C : Cell (d + 1)) (i : Fin (d + 1)) : Cell d where
  lower := fun j => C.lower (i.succAbove j)
  upper := fun j => C.upper (i.succAbove j)
  lower_le_upper := fun j => C.lower_le_upper (i.succAbove j)

def cellFaceMap {d : ℕ} (i : Fin (d + 1)) (t : ℝ) (u : Coord d) : Coord (d + 1) :=
  i.insertNth (α := fun _ : Fin (d + 1) => ℝ) t u

lemma cellFaceMap_contDiff {d : ℕ} (i : Fin (d + 1)) (t : ℝ) (r : WithTop ℕ∞) :
    ContDiff ℝ r (cellFaceMap i t) := by
  apply contDiff_pi.mpr
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simpa only [cellFaceMap, Fin.insertNth_apply_same] using
      (contDiff_const : ContDiff ℝ r (fun _ : Coord d => t))
  · simpa only [cellFaceMap, Fin.insertNth_apply_succAbove] using
      (contDiff_apply ℝ ℝ l : ContDiff ℝ r (fun u : Coord d => u l))

lemma Cell.insertNth_mem {d : ℕ} (C : Cell (d + 1)) (i : Fin (d + 1))
    {u : Coord d} (hu : u ∈ (C.delete i).carrier) {t : ℝ} (ht : t ∈ Icc (C.lower i) (C.upper i)) :
    cellFaceMap i t u ∈ C.carrier := by
  rw [Cell.mem_carrier]
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simpa only [cellFaceMap, Fin.insertNth_apply_same, mem_Icc] using ht
  · simpa only [cellFaceMap, Fin.insertNth_apply_succAbove, Cell.delete] using
      (Cell.mem_carrier.mp hu l)

lemma integral_cell_insertNth {d : ℕ} (C : Cell (d + 1)) (i : Fin (d + 1))
    (f : Coord (d + 1) → ℝ) (hf : Integrable f C.measure) :
    (∫ x, f x ∂C.measure) = ∫ u, (∫ t in Icc (C.lower i) (C.upper i),
      f (cellFaceMap i t u)) ∂(C.delete i).measure := by
  let μ : Fin (d + 1) → Measure ℝ := fun j => volume.restrict (Icc (C.lower j) (C.upper j))
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) i
  have hm := (measurePreserving_piFinSuccAbove μ i).symm
  have hμall : Measure.pi μ = C.measure := C.measure_eq_pi.symm
  have hμrest : Measure.pi (fun j => μ (i.succAbove j)) = (C.delete i).measure := by
    rw [Cell.measure_eq_pi]
    rfl
  have hi : Integrable f (Measure.pi μ) := by rw [hμall]; exact hf
  have hi' := (hm.integrable_comp_emb e.symm.measurableEmbedding).mpr hi
  have hsplit := (hm.integral_comp' f).symm
  have he : (fun p : ℝ × Coord d => f (e.symm p)) =
      (fun p : ℝ × Coord d => f (cellFaceMap i p.1 p.2)) := by
    funext p
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, cellFaceMap]
    rfl
  change Integrable (fun p : ℝ × Coord d => f (e.symm p))
    ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) at hi'
  rw [he, hμrest] at hi'
  change (∫ x, f x ∂Measure.pi μ) = ∫ p : ℝ × Coord d, f (e.symm p)
    ∂((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) at hsplit
  rw [he, hμrest, integral_prod_symm _ hi', hμall] at hsplit
  exact hsplit

lemma cell_coordinate_ftc {d : ℕ} (C : Cell (d + 1)) {U : Set (Coord (d + 1))}
    {f : Coord (d + 1) → ℝ} (hU : IsOpen U) (hCU : C.carrier ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) (i : Fin (d + 1)) :
    iteratedRIntegral C (simplexCoordinateDerivative f i) =
      iteratedRIntegral (C.delete i) (fun u => f (cellFaceMap i (C.upper i) u)) -
      iteratedRIntegral (C.delete i) (fun u => f (cellFaceMap i (C.lower i) u)) := by
  have hdc : ContinuousOn (simplexCoordinateDerivative f i) C.carrier :=
    (continuousOn_simplexCoordinateDerivative hU hf i).mono hCU
  have hup : ContinuousOn (fun u => f (cellFaceMap i (C.upper i) u)) (C.delete i).carrier :=
    (hf.continuousOn.mono hCU).comp (cellFaceMap_contDiff i (C.upper i) 1).continuous.continuousOn
      (fun _ hu => C.insertNth_mem i hu ⟨C.lower_le_upper i, le_rfl⟩)
  have hlo : ContinuousOn (fun u => f (cellFaceMap i (C.lower i) u)) (C.delete i).carrier :=
    (hf.continuousOn.mono hCU).comp (cellFaceMap_contDiff i (C.lower i) 1).continuous.continuousOn
      (fun _ hu => C.insertNth_mem i hu ⟨le_rfl, C.lower_le_upper i⟩)
  rw [iteratedRIntegral_eq_setIntegral hdc, iteratedRIntegral_eq_setIntegral hup,
    iteratedRIntegral_eq_setIntegral hlo]
  change (∫ x, simplexCoordinateDerivative f i x ∂C.measure) =
    (∫ u, f (cellFaceMap i (C.upper i) u) ∂(C.delete i).measure) -
      ∫ u, f (cellFaceMap i (C.lower i) u) ∂(C.delete i).measure
  rw [← integral_sub (Cell.integrable_measure hup) (Cell.integrable_measure hlo),
    integral_cell_insertNth C i _ (Cell.integrable_measure hdc)]
  change (∫ u in (C.delete i).carrier, ∫ t in Icc (C.lower i) (C.upper i),
    simplexCoordinateDerivative f i (cellFaceMap i t u)) =
      ∫ u in (C.delete i).carrier,
        f (cellFaceMap i (C.upper i) u) - f (cellFaceMap i (C.lower i) u)
  apply setIntegral_congr_fun (C.delete i).isClosed_carrier.measurableSet
  intro u hu
  have hline : MapsTo (fun t => cellFaceMap i t u) (Icc (C.lower i) (C.upper i)) C.carrier :=
    fun _ ht => C.insertNth_mem i hu ht
  have hc : ContinuousOn (fun t => simplexCoordinateDerivative f i (cellFaceMap i t u))
      (Icc (C.lower i) (C.upper i)) :=
    hdc.comp (Continuous.finInsertNth (A := fun _ : Fin (d + 1) => ℝ) i
      (f := fun t : ℝ => t) (g := fun _ : ℝ => u) continuous_id continuous_const).continuousOn hline
  have hint : IntervalIntegrable (fun t => simplexCoordinateDerivative f i (cellFaceMap i t u))
      volume (C.lower i) (C.upper i) :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le (C.lower_le_upper i)] using hc)
  dsimp only
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (C.lower_le_upper i)]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => f (cellFaceMap i t u)) _ hint
  intro t ht
  have hts := hline (by simpa only [uIcc_of_le (C.lower_le_upper i)] using ht)
  have hfd := hf.differentiableOn_one.differentiableAt (hU.mem_nhds (hCU hts))
  simpa only [simplexCoordinateDerivative, cellFaceMap] using!
    hfd.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_insertNth i u t)

end Rudin.PMA.Chapter10
