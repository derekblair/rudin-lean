import Rudin.PMA.Chapter10.Simplex

set_option autoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace Rudin.PMA.Chapter10.FidelityProbes

/-- The zero extension retains its boundary value and has a jump immediately
beyond the boundary, yet all the iterated Riemann integrals exist. -/
theorem simplex_extension_boundary_jump :
    simplexExtension (fun _ : Coord 2 => 7) (Fin.snoc (1 : Coord 1) 0) = 7 ∧
      (∀ t : ℝ, 0 < t →
        simplexExtension (fun _ : Coord 2 => 7) (Fin.snoc (1 : Coord 1) t) = 0) ∧
      IteratedRIntegrable (Cell.unit 2) (simplexExtension (fun _ : Coord 2 => 7)) := by
  have hmem : Fin.snoc (1 : Coord 1) 0 ∈ standardSimplex 2 := by
    rw [mem_standardSimplex_snoc]
    norm_num
  refine ⟨?_, ?_, (pma10_4.1 2 (fun _ => 7) continuousOn_const).1⟩
  · simp only [simplexExtension, indicator_of_mem hmem]
  · intro t ht
    have hnot : Fin.snoc (1 : Coord 1) t ∉ standardSimplex 2 := by
      intro h
      have hs : 1 + t ≤ 1 := by
        simpa using (mem_standardSimplex_snoc.mp h).2.2
      linarith
    exact indicator_of_notMem hnot _

/-- At the boundary where a simplex fiber collapses to its endpoint, its
nonzero endpoint value contributes zero to the existing native integral. -/
theorem collapsed_simplex_fiber_integral :
    Chapter06.RIntegrable
      (fun t => simplexExtension (fun _ : Coord 2 => 7) (Fin.snoc (1 : Coord 1) t)) 0 1 ∧
    Chapter06.RIntegral
      (fun t => simplexExtension (fun _ : Coord 2 => 7) (Fin.snoc (1 : Coord 1) t)) 0 1 = 0 := by
  have hx : (1 : Coord 1) ∈ (Cell.unit 1).carrier := by
    rw [Cell.mem_carrier]
    intro i
    norm_num [Cell.unit]
  have h := simplex_slice_integrable_formula
    (f := fun _ : Coord 2 => 7) (g := fun _ : Coord 2 => 7)
    continuous_const (fun _ _ => rfl) hx
  refine ⟨h.1, ?_⟩
  simpa [nativeSliceIntegral, Cell.unit, simplexSliceFormula] using h.2

end Rudin.PMA.Chapter10.FidelityProbes
