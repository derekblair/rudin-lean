import Rudin.PMA.Chapter10.AreaElements
import Rudin.PMA.Chapter10.CellTriangulation
import Rudin.PMA.Chapter10.VolumeElements

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def torusCell (a : ℝ) (ha : 0 < a) : Cell 3 where
  lower := 0
  upper := ![a, 2 * Real.pi, 2 * Real.pi]
  lower_le_upper := by intro i; fin_cases i <;> simp <;> positivity

def torusOuterCell : Cell 2 where
  lower := 0
  upper := fun _ => 2 * Real.pi
  lower_le_upper := by intro i; dsimp; positivity

/-- Source parameter order is (radius t, meridian angle u, azimuth v). -/
def torusMap (b : ℝ) (u : Coord 3) : Euclidean 3 :=
  coordEquivEuclidean 3
    ![u 0 * Real.cos (u 1), (b + u 0 * Real.sin (u 1)) * Real.cos (u 2),
      (b + u 0 * Real.sin (u 1)) * Real.sin (u 2)]

def torusOuterMap (a b : ℝ) (u : Coord 2) : Euclidean 3 := torusMap b ![a, u 0, u 1]

def solidTorus (a b : ℝ) : Set (Euclidean 3) :=
  {x | x 0 ^ 2 + (Real.sqrt (x 1 ^ 2 + x 2 ^ 2) - b) ^ 2 ≤ a ^ 2}

def torusUnitNormal (u : Coord 2) : Euclidean 3 :=
  coordEquivEuclidean 3
    ![Real.cos (u 0), Real.sin (u 0) * Real.cos (u 1), Real.sin (u 0) * Real.sin (u 1)]

def torusJacobian (b : ℝ) (u : Coord 3) : ℝ :=
  Matrix.det (fun i j : Fin 3 => fderiv ℝ (torusMap b) u (Pi.single j 1) i)

lemma torusMap_contDiff (b : ℝ) (r : WithTop ENat) : ContDiff ℝ r (torusMap b) := by
  apply (coordEquivEuclidean 3).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  have hc (j : Fin 3) : ContDiff ℝ r (fun u : Coord 3 => u j) := contDiff_apply ℝ ℝ j
  fin_cases i
  · exact (hc 0).mul (hc 1).cos
  · exact (contDiff_const.add ((hc 0).mul (hc 1).sin)).mul (hc 2).cos
  · exact (contDiff_const.add ((hc 0).mul (hc 1).sin)).mul (hc 2).sin

lemma torusOuterMap_contDiff (a b : ℝ) (r : WithTop ENat) : ContDiff ℝ r (torusOuterMap a b) := by
  apply (torusMap_contDiff b r).comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ 0
  · exact contDiff_apply ℝ ℝ 1

def torusSolidSurface (a b : ℝ) (ha : 0 < a) : Surface 3 3 univ where
  domain := .cell (torusCell a ha)
  map := torusMap b
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (torusMap_contDiff b 1).contDiffOn
  mapsTo := mapsTo_univ _ _

def torusOuterSurface (a b : ℝ) : Surface 2 3 univ where
  domain := .cell torusOuterCell
  map := torusOuterMap a b
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (torusOuterMap_contDiff a b 1).contDiffOn
  mapsTo := mapsTo_univ _ _

/-- Source 10.47 uses the actual solid torus, its native parameter volume, and
its outer surface. Functional boundary agreement tests every continuous two-form.
Outwardness is a local positive displacement in the explicitly identified unit
normal direction, without an unnecessary global-ray claim. -/
def pma10_47_contract : Prop :=
  ∀ (a b : ℝ) (ha : 0 < a), a < b →
    (torusSolidSurface a b ha).IsC2 ∧ (torusOuterSurface a b).IsC2 ∧
    InjOn (torusMap b) (interior (torusCell a ha).carrier) ∧
    torusMap b '' (torusCell a ha).carrier = solidTorus a b ∧
    (∀ u, torusJacobian b u = u 0 * (b + u 0 * Real.sin (u 1))) ∧
    (∀ u ∈ (torusCell a ha).carrier,
      0 ≤ torusJacobian b u ∧ (0 < torusJacobian b u ↔ 0 < u 0)) ∧
    (torusSolidSurface a b ha).domain.Integrable
      (surfaceIntegrand (torusSolidSurface a b ha) volumeForm) ∧
    (∀ u, surfaceIntegrand (torusSolidSurface a b ha) volumeForm u = torusJacobian b u) ∧
    surfaceIntegral (torusSolidSurface a b ha) volumeForm = 2 * Real.pi ^ 2 * a ^ 2 * b ∧
    (volume (solidTorus a b)).toReal = 2 * Real.pi ^ 2 * a ^ 2 * b ∧
    (∃ Γ : SimplexChain 3 3 univ,
      (∀ ω : FormField 3, IsFormOn univ 3 ω →
        chainIntegral ω Γ = surfaceIntegral (torusSolidSurface a b ha) ω) ∧
      (∀ ω : FormField 3, IsFormOn univ 2 ω →
        chainIntegral ω (chainBoundary Γ) = surfaceIntegral (torusOuterSurface a b) ω)) ∧
    (∀ u ∈ torusOuterCell.carrier,
      surfaceNormal (torusOuterSurface a b) u =
        (a * (b + a * Real.sin (u 0))) • torusUnitNormal u ∧
      ‖torusUnitNormal u‖ = 1 ∧ 0 < a * (b + a * Real.sin (u 0)) ∧
      ‖surfaceNormal (torusOuterSurface a b) u‖ = a * (b + a * Real.sin (u 0)) ∧
      ∀ s ∈ Ioo 0 (b - a), torusOuterMap a b u + s • torusUnitNormal u ∉ solidTorus a b) ∧
    (torusOuterSurface a b).domain.Integrable (fun u => ‖surfaceNormal (torusOuterSurface a b) u‖) ∧
    surfaceArea (torusOuterSurface a b) = 4 * Real.pi ^ 2 * a * b ∧
    (∀ x ∈ solidTorus a b, x 2 ≤ b + a) ∧
    torusOuterMap a b ![Real.pi / 2, Real.pi / 2] = (b + a) • coordinateVector 3 2 ∧
    surfaceNormal (torusOuterSurface a b) ![Real.pi / 2, Real.pi / 2] =
      (a * (b + a)) • coordinateVector 3 2

end Rudin.PMA.Chapter10
