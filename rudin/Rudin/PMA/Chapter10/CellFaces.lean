import Rudin.PMA.Chapter10.CellFTC
import Rudin.PMA.Chapter10.SurfaceChains

noncomputable section
set_option autoImplicit false
open Set Function Module
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

def cellFaceLinear {d : ℕ} (i : Fin (d + 1)) : Coord d →L[ℝ] Coord (d + 1) :=
  ContinuousLinearMap.pi (i.insertNth (α := fun _ : Fin (d + 1) => Coord d →L[ℝ] ℝ) 0
    (fun l => ContinuousLinearMap.proj l))

set_option backward.isDefEq.respectTransparency false in
lemma cellFaceMap_hasFDerivAt {d : ℕ} (i : Fin (d + 1)) (t : ℝ) (u : Coord d) :
    HasFDerivAt (cellFaceMap i t) (cellFaceLinear i) u := by
  apply hasFDerivAt_pi.mpr
  intro j
  refine Fin.succAboveCases i ?_ (fun l => ?_) j
  · simpa only [cellFaceMap, Fin.insertNth_apply_same, cellFaceLinear,
      ContinuousLinearMap.proj_pi, Fin.insertNth_apply_same] using
      (hasFDerivAt_const (x := u) t)
  · have hp : HasFDerivAt (fun v : Coord d => v l)
        (ContinuousLinearMap.proj l : Coord d →L[ℝ] ℝ) u := hasFDerivAt_apply l u
    simpa only [cellFaceMap, Fin.insertNth_apply_succAbove, cellFaceLinear,
      ContinuousLinearMap.proj_pi] using hp

lemma cellFaceLinear_single {d : ℕ} (i : Fin (d + 1)) (j : Fin d) :
    cellFaceLinear i (Pi.single j 1) = Pi.single (i.succAbove j) 1 := by
  ext l
  refine Fin.succAboveCases i ?_ (fun m => ?_) l
  · simp [cellFaceLinear, Pi.single_apply, Fin.succAbove_ne, Fin.ne_succAbove]
  · simp [cellFaceLinear, Pi.single_apply, eq_comm]

/-- A globally C1 map on a cell, used for the literal trigonometric examples. -/
def cellMapSurface {d n : ℕ} (C : Cell d) (F : Coord d → Euclidean n)
    (hF : ContDiff ℝ 1 F) : Surface d n univ where
  domain := .cell C
  map := F
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := hF.contDiffOn
  mapsTo := mapsTo_univ _ _

lemma cellMapSurface_isC2 {d n : ℕ} (C : Cell d) (F : Coord d → Euclidean n)
    (hF : ContDiff ℝ 2 F) : (cellMapSurface C F (hF.of_le (by norm_num))).IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _, hF.contDiffOn⟩

def cellFaceSurface {d n : ℕ} (C : Cell (d + 1)) (F : Coord (d + 1) → Euclidean n)
    (hF : ContDiff ℝ 1 F) (i : Fin (d + 1)) (t : ℝ) : Surface d n univ :=
  cellMapSurface (C.delete i) (F ∘ cellFaceMap i t) (hF.comp (cellFaceMap_contDiff i t 1))

lemma cellFaceSurface_isC2 {d n : ℕ} (C : Cell (d + 1)) (F : Coord (d + 1) → Euclidean n)
    (hF : ContDiff ℝ 2 F) (i : Fin (d + 1)) (t : ℝ) :
    (cellFaceSurface C F (hF.of_le (by norm_num)) i t).IsC2 :=
  ⟨univ, isOpen_univ, subset_univ _, (hF.comp (cellFaceMap_contDiff i t 2)).contDiffOn⟩

def standardCellFace {d : ℕ} (C : Cell (d + 1)) (i : Fin (d + 1)) (t : ℝ) :
    Surface d (d + 1) univ :=
  cellFaceSurface C (coordEquivEuclidean (d + 1)) (coordEquivEuclidean (d + 1)).contDiff i t

lemma standardCellFace_integrand {d : ℕ} (C : Cell (d + 1)) (i : Fin (d + 1))
    (t : ℝ) (ω : FormField (d + 1)) (u : Coord d) :
    surfaceIntegrand (standardCellFace C i t) ω u =
      omittedCoefficient ω i (coordEquivEuclidean (d + 1) (cellFaceMap i t u)) := by
  have hd := (coordEquivEuclidean (d + 1)).hasFDerivAt.comp u (cellFaceMap_hasFDerivAt i t u)
  change evaluateForm d (fun j => fderiv ℝ
    (coordEquivEuclidean (d + 1) ∘ cellFaceMap i t) u (Pi.single j 1)) (ω _) = _
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    cellFaceLinear_single, coordEquivEuclidean_single, omittedCoefficient]
  rfl

lemma cellFaceSurface_pullback_integral {d n : ℕ} (C : Cell (d + 1))
    (F : Coord (d + 1) → Euclidean n) (hF : ContDiff ℝ 1 F)
    (i : Fin (d + 1)) (t : ℝ) {ω : FormField n} (hω : IsFormOn univ d ω) :
    surfaceIntegral (cellFaceSurface C F hF i t) ω =
      surfaceIntegral (standardCellFace C i t)
        (pullbackForm (F ∘ (coordEquivEuclidean (d + 1)).symm) ω) := by
  let T := F ∘ (coordEquivEuclidean (d + 1)).symm
  have hT : ContDiffOn ℝ 1 T univ := (hF.comp (coordEquivEuclidean (d + 1)).symm.contDiff).contDiffOn
  calc
    surfaceIntegral (cellFaceSurface C F hF i t) ω =
        surfaceIntegral ((standardCellFace C i t).mapBy T isOpen_univ hT (mapsTo_univ _ _)) ω := by
      apply surfaceIntegral_congr_map rfl
      funext u
      exact (congrArg F ((coordEquivEuclidean (d + 1)).symm_apply_apply _)).symm
    _ = _ := (pma10_25 (d + 1) n d univ univ T (standardCellFace C i t) ω
      isOpen_univ isOpen_univ hT (mapsTo_univ _ _) hω).2.2.2.2

end Rudin.PMA.Chapter10
