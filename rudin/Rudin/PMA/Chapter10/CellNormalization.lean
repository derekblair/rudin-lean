import Rudin.PMA.Chapter10.SquareBoundaries
import Rudin.PMA.Chapter10.ExactOneForms
import Rudin.PMA.Chapter10.SimplexChains

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The coordinatewise affine map from the unit cell to an arbitrary cell. -/
def cellNormalize {k : ℕ} (C : Cell k) (u : Coord k) : Coord k :=
  fun i => C.lower i + (C.upper i - C.lower i) * u i

lemma cellNormalize_contDiff {k : ℕ} (C : Cell k) (r : WithTop ENat) :
    ContDiff ℝ r (cellNormalize C) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_const.add (contDiff_const.mul (contDiff_apply ℝ ℝ i))

lemma cellNormalize_mapsTo {k : ℕ} (C : Cell k) :
    MapsTo (cellNormalize C) (Cell.unit k).carrier C.carrier := by
  intro u hu
  rw [Cell.mem_carrier] at hu ⊢
  intro i
  have hi : 0 ≤ u i ∧ u i ≤ 1 := hu i
  have hw : 0 ≤ C.upper i - C.lower i := sub_nonneg.mpr (C.lower_le_upper i)
  change C.lower i ≤ C.lower i + (C.upper i - C.lower i) * u i ∧
    C.lower i + (C.upper i - C.lower i) * u i ≤ C.upper i
  constructor <;> nlinarith

def cellNormalizeLinear {k : ℕ} (C : Cell k) : Coord k →L[ℝ] Coord k :=
  ContinuousLinearMap.pi (fun i => (C.upper i - C.lower i) • ContinuousLinearMap.proj i)

lemma cellNormalize_hasFDerivAt {k : ℕ} (C : Cell k) (u : Coord k) :
    HasFDerivAt (cellNormalize C) (cellNormalizeLinear C) u := by
  convert (cellNormalizeLinear C).hasFDerivAt.const_add C.lower using 1
  funext v
  ext i
  rfl

lemma cellNormalize_det {k : ℕ} (C : Cell k) (u : Coord k) :
    LinearMap.det (fderiv ℝ (cellNormalize C) u).toLinearMap =
      ∏ i, (C.upper i - C.lower i) := by
  rw [(cellNormalize_hasFDerivAt C u).fderiv, ← LinearMap.det_toMatrix']
  have he : LinearMap.toMatrix' (cellNormalizeLinear C).toLinearMap =
      Matrix.diagonal (fun i => C.upper i - C.lower i) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, cellNormalizeLinear, Matrix.diagonal_apply,
      Pi.single_apply, eq_comm]
  rw [he, Matrix.det_diagonal]

def Surface.normalizeCell {k n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (C : Cell k) (hD : Φ.domain = .cell C) : Surface k n E :=
  Φ.precompose (.cell (Cell.unit k)) (cellNormalize C) (cellNormalize_contDiff C 1)
    (by rw [hD]; exact cellNormalize_mapsTo C)

lemma surfaceIntegral_normalizeInterval {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 1 n E) (C : Cell 1) (hD : Φ.domain = .cell C)
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral (Φ.normalizeCell C hD) ω = surfaceIntegral Φ ω := by
  have hc := Φ.continuousOn_integrand hω
  have hn := (Φ.normalizeCell C hD).continuousOn_integrand hω
  rw [hD] at hc
  change iteratedRIntegral (Cell.unit 1) _ = Φ.domain.integral _
  rw [hD]
  change iteratedRIntegral (Cell.unit 1) _ = iteratedRIntegral C _
  rw [iteratedRIntegral_one_eq_intervalIntegral hn, iteratedRIntegral_one_eq_intervalIntegral hc]
  calc
    _ = ∫ t in (0 : ℝ)..1, (C.upper 0 - C.lower 0) *
        surfaceIntegrand Φ ω (fun _ => C.lower 0 + (C.upper 0 - C.lower 0) * t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : (fun _ : Fin 1 => t) ∈ (Cell.unit 1).carrier := by
        have h : t ∈ Icc (0 : ℝ) 1 := by simpa [Cell.unit, uIcc_of_le zero_le_one] using ht
        exact ⟨fun _ => h.1, fun _ => h.2⟩
      have he := surfaceIntegrand_precompose Φ (.cell (Cell.unit 1)) (cellNormalize C)
        (cellNormalize_contDiff C 1) (by rw [hD]; exact cellNormalize_mapsTo C) hω ht'
      have hv : cellNormalize C (fun _ => t) =
          (fun _ => C.lower 0 + (C.upper 0 - C.lower 0) * t) := by
        funext i
        fin_cases i
        rfl
      simpa only [Surface.normalizeCell, cellNormalize_det, Fin.prod_univ_one, hv] using he
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      simpa only [smul_eq_mul, mul_zero, add_zero, mul_one, add_sub_cancel] using
        (intervalIntegral.smul_integral_comp_add_mul
          (fun t => surfaceIntegrand Φ ω (fun _ => t)) (a := (0 : ℝ)) (b := 1)
          (C.upper 0 - C.lower 0) (C.lower 0))

/-- Turn a C² parametrized interval into its actual normalized one-simplex. -/
def Surface.intervalSimplex {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 1 n E)
    (C : Cell 1) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2) : C2Simplex 1 n E where
  map := Φ.map ∘ cellNormalize C
  regularity := by
    obtain ⟨U, hU, hDU, hΦ⟩ := h₂
    refine ⟨cellNormalize C ⁻¹' U, hU.preimage (cellNormalize_contDiff C 2).continuous, ?_,
      hΦ.comp (cellNormalize_contDiff C 2).contDiffOn (fun _ hu => hu)⟩
    intro u hu
    apply hDU
    rw [hD]
    exact cellNormalize_mapsTo C (standardSimplex_subset_unit 1 hu)
  mapsTo := by
    intro u hu
    apply Φ.mapsTo
    rw [hD]
    exact cellNormalize_mapsTo C (standardSimplex_subset_unit 1 hu)

lemma surfaceIntegral_intervalSimplex {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 1 n E) (C : Cell 1) (hD : Φ.domain = .cell C) (h₂ : Φ.IsC2)
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral (Φ.intervalSimplex C hD h₂).toSurface ω = surfaceIntegral Φ ω := by
  calc
    _ = surfaceIntegral (Φ.normalizeCell C hD) ω := by
      unfold surfaceIntegral
      rw [ParameterDomain.one_integral_eq_intervalIntegral
        ((Φ.intervalSimplex C hD h₂).toSurface.continuousOn_integrand hω),
        ParameterDomain.one_integral_eq_intervalIntegral
        ((Φ.normalizeCell C hD).continuousOn_integrand hω)]
      rfl
    _ = _ := surfaceIntegral_normalizeInterval Φ C hD hω

end Rudin.PMA.Chapter10
