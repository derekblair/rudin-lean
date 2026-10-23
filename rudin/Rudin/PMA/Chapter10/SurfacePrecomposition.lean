import Rudin.PMA.Chapter10.SimplexOrientation
import Rudin.PMA.Chapter10.SurfacePullbacks

noncomputable section
set_option autoImplicit false
open Set Function Module MeasureTheory
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- Restrict and reparametrize a genuine C¹ surface. No C² extension is needed. -/
def Surface.precompose {k l n : ℕ} {E : Set (Euclidean n)} (Φ : Surface k n E)
    (D : ParameterDomain l) (A : Coord l → Coord k) (hA : ContDiff ℝ 1 A)
    (hAD : MapsTo A D.carrier Φ.domain.carrier) : Surface l n E where
  domain := D
  map := Φ.map ∘ A
  neighborhood := A ⁻¹' Φ.neighborhood
  open_neighborhood := Φ.open_neighborhood.preimage hA.continuous
  domain_subset := fun _ hu => Φ.domain_subset (hAD hu)
  regularity := Φ.regularity.comp hA.contDiffOn (fun _ hu => hu)
  mapsTo := Φ.mapsTo.comp hAD

lemma surfaceIntegrand_precompose {k n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface k n E) (D : ParameterDomain k) (A : Coord k → Coord k)
    (hA : ContDiff ℝ 1 A) (hAD : MapsTo A D.carrier Φ.domain.carrier)
    {ω : FormField n} (hω : IsFormOn E k ω) :
    EqOn (surfaceIntegrand (Φ.precompose D A hA hAD) ω)
      (fun u => LinearMap.det (fderiv ℝ A u).toLinearMap * surfaceIntegrand Φ ω (A u))
      D.carrier := by
  intro u hu
  change evaluateForm k (fun j => fderiv ℝ (Φ.map ∘ A) u (Pi.single j 1))
    (ω (Φ.map (A u))) = _
  rw [fderiv_comp u (Φ.differentiableAt (hAD hu))
    (hA.differentiable (by norm_num)).differentiableAt]
  exact evaluateForm_precompose _ _ (hω.1 _ (Φ.mapsTo (hAD hu)))

lemma surfaceIntegral_congr_map {k n : ℕ} {E : Set (Euclidean n)}
    {Φ Ψ : Surface k n E} (hD : Φ.domain = Ψ.domain) (hmap : Φ.map = Ψ.map)
    (ω : FormField n) : surfaceIntegral Φ ω = surfaceIntegral Ψ ω := by
  unfold surfaceIntegral
  rw [hD]
  congr 1
  funext u
  unfold surfaceIntegrand
  rw [hmap]

def intervalReverse (C : Cell 1) (u : Coord 1) : Coord 1 := C.lower + C.upper - u

lemma intervalReverse_contDiff (C : Cell 1) : ContDiff ℝ 1 (intervalReverse C) :=
  contDiff_const.sub contDiff_id

lemma intervalReverse_mapsTo (C : Cell 1) : MapsTo (intervalReverse C) C.carrier C.carrier := by
  intro u hu
  rw [Cell.mem_carrier] at hu ⊢
  intro i
  have h := hu i
  change C.lower i ≤ C.lower i + C.upper i - u i ∧
    C.lower i + C.upper i - u i ≤ C.upper i
  constructor <;> linarith

def Surface.reverse {n : ℕ} {E : Set (Euclidean n)} (Φ : Surface 1 n E)
    (C : Cell 1) (hD : Φ.domain = .cell C) : Surface 1 n E :=
  Φ.precompose (.cell C) (intervalReverse C) (intervalReverse_contDiff C)
    (by rw [hD]; exact intervalReverse_mapsTo C)

lemma intervalReverse_det (C : Cell 1) (u : Coord 1) :
    LinearMap.det (fderiv ℝ (intervalReverse C) u).toLinearMap = -1 := by
  have hd : HasFDerivAt (intervalReverse C) (-ContinuousLinearMap.id ℝ (Coord 1)) u :=
    (hasFDerivAt_id u).const_sub (C.lower + C.upper)
  rw [hd.fderiv, ← LinearMap.det_toMatrix']
  rw [Matrix.det_fin_one]
  simp [LinearMap.toMatrix'_apply]

lemma surfaceIntegral_reverse {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 1 n E) (C : Cell 1) (hD : Φ.domain = .cell C)
    {ω : FormField n} (hω : IsFormOn E 1 ω) :
    surfaceIntegral (Φ.reverse C hD) ω = -surfaceIntegral Φ ω := by
  have hc := Φ.continuousOn_integrand hω
  have hr := (Φ.reverse C hD).continuousOn_integrand hω
  rw [hD] at hc
  change iteratedRIntegral C _ = -Φ.domain.integral _
  rw [hD]
  change iteratedRIntegral C _ = -iteratedRIntegral C _
  rw [iteratedRIntegral_one_eq_intervalIntegral hr,
    iteratedRIntegral_one_eq_intervalIntegral hc]
  calc
    _ = ∫ t in C.lower 0..C.upper 0,
        -surfaceIntegrand Φ ω (fun _ => C.lower 0 + C.upper 0 - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : (fun _ : Fin 1 => t) ∈ C.carrier := by
        rw [Cell.mem_carrier]
        intro i
        fin_cases i
        simpa [uIcc_of_le (C.lower_le_upper 0)] using ht
      have he := surfaceIntegrand_precompose Φ (.cell C) (intervalReverse C)
        (intervalReverse_contDiff C) (by rw [hD]; exact intervalReverse_mapsTo C) hω ht'
      have hv : intervalReverse C (fun _ => t) =
          (fun _ => C.lower 0 + C.upper 0 - t) := by
        funext i
        fin_cases i
        rfl
      simpa only [Surface.reverse, intervalReverse_det, hv, neg_one_mul] using he
    _ = _ := by
      rw [intervalIntegral.integral_neg]
      congr 1
      simpa using intervalIntegral.integral_comp_sub_left
        (fun t => surfaceIntegrand Φ ω (fun _ => t)) (a := C.lower 0) (b := C.upper 0)
        (C.lower 0 + C.upper 0)

lemma evaluateForm_one_zero {n : ℕ} {a : CotangentExterior n}
    (ha : a ∈ (⋀[ℝ]^1 (Coord n))) : evaluateForm 1 (fun _ => 0) a = 0 := by
  rw [standard_expansion a ha]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro S hS
  suffices hz : evaluateForm 1 (fun _ => (0 : Euclidean n)) (standardWedge S) = 0 by
    rw [hz, mul_zero]
  rw [standardWedge_eq_coordinateWedge, evaluateForm_coordinateWedge]
  change Matrix.det (0 : Matrix (Fin 1) (Fin 1) ℝ) = 0
  simp

lemma surfaceIntegral_constant_map {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 1 n E) {p : Euclidean n} (hp : Φ.map = fun _ => p)
    {ω : FormField n} (hω : IsFormOn E 1 ω) : surfaceIntegral Φ ω = 0 := by
  have hc := Φ.continuousOn_integrand hω
  rw [surfaceIntegral, ParameterDomain.integral_eq_setIntegral hc]
  have he : EqOn (surfaceIntegrand Φ ω) (fun _ => 0) Φ.domain.carrier := by
    intro u hu
    change evaluateForm 1 (fun j => fderiv ℝ Φ.map u (Pi.single j 1)) (ω (Φ.map u)) = 0
    rw [hp]
    rw [fderiv_const_apply]
    apply evaluateForm_one_zero
    simpa only [hp] using hω.1 _ (Φ.mapsTo hu)
  rw [setIntegral_congr_fun Φ.domain.isClosed.measurableSet he]
  simp

end Rudin.PMA.Chapter10
