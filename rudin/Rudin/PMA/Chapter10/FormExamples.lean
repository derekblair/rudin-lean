import Rudin.PMA.Chapter10.FormsAlgebra
import Rudin.PMA.Chapter10.FormRegularity
import Rudin.PMA.Chapter10.IntegrationMeasure

set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The coordinate one-form `xᵢ dxⱼ`. -/
def coordinateOneForm {n : ℕ} (i j : Fin n) : FormField n := fun x => x i • dx j

def xyDifferential : FormField 3 := coordinateOneForm 0 1 + coordinateOneForm 1 0

def ellipseCell : Cell 1 where
  lower := 0
  upper := fun _ => 2 * Real.pi
  lower_le_upper := fun _ => by positivity

def ellipseMap (a b : ℝ) (u : Coord 1) : Euclidean 2 :=
  coordEquivEuclidean 2 ![a * Real.cos (u 0), b * Real.sin (u 0)]

def sphericalCell : Cell 3 where
  lower := 0
  upper := ![1, Real.pi, 2 * Real.pi]
  lower_le_upper := by intro i; fin_cases i <;> simp <;> positivity

def sphericalMap (u : Coord 3) : Euclidean 3 :=
  coordEquivEuclidean 3 ![u 0 * Real.sin (u 1) * Real.cos (u 2),
    u 0 * Real.sin (u 1) * Real.sin (u 2), u 0 * Real.cos (u 1)]

def volumeForm : FormField 3 := fun _ => coordinateWedge (id : Fin 3 → Fin 3)

def sphericalJacobian (u : Coord 3) : ℝ :=
  Matrix.det (fun i j : Fin 3 => fderiv ℝ sphericalMap u (Pi.single j 1) i)

/-- The three worked examples use the native surface integral, with its
iterated Riemann integrability witnessed explicitly. Surfaces remain maps,
so the spherical parametrization may identify boundary points. The geometric
area/volume interpretation of positive volume elements is developed further
at 10.44–10.45; the native numerical integrals are stated here. -/
def pma10_12_contract : Prop :=
  (∀ Φ : Surface 1 3 univ, Φ.domain = .cell (Cell.unit 1) →
    IteratedRIntegrable (Cell.unit 1) (surfaceIntegrand Φ xyDifferential) ∧
    surfaceIntegral Φ xyDifferential =
      Φ.map 1 0 * Φ.map 1 1 - Φ.map 0 0 * Φ.map 0 1 ∧
    (Φ.map 0 = Φ.map 1 → surfaceIntegral Φ xyDifferential = 0)) ∧
  (∀ a b : ℝ, 0 < a → 0 < b → ∃ Φ : Surface 1 2 univ,
    Φ.domain = .cell ellipseCell ∧ Φ.map = ellipseMap a b ∧
    Φ.map 0 = Φ.map (fun _ => 2 * Real.pi) ∧
    IteratedRIntegrable ellipseCell (surfaceIntegrand Φ (coordinateOneForm 0 1)) ∧
    IteratedRIntegrable ellipseCell (surfaceIntegrand Φ (coordinateOneForm 1 0)) ∧
    surfaceIntegral Φ (coordinateOneForm 0 1) = Real.pi * a * b ∧
    surfaceIntegral Φ (coordinateOneForm 1 0) = -(Real.pi * a * b)) ∧
  (∃ Φ : Surface 3 3 univ,
    Φ.domain = .cell sphericalCell ∧ Φ.map = sphericalMap ∧
    (∀ u, sphericalJacobian u = (u 0)^2 * Real.sin (u 1)) ∧
    IteratedRIntegrable sphericalCell (surfaceIntegrand Φ volumeForm) ∧
    surfaceIntegral Φ volumeForm = 4 * Real.pi / 3 ∧
    sphericalMap '' sphericalCell.carrier = Metric.closedBall 0 1 ∧
    InjOn sphericalMap (interior sphericalCell.carrier))

theorem dx_eq_coordinateWedge {n : ℕ} (j : Fin n) :
    dx j = coordinateWedge (fun _ : Fin 1 => j) := by
  simp [coordinateWedge, dx, ExteriorAlgebra.ιMulti_succ_apply]

theorem evaluateForm_dx {n : ℕ} (v : Fin 1 → Euclidean n) (j : Fin n) :
    evaluateForm 1 v (dx j) = v 0 j := by
  rw [dx_eq_coordinateWedge, evaluateForm_coordinateWedge]
  exact Matrix.det_fin_one _

theorem surfaceIntegrand_coordinateOneForm {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 1 n E) (i j : Fin n) (u : Coord 1) :
    surfaceIntegrand Φ (coordinateOneForm i j) u =
      Φ.map u i * (fderiv ℝ Φ.map u (Pi.single 0 1)) j := by
  simp only [surfaceIntegrand, coordinateOneForm, map_smul, smul_eq_mul, evaluateForm_dx]

theorem isFormOn_coordinateOneForm {n : ℕ} (E : Set (Euclidean n)) (i j : Fin n) :
    IsFormOn E 1 (coordinateOneForm i j) := by
  constructor
  · intro x hx
    apply Submodule.smul_mem
    rw [dx_eq_coordinateWedge]
    exact coordinateWedge_mem _
  · intro S
    change ContinuousOn (fun x : Euclidean n =>
      (exteriorBasis n).repr (x i • dx j) S) E
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).continuous.continuousOn.mul
      continuousOn_const

theorem isFormOn_xyDifferential : IsFormOn (univ : Set (Euclidean 3)) 1 xyDifferential := by
  have h₁ := isFormOn_coordinateOneForm (univ : Set (Euclidean 3)) 0 1
  have h₂ := isFormOn_coordinateOneForm (univ : Set (Euclidean 3)) 1 0
  refine ⟨fun x hx => Submodule.add_mem _ (h₁.1 x hx) (h₂.1 x hx), ?_⟩
  intro S
  change ContinuousOn (fun x => (exteriorBasis 3).repr
    (coordinateOneForm 0 1 x + coordinateOneForm 1 0 x) S) univ
  simp only [map_add, Finsupp.add_apply]
  exact (h₁.2 S).add (h₂.2 S)

theorem iteratedRIntegral_one (C : Cell 1) (f : Coord 1 → ℝ) :
    iteratedRIntegral C f = Chapter06.RIntegral (fun t => f (fun _ => t))
      (C.lower 0) (C.upper 0) := by
  change Chapter06.RIntegral (fun t => f (Fin.snoc (0 : Coord 0) t))
    (C.lower 0) (C.upper 0) = _
  congr 1

theorem iteratedRIntegral_one_eq_intervalIntegral {C : Cell 1} {f : Coord 1 → ℝ}
    (hf : ContinuousOn f C.carrier) :
    iteratedRIntegral C f = ∫ t in C.lower 0..C.upper 0, f (fun _ => t) := by
  rw [iteratedRIntegral_one]
  apply rIntegral_eq_intervalIntegral_of_continuousOn (C.lower_le_upper 0)
  apply hf.comp (continuous_pi fun _ => continuous_id).continuousOn
  intro t ht
  rw [Cell.mem_carrier]
  intro i
  fin_cases i
  exact ht

set_option backward.isDefEq.respectTransparency false in
theorem surface_coordinate_hasDerivAt {n : ℕ} {E : Set (Euclidean n)}
    (Φ : Surface 1 n E) {t : ℝ} (ht : (fun _ : Fin 1 => t) ∈ Φ.domain.carrier)
    (i : Fin n) : HasDerivAt (fun s => Φ.map (fun _ : Fin 1 => s) i)
      ((fderiv ℝ Φ.map (fun _ => t) (Pi.single 0 1)) i) t := by
  have hd := (Φ.regularity.differentiableOn (by norm_num)).differentiableAt
    (Φ.open_neighborhood.mem_nhds (Φ.domain_subset ht))
  let L : ℝ →L[ℝ] Coord 1 := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)
  have h := ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).hasFDerivAt.comp
    (fun _ : Fin 1 => t) hd.hasFDerivAt).comp t L.hasFDerivAt
  have hone : L 1 = Pi.single (0 : Fin 1) 1 := by ext j; fin_cases j; rfl
  rw [← hone]
  change HasDerivAt (fun s => Φ.map (L s) i)
    ((fderiv ℝ Φ.map (fun _ => t) (L 1)) i) t
  convert! h.hasDerivAt using 1

theorem surfaceIntegrand_xyDifferential (Φ : Surface 1 3 univ) (u : Coord 1) :
    surfaceIntegrand Φ xyDifferential u =
      Φ.map u 0 * (fderiv ℝ Φ.map u (Pi.single 0 1)) 1 +
      Φ.map u 1 * (fderiv ℝ Φ.map u (Pi.single 0 1)) 0 := by
  simp only [xyDifferential, surfaceIntegrand, Pi.add_apply, map_add,
    coordinateOneForm, map_smul, smul_eq_mul, evaluateForm_dx]

theorem xyDifferential_endpoint (Φ : Surface 1 3 univ)
    (hD : Φ.domain = .cell (Cell.unit 1)) :
    IteratedRIntegrable (Cell.unit 1) (surfaceIntegrand Φ xyDifferential) ∧
    surfaceIntegral Φ xyDifferential =
      Φ.map 1 0 * Φ.map 1 1 - Φ.map 0 0 * Φ.map 0 1 := by
  have hc := Φ.continuousOn_integrand isFormOn_xyDifferential
  rw [hD] at hc
  refine ⟨iteratedRIntegrable_of_continuousOn hc, ?_⟩
  change Φ.domain.integral _ = _
  rw [hD]
  change iteratedRIntegral (Cell.unit 1) _ = _
  rw [iteratedRIntegral_one_eq_intervalIntegral hc]
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, (fun _ : Fin 1 => t) ∈ Φ.domain.carrier := by
    intro t ht
    rw [hD]
    exact ⟨fun _ => ht.1, fun _ => ht.2⟩
  have hi : IntervalIntegrable (fun t => surfaceIntegrand Φ xyDifferential (fun _ => t))
      volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1), Function.comp_def, id_eq] using
      hc.comp (continuous_pi fun _ => continuous_id).continuousOn
        (fun t ht => show (fun _ : Fin 1 => t) ∈ (Cell.unit 1).carrier from
          ⟨fun _ => ht.1, fun _ => ht.2⟩)
  change (∫ t in (0 : ℝ)..1, surfaceIntegrand Φ xyDifferential (fun _ => t)) = _
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => Φ.map (fun _ => t) 0 * Φ.map (fun _ => t) 1) _ hi
  intro t ht
  have ht' : t ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using ht
  have hd := (surface_coordinate_hasDerivAt Φ (hmem t ht') 0).mul
    (surface_coordinate_hasDerivAt Φ (hmem t ht') 1)
  convert hd using 1
  rw [surfaceIntegrand_xyDifferential]
  ring

@[simp] theorem coordEquivEuclidean_apply_coordinate {n : ℕ} (x : Coord n) (i : Fin n) :
    coordEquivEuclidean n x i = x i := rfl

theorem contDiff_ellipseMap (a b : ℝ) : ContDiff ℝ 1 (ellipseMap a b) := by
  apply (coordEquivEuclidean 2).contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp <;> fun_prop

def ellipseSurface (a b : ℝ) : Surface 1 2 univ where
  domain := .cell ellipseCell
  map := ellipseMap a b
  neighborhood := univ
  open_neighborhood := isOpen_univ
  domain_subset := subset_univ _
  regularity := (contDiff_ellipseMap a b).contDiffOn
  mapsTo := mapsTo_univ _ _

theorem ellipseSurface_closed (a b : ℝ) :
    (ellipseSurface a b).map 0 = (ellipseSurface a b).map (fun _ => 2 * Real.pi) := by
  ext i
  fin_cases i <;> simp [ellipseSurface, ellipseMap]

theorem ellipse_coordinate_derivatives (a b t : ℝ) :
    HasDerivAt (fun s => ellipseMap a b (fun _ => s) 0) (-a * Real.sin t) t ∧
    HasDerivAt (fun s => ellipseMap a b (fun _ => s) 1) (b * Real.cos t) t := by
  constructor
  · simpa [ellipseMap, mul_neg] using (Real.hasDerivAt_cos t).const_mul a
  · simpa [ellipseMap] using (Real.hasDerivAt_sin t).const_mul b

theorem ellipse_integrands (a b : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (2 * Real.pi)) :
    surfaceIntegrand (ellipseSurface a b) (coordinateOneForm 0 1) (fun _ => t) =
      (a * b) * Real.cos t ^ 2 ∧
    surfaceIntegrand (ellipseSurface a b) (coordinateOneForm 1 0) (fun _ => t) =
      -(a * b) * Real.sin t ^ 2 := by
  have hmem : (fun _ : Fin 1 => t) ∈ (ellipseSurface a b).domain.carrier :=
    ⟨fun _ => ht.1, fun _ => ht.2⟩
  have h₀ := (surface_coordinate_hasDerivAt (ellipseSurface a b) hmem 0).unique
    (ellipse_coordinate_derivatives a b t).1
  have h₁ := (surface_coordinate_hasDerivAt (ellipseSurface a b) hmem 1).unique
    (ellipse_coordinate_derivatives a b t).2
  change (fderiv ℝ (ellipseMap a b) (fun _ => t) (Pi.single 0 1)) 0 = _ at h₀
  change (fderiv ℝ (ellipseMap a b) (fun _ => t) (Pi.single 0 1)) 1 = _ at h₁
  simp only [surfaceIntegrand_coordinateOneForm, ellipseSurface, h₀, h₁, ellipseMap,
    coordEquivEuclidean_apply_coordinate, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  constructor <;> ring

theorem ellipse_integrals (a b : ℝ) :
    IteratedRIntegrable ellipseCell
      (surfaceIntegrand (ellipseSurface a b) (coordinateOneForm 0 1)) ∧
    IteratedRIntegrable ellipseCell
      (surfaceIntegrand (ellipseSurface a b) (coordinateOneForm 1 0)) ∧
    surfaceIntegral (ellipseSurface a b) (coordinateOneForm 0 1) = Real.pi * a * b ∧
    surfaceIntegral (ellipseSurface a b) (coordinateOneForm 1 0) = -(Real.pi * a * b) := by
  have hc₀ := (ellipseSurface a b).continuousOn_integrand (isFormOn_coordinateOneForm univ 0 1)
  have hc₁ := (ellipseSurface a b).continuousOn_integrand (isFormOn_coordinateOneForm univ 1 0)
  refine ⟨iteratedRIntegrable_of_continuousOn hc₀,
    iteratedRIntegrable_of_continuousOn hc₁, ?_, ?_⟩
  · change iteratedRIntegral ellipseCell _ = _
    rw [iteratedRIntegral_one_eq_intervalIntegral hc₀]
    change (∫ t in (0 : ℝ)..2 * Real.pi,
      surfaceIntegrand (ellipseSurface a b) (coordinateOneForm 0 1) (fun _ => t)) = _
    calc
      _ = ∫ t in (0 : ℝ)..2 * Real.pi, (a * b) * Real.cos t ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (ellipse_integrands a b (by simpa [uIcc_of_le (by positivity : 0 ≤ 2 * Real.pi)] using ht)).1
      _ = Real.pi * a * b := by
        rw [intervalIntegral.integral_const_mul, integral_cos_sq]
        simp
        ring
  · change iteratedRIntegral ellipseCell _ = _
    rw [iteratedRIntegral_one_eq_intervalIntegral hc₁]
    change (∫ t in (0 : ℝ)..2 * Real.pi,
      surfaceIntegrand (ellipseSurface a b) (coordinateOneForm 1 0) (fun _ => t)) = _
    calc
      _ = ∫ t in (0 : ℝ)..2 * Real.pi, -(a * b) * Real.sin t ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (ellipse_integrands a b (by simpa [uIcc_of_le (by positivity : 0 ≤ 2 * Real.pi)] using ht)).2
      _ = -(Real.pi * a * b) := by
        rw [intervalIntegral.integral_const_mul, integral_sin_sq]
        simp
        ring

end Rudin.PMA.Chapter10
