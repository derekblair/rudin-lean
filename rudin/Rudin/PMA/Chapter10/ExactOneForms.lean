import Rudin.PMA.Chapter10.ExteriorDerivative

noncomputable section
set_option autoImplicit false
open Set Filter Function MeasureTheory
open scoped BigOperators Topology

namespace Rudin.PMA.Chapter10
open Chapter09 Chapter06

theorem ParameterDomain.one_integral_eq_intervalIntegral {D : ParameterDomain 1}
    {f : Coord 1 → ℝ} (hf : ContinuousOn f D.carrier) :
    D.integral f = ∫ t in D.interval.1..D.interval.2, f (fun _ => t) := by
  cases D with
  | cell C => exact iteratedRIntegral_one_eq_intervalIntegral hf
  | simplex =>
      have hc : ContinuousOn (fun t : ℝ => f (fun _ => t)) (Icc 0 1) := by
        apply hf.comp (continuous_pi fun _ => continuous_id).continuousOn
        intro t ht
        exact (ParameterDomain.one_mem .simplex (fun _ => t)).mpr ht
      have hzero : (0 : Coord 0) ∈ (Cell.unit 0).carrier := by
        rw [Cell.mem_carrier]
        intro i
        exact Fin.elim0 i
      have hi := (simplex_iteratedRIntegrable hf).1 (0 : Coord 0) hzero
      have he : EqOn (fun t : ℝ => simplexExtension f (fun _ : Fin 1 => t))
          (fun t => f (fun _ => t)) (Icc 0 1) := by
        intro t ht
        exact Set.indicator_of_mem ((ParameterDomain.one_mem .simplex (fun _ => t)).mpr ht) f
      change iteratedRIntegral (Cell.unit 1) (simplexExtension f) = _
      rw [iteratedRIntegral_one]
      change RIntegral (fun t => simplexExtension f (fun _ : Fin 1 => t)) 0 1 = _
      rw [rIntegral_congr_of_integrable (by simpa only [Cell.unit, Cell.init, Fin.snoc_zero, Pi.zero_apply, Pi.one_apply] using hi)
        (pma6_8 _ id 0 1 zero_le_one hc (monotone_id.monotoneOn _)) he]
      exact rIntegral_eq_intervalIntegral_of_continuousOn zero_le_one hc

theorem isFormOn_scalarDifferential {n : ℕ} {E : Set (Euclidean n)} {f : Euclidean n → ℝ}
    (hE : IsOpen E) (hf : ContDiffOn ℝ 1 f E) : IsFormOn E 1 (scalarDifferential f) := by
  rw [← exteriorDerivative_scalarForm]
  exact (isCFormOn_exteriorDerivative (r := 0) hE (isCFormOn_scalarForm hf)).isFormOn

theorem surface_scalar_comp_hasDerivAt {n : ℕ} {E : Set (Euclidean n)} {f : Euclidean n → ℝ}
    (hE : IsOpen E) (hf : ContDiffOn ℝ 1 f E) (Φ : Surface 1 n E) {t : ℝ}
    (ht : (fun _ : Fin 1 => t) ∈ Φ.domain.carrier) :
    HasDerivAt (fun s => f (Φ.map (fun _ : Fin 1 => s)))
      (surfaceIntegrand Φ (scalarDifferential f) (fun _ => t)) t := by
  have hdΦ := (Φ.regularity.differentiableOn_one).differentiableAt
    (Φ.open_neighborhood.mem_nhds (Φ.domain_subset ht))
  have hdf := hf.differentiableOn_one.differentiableAt (hE.mem_nhds (Φ.mapsTo ht))
  let L : ℝ →L[ℝ] Coord 1 := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ ℝ)
  have hh := (hdf.hasFDerivAt.comp (fun _ : Fin 1 => t) hdΦ.hasFDerivAt).comp t L.hasFDerivAt
  have hone : L 1 = Pi.single (0 : Fin 1) 1 := by ext j; fin_cases j; rfl
  rw [surfaceIntegrand, evaluateForm_scalarDifferential hdf]
  simpa! only [Function.comp_def, ContinuousLinearMap.comp_apply, hone, L,
    ContinuousLinearMap.coe_pi', ContinuousLinearMap.id_apply] using! hh.hasDerivAt

theorem scalarDifferential_surface_endpoints {n : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → ℝ} (hE : IsOpen E) (hf : ContDiffOn ℝ 1 f E) (Φ : Surface 1 n E) :
    Φ.domain.Integrable (surfaceIntegrand Φ (scalarDifferential f)) ∧
      surfaceIntegral Φ (scalarDifferential f) =
        f (Φ.map (fun _ => Φ.domain.interval.2)) - f (Φ.map (fun _ => Φ.domain.interval.1)) := by
  have hc := Φ.continuousOn_integrand (isFormOn_scalarDifferential hE hf)
  refine ⟨ParameterDomain.integrable_of_continuousOn hc, ?_⟩
  rw [surfaceIntegral, ParameterDomain.one_integral_eq_intervalIntegral hc]
  have hline : ContinuousOn (fun t : ℝ => surfaceIntegrand Φ (scalarDifferential f) (fun _ => t))
      (Icc Φ.domain.interval.1 Φ.domain.interval.2) :=
    hc.comp (continuous_pi fun _ => continuous_id).continuousOn
      (fun t ht => (Φ.domain.one_mem (fun _ => t)).mpr ht)
  have hi : IntervalIntegrable
      (fun t : ℝ => surfaceIntegrand Φ (scalarDifferential f) (fun _ => t)) volume
      Φ.domain.interval.1 Φ.domain.interval.2 :=
    ContinuousOn.intervalIntegrable (by simpa only [uIcc_of_le Φ.domain.interval_order] using hline)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => f (Φ.map (fun _ : Fin 1 => t))) _ hi
  intro t ht
  apply surface_scalar_comp_hasDerivAt hE hf Φ
  exact (Φ.domain.one_mem (fun _ => t)).mpr (by
    simpa only [uIcc_of_le Φ.domain.interval_order] using ht)

theorem scalarDifferential_closed_surface {n : ℕ} {E : Set (Euclidean n)}
    {f : Euclidean n → ℝ} (hE : IsOpen E) (hf : ContDiffOn ℝ 1 f E) (Φ : Surface 1 n E)
    (hclosed : Φ.map (fun _ => Φ.domain.interval.1) = Φ.map (fun _ => Φ.domain.interval.2)) :
    surfaceIntegral Φ (scalarDifferential f) = 0 := by
  rw [(scalarDifferential_surface_endpoints hE hf Φ).2, hclosed, sub_self]

theorem xdy_not_exact : ¬ ∃ f : Euclidean 2 → ℝ, ContDiff ℝ 1 f ∧
    EqOn (scalarDifferential f) (coordinateOneForm 0 1) univ := by
  rintro ⟨f, hf, he⟩
  have hclosed : (ellipseSurface 1 1).map (fun _ => (ellipseSurface 1 1).domain.interval.1) =
      (ellipseSurface 1 1).map (fun _ => (ellipseSurface 1 1).domain.interval.2) := by
    simpa only [ellipseSurface, ParameterDomain.interval, ellipseCell, Pi.zero_apply] using!
      ellipseSurface_closed 1 1
  have hz := scalarDifferential_closed_surface isOpen_univ hf.contDiffOn (ellipseSurface 1 1) hclosed
  have heq := FormEqOn.of_eqOn (isFormOn_scalarDifferential isOpen_univ hf.contDiffOn)
    (isFormOn_coordinateOneForm univ 0 1) he (ellipseSurface 1 1)
  have hπ := (ellipse_integrals 1 1).2.2.1
  rw [heq, hπ] at hz
  exact Real.pi_ne_zero (by simpa only [mul_one] using hz)

theorem pma10_19 : pma10_19_contract := by
  refine ⟨fun _ _ _ hE hf Φ => scalarDifferential_surface_endpoints hE hf Φ, ?_,
    fun _ _ _ hE hf Φ hc => scalarDifferential_closed_surface hE hf Φ hc, xdy_not_exact⟩
  intro n E f hE hf Φ Ψ ha hb
  rw [(scalarDifferential_surface_endpoints hE hf Φ).2,
    (scalarDifferential_surface_endpoints hE hf Ψ).2, ha, hb]

end Rudin.PMA.Chapter10
