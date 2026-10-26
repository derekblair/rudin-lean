import Rudin.PMA.Chapter10.VectorPotentials

/-!
# Gauge facts for the counterexample attack on PMA 10.43

These lemmas do not prove or disprove the C² vector-potential clause. They
identify its gauge quantifier: the C¹ potentials form a C²-scalar-gradient
orbit, and the desired endpoint asks whether that orbit contains a C² field.
Only C¹ regularity of the gradient follows from a C² scalar gauge function.
-/

noncomputable section
set_option autoImplicit false
open Set Function

namespace Rudin.PMA.Chapter10.GaugeResearch
open Chapter09

lemma coordinatePartial_sub {n : ℕ} {f g : Euclidean n → ℝ} {x : Euclidean n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin n) :
    coordinatePartial (fun y => f y - g y) x i =
      coordinatePartial f x i - coordinatePartial g x i := by
  change coordinatePartial (f - g) x i = _
  rw [coordinatePartial_eq_fderiv (hf.sub hg), coordinatePartial_eq_fderiv hf,
    coordinatePartial_eq_fderiv hg]
  simpa only [sub_apply] using
    congrArg (fun A : Euclidean n →L[ℝ] ℝ => A (coordinateVector n i)) (fderiv_sub hf hg)

lemma curl_add_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {G H : VectorField} (hG : ContDiffOn ℝ 1 G E) (hH : ContDiffOn ℝ 1 H E) :
    EqOn (curl (G + H)) (curl G + curl H) E := by
  intro x hx
  have hdG (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (contDiffOn_map_coordinate hG i).differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  have hdH (i : Fin 3) : DifferentiableAt ℝ (fun y => H y i) x :=
    (contDiffOn_map_coordinate hH i).differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  ext i
  fin_cases i <;>
    simp [curl, coordinatePartial_add (hdG _) (hdH _)] <;> ring

lemma curl_sub_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {G H : VectorField} (hG : ContDiffOn ℝ 1 G E) (hH : ContDiffOn ℝ 1 H E) :
    EqOn (curl (G - H)) (curl G - curl H) E := by
  intro x hx
  have hdG (i : Fin 3) : DifferentiableAt ℝ (fun y => G y i) x :=
    (contDiffOn_map_coordinate hG i).differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  have hdH (i : Fin 3) : DifferentiableAt ℝ (fun y => H y i) x :=
    (contDiffOn_map_coordinate hH i).differentiableOn_one.differentiableAt (hE.mem_nhds hx)
  ext i
  fin_cases i <;>
    simp [curl, coordinatePartial_sub (hdG _) (hdH _)] <;> ring

lemma curl_congr_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {G H : VectorField} (he : EqOn G H E) : EqOn (curl G) (curl H) E := by
  intro x hx
  have hp (i j : Fin 3) : coordinatePartial (fun y => G y i) x j =
      coordinatePartial (fun y => H y i) x j :=
    coordinatePartial_congr_of_eqOn hE (fun y hy => congrArg (fun v => v i) (he hy)) hx j
  simp only [curl, hp]

/-- A C² scalar gauge preserves curl, with the resulting field only required
to be C¹. This is the regularity available when comparing C¹ potentials. -/
lemma curl_add_gradient_eqOn {E : Set (Euclidean 3)} (hE : IsOpen E)
    {G : VectorField} (hG : ContDiffOn ℝ 1 G E)
    {u : Euclidean 3 → ℝ} (hu : ContDiffOn ℝ 2 u E) :
    EqOn (curl (G + gradient u)) (curl G) E := by
  intro x hx
  calc
    curl (G + gradient u) x = (curl G + curl (gradient u)) x :=
      curl_add_eqOn hE hG (contDiffOn_gradient hE hu) hx
    _ = curl G x := by simp only [Pi.add_apply, curl_gradient_eq_zero hE hu hx, Pi.zero_apply,
        add_zero]

/-- Any two C¹ potentials of the same field differ by the gradient of a C²
scalar. No C³ regularity of this scalar is asserted. -/
lemma same_curl_difference_is_gradient {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {G H : VectorField} (hG : ContDiffOn ℝ 1 G E) (hH : ContDiffOn ℝ 1 H E)
    (he : EqOn (curl G) (curl H) E) :
    ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) (G - H) E := by
  apply scalarPotential_c2_of_equivalent_convex e hU hE hc (hG.sub hH)
  intro x hx
  change curl (G - H) x = (0 : VectorField) x
  rw [curl_sub_eqOn hE hG hH hx]
  simp only [Pi.sub_apply, he hx, sub_self, Pi.zero_apply]

/-- Exact reformulation of the missing endpoint relative to any fixed C¹
potential: some C² scalar gauge must make the entire field C². -/
lemma exists_c2_potential_iff_exists_c2_gauge {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {F G : VectorField} (hG : ContDiffOn ℝ 1 G E) (hcurl : EqOn (curl G) F E) :
    (∃ H : VectorField, ContDiffOn ℝ 2 H E ∧ EqOn (curl H) F E) ↔
      ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧
        ContDiffOn ℝ 2 (G + gradient u) E := by
  constructor
  · rintro ⟨H, hH, hHcurl⟩
    obtain ⟨u, hu, hgrad⟩ := same_curl_difference_is_gradient e hU hE hc
      (hH.of_le (by norm_num)) hG (hHcurl.trans hcurl.symm)
    refine ⟨u, hu, hH.congr ?_⟩
    intro x hx
    simp only [Pi.add_apply, hgrad hx, Pi.sub_apply, add_sub_cancel]
  · rintro ⟨u, hu, hreg⟩
    exact ⟨G + gradient u, hreg, (curl_add_gradient_eqOn hE hG hu).trans hcurl⟩

/-- A counterexample must obstruct every C² scalar gauge, not merely the
zero gauge or a distinguished potential chosen by an elliptic equation. -/
lemma no_c2_potential_iff_all_gauges_fail {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {F G : VectorField} (hG : ContDiffOn ℝ 1 G E) (hcurl : EqOn (curl G) F E) :
    (¬ ∃ H : VectorField, ContDiffOn ℝ 2 H E ∧ EqOn (curl H) F E) ↔
      ∀ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E →
        ¬ ContDiffOn ℝ 2 (G + gradient u) E := by
  rw [exists_c2_potential_iff_exists_c2_gauge e hU hE hc hG hcurl]
  simp only [not_exists, not_and]

/-- Even when a field has a C² potential, a C² scalar gauge with a non-C²
gradient produces a non-C² potential of the same field. -/
lemma rough_gauge_preserves_potential {E : Set (Euclidean 3)} (hE : IsOpen E)
    {F G : VectorField} (hG : ContDiffOn ℝ 2 G E) (hcurl : EqOn (curl G) F E)
    {u : Euclidean 3 → ℝ} (hu : ContDiffOn ℝ 2 u E)
    (hrough : ¬ ContDiffOn ℝ 2 (gradient u) E) :
    ContDiffOn ℝ 1 (G + gradient u) E ∧
      EqOn (curl (G + gradient u)) F E ∧
      ¬ ContDiffOn ℝ 2 (G + gradient u) E := by
  have hG₁ : ContDiffOn ℝ 1 G E := hG.of_le (by norm_num)
  refine ⟨hG₁.add (contDiffOn_gradient hE hu),
    (curl_add_gradient_eqOn hE hG₁ hu).trans hcurl, ?_⟩
  intro hreg
  apply hrough
  simpa only [Pi.add_apply, add_sub_cancel_left] using hreg.sub hG

end Rudin.PMA.Chapter10.GaugeResearch
