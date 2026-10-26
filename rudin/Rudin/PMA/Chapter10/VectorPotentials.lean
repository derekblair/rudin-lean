import Rudin.PMA.Chapter10.VectorFormDerivatives
import Rudin.PMA.Chapter10.DiffeomorphicExactness
import Rudin.PMA.Chapter10.PotentialRegularity

noncomputable section
set_option autoImplicit false
open Set Function
open scoped BigOperators

namespace Rudin.PMA.Chapter10
open Chapter09

/-- The exact four assertions of source 10.43. In particular, the last clause
retains the printed C² vector-potential conclusion. The C¹ vector-potential
helper below is not a proof of that stronger clause. -/
def pma10_43_contract : Prop :=
  (∀ (E : Set (Euclidean 3)) (u : Euclidean 3 → ℝ),
    IsOpen E → ContDiffOn ℝ 2 u E → EqOn (curl (gradient u)) 0 E) ∧
  (∀ (E : Set (Euclidean 3)) (G : VectorField),
    IsOpen E → ContDiffOn ℝ 2 G E → EqOn (divergence (curl G)) 0 E) ∧
  (∀ (U E : Set (Euclidean 3)) (e : C2DomainEquivalence U E) (F : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E → EqOn (curl F) 0 E →
      ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) F E) ∧
  (∀ (U E : Set (Euclidean 3)) (e : C2DomainEquivalence U E) (F : VectorField),
    IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E → EqOn (divergence F) 0 E →
      ∃ G : VectorField, ContDiffOn ℝ 2 G E ∧ EqOn (curl G) F E)

lemma gradient_eqOn_iff_form_derivative {E : Set (Euclidean 3)}
    (u : Euclidean 3 → ℝ) (F : VectorField) :
    EqOn (gradient u) F E ↔
      EqOn (exteriorDerivative (scalarForm u)) (vectorOneForm F) E := by
  rw [exteriorDerivative_scalarForm_gradient]
  exact (vectorOneForm_eqOn_iff (gradient u) F).symm

lemma curl_eqOn_iff_form_derivative {E : Set (Euclidean 3)} (hE : IsOpen E)
    {G : VectorField} (hG : ContDiffOn ℝ 1 G E) (F : VectorField) :
    EqOn (curl G) F E ↔
      EqOn (exteriorDerivative (vectorOneForm G)) (vectorTwoForm F) E := by
  have hd := exteriorDerivative_vectorOneForm hE hG
  constructor
  · intro h
    exact hd.trans ((vectorTwoForm_eqOn_iff (curl G) F).mpr h)
  · intro h
    exact (vectorTwoForm_eqOn_iff (curl G) F).mp (hd.symm.trans h)

lemma curl_gradient_eq_zero {E : Set (Euclidean 3)} (hE : IsOpen E)
    {u : Euclidean 3 → ℝ} (hu : ContDiffOn ℝ 2 u E) :
    EqOn (curl (gradient u)) 0 E := by
  have hg : ContDiffOn ℝ 1 (gradient u) E := contDiffOn_gradient hE hu
  apply (vectorOneForm_closed_iff hE hg).mp
  refine ⟨isCFormOn_vectorOneForm hg, ?_⟩
  intro x hx
  rw [vectorOneForm_gradient, ← exteriorDerivative_scalarForm]
  exact exteriorDerivative_twice_eq_zero hE (isCFormOn_scalarForm hu) hx

lemma divergence_curl_eq_zero {E : Set (Euclidean 3)} (hE : IsOpen E)
    {G : VectorField} (hG : ContDiffOn ℝ 2 G E) :
    EqOn (divergence (curl G)) 0 E := by
  have hG₁ : ContDiffOn ℝ 1 G E := hG.of_le (by norm_num)
  have hc : ContDiffOn ℝ 1 (curl G) E := contDiffOn_curl hE hG
  apply (vectorTwoForm_closed_iff hE hc).mp
  refine ⟨isCFormOn_vectorTwoForm hc, ?_⟩
  intro x hx
  have he := exteriorDerivative_vectorOneForm hE hG₁
  calc
    exteriorDerivative (vectorTwoForm (curl G)) x =
        exteriorDerivative (exteriorDerivative (vectorOneForm G)) x :=
      (exteriorDerivative_congr_of_eqOn hE he hx).symm
    _ = 0 := exteriorDerivative_twice_eq_zero hE (isCFormOn_vectorOneForm hG) hx

lemma formCoefficient_vectorOneForm_singleton (F : VectorField)
    (x : Euclidean 3) (i : Fin 3) :
    formCoefficient (vectorOneForm F) {i} x = F x i := by
  have he := congrArg (fun G : VectorField => G x i) (oneFormVector_vectorOneForm F)
  simpa only [oneFormVector, coordEquivEuclidean_apply_coordinate] using he

/-- The scalar converse has the full printed C² regularity: every first
partial of the C¹ primitive is a component of the prescribed C¹ field. -/
lemma scalarPotential_c2_of_equivalent_convex {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) (hz : EqOn (curl F) 0 E) :
    ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) F E := by
  have hω := isCFormOn_vectorOneForm hF
  have hex : IsExactOn E 1 (vectorOneForm F) :=
    pma10_40.2 3 3 U E e hU hE hc 0 (vectorOneForm F)
      ((vectorOneForm_closed_iff hE hF).mpr hz)
  obtain ⟨u, hu, hp⟩ := (one_form_exact_iff_potential hE hω.isFormOn).mp hex
  have hpu : ∀ x ∈ E, ∀ i : Fin 3, coordinatePartial u x i = F x i := by
    intro x hx i
    exact (hp x hx i).trans (formCoefficient_vectorOneForm_singleton F x i)
  refine ⟨u, contDiffOn_two_of_coordinatePartials_eq hE hu hF hpu, ?_⟩
  intro x hx
  ext i
  simpa only [gradient, coordEquivEuclidean_apply_coordinate] using hpu x hx i

/-- The C¹ vector potential that follows from the proved C¹ Poincaré lemma.
This is deliberately separate from the stronger C² output in source10.43. -/
lemma vectorPotential_c1_of_equivalent_convex {U E : Set (Euclidean 3)}
    (e : C2DomainEquivalence U E) (hU : IsOpen U) (hE : IsOpen E) (hc : Convex ℝ U)
    {F : VectorField} (hF : ContDiffOn ℝ 1 F E) (hz : EqOn (divergence F) 0 E) :
    ∃ G : VectorField, ContDiffOn ℝ 1 G E ∧ EqOn (curl G) F E := by
  have hex : IsExactOn E 2 (vectorTwoForm F) :=
    pma10_40.2 3 3 U E e hU hE hc 1 (vectorTwoForm F)
      ((vectorTwoForm_closed_iff hE hF).mpr hz)
  obtain ⟨η, hη, hdη⟩ := hex
  have hG : ContDiffOn ℝ 1 (oneFormVector η) E := contDiffOn_oneFormVector hη
  refine ⟨oneFormVector η, hG, (curl_eqOn_iff_form_derivative hE hG F).mpr ?_⟩
  have he : EqOn (vectorOneForm (oneFormVector η)) η E :=
    vectorOneForm_oneFormVector hη.isFormOn
  intro x hx
  exact (exteriorDerivative_congr_of_eqOn hE he hx).trans (hdη hx)

theorem pma10_43_forward :
    (∀ (E : Set (Euclidean 3)) (u : Euclidean 3 → ℝ),
      IsOpen E → ContDiffOn ℝ 2 u E → EqOn (curl (gradient u)) 0 E) ∧
    (∀ (E : Set (Euclidean 3)) (G : VectorField),
      IsOpen E → ContDiffOn ℝ 2 G E → EqOn (divergence (curl G)) 0 E) :=
  ⟨fun _ _ hE hu => curl_gradient_eq_zero hE hu,
    fun _ _ hE hG => divergence_curl_eq_zero hE hG⟩

theorem pma10_43_scalar_converse :
    ∀ (U E : Set (Euclidean 3)) (e : C2DomainEquivalence U E) (F : VectorField),
      IsOpen U → IsOpen E → Convex ℝ U → ContDiffOn ℝ 1 F E → EqOn (curl F) 0 E →
        ∃ u : Euclidean 3 → ℝ, ContDiffOn ℝ 2 u E ∧ EqOn (gradient u) F E :=
  fun _ _ e _ hU hE hc hF hz => scalarPotential_c2_of_equivalent_convex e hU hE hc hF hz

end Rudin.PMA.Chapter10
